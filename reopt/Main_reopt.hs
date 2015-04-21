{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import           Control.Lens
import           Control.Monad
import           Control.Monad.State.Strict
import qualified Data.ByteString as B
import           Data.Elf
import           Data.Foldable (traverse_)
import           Data.Map (Map)
import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Version
import           GHC.TypeLits
import           Numeric (showHex)
import           System.Console.CmdArgs.Explicit
import           System.Environment (getArgs)
import           System.Exit (exitFailure)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Int
import           Data.Word

import           Paths_reopt (version)
import           Data.Type.Equality as Equality

import           Flexdis86 (InstructionInstance(..))
import           Reopt
import           Reopt.Memory
import           Reopt.Semantics.AbsDomain
import           Reopt.Semantics.CFGDiscovery
import           Reopt.Semantics.DeadRegisterElimination
import           Reopt.Semantics.Monad (Type(..))
import           Reopt.Semantics.Representation
import qualified Reopt.Semantics.StateNames as N

------------------------------------------------------------------------
-- Args

-- | Action to perform when running
data Action
   = DumpDisassembly -- ^ Print out disassembler output only.
   | ShowCFG         -- ^ Print out control-flow microcode.
   | ShowCFGAI       -- ^ Print out control-flow microcode + abs domain
   | ShowGaps        -- ^ Print out gaps in discovered blocks
   | ShowHelp        -- ^ Print out help message
   | ShowVersion     -- ^ Print out version

-- | Command line arguments.
data Args = Args { _reoptAction :: Action
                 , _programPath :: FilePath
                 }

-- | Action to perform when running.
reoptAction :: Simple Lens Args Action
reoptAction = lens _reoptAction (\s v -> s { _reoptAction = v })

-- | Action to perform when running.
programPath :: Simple Lens Args FilePath
programPath = lens _programPath (\s v -> s { _programPath = v })

-- | Initial arguments if nothing is specified.
defaultArgs :: Args
defaultArgs = Args { _reoptAction = ShowCFG
                   , _programPath = ""
                   }

------------------------------------------------------------------------
-- Argument processing

disassembleFlag :: Flag Args
disassembleFlag = flagNone [ "disassemble", "d" ] upd help
  where upd  = reoptAction .~ DumpDisassembly
        help = "Disassemble code segment of binary, and print it in an objdump style."

cfgFlag :: Flag Args
cfgFlag = flagNone [ "cfg", "c" ] upd help
  where upd  = reoptAction .~ ShowCFG
        help = "Print out recovered control flow graph of executable."

cfgAIFlag :: Flag Args
cfgAIFlag = flagNone [ "ai", "a" ] upd help
  where upd  = reoptAction .~ ShowCFGAI
        help = "Print out recovered control flow graph + AI of executable."

gapFlag :: Flag Args
gapFlag = flagNone [ "gap", "g" ] upd help
  where upd  = reoptAction .~ ShowGaps
        help = "Print out gaps in the recovered  control flow graph of executable."

arguments :: Mode Args
arguments = mode "reopt" defaultArgs help filenameArg flags
  where help = reoptVersion ++ "\n" ++ copyrightNotice
        flags = [ disassembleFlag
                , cfgFlag
                , cfgAIFlag
                , gapFlag
                , flagHelpSimple (reoptAction .~ ShowHelp)
                , flagVersion (reoptAction .~ ShowVersion)
                ]

reoptVersion :: String
reoptVersion = "Reopt binary reoptimizer (reopt) "
             ++ versionString ++ ", June 2014."
  where [h,l,r] = versionBranch version
        versionString = show h ++ "." ++ show l ++ "." ++ show r

copyrightNotice :: String
copyrightNotice = "Copyright 2014 Galois, Inc. All rights reserved."

filenameArg :: Arg Args
filenameArg = Arg { argValue = setFilename
                  , argType = "FILE"
                  , argRequire = False
                  }
  where setFilename :: String -> Args -> Either String Args
        setFilename nm a = Right (a & programPath .~ nm)

getCommandLineArgs :: IO Args
getCommandLineArgs = do
  argStrings <- getArgs
  case process arguments argStrings of
    Left msg -> do
      putStrLn msg
      exitFailure
    Right v -> return v

------------------------------------------------------------------------
-- Execution

showUsage :: IO ()
showUsage = do
  putStrLn "For help on using reopt, run \"reopt --help\"."

readElf64 :: FilePath -> IO (Elf Word64)
readElf64 path = do
  when (null path) $ do
    putStrLn "Please specify a binary."
    showUsage
    exitFailure
  bs <- B.readFile path
  case parseElf bs of
    Left (_,msg) -> do
      putStrLn $ "Error reading " ++ path ++ ":"
      putStrLn $ "  " ++ msg
      exitFailure
    Right (Elf32 _) -> do
      putStrLn "32-bit executables are not yet supported."
      exitFailure
    Right (Elf64 e) ->
      return e

dumpDisassembly :: FilePath -> IO ()
dumpDisassembly path = do
  e <- readElf64 path
  let sections = filter isCodeSection $ e^..elfSections
  when (null sections) $ do
    putStrLn "Binary contains no executable sections."
  mapM_ printSectionDisassembly sections
  -- print $ Set.size $ instructionNames sections
  --print $ Set.toList $ instructionNames sections

getCFG :: FilePath -> IO (Memory Word64, (CFG, Set CodeAddr))
getCFG path =  do
  e <- readElf64 path
  mi <- elfInterpreter e
  case mi of
    Nothing ->
      return ()
    Just{} ->
      fail "reopt does not yet support generating CFGs from dynamically linked executables."
  -- Build model of executable memory from elf.
  mem <- loadElf e
  -- Get list of code locations to explore starting from entry points (i.e., eltEntry)
  return $ (mem, cfgFromAddress mem (elfEntry e))

getCFGAI :: (PrettyF d, AbsDomain d) => FilePath
            -> IO (Memory Word64, (CFG, Set CodeAddr, AbsState d))
getCFGAI path =  do
  e <- readElf64 path
  mi <- elfInterpreter e
  case mi of
    Nothing ->
      return ()
    Just{} ->
      fail "reopt does not yet support generating CFGs from dynamically linked executables."
  -- Build model of executable memory from elf.
  mem <- loadElf e
  -- Get list of code locations to explore starting from entry points (i.e., eltEntry)
  return $ (mem, absInt mem (elfEntry e))

isInterestingCode :: Memory Word64 -> (CodeAddr, Maybe CodeAddr) -> Bool
isInterestingCode mem (start, Just end) = go start end
  where
    isNop ii = (iiOp ii == "nop")
               || (iiOp ii == "xchg" &&
                   case iiArgs ii of
                    [x, y] -> x == y
                    _      -> False)

    go b e | b < e = case readInstruction mem b of
                      Left _           -> False -- FIXME: ignore illegal sequences?
                      Right (ii, next) -> not (isNop ii) || go next e
           | otherwise = False

isInterestingCode _ _ = True -- Last bit

showGaps :: FilePath ->  IO ()
showGaps path = do (mem, (cfg, ends)) <- getCFG path
                   let blocks = [ addr | DecompiledBlock addr <- Map.keys (cfg ^. cfgBlocks) ]
                   let gaps = filter (isInterestingCode mem)
                              $ out_gap blocks (Set.elems ends)

                   mapM_ (print . pretty . ppOne) gaps
  where
    ppOne (start, m_end) = text ("[" ++ showHex start "..") <>
                           case m_end of
                            Nothing -> text "END)"
                            Just e  -> text (showHex e ")")

    in_gap start bs@(b:_) ess = (start, Just b) : out_gap bs (dropWhile (<= b) ess)
    in_gap start [] _ = [(start, Nothing)]

    out_gap (b:bs') ess@(e:es')
      | b < e          = out_gap bs' ess
      | b == e         = out_gap bs' es'
    out_gap bs (e:es') = in_gap e bs es'
    out_gap _ _        = []

showCFG :: FilePath -> IO ()
showCFG path = do
  (_, (g0, _)) <- getCFG path
  let g = eliminateDeadRegisters g0
  print (pretty g)  
{-
  putStrLn $ "Found potential calls: " ++ show (Map.size (cfgCalls g))

  let rCalls = reverseEdges (cfgCalls g)

  let rEdgeMap = reverseEdges (cfgSuccessors g)


  let sources = getTargets (Map.keys rCalls) rEdgeMap

  forM_ (Set.toList sources) $ \a -> do
    let Just b = findBlock g (DecompiledBlock a)
    when (hasCall b == False) $ do
      print $ "Found start " ++ showHex a ""
      print (pretty b)
-}

showCFGAndAI :: FilePath -> IO ()
showCFGAndAI path = do
  (_, (g0, _, abst :: AbsState StackHeapSet)) <- getCFGAI path
  let g  = eliminateDeadRegisters g0
      ppOne b = vcat [case (blockLabel b, Map.lookup (blockParent (blockLabel b)) abst) of
                       (DecompiledBlock _, Just ab) -> pretty ab
                       _                            -> empty
                     , pretty b]
                
        where
          k = blockLabel b
                  
  print $ vcat (map ppOne $ Map.elems (g^.cfgBlocks))

hasCall :: Block -> Bool
hasCall b = any isCallComment (blockStmts b)
  where isCallComment (Comment s) = "call" `isInfixOf` s
        isCallComment _ = False

------------------------------------------------------------------------
-- Function determination

{-
A procedure is a contiguous set of blocks that:
 * Has a unique entry point.
 * Returns to the address stored at the address "sp".
-}


type AbsStack = Map Int64 Word64

emptyAbsStack :: AbsStack
emptyAbsStack = Map.empty

{-
data ProcState
   = ProcState { addrStart ::
               }


-- Map BlockLabel AbsStack

-- Returns map that maps address at start of procedure to the
-- set of labels within that procedure.
findProcedure :: CFG Block
                 -- ^ CFG
              -> Set Word64
                 -- ^ Potential call locations
              -> Map Word64 (Set BlockLabel)
findProcudure g s = undefined g s
-}



------------------------------------------------------------------------
-- Call detection


-- | @v `asOffsetOf` b@ returns @Just o@ if @v@ can be interpreted
-- as a constant offset from a term at base @b@, and @Nothing@
-- otherwise.
asOffsetOf :: Value tp -> Value tp -> Maybe Integer
asOffsetOf v base
  | v == base = Just 0
  | Just (BVAdd _ v' (BVValue _ o)) <- valueAsApp v
  , v' == base = Just o
  | otherwise = Nothing

runStmt :: Stmt -> State AbsStack ()
runStmt (Write (MemLoc a _) (BVValue _ v))
  | Just o <- a `asOffsetOf` (Initial N.rsp) = do
    modify $ Map.insert (fromInteger o) (fromInteger v)
runStmt _ = return ()

lookupStack :: Int64 -> AbsStack -> Maybe Word64
lookupStack o s = Map.lookup o s

decompiledBlocks :: CFG -> [Block]
decompiledBlocks g =
  [ b | b <- Map.elems (g^.cfgBlocks)
      , DecompiledBlock _ <- [blockLabel b]
      ]

findBlock :: CFG -> BlockLabel -> Maybe Block
findBlock g l = Map.lookup l (g^.cfgBlocks)

-- | Maps blocks to set of concrete addresses they may call.
type CallState = Map CodeAddr (Set CodeAddr)

addAddrs :: CodeAddr -> Value (BVType 64) -> State CallState ()
addAddrs b (BVValue _ o) =
  modify $ Map.insertWith Set.union b (Set.singleton (fromInteger o))
addAddrs _ _ = return ()

detectCalls :: CFG -> Block -> AbsStack -> State CallState ()
detectCalls g b initStack = do
  let finStack = flip execState initStack $
                   traverse_ runStmt (blockStmts b)
  case blockTerm b of
    FetchAndExecute x86_state -> do
      let rsp = x86_state^.register N.rsp
      case rsp `asOffsetOf` (Initial N.rsp) of
        Just o | Just _ <- lookupStack (fromInteger o) finStack -> do
          addAddrs (blockParent (blockLabel b)) (x86_state^.curIP)
        _ -> return ()
    Branch _ x y -> do
      let Just xb = findBlock g x
          Just yb = findBlock g y
      detectCalls g xb finStack
      detectCalls g yb finStack

cfgCalls :: CFG -> CallState
cfgCalls g = flip execState Map.empty $ do
  traverse_ (\b -> detectCalls g b emptyAbsStack) (decompiledBlocks g)

detectSuccessors :: CFG -> Block -> State CallState ()
detectSuccessors g b = do
  case blockTerm b of
    FetchAndExecute x86_state -> do
      addAddrs (blockParent (blockLabel b)) (x86_state^.curIP)
    Branch _ x y -> do
      let Just xb = findBlock g x
          Just yb = findBlock g y
      detectSuccessors g xb
      detectSuccessors g yb

cfgSuccessors :: CFG -> CallState
cfgSuccessors g = flip execState Map.empty $ do
  traverse_ (detectSuccessors g) (decompiledBlocks g)

toAllList :: Map a (Set b) -> [(a,b)]
toAllList m = do
  (k,s) <- Map.toList m
  v <- Set.toList s
  return (k,v)

reverseEdges :: Ord a => Map a (Set a) -> Map a (Set a)
reverseEdges m = flip execState Map.empty $ do
  forM_ (toAllList m) $ \(k,v) -> do
    modify $ Map.insertWith Set.union v (Set.singleton k)

getTargets :: (Ord a, Ord b) => [a] -> Map a (Set b) -> Set b
getTargets l m = foldl' Set.union Set.empty $
  fmap (fromMaybe Set.empty . (`Map.lookup` m)) l

------------------------------------------------------------------------
-- Pattern match on stack pointer possibilities.

{-
printSP :: Block -> IO ()
printSP b = do
  case blockTerm b of
    Branch _ _ _ -> return ()
    FetchAndExecute s -> do
      let rsp_val = s^.register N.rsp
      case rsp_val of
        _ | Initial v <- rsp_val
          , Just Refl <- testEquality v N.rsp ->
            return ()
        _ | Just (BVAdd _ (Initial r) BVValue{}) <- valueAsApp rsp_val
          , Just Refl <- testEquality r N.rsp -> do
            return ()
        _ | Just (BVAdd _ (Initial r) BVValue{}) <- valueAsApp rsp_val
          , Just Refl <- testEquality r N.rbp -> do
            return ()
          | otherwise -> do
            print $ "Block " ++ show (pretty (blockLabel b))
            print $ "RSP = " ++ show (pretty rsp_val)
      let rbp_val = s^.register N.rbp
      case rbp_val of
           -- This leaves the base pointer unchanged.  It is likely an
           -- internal block.
        _ | Initial v <- rbp_val
          , Just Refl <- testEquality v N.rbp ->
            return ()
           -- This assigns the base pointer the current stack.
           -- It is likely a function entry point
        _ | Just (BVAdd _ (Initial r) BVValue{}) <- valueAsApp rbp_val
          , Just Refl <- testEquality r N.rsp -> do
            return ()
           -- This block assigns the base pointer a value from the stack.
           -- It is likely a function exit.
        _ | AssignedValue (assignRhs -> Read (MemLoc addr _)) <- rbp_val
          , Initial v <- addr
          , Just Refl <- testEquality v N.rbp -> do
            return ()
           -- This block assigns the base pointer a value from the stack.
           -- It is likely a function exit.
        _ | AssignedValue (assignRhs -> Read (MemLoc addr _)) <- rbp_val
          , Just (BVAdd _ (Initial v) BVValue{}) <- valueAsApp addr
          , Just Refl <- testEquality v N.rsp -> do
            return ()

        _ | otherwise -> do
            print $ "Block " ++ show (pretty (blockLabel b))
            print $ "RBP = " ++ show (pretty rbp_val)
-}

{-
printIP :: Block -> IO ()
printIP b =
    case blockTerm b of
      Branch _ _ _ -> return ()
      FetchAndExecute s ->
        case s^.cur of
          Initial a -> do
            print $ "Block " ++ show (pretty (blockLabel b))
            print $ "Next IP " ++ show a
          BVValue _ _ -> return ()
          AssignedValue a -> do
            print $ "Block " ++ show (pretty (blockLabel b))
            print $ "Next IP: " ++ show (pretty a)
-}

main :: IO ()
main = do
  args <- getCommandLineArgs
  case args^.reoptAction of
    DumpDisassembly -> do
      dumpDisassembly (args^.programPath)
    ShowCFG -> do
      showCFG (args^.programPath)
    ShowCFGAI -> do
      showCFGAndAI (args^.programPath)      
    ShowGaps -> showGaps (args^.programPath)
    ShowHelp ->
      print $ helpText [] HelpFormatDefault arguments
    ShowVersion ->
      putStrLn (modeHelp arguments)
