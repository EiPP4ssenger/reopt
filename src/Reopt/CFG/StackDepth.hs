{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Reopt.CFG.StackDepth
  ( maximumStackDepth
  , StackDepthValue(..)
  , StackDepthOffset(..)
  , stackDepthOffsetValue
  , maxConstStackDepth
  ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Data.Foldable as Fold (traverse_)
import           Data.Int
import           Data.List (partition)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Monoid (Any(..))
import           Data.Parameterized.Classes
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Word
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.AbsDomain.AbsState
import           Data.Macaw.Discovery.Info
import           Data.Macaw.CFG
import           Data.Macaw.Memory (MemWidth)
import           Data.Macaw.Types

import           Reopt.Machine.X86State

$(pure [])

-- | A symbolic value indicating a stack offset.
data StackDepthOffset arch ids
   = Pos (BVValue arch ids (ArchAddrWidth arch))
   | Neg (BVValue arch ids (ArchAddrWidth arch))

$(pure [])

deriving instance OrdF  (ArchReg arch) => Eq (StackDepthOffset arch ids)
deriving instance OrdF  (ArchReg arch) => Ord (StackDepthOffset arch ids)
deriving instance ShowF (ArchReg arch) => Show (StackDepthOffset arch ids)

$(pure [])

stackDepthOffsetValue :: StackDepthOffset arch ids -> BVValue arch ids (ArchAddrWidth arch)
stackDepthOffsetValue (Pos v) = v
stackDepthOffsetValue (Neg v) = v

$(pure [])

negateStackDepthOffset :: StackDepthOffset arch ids -> StackDepthOffset arch ids
negateStackDepthOffset (Pos x) = Neg x
negateStackDepthOffset (Neg x) = Pos x

$(pure [])

isNegativeDepth :: StackDepthOffset arch ids -> Bool
isNegativeDepth (Neg _) = True
isNegativeDepth _ = False

$(pure [])

-- One stack expression, basically staticPart + \Sigma dynamicPart
data StackDepthValue arch ids = SDV { staticPart :: !Int64
                                    , dynamicPart :: !(Set (StackDepthOffset arch ids))
                                    }

deriving instance OrdF (ArchReg arch) => Eq (StackDepthValue arch ids)
deriving instance OrdF (ArchReg arch) => Ord (StackDepthValue arch ids)
deriving instance ShowF (ArchReg arch) => Show (StackDepthValue arch ids)

$(pure [])

instance ShowF (ArchReg arch) => Pretty (StackDepthValue arch ids) where
  pretty sdv = integer (fromIntegral $ staticPart sdv)
               <+> go (Set.toList $ dynamicPart sdv)
    where
      go []           = mempty
      go (Pos x : xs) = text "+" <+> pretty x <+> go xs
      go (Neg x : xs) = text "-" <+> pretty x <+> go xs

$(pure [])

-- | Create a stack depth for the givne interger
constantDepthValue :: Int64 -> StackDepthValue arch ids
constantDepthValue c = SDV c Set.empty

$(pure [])

-- | Add two stack depth values
addStackDepthValue :: OrdF (ArchReg arch)
                   => StackDepthValue arch ids
                   -> StackDepthValue arch ids
                   -> StackDepthValue arch ids
addStackDepthValue sdv1 sdv2  = SDV (staticPart sdv1 + staticPart sdv2)
                                    (dynamicPart sdv1 `Set.union` dynamicPart sdv2)

$(pure [])

-- | Negate a stack depth
negateStackDepthValue :: OrdF (ArchReg arch)
                      => StackDepthValue arch ids
                      -> StackDepthValue arch ids
negateStackDepthValue sdv = SDV { staticPart  = - (staticPart sdv)
                                , dynamicPart = Set.map negateStackDepthOffset (dynamicPart sdv)
                                }

$(pure [])

-- | v1 `subsumes` v2 if a stack of depth v1 is always larger than a
-- stack of depth v2.  Note that we are interested in negative values
-- primarily.
subsumes :: OrdF (ArchReg arch) => StackDepthValue arch ids -> StackDepthValue arch ids -> Bool
subsumes v1 v2
  | dynamicPart v2 `Set.isSubsetOf` dynamicPart v1 = staticPart v1 <= staticPart v2
  -- FIXME: subsets etc.
  | otherwise = False

$(pure [])

-- could do this online, this helps with debugging though.
minimizeStackDepthValues :: forall arch ids
                         .  OrdF (ArchReg arch)
                         => Set (StackDepthValue arch ids)
                         -> Set (StackDepthValue arch ids)
minimizeStackDepthValues s = Set.fromList (Set.fold go [] s)
  where
    discardPositive v = v { dynamicPart = Set.filter isNegativeDepth (dynamicPart v) }
    -- FIXME: can we use ordering to simplify this?
    go :: StackDepthValue arch ids -> [StackDepthValue arch ids] -> [StackDepthValue arch ids]
    go v0 xs | dominated = xs'
             | otherwise = v : xs'
      where v = discardPositive v0
            (_subs, xs') = partition (subsumes v) xs
            dominated   = any (`subsumes` v) xs'

-- -----------------------------------------------------------------------------

$(pure [])

-- For now this is just the set of stack addresses referenced by the
-- program --- note that as it is partially symbolic, we can't always
-- statically determine the stack depth (might depend on arguments, for example).
type BlockStackDepths arch ids = Set (StackDepthValue arch ids)

$(pure [])

-- We use BlockLabel but only really need CodeAddr (sub-blocks shouldn't appear)
data StackDepthState arch ids
   = SDS { _blockInitStackPointers :: !(Map (ArchSegmentedAddr arch) (StackDepthValue arch ids))
         , _blockStackRefs :: !(BlockStackDepths arch ids)
         , _blockFrontier  :: ![ArchSegmentedAddr arch]
           -- ^ Set of blocks to explore next.
         }

$(pure [])

-- | Maps blocks already seen to the expected depth at the start of the block.
blockInitStackPointers :: Simple Lens (StackDepthState arch ids)
                                      (Map (ArchSegmentedAddr arch) (StackDepthValue arch ids))
blockInitStackPointers = lens _blockInitStackPointers (\s v -> s { _blockInitStackPointers = v })

$(pure [])

blockStackRefs :: Simple Lens (StackDepthState arch ids) (BlockStackDepths arch ids)
blockStackRefs = lens _blockStackRefs (\s v -> s { _blockStackRefs = v })

$(pure [])

-- | Set of blocks to visit next.
blockFrontier :: Simple Lens (StackDepthState arch ids) [ArchSegmentedAddr arch]
blockFrontier = lens _blockFrontier (\s v -> s { _blockFrontier = v })

-- ----------------------------------------------------------------------------------------

$(pure [])

type StackDepthM arch ids a = ExceptT String (State (StackDepthState arch ids)) a

$(pure [])

addBlock :: (OrdF (ArchReg arch), ShowF (ArchReg arch))
         => ArchSegmentedAddr arch
         -> StackDepthValue arch ids
         -> StackDepthM arch ids ()
addBlock a start = do
  let lbl = mkRootBlockLabel a
  ptrs <- use blockInitStackPointers
  case Map.lookup a ptrs of
    Nothing     -> do
      blockInitStackPointers %= Map.insert a start
      blockFrontier %= (a:)
    Just old_start
      | start == old_start ->
        return ()
      | otherwise       ->
        throwError $ "Block stack depth mismatch at " ++ show (pretty lbl) ++ ": "
             ++ show (pretty start) ++ " and " ++ show (pretty old_start)

$(pure [])

addDepth :: OrdF (ArchReg arch) => Set (StackDepthValue arch ids) -> StackDepthM arch ids ()
addDepth v = blockStackRefs %= Set.union v

------------------------------------------------------------------------
-- Stack pointer detection

$(pure [])

-- | Return true if value references stack pointer
valueHasSP :: forall ids utp . Value X86_64 ids utp -> Bool
valueHasSP v0 =
   case v0 of
     BVValue _sz _i -> False
     RelocatableValue{} -> False
     Initial r      -> testEquality r sp_reg /= Nothing
     AssignedValue (Assignment _ rhs) -> goAssignRHS rhs
  where
    goAssignRHS :: forall tp. AssignRhs X86_64 ids tp -> Bool
    goAssignRHS v =
      case v of
        EvalApp a -> getAny $ foldApp (Any . valueHasSP)  a
        EvalArchFn (MemCmp _sz cnt src dest rev) _ ->
          or [ valueHasSP cnt, valueHasSP src, valueHasSP dest, valueHasSP rev ]
        _ -> False

$(pure [])


parseStackPointer' :: StackDepthValue X86_64 ids
                   -> BVValue X86_64 ids (ArchAddrWidth X86_64)
                   -> StackDepthValue X86_64 ids
parseStackPointer' sp0 addr
  -- assert sp occurs in at most once in either x and y
  | Just (BVAdd _ x y) <- valueAsApp addr =
      addStackDepthValue (parseStackPointer' sp0 x)
                         (parseStackPointer' sp0 y)

  | Just (BVSub _ x y) <- valueAsApp addr =
      addStackDepthValue (parseStackPointer' sp0 x)
                         (negateStackDepthValue (parseStackPointer' sp0 y))
  | BVValue _ i <- addr = constantDepthValue (fromIntegral i)
  | Initial n <- addr
  , Just Refl <- testEquality n sp_reg = sp0
  | otherwise = SDV { staticPart = 0
                    , dynamicPart = Set.singleton (Pos addr)
                    }

$(pure [])

-- FIXME: performance
parseStackPointer :: StackDepthValue X86_64 ids
                  -> BVValue X86_64 ids 64
                  -> Set (StackDepthValue X86_64 ids)
parseStackPointer sp0 addr0
  | valueHasSP addr0 = Set.singleton (parseStackPointer' sp0 addr0)
  | otherwise        = Set.empty

-- -----------------------------------------------------------------------------

$(pure [])

goStmt :: StackDepthValue X86_64 ids -> Stmt X86_64 ids -> StackDepthM X86_64 ids ()
goStmt init_sp (AssignStmt (Assignment _ (ReadMem addr _))) =
  addDepth $ parseStackPointer init_sp addr
goStmt init_sp (WriteMem addr v) = do
  addDepth $ parseStackPointer init_sp addr
  case testEquality (typeRepr v) (knownType :: TypeRepr (BVType 64)) of
    Just Refl -> addDepth $ parseStackPointer init_sp v
    _ -> return ()
goStmt _ _ = return ()

$(pure [])

-- | Check each general purpose register to see if we should add a stack pointer
addStateVars :: StackDepthValue X86_64 ids
             -> RegState X86Reg (Value X86_64 ids)
             -> StackDepthM X86_64 ids ()
addStateVars init_sp s = do
  forM_ gpRegList $ \r -> do
    addDepth $ parseStackPointer init_sp (s ^. boundValue r)

$(pure [])

recoverBlock :: ParsedBlockRegion X86_64 ids
                -- ^ Region to recover blocks in
             -> StackDepthValue X86_64 ids
                -- ^ Value of initial stack pointer
             -> Word64
                -- ^ Index of block
             -> StackDepthM X86_64 ids ()
recoverBlock region init_sp idx = do
  Just b <- return $ Map.lookup idx (regionBlockMap region)
  -- overapproximates by viewing all registers as uses of the
  -- sp between blocks
  traverse_ (goStmt init_sp) (pblockStmts b)
  case pblockTerm b of
    ParsedTranslateError _ ->
      throwError "Cannot identify stack depth in code where translation error occurs"
    ClassifyFailure _ ->
      throwError $ "Classification failed in StackDepth: " ++ show (regionAddr region)
    ParsedBranch _c x y -> do
      recoverBlock region init_sp x
      recoverBlock region init_sp y

    ParsedCall proc_state m_ret_addr -> do
      addStateVars init_sp proc_state

      let sp'  = parseStackPointer' init_sp (proc_state ^. boundValue sp_reg)
      case m_ret_addr of
        Nothing -> return ()
        Just ret_addr ->
          addBlock ret_addr (addStackDepthValue sp' $ constantDepthValue 8)

    ParsedJump proc_state tgt_addr -> do
      addStateVars init_sp proc_state
      let sp' = parseStackPointer' init_sp (proc_state ^. boundValue sp_reg)
      addBlock tgt_addr sp'

    ParsedReturn _proc_state -> do
      pure ()

    ParsedSyscall proc_state next_addr -> do
      addStateVars init_sp proc_state
      let sp'  = parseStackPointer' init_sp (proc_state ^. boundValue sp_reg)
      addBlock next_addr sp'

    ParsedLookupTable proc_state _idx vec -> do
      addStateVars init_sp proc_state
      let sp'  = parseStackPointer' init_sp (proc_state ^. boundValue sp_reg)
      traverse_ (\a -> addBlock a sp') vec

$(pure [])

-- | Explore states until we have reached end of frontier.
recoverIter :: DiscoveryFunInfo X86_64 ids
            -> StackDepthState X86_64 ids
            -> Either String (StackDepthState X86_64 ids)
recoverIter finfo s =
  case s^.blockFrontier of
    [] -> Right s
    addr:rest ->
      case Map.lookup addr (finfo^.parsedBlocks) of
        Nothing -> Left $ "Stack depth could not find " ++ show addr
        Just region -> do
          case Map.lookup (regionAddr region) (s^.blockInitStackPointers) of
            Nothing -> Left $ "Could not find stack height"
            Just init_sp -> do
              let s' = s & blockFrontier .~ rest
              case runState (runExceptT (recoverBlock region init_sp 0)) s' of
                (Right (), s2) -> recoverIter finfo s2
                (Left e, _) -> Left e

$(pure [])

-- | Returns the maximum stack argument used by the function, that is,
-- the highest index above sp0 that is read or written.
maximumStackDepth :: DiscoveryFunInfo X86_64 ids
                  -> SegmentedAddr 64
                  -> Either String (BlockStackDepths X86_64 ids)
maximumStackDepth finfo _ =
    case recoverIter finfo s0 of
      Right s -> Right $ minimizeStackDepthValues $ s ^. blockStackRefs
      Left e  -> Left e
  where
    addr = discoveredFunAddr finfo
    sdv0 = SDV { staticPart = 0, dynamicPart = Set.empty }
    s0   = SDS { _blockInitStackPointers = Map.singleton addr sdv0
               , _blockStackRefs         = Set.empty
               , _blockFrontier          = [addr]
               }

$(pure [])

newtype ConstStackDepth = CSD Integer

fromX86Offset :: Int64 -> ConstStackDepth
fromX86Offset i | i < 0 = CSD (negate (toInteger i))
                | otherwise = CSD 0

csdMax :: ConstStackDepth -> ConstStackDepth -> ConstStackDepth
csdMax (CSD x) (CSD y) = CSD (max x y)

$(pure [])

type StackWarning w = (SegmentedAddr w, String)

data ConstStackState w =
  ConstStackState { _stackDepthWarnings :: ![StackWarning w]
                  , _maxStackDepth :: !ConstStackDepth
                  }

stackDepthWarnings :: Simple Lens (ConstStackState w) [StackWarning w]
stackDepthWarnings = lens _stackDepthWarnings (\s v -> s { _stackDepthWarnings = v })

maxStackDepth :: Simple Lens (ConstStackState w) ConstStackDepth
maxStackDepth = lens _maxStackDepth (\s v -> s { _maxStackDepth = v })

$(pure [])

type ConstStackM w = State (ConstStackState w)

addWarning :: SegmentedAddr w -> String -> ConstStackM w ()
addWarning addr msg =
  stackDepthWarnings %= ((addr,msg):)

-- | Update the stack depth based on the address of a write.
maxAddr :: ( OrdF (ArchReg arch)
           , ShowF (ArchReg arch)
           , MemWidth (ArchAddrWidth arch)
           )
        => AbsProcessorState (ArchReg arch) ids
           -- ^ Abstract state at end of block
        -> Int64
           -- ^ Adjustment to apply to stack pointer in computing height.
        -> ArchAddrValue arch ids
           -- ^ Address to consider
        -> ConstStackM (ArchAddrWidth arch) ()
maxAddr ps adj addr =
  case transferValue ps addr of
    StackOffset _base off
      | Just (v,_) <- Set.minView off -> do
        maxStackDepth %= csdMax (fromX86Offset (adj + v))
    _ -> pure ()

-- | Update the stack depth based on the stack pointer value at the end of a block.
maxStackPointer :: ( OrdF (ArchReg arch)
                   , ShowF (ArchReg arch)
                   , MemWidth (ArchAddrWidth arch)
                   )
                => ArchSegmentedAddr arch
                   -- ^ Address of this blcok
                -> AbsProcessorState (ArchReg arch) ids
                   -- ^ Abstract state at end of block
                -> Int64
                   -- ^ Adjustment to apply to stack pointer in computing height.
                -> ArchAddrValue arch ids
                   -- ^ Address to consider
                -> ConstStackM (ArchAddrWidth arch) ()
maxStackPointer block_addr ps adj addr =
  case transferValue ps addr of
    StackOffset _base off | Just (v,_) <- Set.minView off -> do
      maxStackDepth %= csdMax (fromX86Offset (adj + v))
    _ -> do
      addWarning block_addr "Could not compute final stack pointer in block."


maxStmt :: ( OrdF (ArchReg arch)
           , ShowF (ArchReg arch)
           , MemWidth (ArchAddrWidth arch)
           )
        => AbsProcessorState (ArchReg arch) ids
        -> Stmt arch ids
        -> ConstStackM (ArchAddrWidth arch) ()
maxStmt ps stmt =
  case stmt of
    WriteMem addr _val ->
      maxAddr ps 0 addr
    _ -> pure ()

-- | Interpret blcok to look for
maxBlock :: ( OrdF (ArchReg arch)
            , ShowF (ArchReg arch)
            , MemWidth (ArchAddrWidth arch)
            , RegisterInfo (ArchReg arch)
            )
         => ArchSegmentedAddr arch
            -- ^ Address of this block
         -> ParsedBlock arch ids
         -> ConstStackM (ArchAddrWidth arch) ()
maxBlock block_addr b = do
  let absState = pblockState b
  traverse_ (maxStmt absState) (pblockStmts b)
  case pblockTerm b of
    ParsedCall s _ -> do
      -- Add 8 to reflect stack pointer contains return address
      maxStackPointer block_addr absState 8 (s^.boundValue sp_reg)
    ParsedJump s _ -> do
      maxStackPointer block_addr absState 0 (s^.boundValue sp_reg)
    ParsedLookupTable s _ _ -> do
      maxStackPointer block_addr absState 0 (s^.boundValue sp_reg)
    ParsedReturn{} -> do
      pure ()
    ParsedBranch{} -> do
      pure ()
    ParsedSyscall s _ -> do
      maxStackPointer block_addr absState 0 (s^.boundValue sp_reg)
    ParsedTranslateError{} -> do
      pure ()
    ClassifyFailure{} -> do
      pure ()

maxRegion :: ( OrdF (ArchReg arch)
             , ShowF (ArchReg arch)
             , MemWidth (ArchAddrWidth arch)
             , RegisterInfo (ArchReg arch)
             )
          => ParsedBlockRegion arch ids
          -> ConstStackM (ArchAddrWidth arch) ()
maxRegion r = traverse_ (maxBlock (regionAddr r)) (regionBlockMap r)

-- | Returns the maximum stack argument used by the function, that is,
-- the highest index above sp0 that is read or written.
maxConstStackDepth :: ( OrdF (ArchReg arch)
                      , ShowF (ArchReg arch)
                      , MemWidth (ArchAddrWidth arch)
                      , RegisterInfo (ArchReg arch)
                      )
                   => DiscoveryFunInfo arch ids
                   -> (ConstStackDepth, [StackWarning (ArchAddrWidth arch)])
maxConstStackDepth finfo =
    case runState (traverse_ maxRegion (finfo^.parsedBlocks)) s0 of
      ((), s) -> (s^.maxStackDepth, reverse (s^.stackDepthWarnings))
  where
    s0   = ConstStackState  { _stackDepthWarnings = []
                            , _maxStackDepth = CSD 0
                            }
