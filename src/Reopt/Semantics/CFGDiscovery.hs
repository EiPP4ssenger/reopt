------------------------------------------------------------------------
-- |
-- Module           : Reopt.Semantics.CFGDiscovery
-- Description      : Control Flow Graph discovery support
-- Copyright        : (c) Galois, Inc 2015
-- Maintainer       : Simon Winwood <sjw@galois.com>
-- Stability        : provisional
--
-- This contains an implementation of a CFG discovery algorithm based
-- upon an interleaved abstract interpretation (currently unsound)
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

module Reopt.Semantics.CFGDiscovery
       ( cfgFromAddress
         -- Abstract Interpreter
       , absInt
       , AbsState
       , AbsBlockState(..)
       , absX86State
         -- Domains
       , PointedSet(..)
       , StackHeapSet
         -- Helpers
       , PrettyF(..)
       )
       where

import           Control.Applicative ( (<$>), (<*>) )
import           Control.Lens
import           Control.Monad.State.Strict
import           Data.Bits
import qualified Data.Foldable as Fold
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (catMaybes, isNothing, fromMaybe)
import           Data.Monoid (mappend, mempty)
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MF
import           Data.Parameterized.NatRepr
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Vector as V
import           Data.Word
import           Debug.Trace
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Reopt.Memory
import           Reopt.Semantics.AbsDomain
import           Reopt.Semantics.Implementation
import           Reopt.Semantics.Representation
import qualified Reopt.Semantics.StateNames as N
import           Reopt.Semantics.Types
import qualified Reopt.Semantics.WorkList as WL

------------------------------------------------------------------------
-- Pointed set domains

data PointedSet tp = PointedSet { psTyp :: (TypeRepr tp)
                                , _psValue :: Maybe (Set Integer) }

psValue :: Simple Lens (PointedSet tp) (Maybe (Set Integer))
psValue = lens _psValue (\s v -> s { _psValue = v })

prettySet :: (a -> Doc) -> Set a -> Doc
prettySet f vs = encloseSep lbrace rbrace comma (map f (S.toList vs))

instance PrettyF PointedSet where
  prettyF ps = case ps ^. psValue of
                Nothing -> text "TOP"
                Just vs -> prettySet (\v' -> text (showHex v' "")) vs

instance Eq (PointedSet a) where
  x == y =  x ^. psValue == y ^. psValue

instance EqF PointedSet where
  eqF = (==)

instance POSet PointedSet where
  leq x y = case (x ^. psValue, y ^. psValue) of
             (_, Nothing)      -> True
             (Nothing, _)      -> False
             (Just v, Just v') -> v `S.isSubsetOf` v'

instance Lattice PointedSet where
  top tp      = PointedSet { psTyp = tp, _psValue = Nothing }
  bottom tp   = PointedSet { psTyp = tp, _psValue = Just S.empty }

  lub x y = PointedSet { psTyp = psTyp x, _psValue = val }
    where
      val = case (x ^. psValue, y ^. psValue) of
             (_, Nothing)      -> Nothing
             (Nothing, _)      -> Nothing
             (Just v, Just v') -> Just $ v `S.union` v' 

  glb x y = case (x ^. psValue, y ^. psValue) of
             (_, Nothing)      -> y
             (Nothing, _)      -> x
             (Just v, Just v') ->
               PointedSet { psTyp = psTyp x, _psValue = Just $ v `S.intersection` v' }

  isTop ps = isNothing ( ps ^. psValue )

clampForType :: TypeRepr tp -> Integer -> Integer
clampForType tp = case tp of BVTypeRepr n -> \v -> v .&. maxUnsigned n
                               
instance AbsDomain PointedSet where
  transfer app =
    case app of
     BVAdd n x y -> binop (+) n x y
     _           -> top (appType app)
    where
      binop f n v v' =
        case (v ^. psValue, v' ^. psValue) of
         (Just vs, Just vs') ->
           abstract (psTyp v) [ f x y .&. maxUnsigned n
                                  | x <- S.toList vs
                                  , y <- S.toList vs' ]
         _                   -> top (psTyp v)
    
  concretize d = d ^. psValue
  abstract tp vs =
    let insertOne s v = S.insert (clampForType tp v) s
    in PointedSet { psTyp = tp
                  , _psValue = Just $ Fold.foldl' insertOne S.empty vs }

  -- singleton tp v = PointedSet { psTyp = tp, _psValue = Just (S.singleton v) }

newtype ClampedSet tp = ClampedSet { unClampSet :: PointedSet tp }

deriving instance POSet ClampedSet
deriving instance PrettyF ClampedSet

clampSet :: PointedSet tp -> ClampedSet tp
clampSet vs 
  | Just ps <- vs ^. psValue
  , S.size ps > 20  = ClampedSet $ vs & psValue .~ Nothing
  | otherwise       = ClampedSet vs

instance Lattice ClampedSet where
  top = ClampedSet . top
  bottom = ClampedSet . bottom
  isTop  = isTop . unClampSet
  
  lub x y = clampSet $ lub (unClampSet x) (unClampSet y)
  glb x y = clampSet $ glb (unClampSet x) (unClampSet y)

instance AbsDomain ClampedSet where
  transfer app = clampSet $ transfer (mapApp unClampSet app)
  concretize d = unClampSet d ^. psValue
  abstract tp vs = clampSet $ abstract tp vs

------------------------------------------------------------------------
-- Differentiating between stack and heap pointers

newtype StackHeapSet tp = StackHeapSet { _shs :: PairF ClampedSet PointedSet tp }

instance PrettyF StackHeapSet where
  prettyF ps = text "HEAP:" <+> prettyF (ps ^. shs . _1)
               <+> text "SP:" <+> prettyF (ps ^. shs . _2)

shs :: Lens (StackHeapSet tp) (StackHeapSet tp')
            (PairF ClampedSet PointedSet tp) (PairF ClampedSet PointedSet tp')
shs = lens _shs (\s v -> s { _shs = v })

deriving instance POSet StackHeapSet
deriving instance Lattice StackHeapSet

instance AbsDomain StackHeapSet where
  transfer app   = StackHeapSet $ transfer (mapApp (view shs) app)
  concretize d   = concretize (d ^. (shs . _1)) -- FIXME: correct?
  abstract tp vs = StackHeapSet $ PairF (abstract tp vs) (bottom tp)
  finishBlock f  = shs . _2 . psValue %~ normalizeSP
    where
      normalizeSP m_v = (\x -> S.map (\v -> v - x)) <$> sp' <*> m_v
      sp' = case concretize (f N.rsp ^. shs . _2) of
             Just vs | [v] <- S.toList vs -> Just v
             _ -> trace "Post-sp isn't a singleton" Nothing
  initialState r 
    | Just Refl <- testEquality r N.rsp
      = let v = StackHeapSet $ PairF (top knownType) (singleton knownType 0)
        in trace ("initialState " ++ show (prettyF v)) v
    | otherwise  = top (N.registerType r)

------------------------------------------------------------------------
-- Interpreter state

data AbsBlockState f
  = AbsBlockState { _absX86State :: X86State' f
                  , _absParents :: Set CodeAddr }

absX86State :: Lens (AbsBlockState f) (AbsBlockState g) (X86State' f) (X86State' g)
absX86State = lens _absX86State (\s v -> s { _absX86State = v })

absParents :: Simple Lens (AbsBlockState f) (Set CodeAddr)
absParents = lens _absParents (\s v -> s { _absParents = v })

initAbsBlockState :: AbsDomain d => CodeAddr -> AbsBlockState d
initAbsBlockState ip =
  AbsBlockState
   { _absX86State = mkX86State initialState
                    & register N.rip .~ singleton knownType (fromIntegral ip)
   , _absParents = S.empty }
                      
joinBlockState :: forall d. AbsDomain d =>
                  AbsBlockState d -> AbsBlockState d -> Maybe (AbsBlockState d)
joinBlockState new old
  | (merged, True) <- runState go False = Just (AbsBlockState merged parents)
  | not ((new ^. absParents) `S.isSubsetOf` (old ^. absParents))
    = Just (old & absParents .~ parents)
  | otherwise = Nothing
  where
    parents = (new ^. absParents) `S.union` (old ^. absParents)
    
    go = zipWithX86StateM join1 (new ^. absX86State) (old ^. absX86State)
    join1 :: forall tp. d tp -> d tp -> State Bool (d tp)
    join1 v v' = case joinD v v' of
                  Nothing -> return v'
                  Just nv -> put True >> return nv

type AbsState d = Map CodeAddr (AbsBlockState d)

emptyAbsState :: AbsState d
emptyAbsState = M.empty

data InterpState d = InterpState
                     { _cfg      :: !CFG
                     , _failedAddrs  :: !(Set CodeAddr)
                     , _guessedAddrs :: !(Set CodeAddr)
                     , _blockEnds   :: !(Set CodeAddr)                     
                     , _genState :: !GlobalGenState
                     , _memory   :: !(Memory Word64) -- read only
                     , _absState :: !(AbsState d)
                     }

emptyInterpState mem = InterpState
      { _cfg = emptyCFG
      , _failedAddrs = S.empty
      , _guessedAddrs = S.empty
      , _blockEnds   = S.empty
      , _genState    = emptyGlobalGenState
      , _memory      = mem
      , _absState    = emptyAbsState
      }

cfg :: Simple Lens (InterpState d) CFG
cfg = lens _cfg (\s v -> s { _cfg = v })

genState :: Simple Lens (InterpState d) GlobalGenState
genState = lens _genState (\s v -> s { _genState = v })

failedAddrs :: Simple Lens (InterpState d) (Set CodeAddr)
failedAddrs = lens _failedAddrs (\s v -> s { _failedAddrs = v })

guessedAddrs :: Simple Lens (InterpState d) (Set CodeAddr)
guessedAddrs = lens _guessedAddrs (\s v -> s { _guessedAddrs = v })

blockEnds :: Simple Lens (InterpState d) (Set CodeAddr)
blockEnds = lens _blockEnds (\s v -> s { _blockEnds = v })

memory :: Simple Lens (InterpState d) (Memory Word64)
memory = lens _memory (\s v -> s { _memory = v })

absState :: Lens (InterpState d) (InterpState d') (AbsState d) (AbsState d')
absState = lens _absState (\s v -> s { _absState = v })

liftEither :: StateT s (Either e) a -> State s (Either e a)
liftEither m = state go
  where
    go s = case runStateT m s of
            Left e       -> (Left e,  s)
            Right (r, t) -> (Right r, t)

  -- FIXME: move
subMonad :: (MonadState s m) =>
            Simple Lens s t
            -> State t r
            -> m r
subMonad l m = l %%= runState m

------------------------------------------------------------------------
-- Block discovery

-- | Does a simple lookup in the cfg at a given DecompiledBlock address.
lookupBlock :: MonadState (InterpState d) m => CodeAddr -> m (Maybe Block)
lookupBlock addr = uses (cfg . cfgBlocks) (M.lookup (DecompiledBlock addr))

lookupAbsState :: MonadState (InterpState d) m => 
                  CodeAddr -> m (Maybe (AbsBlockState d))
lookupAbsState addr = uses absState (M.lookup addr)

newtype Hex = Hex Integer
              deriving (Eq, Ord)

mkHex :: Integer -> Hex
mkHex = Hex

instance Show Hex where
  show (Hex v) = showHex v ""

-- | This is the worker for getBlock, in the case that the cfg doesn't
-- contain the address of interest.
reallyGetBlock :: MonadState (InterpState d) m => ExploreLoc -> m (Maybe Block)
reallyGetBlock loc = do
  mem <- use memory
  r <- subMonad genState (liftEither $ disassembleBlock mem loc)
  case r of
   Left _e -> trace ("Failed for address " ++ show (pretty loc)) $
              do failedAddrs %= S.insert (loc_ip loc)
                 return Nothing
   Right (bs, next_ip) ->
     do cfg       %= insertBlocksForCode (loc_ip loc) next_ip bs
        blockEnds %= S.insert next_ip
        lookupBlock (loc_ip loc)

-- | Returns a block at the given location, if at all possible.  This
-- will disassemble the binary if the block hasn't been seen before.
-- In particular, this ensures that a block and all it's children are
-- present in the cfg (assuming successful disassembly)
getBlock :: MonadState (InterpState d) m => ExploreLoc -> m (Maybe Block)
getBlock loc = do let addr = (loc_ip loc)
                  m_b <- lookupBlock addr
                  failed <- uses failedAddrs (S.member addr)
                  case m_b of
                    Nothing | not failed -> reallyGetBlock loc
                    _                    -> return m_b

------------------------------------------------------------------------
-- Transfer functions

-- type Path = [(Value BoolType, Bool)]

-- blockPaths :: CFG -> Block -> [(X86State, Path)]
-- blockPaths c root = traverseBlockAndChildren c root go merge
--   where
--     merge cond l _ r = map (_2 %~ (:) (cond, True)) l
--                        ++ map (_2 %~ (:) (cond, False)) r
--     go b = case blockTerm b of
--             FetchAndExecute s -> [(s, [])]
--             _                 -> [] 

type AssignState d = MapF Assignment d

transferValue :: AbsDomain d => AbsBlockState d -> AssignState d -> Value tp -> d tp
transferValue ab m v =
  case v of
   BVValue n i -> singleton (BVTypeRepr n) i
   -- Invariant: v is in m
   AssignedValue k@Assignment{} ->
     case MF.lookup k m of
      Just v -> v
      Nothing -> error $ "Missing abstract state for "
                          ++ show (ppAssignId $ assignId k)
   Initial r -> ab ^. (absX86State . register r)
   
transferApp :: AbsDomain d => AbsBlockState d -> AssignState d
               -> App Value tp -> d tp
transferApp ab m app = transfer $ mapApp (transferValue ab m) app

-- FIXME: move
type_width' :: TypeRepr tp -> Int
type_width' (BVTypeRepr n) = widthVal n

transferStmt :: forall d. AbsDomain d => AbsBlockState d -> Stmt
                -> State (AssignState d) (Set CodeAddr)
transferStmt ab stmt = go stmt
  where
    go :: Stmt -> State (AssignState d) (Set CodeAddr)
    go (AssignStmt assign@(Assignment _ rhs)) =
      do modify (\m -> MF.insert assign (evalRHS m rhs) m)
         return S.empty
    go (Write (MemLoc _ tp) v)
      | type_width' tp == 64 = do
          vs <- gets (\s -> transferValue ab s v)
          return $ case concretize vs of
                    Nothing  -> S.empty
                    Just vs' -> S.map fromInteger vs'
    go _                     = return S.empty

    evalRHS :: forall tp.  AssignState d -> AssignRhs tp -> d tp
    evalRHS m rhs =
      case rhs of
       EvalApp app    -> transferApp ab m app
       SetUndefined _ -> top (assignRhsType rhs)
       Read _         -> top (assignRhsType rhs)

abstractState :: AbsDomain d =>
                 AbsBlockState d -> AssignState d
                 -> X86State -> [(ExploreLoc, AbsBlockState d)]
abstractState ab m s =
  case concretize (abst ^. curIP) of
   Nothing  -> trace "Hit top" [] -- we hit top, so give up
   Just ips ->
     let parent = fromMaybe (error "Expecting 1 parent")
                            (concretize (ab ^. (absX86State . register N.rip)))
     in
     [ (loc, AbsBlockState { _absX86State = abst & curIP .~ x_w
                           , _absParents = S.map fromInteger parent
                           })
     | x <- S.toList ips
     , let x_w = singleton knownType x
     , let t = case s ^. x87TopReg of
                BVValue _ v -> v
                _ -> error "x87top is not concrete"
     , let loc = ExploreLoc { loc_ip = fromInteger x
                            , loc_x87_top = fromInteger t
                            }
     ]
  where
    abst = let s0 = mkX86State (\r -> transferValue ab m (s ^. register r))
           in mapX86State (finishBlock (\r -> s0 ^. register r)) s0

transferBlock :: (PrettyF d, AbsDomain d) => CFG -> Block -> AbsBlockState d
                 -> (Set CodeAddr, [(ExploreLoc, AbsBlockState d)])
transferBlock c root ab =
  traverseBlockAndChildren c root leaf merge MF.empty
  & _1 %~ S.unions
  where
    merge b l r m = let (guesses, m_b) = go b m
                    in l m_b `mappend` r m_b `mappend` (guesses, [])
    leaf b m = case blockTerm b of
                 FetchAndExecute s -> let (guesses, m_b) = go b m
                                      in (guesses, abstractState ab m_b s)
                 _                 -> mempty -- can't happen

    go b = runState (mapM (transferStmt ab) (blockStmts b))
      
-- | Joins in the new abstract state and returns the locations for
-- which the new state is changed.
mergeBlocks :: forall d. (PrettyF d, AbsDomain d)
               => [(ExploreLoc, AbsBlockState d)]
               -> State (AbsState d) [ExploreLoc]
mergeBlocks bs = state (\s -> Fold.foldl' mergeBlock ([], s) bs)
  where
    mergeBlock :: ([ExploreLoc], AbsState d)
                  -> (ExploreLoc, AbsBlockState d)
                  -> ([ExploreLoc], AbsState d)
    mergeBlock r@(locs, s) (loc, ab) =
      let upd :: AbsBlockState d -> ([ExploreLoc], AbsState d)
          upd new = ( loc : locs, M.insert (loc_ip loc) new s )
      in
      case M.lookup (loc_ip loc) s of
       -- We have seen this block before, so need to join and see if
       -- the results is changed.
       Just ab' -> case joinBlockState ab ab' of
                    Nothing  -> r
                    Just new ->
                      trace ("Merging\n"
                             ++ show (pretty ab) 
                             ++ "\n" ++ show (pretty ab')
                             ++ "\n" ++ show (pretty new)
                            ) $ upd new

       -- We haven't seen this block before
       Nothing  -> upd ab

transferLoc :: (PrettyF d, AbsDomain d, MonadState (InterpState d) m)
               => ExploreLoc -> m [ExploreLoc]
transferLoc loc = 
  do m_b  <- getBlock loc
     m_ab <- lookupAbsState (loc_ip loc)
     case (m_b, m_ab) of
      (Just b, Just s) ->
        do c <- use cfg
           let (guesses, vs) = transferBlock c b s
           guessedAddrs %= S.union guesses
           subMonad absState (mergeBlocks vs)
      _                -> return []

------------------------------------------------------------------------
-- Main loop

absInt :: (PrettyF d, AbsDomain d) =>
          Memory Word64
          -- ^ Memory to use when decoding instructions.
          -> CodeAddr
          -- ^ Location to start disassembler form.
          -> (CFG, Set CodeAddr, AbsState d)
absInt mem start = (s' ^. cfg, s' ^. blockEnds, s' ^. absState)
  where
    s' = go (emptyInterpState mem) (S.singleton start)
    -- go :: InterpState PointedSet -> Set CodeAddr -> InterpState PointedSet
    go st roots
      | S.null roots = st
      | otherwise    =
          let wl   = WL.fromSet (S.map rootLoc roots)
              st'  = st & absState %~ addTops roots
              st'' = execState (WL.iterate transferLoc wl) st'
              cfgAddrs = S.map blockParent (M.keysSet (st'' ^. (cfg . cfgBlocks)))
              roots' = (st'' ^. guessedAddrs)
                       `S.difference`
                       ( cfgAddrs `S.union` (st'' ^. failedAddrs ) )
          in go (st'' & guessedAddrs .~ S.empty) (S.filter isCodePointer roots')
    
    addTops roots m = 
      Fold.foldl' (\m' k -> M.insert k (initAbsBlockState k) m') m roots
             
    isCodePointer :: CodeAddr -> Bool
    isCodePointer val = addrHasPermissions (fromIntegral val) pf_x mem

cfgFromAddress :: Memory Word64
                  -- ^ Memory to use when decoding instructions.
               -> CodeAddr
                  -- ^ Location to start disassembler form.
               -> (CFG, Set CodeAddr)
cfgFromAddress mem start = (c, ends)
  where
    (c, ends, _abs :: AbsState PointedSet) = absInt mem start
    
------------------------------------------------------------------------
-- Pretty printing utilities (copied)

bracketsep :: [Doc] -> Doc
bracketsep [] = text "{}"
bracketsep (h:l) =
  vcat ([text "{" <+> h] ++ fmap (text "," <+>) l ++ [text "}"])

ppValueEq :: (PrettyF d, AbsDomain d)
             => N.RegisterName cl -> d (N.RegisterType cl) -> Maybe Doc
ppValueEq r v -- FIXME: doing this to detect top is ugly
  | isTop v   = Nothing
  | otherwise = Just $ text (show r) <+> text "=" <+> prettyF v

-- | Pretty print  a register equals a value.
rec :: (PrettyF d, AbsDomain d)
       => N.RegisterName cl -> d (N.RegisterType cl) -> Maybe Doc
rec nm v = ppValueEq nm v

recv :: (PrettyF d, AbsDomain d) => (Int -> N.RegisterName cl)
        -> V.Vector (d (N.RegisterType cl)) -> [Maybe Doc]
recv mkR v = f <$> [0..V.length v - 1]
  where
    f i = ppValueEq (mkR i) (v V.! i)

-- FIXME: move
class PrettyF (f :: k -> *) where
  prettyF     :: f a -> Doc
  
  prettyListF :: [f a] -> Doc
  prettyListF = list . map prettyF
  
instance (AbsDomain d, PrettyF d) => Pretty (AbsBlockState d) where
  pretty st =
    vcat [ text "parent =" <+> prettySet (\v -> text $ showHex v "")
                                         (st ^. absParents)
         , bracketsep $ catMaybes ([ rec   N.rip (s^.curIP)]
                                   ++ recv N.GPReg (s^.reg64Regs)
                                   ++ recv N.FlagReg (s^.flagRegs)
                                   ++ recv N.X87ControlReg (s^.x87ControlWord)
                                   ++ recv N.X87StatusReg (s^.x87StatusWord)
                                   ++ recv N.X87TagReg (s^.x87TagWords)
                                   ++ recv N.X87FPUReg (s^.x87Regs)
                                   ++ recv N.XMMReg (s^.xmmRegs) )
         ]
    where s = st ^. absX86State
