{-|
Copyright   : (c) Galois Inc, 2015-2016
Maintainer  : jhendrix@galois.com

This module provides methods for constructing functions from the basic
blocks discovered by 'Data.Macaw.Discovery'.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Reopt.CFG.Recovery
  ( recoverFunction
  ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Data.Foldable as Fold (toList, traverse_)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
--import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String (fromString)
--import           Data.Type.Equality
import qualified GHC.Err.Located as Loc
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.Architecture.Syscall
import           Data.Macaw.CFG
import           Data.Macaw.DebugLogging
import           Data.Macaw.Discovery.Info
import           Data.Macaw.Memory
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types

import           Reopt.CFG.FnRep
import           Reopt.CFG.FunctionArgs (AddrToFunctionTypeMap)
import           Reopt.CFG.RegisterUse
--import           Reopt.CFG.StackDepth
import           Reopt.Machine.X86State

import Debug.Trace

------------------------------------------------------------------------
-- Utilities

hasWidth :: HasRepr f TypeRepr => f tp -> NatRepr w -> Maybe (tp :~: BVType w)
hasWidth f w =
  case typeRepr f of
    BVTypeRepr n -> do
      Refl <- testEquality n w
      pure Refl

------------------------------------------------------------------------
-- FnRegValue

data FnRegValue tp
   = CalleeSaved !(X86Reg tp)
     -- ^ This is a callee saved register.
   | FnRegValue !(FnValue tp)
     -- ^ A value assigned to a register

instance Pretty (FnRegValue tp) where
  pretty (CalleeSaved r)     = text "calleeSaved" <> parens (text $ show r)
  pretty (FnRegValue v)      = pretty v

instance ShowF FnRegValue where
  showF = show . pretty

------------------------------------------------------------------------
-- RecoverState

data RecoverState ids = RS { rsMemory        :: !(Memory 64)
                           , rsInterp :: !(DiscoveryFunInfo X86_64 ids)
                           , _rsNextAssignId :: !FnAssignId
                           , _rsAssignMap :: !(MapF (AssignId ids) FnAssignment)

                             -- Local state
                           , _rsCurLabel  :: !(BlockLabel 64)
                           , _rsCurStmts  :: !(Seq FnStmt)

                           , rsSyscallPersonality  :: !(SyscallPersonality X86_64)
                             -- ^ System call personality
                           , rsCurrentFunctionType :: !FunctionType
                           , rsFunctionArgs        :: !AddrToFunctionTypeMap
                           }

rsNextAssignId :: Simple Lens (RecoverState ids) FnAssignId
rsNextAssignId = lens _rsNextAssignId (\s v -> s { _rsNextAssignId = v })

rsCurLabel :: Simple Lens (RecoverState ids) (BlockLabel 64)
rsCurLabel = lens _rsCurLabel (\s v -> s { _rsCurLabel = v })

-- | List of statements accumulated so far.
rsCurStmts :: Simple Lens (RecoverState ids) (Seq FnStmt)
rsCurStmts = lens _rsCurStmts (\s v -> s { _rsCurStmts = v })

-- | Map from assignments in original block to assignment in
rsAssignMap :: Simple Lens (RecoverState ids) (MapF (AssignId ids) FnAssignment)
rsAssignMap = lens _rsAssignMap (\s v -> s { _rsAssignMap = v })

------------------------------------------------------------------------
-- Recover

data RecoverResult ids a
  = RecoverError !String
  | RecoverSuccess !a !(RecoverState ids)

newtype Recover ids a = Recover { runRecover :: RecoverState ids -> RecoverResult ids a
                                }

evalRecover :: RecoverState ids -> Recover ids a -> Either String a
evalRecover s0 m =
  case runRecover m s0 of
    RecoverError msg -> Left msg
    RecoverSuccess r _ -> Right r

instance Functor (Recover ids) where
  fmap f m = Recover $ \s ->
    case runRecover m s of
      RecoverError msg -> RecoverError msg
      RecoverSuccess v t -> RecoverSuccess (f v) t

instance Applicative (Recover ids) where
  pure v = Recover (\s -> RecoverSuccess v s)
  mf <*> mv = Recover $ \s0 ->
    case runRecover mf s0 of
      RecoverError msg -> RecoverError msg
      RecoverSuccess f s1 -> runRecover (f <$> mv) s1

instance Monad (Recover ids) where
  return = pure
  m >>= h = Recover $ \s0 ->
    case runRecover m s0 of
      RecoverError msg -> RecoverError msg
      RecoverSuccess v s1 -> runRecover (h v) s1

instance MonadError String (Recover ids) where
  throwError msg = Recover $ \_ -> RecoverError msg
  catchError m h = Recover $ \s ->
    case runRecover m s of
      RecoverError msg -> runRecover (h msg) s
      RecoverSuccess v t -> RecoverSuccess v t

instance MonadState (RecoverState ids) (Recover ids) where
  get  = Recover $ \s -> RecoverSuccess s s
  put t = Recover $ \_ -> RecoverSuccess () t

-- | Create a few assignment id.
freshId :: Recover ids FnAssignId
freshId = do
  FnAssignId next_id <- use rsNextAssignId
  rsNextAssignId .= FnAssignId (next_id + 1)
  return $! FnAssignId next_id

-- | Create a return variable with the given type.
mkReturnVar :: TypeRepr tp -> Recover ids (FnReturnVar tp)
mkReturnVar tp = (\next_id -> FnReturnVar next_id tp) <$> freshId

addFnStmt :: FnStmt -> Recover ids ()
addFnStmt stmt = rsCurStmts %= (Seq.|> stmt)

mkFnAssign :: FnAssignRhs tp -> Recover ids (FnAssignment tp)
mkFnAssign rhs = (\next_id -> FnAssignment next_id rhs) <$> freshId


emitAssign :: AssignId ids tp -> FnAssignRhs tp -> Recover ids ()
emitAssign asgn rhs = do
  fnAssign <- mkFnAssign rhs
  rsAssignMap %= MapF.insert asgn fnAssign
  addFnStmt $ FnAssignStmt fnAssign

mkAddAssign :: FnAssignRhs tp -> Recover ids (FnValue tp)
mkAddAssign rhs = do
  fnAssign <- mkFnAssign rhs
  addFnStmt $ FnAssignStmt fnAssign
  return $ FnAssignedValue fnAssign

------------------------------------------------------------------------
-- valueDependencies

{-
-- | Compute the complete set of functional values needed to evaluate the given values.
--
-- e.g. 'valueDependencies l' will return the complete set of assignments needed to compute the values in 'l'
-- or return an error if the values in 'l' depend on architecture-specific functions or memory.
valueDependencies :: forall ids . [Some (Value X86_64 ids)] -> Either String (Set (Some (AssignId ids)))
valueDependencies = go Set.empty
  where go :: Set (Some (AssignId ids))
           -> [Some (Value X86_64 ids)]
           -> Either String (Set (Some (AssignId ids)))
        go s [] = Right s
        go s (Some v:r) =
          case v of
            BVValue{} -> go s r
            RelocatableValue{} -> go s r
            Initial{} -> go s r
            AssignedValue a
              | Set.member (Some (assignId a)) s -> go s r
              | otherwise ->
                case assignRhs a of
                  EvalApp app -> go (Set.insert (Some (assignId a)) s) (foldAppl (\prev l -> Some l:prev) r app)
                  SetUndefined{} -> go s r
                  ReadMem{} -> Left $ "Depends on read " ++ show (pretty a)
                  EvalArchFn{} -> Left $ "Depends on archfn " ++ show (pretty a)
-}

------------------------------------------------------------------------
-- recoverValue

-- | Recover a stack value
recoverValue' :: Loc.HasCallStack
              => RecoverState ids
              -> MapF X86Reg FnValue
              -> Value X86_64 ids tp
              -> Either String (FnValue tp)
recoverValue' s curRegs v = do
  let interpState = rsInterp s
  let mem = rsMemory s
  let assignMap   = s^.rsAssignMap
  case v of
    _ | Just Refl <- hasWidth v (memWidth mem)
      , Just addr <- asLiteralAddr mem v -> do
        let seg = addrSegment addr
        case () of
          _ | segmentFlags seg `Perm.hasPerm` Perm.execute
            , Just ft <- Map.lookup addr (rsFunctionArgs s) -> do
                Right $! FnFunctionEntryValue ft addr

          _ | Map.member addr (interpState^.parsedBlocks) -> do
              Right $! FnBlockValue addr


            | segmentFlags seg `Perm.hasPerm` Perm.write -> do
              Right $! FnGlobalDataAddr addr

            -- FIXME: do something more intelligent with rodata?
            | segmentFlags seg `Perm.hasPerm` Perm.read -> do
              Right $! FnGlobalDataAddr addr

            | otherwise -> do
              Right $! FnValueUnsupported ("segment pointer " ++ show addr) (typeRepr v)

    RelocatableValue{} -> Loc.error "Expected relocatable value to be covered by previous case."
    BVValue w i ->
      Right $ FnConstantValue w i

    AssignedValue asgn -> do
      case MapF.lookup (assignId asgn) assignMap of
        Just fnAssign -> Right $! FnAssignedValue fnAssign
        Nothing -> Left $ "Encountered uninitialized assignment: " ++ show (assignId asgn) ++ "\n"
          ++ show assignMap
    Initial reg -> do
      case MapF.lookup reg curRegs of
        Nothing ->
          Right (FnValueUnsupported ("Initial register " ++ show reg) (typeRepr reg))
        Just v' ->
          Right v'

{-
data RecoverBlockState ids
   = RBC { _rbsState :: (RecoverState ids)
         , blockInitRegs :: !(MapF X86Reg FnValue)
         }

type BlockRecover ids a = StateT (RecoverBlockState ids) (Except String) a
-}

recoverValue :: Loc.HasCallStack
             => MapF X86Reg FnValue
                -- ^ Value of initial registers to block
             -> Value X86_64 ids tp
             -> Recover ids (FnValue tp)
recoverValue regs v = do
  s <- get
  case recoverValue' s regs v of
    Left msg -> Loc.error $ "Error at " ++ show (s^.rsCurLabel) ++ "\n" ++ msg
    Right fnVal -> pure fnVal

------------------------------------------------------------------------
-- recoverRegister

recoverRegister :: Loc.HasCallStack
                => MapF X86Reg FnValue
                   -- ^ Value of initial registers to block
                -> RegState X86Reg (Value X86_64 ids)

                -> X86Reg tp
                -> Recover ids (FnValue tp)
recoverRegister regs proc_state r = do
  s <- get
  case recoverValue' s regs (proc_state ^. boundValue r) of
    Left msg -> do
      Loc.error $ "Unbound register " ++ show r ++ "\n"
           ++ msg ++ "\n"
    Right fnVal -> pure fnVal

------------------------------------------------------------------------
-- recoverStmt

-- | Add statements for the assignment
recoverAssign :: Loc.HasCallStack
              => MapF X86Reg FnValue
                 -- ^ Value of initial registers to block
              -> Assignment X86_64 ids tp
              -> Recover ids ()
recoverAssign regs asgn = do
  m_seen <- uses rsAssignMap (MapF.lookup (assignId asgn))
  case m_seen of
    Just{} -> return ()
    Nothing -> do
      rhs <-
        case assignRhs asgn of
          EvalApp app -> do
            app' <- traverseApp (recoverValue regs) app
            pure (FnEvalApp app')
          SetUndefined w ->
            pure (FnSetUndefined w)
          ReadMem addr tp -> do
            fn_addr <- recoverValue regs addr
            pure (FnReadMem fn_addr tp)
          EvalArchFn (RepnzScas sz val buf cnt) _ -> do
            fn_val <- recoverValue regs val
            fn_buf <- recoverValue regs buf
            fn_cnt <- recoverValue regs cnt
            pure (FnRepnzScas sz fn_val fn_buf fn_cnt)
          EvalArchFn _ (BVTypeRepr w) -> do
            trace ("recoverAssign does not yet support assignment " ++ show (pretty asgn)) $ do
              pure (FnSetUndefined w)
      emitAssign (assignId asgn) rhs

recoverWrite :: MapF X86Reg FnValue
                 -- ^ Value of initial registers to block
             -> BVValue X86_64 ids 64
             -> Value X86_64 ids tp
             -> Recover ids ()
recoverWrite regs addr val = do
  r_addr <- recoverValue regs addr
  r_val  <- recoverValue regs val
  addFnStmt $ FnWriteMem r_addr r_val

-- | This should add code as needed to support the statement.
recoverStmt :: MapF X86Reg FnValue
                 -- ^ Value of initial registers to block
            -> Stmt X86_64 ids
            -> Recover ids ()
recoverStmt regs s = do
  case s of
    AssignStmt asgn -> do
      recoverAssign regs asgn
    WriteMem addr val -> do
      recoverWrite regs addr val
    Comment msg -> do
      addFnStmt $ FnComment msg
    ExecArchStmt (MemCopy bytesPerCopy nValues src dest direction) -> do
      stmt <- FnMemCopy bytesPerCopy <$> recoverValue regs nValues
                                     <*> recoverValue regs src
                                     <*> recoverValue regs dest
                                     <*> recoverValue regs direction
      addFnStmt stmt
    ExecArchStmt (MemSet count v ptr df) -> do
      stmt <- FnMemSet <$> recoverValue regs count
                       <*> recoverValue regs v
                       <*> recoverValue regs ptr
                       <*> recoverValue regs df
      addFnStmt stmt
    _ -> trace ("recoverStmt undefined for " ++ show (pretty s)) $ do
      addFnStmt $ FnComment (fromString $ "UNIMPLEMENTED: " ++ show (pretty s))
      return ()

--------------------------------------------------------------------------------
-- Phi support

-- | The value from the blocks representation to assign to the phi value
data PhiSource ids tp
   = AssignPhi !(TypedAssignId ids tp)
   | RegPhi !(X86Reg tp)

-- | Maps a phi variable in a block to the source in the previous block that should acquire the value from.
data PhiSourceBinding ids tp
   = PhiSourceBinding { phiBindingVar :: !(FnPhiVar tp)
                      , phiBindingValue :: !(PhiSource ids tp)
                      }

-- | Maps each block to the set of phi bindings for that block
type PhiSourceBindingMap ids = Map (BlockLabel 64) [Some (PhiSourceBinding ids)]

mkPhiBindings :: forall ids
              .  DependencySet X86Reg ids
              -> Recover ids [Some (PhiSourceBinding ids)]
mkPhiBindings s = do
  let mkAssignBinding :: Some (TypedAssignId ids) -> Recover ids (Some (PhiSourceBinding ids))
      mkAssignBinding (Some a) = do
        nm <- freshId
        pure $! Some (PhiSourceBinding (FnPhiVar nm (typeRepr a)) (AssignPhi a))
  assignBindings <- mapM mkAssignBinding (Set.toList (s^.depAssignments))
  let mkRegBinding :: Some X86Reg -> Recover ids (Some (PhiSourceBinding ids))
      mkRegBinding (Some r) = do
        nm <- freshId
        pure $! Some (PhiSourceBinding (FnPhiVar nm (typeRepr r)) (RegPhi r))
  regBindings <- mapM mkRegBinding (Set.toList (s^.depRegisters))
  pure $! assignBindings ++ regBindings

mkPhiBindingMap :: PreDependencyMap X86Reg ids
                -> Recover ids (PhiSourceBindingMap ids)
mkPhiBindingMap m = traverse mkPhiBindings (preDependencyMapEntries m)

-- | This function constructs a map from the successor nodes to the
mkPhiAssignMap :: PhiSourceBindingMap ids
                  -- ^ Global phi binding map
               -> SegmentedAddr 64
                  -- ^ Starting IP for the block
               -> ParsedBlock X86_64 ids
                  -- ^ Current block
               -> MapF X86Reg FnRegValue
                  -- ^ Register state at start of block
               -> MapF (AssignId ids) FnValue
                  -- ^ Map from assigned assignments identifiers to value that was assigned.
               -> Recover ids (Map (BlockLabel 64) PhiValueMap)
mkPhiAssignMap phiBindingMap addr b regs assignMap = fmap Map.fromList $ do
  forM (nextLabelsForTermStmt addr (pblockTerm b)) $ \next_lbl -> do
    -- Get bindings needed by next label
    let bindings = fromMaybe [] (Map.lookup next_lbl phiBindingMap)
    -- Crate phiValMap
    phiValMap <- fmap MapF.fromList $ forM bindings $ \(Some binding) -> do
      let var = phiBindingVar binding
      val <-
        case phiBindingValue binding of
          AssignPhi (TypedAssignId a _) ->
            case MapF.lookup a assignMap of
              Nothing -> error $ "Internal: Assignment map does not contain " ++ show a
              Just v -> pure v
          RegPhi r ->
            case MapF.lookup r regs of
              Just (FnRegValue v) -> pure v
              Just (CalleeSaved cr) -> error $ "Internal: Reg map has callee saved value " ++ show cr
              Nothing ->
                error $ "Internal: Reg map does not contain " ++ show r ++ "\n"
                  ++ show (ppParsedBlock addr b)
      pure (MapF.Pair var val)
    pure (next_lbl, phiValMap)

------------------------------------------------------------------------
-- recoverBlock

-- Figure out what is preserved across the function call.
getPostCallValue :: BlockLabel 64
                    -- ^ Label of block making call
                 -> MapF X86Reg FnValue
                    -- ^ Value of registers at start of block
                 -> RegState X86Reg (Value X86_64 ids)
                     -- ^ Value of registers before call
                 -> [FnReturnVar (BVType 64)] -- ^ Integer values returned by function.
                 -> [FnReturnVar XMMType]     -- ^ Floating point values returned by function.
                 -> X86Reg tp
                 -> Recover ids (FnValue tp)
getPostCallValue lbl regs proc_state intrs floatrs r = do
  case r of
    _ | Just Refl <- testEquality (typeRepr r) (BVTypeRepr n64)
      , Just rv <- lookup r ([rax_reg, rdx_reg] `zip` intrs) ->
        return $ FnReturn rv
      | Just Refl <- testEquality r sp_reg -> do
        spv <- recoverRegister regs proc_state sp_reg
        mkAddAssign $ FnEvalApp $ BVAdd knownNat spv (FnConstantValue n64 8)

    _ | Just Refl <- testEquality (typeRepr r) (BVTypeRepr n128)
      , Just rv <- lookup r (zip x86FloatResultRegs floatrs) ->
        return $ FnReturn rv

   -- df is 0 after a function call.
    _ | Just Refl <- testEquality r df_reg -> return $ FnConstantValue knownNat 0

    _ | Some r `Set.member` x86CalleeSavedRegs ->
        recoverRegister regs proc_state r
    _ -> trace ("WARNING: Nothing known about register "
                                         ++ show r ++ " at " ++ show lbl ++ "\n"
                                        ) $ do
      let nm = "post-call register " ++ show r
      return $! FnValueUnsupported nm (typeRepr r)

-- | Get value for register after a system call.
--
-- This is subtly different to that for function calls.
getPostSyscallValue :: BlockLabel 64
                       -- ^ Label of block where we syscall occurred.
                    -> MapF X86Reg FnValue
                    -- ^ Value of registers at start of block
                    -> RegState X86Reg (Value X86_64 ids)
                       -- ^ Value of registers before syscall
                    -> X86Reg tp
                    -> Recover ids (FnValue tp)
getPostSyscallValue lbl regs proc_state r =
  case r of
    _ | Just Refl <- testEquality r sp_reg -> do
          recoverRegister regs proc_state sp_reg
      | Some r `Set.member` x86CalleeSavedRegs ->
        recoverRegister regs proc_state r

    _ | Just Refl <- testEquality r df_reg -> return $ FnConstantValue knownNat 0

    _ -> debug DFunRecover ("WARNING: Nothing known about register " ++ show r ++ " at " ++ show lbl) $
      return (FnValueUnsupported ("post-syscall register " ++ show r) (typeRepr r))


--

recoverBlock :: forall ids
             .  PostDependencyMap X86Reg ids
                -- ^ Dependency map
             -> PhiSourceBindingMap ids
                -- ^ Maps each block to the set of phi bindings for that block
             -> SegmentedAddr 64
                -- ^ Address of this block
             -> ParsedBlock X86_64 ids
                -- ^ This block
             -> Recover ids FnBlock
recoverBlock postDepMap phiMap block_addr b = do
  let lbl = GeneratedBlock block_addr (pblockLabel b)
  -- Set current label
  rsCurLabel  .= lbl

  let phiVars :: [Some (PhiSourceBinding ids)]
      phiVars = fromMaybe [] $ Map.lookup lbl phiMap

  -- This function creates the final block
  let mkBlock :: FnTermStmt
              -> MapF X86Reg FnRegValue
                 -- ^ Value of registers after block executes
              -> Recover ids FnBlock
      mkBlock tm regs' = do
        stmts <- use rsCurStmts
        rsCurStmts .= Seq.empty
        assignMap <- use rsAssignMap
        amap <- mkPhiAssignMap phiMap (labelAddr lbl) b regs' (fmapF FnAssignedValue assignMap)
        return $! FnBlock { fbLabel = lbl
                          , fbPhiNodes = fmap (mapSome phiBindingVar) phiVars
                          , fbStmts = Fold.toList stmts
                          , fbTerm = tm
                          , fbAssignMap = amap
                          }
  -- Infer values of initial registers
  let regs :: MapF X86Reg FnValue
      regs = MapF.fromList
               [ MapF.Pair r (FnPhiValue v)
               | Some (PhiSourceBinding v (RegPhi r)) <- phiVars
               ]
  -- Recover statements
  Fold.traverse_ (recoverStmt regs) (pblockStmts b)
  -- Get block dependencies as it is used for post-processing
  let postDeps = blockPostDependencies lbl postDepMap
  -- Case split on terminal of block
  case pblockTerm b of
    ParsedTranslateError _ -> do
      Loc.error "Cannot recover function in blocks where translation error occurs."
    ClassifyFailure _ ->
      Loc.error $ "Classification failed in Recovery"
    ParsedBranch c x y -> do
      cv <- recoverValue regs c
      mkBlock (FnBranch cv (lbl { labelIndex = x }) (lbl { labelIndex = y })) (fmapF FnRegValue regs)

    ParsedCall proc_state m_ret_addr -> do
      call_tgt <- recoverRegister regs proc_state ip_reg
      ft <-
        case call_tgt of
          FnFunctionEntryValue ft _ -> pure ft
          _ -> pure ftMaximumFunctionType

      -- Generate May not be used (only if called function returns at these types)
      intrs   <- replicateM (fnNIntRets   ft) $ mkReturnVar (knownType :: TypeRepr (BVType 64))
      floatrs <- replicateM (fnNFloatRets ft) $ mkReturnVar (knownType :: TypeRepr XMMType)

      -- Figure out what is preserved across the function call.
      let backdateReg :: X86Reg tp
                      -> Recover ids (FnRegValue tp)
          backdateReg r = do
            FnRegValue <$> getPostCallValue lbl regs proc_state intrs floatrs r

      regs' <- MapF.fromKeysM backdateReg (postDeps^.depRegisters)
      let ret_lbl = mkRootBlockLabel <$> m_ret_addr

      args <- mapM (\(Some r) -> Some <$> recoverRegister regs proc_state r) (ftArgRegs ft)
      -- args <- (++ stackArgs stk) <$> stateArgs proc_state

      mkBlock (FnCall call_tgt ft args (intrs, floatrs) ret_lbl) regs'

    ParsedJump proc_state tgt_addr -> do
      let go :: X86Reg tp -> Recover ids (FnRegValue tp)
          go r = FnRegValue <$> recoverRegister regs proc_state r
      regs' <- MapF.fromKeysM go (postDeps^.depRegisters)
      let tgt_lbl = mkRootBlockLabel tgt_addr
      mkBlock (FnJump tgt_lbl) regs'

    ParsedReturn proc_state -> do
      ft <- gets rsCurrentFunctionType
      grets' <- mapM (recoverRegister regs proc_state) (ftIntRetRegs ft)
      frets' <- mapM (recoverRegister regs proc_state) (ftFloatRetRegs ft)
      mkBlock (FnRet (grets', frets')) MapF.empty

    ParsedSyscall proc_state next_addr -> do
      sysp <- gets rsSyscallPersonality

      let syscallRegs :: [ArchReg X86_64 (BVType 64)]
          syscallRegs = syscallArgumentRegs


      let args
            | BVValue _ this_call_no <- proc_state^.boundValue syscall_num_reg
            , Just (_,_,argtypes) <- Map.lookup (fromInteger this_call_no) (spTypeInfo sysp) =
              take (length argtypes) syscallRegs
            | otherwise =
              syscallRegs

      let rregs = spResultRegisters sysp


      let mkRet :: MapF X86Reg FnRegValue
                -> Some X86Reg
                -> Recover ids (MapF X86Reg FnRegValue)
          mkRet m (Some r) = do
            rv <- mkReturnVar (typeRepr r)
            return $ MapF.insert r (FnRegValue $ FnReturn rv) m

      initMap <- foldM mkRet MapF.empty rregs

      -- pull the return variables out of initMap (in order of rregs)
      let getVar :: Maybe (FnRegValue tp) -> FnReturnVar tp
          getVar (Just (FnRegValue (FnReturn rv))) = rv
          getVar _ = Loc.error "impossible"

      let rets :: [Some FnReturnVar]
          rets = map f rregs
            where f (Some r) = Some $ getVar $ MapF.lookup r initMap

      -- Fold operation to update register map with values persisted across system calls.
      let go :: X86Reg tp -> Recover ids (FnRegValue tp)
          go r = FnRegValue <$> getPostSyscallValue lbl regs proc_state r
      regs' <- MapF.fromKeysM go (postDeps^.depRegisters)

      call_num <- recoverRegister regs proc_state syscall_num_reg

      args'  <- mapM (recoverRegister regs proc_state) args
      -- args <- (++ stackArgs stk) <$> stateArgs proc_state

      mkBlock (FnSystemCall call_num args' rets (mkRootBlockLabel next_addr)) regs'

    ParsedLookupTable proc_state idx vec -> do
      let go :: X86Reg tp -> Recover ids (FnRegValue tp)
          go r = FnRegValue <$> recoverRegister regs proc_state r
      regs' <- MapF.fromKeysM go (postDeps^.depRegisters)
      idx'   <- recoverValue regs idx
      mkBlock (FnLookupTable idx' vec) regs'

------------------------------------------------------------------------
-- allocateStackFrame

{-
allocateStackFrame :: forall ids
                   .  SegmentedAddr 64
                      -- ^ Starting address of the function
                   -> MapF X86Reg FnValue
                      -- ^ Register state at start of block
                   -> Set (StackDepthValue X86_64 ids)
                   -> Recover ids ()
allocateStackFrame addr regs sd
  | Set.null sd          =
    debug DFunRecover "WARNING: no stack use detected" $ return ()
  | [s] <- Set.toList sd = do
      let lbl = GeneratedBlock addr 0
      -- Invoke allocation is non-zero
      when (not (null (dynamicPart s)) || staticPart s /= 0) $ do
        -- Compute assignments needed for evaluating dynamic part of stack
        let vals = (Some . stackDepthOffsetValue) <$> Set.toList (dynamicPart s)
        case valueDependencies vals of
          Left msg -> throwError $ "Could not allocate stack frame: " ++ msg
          Right asgns -> do
            -- Resolve each assignment in initial block.
            let goStmt :: Set (Some (AssignId ids)) -> Stmt X86_64 ids -> Recover ids (Set (Some (AssignId ids)))
                goStmt depSet (AssignStmt asgn)
                  | Set.member (Some (assignId asgn)) depSet = do
                    recoverAssign regs asgn
                    pure $! Set.delete (Some (assignId asgn)) depSet
                goStmt depSet _ = return depSet
            interp_state <- gets rsInterp
            Just b <- pure $ lookupParsedBlock interp_state lbl
            remaining_asgns <- foldlM goStmt asgns (pblockStmts b)
            when (not (Set.null remaining_asgns)) $ do
              throwError $ "Found unsupported symbolic stack references: " ++ show remaining_asgns
        let doOneDelta :: StackDepthOffset X86_64 ids
                       -> Recover ids (FnValue (BVType 64))
                       -> Recover ids (FnValue (BVType 64))
            doOneDelta (Pos _) _   = Loc.error "Saw positive stack delta"
            doOneDelta (Neg x) m_v = do
              v0 <- m_v
              v  <- recoverValue regs x
              mkAddAssign $ FnEvalApp $ BVAdd knownNat v v0
        let sz0 = toInteger (negate $ staticPart s)
        szv <- foldr doOneDelta (return (FnConstantValue n64 sz0)) (dynamicPart s)
        alloc <- mkAddAssign $ FnAlloca szv
        spTop <- mkAddAssign $ FnEvalApp $ BVAdd knownNat alloc szv
        rsCurRegs %= MapF.insert sp_reg (FnRegValue spTop)

  | otherwise = debug DFunRecover "WARNING: non-singleton stack depth" $ return ()
-}

------------------------------------------------------------------------
-- recoverFunction

-- | Recover the function at a given address.
recoverFunction :: forall ids
                .  SyscallPersonality X86_64
                -> AddrToFunctionTypeMap
                -> Memory 64
                -> DiscoveryFunInfo X86_64 ids
                -> Either String Function
recoverFunction sysp ftypes mem fInfo = do
  let a = discoveredFunAddr fInfo
  let blockPreds = funBlockPreds fInfo
  -- Make dependency context
  let dctx = dependencyContext sysp mem ftypes fInfo
  -- Get post dependencies
  let postDepMap = postDependencyMap dctx blockPreds
  trace ("Predecessors for " ++ show a ++ "\n" ++ show (ppFunPredMap blockPreds)) $ do

  let cft = fromMaybe
              (debug DFunRecover ("Missing type for function " ++ show a) ftMaximumFunctionType) $
              Map.lookup a ftypes

--  let insReg i (Some r) = MapF.insert r (FnRegArg r i)
  {-
  let initRegs :: MapF X86Reg FnValue
      initRegs = MapF.empty
               & flip (ifoldr insReg)        (ftArgRegs cft)
                 -- Set df to 0 at function start.
               & MapF.insert df_reg (FnConstantValue n1 0)
-}
  {-
  let insCalleeSaved (Some r) = MapF.insert r (CalleeSaved r)
  let initRegs' :: MapF X86Reg FnRegValue
      initRegs' = fmapF FnRegValue initRegs
                & flip (foldr insCalleeSaved) x86CalleeSavedRegs
-}

  let rs = RS { rsMemory        = mem
              , rsInterp = fInfo
              , _rsNextAssignId = FnAssignId 0
              , _rsCurLabel  = GeneratedBlock a 0
              , _rsCurStmts  = Seq.empty
              , _rsAssignMap = MapF.empty
              , rsSyscallPersonality = sysp
              , rsCurrentFunctionType = cft
              , rsFunctionArgs        = ftypes
              }

  evalRecover rs $ do
    phiBindingMap <- mkPhiBindingMap $ preDependencyMap dctx postDepMap

    -- The first block is special as it needs to allocate space for
    -- the block stack area.  It should also not be in blockPreds (we
    -- assume no recursion/looping through the initial block)

    -- Make the alloca and init rsp.  This is the only reason we
    -- need rsCurStmts

{-
    case maximumStackDepth fInfo a of
      Right depths -> do
        allocateStackFrame a initRegs depths
      Left msg -> throwError $ "maximumStackDepth: " ++ msg
-}
    blks <-
      -- Iterate through regions
      forM (Map.elems (fInfo^.parsedBlocks)) $ \region -> do
        -- Iterate through individual regions in blocks
        forM (Map.elems (regionBlockMap region)) $ \b -> do
          recoverBlock postDepMap phiBindingMap (regionAddr region) b

    pure Function { fnAddr = a
                  , fnType = cft
                  , fnBlocks = concat blks
                  , fnBlockPredMap = blockPreds
                  }
