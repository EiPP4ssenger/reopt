{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Reopt.CFG.FnRep
   ( FnAssignId(..)
   , FnAssignment(..)
   , FnAssignRhs(..)
   , FnValue(..)
   , Function(..)
   , FunPredMap
   , ppFunPredMap
   , FunctionType(..)
   , FnBlock(..)
   , FnStmt(..)
   , FnTermStmt(..)
   , FnPhiVar(..)
   , FnReturnVar(..)
   , FoldFnValue(..)
   , PhiValueMap
   , fnAssignRHSType
   , fnValueType
   , fnValueWidth
   , ftMaximumFunctionType
   , ftMinimumFunctionType
   , ftArgRegs
   , ftIntRetRegs
   , ftFloatRetRegs
   ) where

import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import qualified Data.Vector as V
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import           Data.Parameterized.Some

import           Data.Macaw.CFG
   ( App(..)
   , BlockLabel
   , ppApp
   , ppLit
   , sexpr
   , appType
   , foldAppl
   )
import           Data.Macaw.Memory (SegmentedAddr)
import           Data.Macaw.Types

import           Reopt.Machine.X86State
  ( X86Reg
  , x86ArgumentRegs
  , x86ResultRegs
  , x86FloatArgumentRegs
  , x86FloatResultRegs
  )
import Reopt.Semantics.Monad (RepValSize(..))

commas :: [Doc] -> Doc
commas = hsep . punctuate (char ',')

newtype FnAssignId = FnAssignId Word64
                   deriving (Eq, Ord)

instance Show FnAssignId where
  show (FnAssignId w) = show w

ppFnAssignId :: FnAssignId -> Doc
ppFnAssignId (FnAssignId w) = text ("r" ++ show w)

data FnAssignment tp
   = FnAssignment { fnAssignId :: !FnAssignId
                  , fnAssignRhs :: !(FnAssignRhs tp)
                  }

instance Pretty (FnAssignment tp) where
  pretty (FnAssignment lhs rhs) = ppFnAssignId lhs <+> text ":=" <+> pretty rhs

instance ShowF FnAssignment where
  showF = show . pretty

-- | This describes the expected arguments and return types of the function.
data FunctionType =
  FunctionType { fnNIntArgs   :: !Int
               , fnNFloatArgs :: !Int
               , fnNIntRets   :: !Int
               , fnNFloatRets :: !Int
               }
  deriving (Ord, Eq, Show)

instance Pretty FunctionType where
  pretty f = parens (int (fnNIntArgs f) <> comma <+> int (fnNFloatArgs f))
             <+> text "->"
             <+> parens (int (fnNIntRets f) <> comma <+> int (fnNFloatRets f))

-- Convenience functions
ftMaximumFunctionType :: FunctionType
ftMaximumFunctionType = FunctionType (length x86ArgumentRegs)
                                     (length x86FloatArgumentRegs)
                                     (length x86ResultRegs)
                                     (length x86FloatResultRegs)

ftMinimumFunctionType :: FunctionType
ftMinimumFunctionType = FunctionType 0 0 0 0

-- | Return the registers used to pass arguments.
ftArgRegs :: FunctionType -> [Some X86Reg]
ftArgRegs ft = fmap Some (ftIntArgRegs ft) ++ fmap Some (ftFloatArgRegs ft)

ftIntArgRegs :: FunctionType -> [X86Reg (BVType 64)]
ftIntArgRegs ft = take (fnNIntArgs ft) x86ArgumentRegs

ftFloatArgRegs :: FunctionType -> [X86Reg (BVType 128)]
ftFloatArgRegs ft = take (fnNFloatArgs ft) x86FloatArgumentRegs

ftIntRetRegs :: FunctionType -> [X86Reg (BVType 64)]
ftIntRetRegs ft = take (fnNIntRets ft) x86ResultRegs

ftFloatRetRegs :: FunctionType -> [X86Reg (BVType 128)]
ftFloatRetRegs ft = take (fnNFloatRets ft) x86FloatResultRegs

-- FIXME: this is in the same namespace as assignments, maybe it shouldn't be?

data FnPhiVar (tp :: Type) =
  FnPhiVar { unFnPhiVar :: !FnAssignId
           , fnPhiVarType :: !(TypeRepr tp)
           }

instance TestEquality FnPhiVar where
  testEquality x y = orderingF_refl (compareF x y)

instance OrdF FnPhiVar where
  compareF x y =
    case compare (unFnPhiVar x) (unFnPhiVar y) of
      LT -> LTF
      GT -> GTF
      EQ ->
        case testEquality (fnPhiVarType x) (fnPhiVarType y) of
          Just Refl -> EQF
          Nothing -> error "mismatched types"

instance Pretty (FnPhiVar tp) where
  pretty = ppFnAssignId . unFnPhiVar

-- | The right-hand side of a function assingment statement.
data FnAssignRhs (tp :: Type) where
  -- An expression with an undefined value.
  FnSetUndefined :: !(NatRepr n) -- Width of undefined value.
                 -> FnAssignRhs (BVType n)
  FnReadMem :: !(FnValue (BVType 64))
            -> !(TypeRepr tp)
            -> FnAssignRhs tp
  FnEvalApp :: !(App FnValue tp)
            -> FnAssignRhs tp
  FnAlloca :: !(FnValue (BVType 64))
           -> FnAssignRhs (BVType 64)
  -- See `RepnzScas` in `Reopt.Machine.X86State`
  FnRepnzScas :: !(RepValSize n)
              -> !(FnValue (BVType n))
              -> !(FnValue (BVType 64))
              -> !(FnValue (BVType 64))
              -> FnAssignRhs (BVType 64)

ppFnAssignRhs :: (forall u . FnValue u -> Doc)
              -> FnAssignRhs tp
              -> Doc
ppFnAssignRhs _  (FnSetUndefined w) = text "undef ::" <+> brackets (text (show w))
ppFnAssignRhs _  (FnReadMem loc _)  = text "*" <> pretty loc
ppFnAssignRhs pp (FnEvalApp a) = ppApp pp a
ppFnAssignRhs pp (FnAlloca sz) = sexpr "alloca" [pp sz]
ppFnAssignRhs pp (FnRepnzScas _ val base off) = sexpr "first_offset_of" [pp val, pp base, pp off]

instance Pretty (FnAssignRhs tp) where
  pretty = ppFnAssignRhs pretty

fnAssignRHSType :: FnAssignRhs tp -> TypeRepr tp
fnAssignRHSType rhs =
  case rhs of
    FnSetUndefined sz -> BVTypeRepr sz
    FnReadMem _ tp -> tp
    FnEvalApp a    -> appType a
    FnAlloca _ -> knownType
    FnRepnzScas{} -> knownType


-- tp <- {BVType 64, BVType 128}
data FnReturnVar tp = FnReturnVar { frAssignId :: !FnAssignId
                                  , frReturnType :: !(TypeRepr tp)
                                  }

instance Pretty (FnReturnVar tp) where
  pretty = ppFnAssignId . frAssignId

-- | A function value.
data FnValue (tp :: Type)
   =  FnValueUnsupported !String !(TypeRepr tp)
      -- | A value that is actually undefined, like a non-argument register at
      -- the start of a function.
   | FnUndefined !(TypeRepr tp)
   | forall n . (tp ~ BVType n) => FnConstantValue !(NatRepr n) !Integer
     -- | Value from an assignment statement.
   | FnAssignedValue !(FnAssignment tp)
     -- | Value from a phi node
   | FnPhiValue !(FnPhiVar tp)
     -- | A value returned by a function call (rax/rdx/xmm0)
   | FnReturn !(FnReturnVar tp)
     -- | The pointer to a function.
   | (tp ~ BVType 64) => FnFunctionEntryValue !FunctionType !(SegmentedAddr 64)
     -- | A pointer to an internal block at the given address.
   | (tp ~ BVType 64) => FnBlockValue !(SegmentedAddr 64)
      -- | Value is a argument passed via a register.
   | FnRegArg !(X86Reg tp) !Int
     -- | A global address
   | (tp ~ BVType 64) => FnGlobalDataAddr !(SegmentedAddr 64)

instance Pretty (FnValue tp) where
  pretty (FnValueUnsupported reason _)
                                  = text $ "unsupported (" ++ reason ++ ")"
  pretty (FnUndefined {})         = text "undef"
  pretty (FnConstantValue sz n)   = ppLit sz n
  pretty (FnAssignedValue ass)    = ppFnAssignId (fnAssignId ass)
  pretty (FnPhiValue phi)         = ppFnAssignId (unFnPhiVar phi)
  pretty (FnReturn var)           = pretty var
  pretty (FnFunctionEntryValue _ n) = text "FunctionEntry"
                                    <> parens (pretty $ show n)
  pretty (FnBlockValue n)         = text "BlockValue"
                                    <> parens (pretty $ show n)
  pretty (FnRegArg _ n)           = text "arg" <> int n
  pretty (FnGlobalDataAddr addr)  = text "data@"
                                    <> parens (pretty $ show addr)

fnValueType :: FnValue tp -> TypeRepr tp
fnValueType v =
  case v of
    FnValueUnsupported _ tp -> tp
    FnUndefined tp -> tp
    FnConstantValue sz _ -> BVTypeRepr sz
    FnAssignedValue (FnAssignment _ rhs) -> fnAssignRHSType rhs
    FnPhiValue phi -> fnPhiVarType phi
    FnReturn ret   -> frReturnType ret
    FnFunctionEntryValue {} -> knownType
    FnBlockValue _ -> knownType
    FnRegArg r _ -> typeRepr r
    FnGlobalDataAddr _ -> knownType

fnValueWidth :: FnValue (BVType w) -> NatRepr w
fnValueWidth = type_width . fnValueType

------------------------------------------------------------------------
-- FoldFnValue

class FoldFnValue a where
  foldFnValue :: (forall u . s -> FnValue u -> s) -> s -> a -> s

instance FoldFnValue (FnAssignRhs tp) where
  foldFnValue _ s (FnSetUndefined {}) = s
  foldFnValue f s (FnReadMem loc _)   = f s loc
  foldFnValue f s (FnEvalApp a)       = foldAppl f s a
  foldFnValue f s (FnAlloca sz)       = s `f` sz
  foldFnValue f s (FnRepnzScas _ val buf cnt) = s `f` val `f` buf `f` cnt

------------------------------------------------------------------------
-- FnStmt

data FnStmt
  = forall tp . FnWriteMem !(FnValue (BVType 64)) !(FnValue tp)
    -- | A comment
  | FnComment !Text
    -- | An assignment statement
  | forall tp . FnAssignStmt !(FnAssignment tp)
    -- FIXME: can we share these with the front-end?
  | FnMemCopy !Integer
             -- /\ Number of bytes to copy at a time (1,2,4,8)
             !(FnValue (BVType 64))
              -- /\ Number of values to move.
             !(FnValue (BVType 64))
              -- /\ Start of source buffer.
             !(FnValue (BVType 64))
              -- /\ Start of destination buffer.
             !(FnValue (BVType 1))

              -- /\ Flag indicates whether direction of move:
              -- True means we should decrement buffer pointers after each copy.
              -- False means we should increment the buffer pointers after each copy.
  | forall n. FnMemSet (FnValue (BVType 64))
                        -- /\ Number of values to assign
                       (FnValue (BVType n))
                        -- /\ Value to assign
                       (FnValue (BVType 64))
                        -- /\ Address to start assigning from.
                       (FnValue (BVType 1))
                        -- /\ Direction flag

instance Pretty FnStmt where
  pretty s =
    case s of
      FnWriteMem addr val -> text "*" <> parens (pretty addr) <+> text "=" <+> pretty val
      FnComment msg -> text "#" <+> text (Text.unpack msg)
      FnAssignStmt assign -> pretty assign
      FnMemCopy  sz cnt src dest rev ->
        text "memcopy" <+> parens (hcat $ punctuate comma args)
        where args = [pretty sz, pretty cnt, pretty src, pretty dest, pretty rev]
      FnMemSet cnt val dest df ->
        text "memset" <+> parens (hcat $ punctuate comma args)
        where args = [pretty cnt, pretty val, pretty dest, pretty df]

instance FoldFnValue FnStmt where
  foldFnValue f s (FnWriteMem addr v)                 = s `f` addr `f` v
  foldFnValue _ s (FnComment {})                      = s
  foldFnValue f s (FnAssignStmt (FnAssignment _ rhs)) = foldFnValue f s rhs
  foldFnValue f s (FnMemCopy _sz cnt src dest rev)    = s `f` cnt `f` src `f` dest `f` rev
  foldFnValue f s (FnMemSet cnt v ptr df)             = s `f` cnt `f` v `f` ptr `f` df

------------------------------------------------------------------------
-- FnTermStmt

data FnTermStmt
   = FnJump !(BlockLabel 64)
   | FnRet !([FnValue (BVType 64)], [FnValue XMMType])
   | FnBranch !(FnValue BoolType) !(BlockLabel 64) !(BlockLabel 64)
     -- ^ A branch to a block within the function, along with the return vars.
   | FnCall !(FnValue (BVType 64))
            FunctionType
            -- Arguments
            [Some FnValue]
            !([FnReturnVar (BVType 64)], [FnReturnVar XMMType])
            !(Maybe (BlockLabel 64))
     -- ^ A call statement to the given location with the arguments listed that
     -- returns to the label.

     -- FIXME: specialized to BSD's (broken) calling convention
   | FnSystemCall !(FnValue (BVType 64)) [(FnValue (BVType 64))] ![ Some FnReturnVar ] (BlockLabel 64)
   | FnLookupTable !(FnValue (BVType 64)) !(V.Vector (SegmentedAddr 64))
   | FnTermStmtUndefined

instance Pretty FnTermStmt where
  pretty s =
    case s of
      FnBranch c x y -> text "branch" <+> pretty c <+> pretty x <+> pretty y
      FnJump lbl -> text "jump" <+> pretty lbl
      FnRet (grets, frets) -> text "return" <+> parens (commas $ (pretty <$> grets) ++ (pretty <$> frets))
      FnCall f _ args (grets, frets) lbl ->
        let arg_docs = (\(Some v) -> pretty v) <$> args
            ret_docs = (pretty <$> grets) ++ (pretty <$> frets)
         in parens (commas ret_docs)
            <+> text ":=" <+> text "call"
            <+> pretty f <> parens (commas arg_docs) <+> pretty lbl
      FnSystemCall call_no args rets lbl ->
        let arg_docs = (pretty <$> args)
            ret_docs = viewSome pretty <$> rets
         in parens (commas ret_docs)
            <+> text ":=" <+> text "syscall"
            <+> pretty call_no <> parens (commas arg_docs) <+> pretty lbl
      FnLookupTable idx vec -> text "lookup" <+> pretty idx <+> text "in"
                               <+> parens (commas $ map (text . show) (V.toList vec))
      FnTermStmtUndefined -> text "undefined term"

instance FoldFnValue FnTermStmt where
  foldFnValue _ s (FnJump {})          = s
  foldFnValue f s (FnBranch c _ _)     = f s c
  foldFnValue f s (FnRet (grets, frets)) = foldl f (foldl f s grets) frets
  foldFnValue f s (FnCall fn _ args _ _) = foldl (\s' (Some v) -> f s' v) (f s fn) args
  foldFnValue f s (FnSystemCall call_no args _rets _lbl) =
    foldl f (f s call_no) args
  foldFnValue f s (FnLookupTable idx _) = s `f` idx
  foldFnValue _ s (FnTermStmtUndefined {}) = s

------------------------------------------------------------------------
-- FnBlock


-- | Map phi variable in a successor block to the value to bind it to.
type PhiValueMap = MapF FnPhiVar FnValue

-- | A block in the function
data FnBlock
   = FnBlock { fbLabel :: !(BlockLabel 64)
               -- | List of function bindings.
             , fbPhiNodes  :: ![Some FnPhiVar]
             , fbStmts :: ![FnStmt]
             , fbTerm  :: !FnTermStmt
--             , fbRegMap :: !(MapF X86Reg FnRegValue)
             , fbAssignMap :: !(Map (BlockLabel 64) PhiValueMap)
               -- ^ Maps labels of next blocks to the phi bindings
             }

instance Pretty FnBlock where
  pretty b =
    pretty (fbLabel b) <$$>
    indent 2 (ppPhis
              <$$> vcat (pretty <$> fbStmts b)
              <$$> pretty (fbTerm b))
    where
      ppPhis = vcat (go <$> fbPhiNodes b)
      go :: Some FnPhiVar -> Doc
      go (Some v) = pretty v
--      goLbl :: (BlockLabel 64, X86Reg tp) -> Doc
--      goLbl (lbl, node) = parens (pretty lbl <> comma <+> prettyF node)

instance FoldFnValue FnBlock where
  foldFnValue f s0 b = foldFnValue f (foldl (foldFnValue f) s0 (fbStmts b)) (fbTerm b)

------------------------------------------------------------------------
-- Function definitions

type FunPredMap w = Map (BlockLabel w) [BlockLabel w]

ppFunPredMap :: FunPredMap w -> Doc
ppFunPredMap m = vcat (ppEntry <$> Map.toList m)
  where ppEntry (lbl, preds) = pretty lbl <+> text ":=" <+> hsep (pretty <$> preds)


data Function = Function { fnAddr :: !(SegmentedAddr 64)
                           -- ^ In memory address of function
                         , fnType :: !FunctionType
                         , fnBlocks :: [FnBlock]
                         , fnBlockPredMap :: !(FunPredMap 64)
                         }

instance Pretty Function where
  pretty fn =
    text "function " <+> pretty (show (fnAddr fn))
    <$$>
    lbrace
    <$$>
    (nest 4 $ vcat (pretty <$> fnBlocks fn))
    <$$>
    rbrace

instance FoldFnValue Function where
  foldFnValue f s0 fn = foldl' (foldFnValue f) s0 (fnBlocks fn)
