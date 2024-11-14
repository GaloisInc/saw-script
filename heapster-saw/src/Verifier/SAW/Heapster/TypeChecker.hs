{-# Language GADTs #-}
{-# Language RecordWildCards #-}
{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
{-# Language BlockArguments #-}
{-# Language RankNTypes #-}
{-# Language TemplateHaskell #-}
{-# Language QuasiQuotes #-}
{-# Language TypeOperators #-}
{-# Language DataKinds #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}
{-# Language KindSignatures #-}
{-# Options_GHC -Wno-unused-foralls #-}
module Verifier.SAW.Heapster.TypeChecker (
  -- * Checker type
  Tc, startTc,

  -- * Checker errors
  TypeError(..),

  -- * Checker entry-points
  tcFunPerm,
  tcCtx,
  tcType,
  tcExpr,
  tcValPerm,
  inParsedCtxM,
  tcAtomicPerms,
  tcValPermInCtx,
  tcSortedMbValuePerms,
  ) where

import Control.Monad
import qualified Data.BitVector.Sized as BV
import Data.BitVector.Sized (BV)
import Data.Functor.Product
import Data.Functor.Constant
import GHC.TypeLits (Nat, KnownNat)
import GHC.Natural

import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind

import Prettyprinter hiding (comma, space)

import qualified Data.Type.RList as RL
import Data.Parameterized.Some (Some(Some), mapSome)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.BoolRepr (BoolRepr(TrueRepr))

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Bytes

import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Located
import Verifier.SAW.Heapster.UntypedAST
import Verifier.SAW.Heapster.ParsedCtx

----------------------------------------------------------------------
-- * Type-checking environment
----------------------------------------------------------------------

data TcEnv = TcEnv {
  tcEnvExprVars :: [(String, TypedName)],
  tcEnvPermEnv :: PermEnv
}

----------------------------------------------------------------------
-- * Type errors
----------------------------------------------------------------------

data TypeError = TypeError Pos String
  deriving Show

mkNuMatching [t| TypeError |]

instance Closable TypeError where
  toClosed = unsafeClose

instance Liftable TypeError where
  mbLift = unClosed . mbLift . fmap toClosed

----------------------------------------------------------------------
-- * Type-checking type
----------------------------------------------------------------------

-- | Type-checking computations carrying a 'TcEnv' and which
-- can fail. Access the environment with 'tcLocal' and 'tcAsk'
-- and fail with 'tcError'.
newtype Tc a = Tc { runTc :: TcEnv -> Either TypeError a }

-- | Run a type-checking computation given an initial permission
-- environment.
startTc ::
  Tc a                  {- ^ typechecking action        -} ->
  PermEnv               {- ^ permission environment     -} ->
  Either TypeError a
startTc tc env = runTc tc (TcEnv [] env)

-- | 'fmap' derived from 'Monad'
instance Functor Tc where
  fmap = liftM

-- | ('<*>') derived from 'Monad'
instance Applicative Tc where
  pure x = Tc \_ -> Right x
  (<*>) = ap

instance Monad Tc where
  Tc f >>= g = Tc \env ->
    do x <- f env
       runTc (g x) env

instance MonadBind Tc where
  mbM m = Tc \env ->
    case mbMatch $ fmap (`runTc` env) m of
      [nuMP| Left e  |] -> Left (mbLift e)
      [nuMP| Right x |] -> Right x

-- | Run type-checking computation with local changes to the
-- type-checking environment.
tcLocal ::
  (TcEnv -> TcEnv)      {- ^ environment update         -} ->
  Tc a -> Tc a
tcLocal f (Tc k) = Tc (k . f)

-- | Get current type-checking environment
tcAsk :: Tc TcEnv
tcAsk = Tc Right

-- | Abort checking with an error message
tcError ::
  Pos                   {- ^ error location             -} ->
  String                {- ^ error message              -} ->
  Tc a
tcError p err = Tc (\_ -> Left (TypeError p err))

----------------------------------------------------------------------
-- * Casting
----------------------------------------------------------------------

-- | Cast a typed value to the requested type or
-- raise an error in 'Tc'
tcCastTyped ::
  Pos                   {- ^ position of expression     -} ->
  TypeRepr a            {- ^ target type                -} ->
  Typed f b             {- ^ expression                 -} ->
  Tc (f a)              {- ^ casted expression          -}
tcCastTyped p tp (Typed tp' f) =
  case testEquality tp tp' of
    Just Refl -> pure f
    Nothing   -> tcError p ("Expected type " ++ show tp ++ ", got type " ++ show tp')

----------------------------------------------------------------------
-- * Extending variable environment
----------------------------------------------------------------------

-- | Run a parsing computation in a context extended with an expression variable
withExprVar ::
  String                {- ^ identifier                 -} ->
  TypeRepr tp           {- ^ type of identifer          -} ->
  ExprVar tp            {- ^ implementation             -} ->
  Tc a -> Tc a
withExprVar str tp x = tcLocal \env ->
  env { tcEnvExprVars = (str, Some (Typed tp x)) : tcEnvExprVars env }

-- | Run a parsing computation in a context extended with 0 or more expression
-- variables
withExprVars ::
  RAssign (Constant String) ctx ->
  CruCtx ctx ->
  RAssign Name ctx ->
  Tc a ->
  Tc a
withExprVars MNil                CruCtxNil           MNil       m = m
withExprVars (xs :>: Constant x) (CruCtxCons ctx tp) (ns :>: n) m = withExprVars xs ctx ns (withExprVar x tp n m)

----------------------------------------------------------------------
-- * Checking Types
----------------------------------------------------------------------

-- | Check an 'AstType' as a 'TypeRepr'
tcType :: AstType -> Tc (Some TypeRepr)
tcType t = mapSome unKnownReprObj <$> tcTypeKnown t

-- | Check an 'AstType' and build a @'KnownRepr' 'TypeRepr'@ instance for it
tcTypeKnown :: AstType -> Tc (Some (KnownReprObj TypeRepr))
tcTypeKnown t =
  case t of
    TyUnit          {} -> pure (Some (mkKnownReprObj UnitRepr))
    TyBool          {} -> pure (Some (mkKnownReprObj BoolRepr))
    TyNat           {} -> pure (Some (mkKnownReprObj NatRepr))
    TyLifetime      {} -> pure (Some (mkKnownReprObj LifetimeRepr))
    TyRwModality    {} -> pure (Some (mkKnownReprObj RWModalityRepr))
    TyPermList      {} -> pure (Some (mkKnownReprObj PermListRepr))

    TyBV p n ->
      withPositive p "Zero bitvector width not allowed" n \w ->
        pure (Some (mkKnownReprObj (BVRepr w)))
    TyLlvmPtr p n ->
      withPositive p "Zero LLVM Ptr width not allowed" n \w ->
        pure (Some (mkKnownReprObj (LLVMPointerRepr w)))
    TyLlvmFrame p n ->
      withPositive p "Zero LLVM Frame width not allowed" n \w ->
        pure (Some (mkKnownReprObj (LLVMFrameRepr w)))
    TyLlvmShape p n ->
      withPositive p "Zero LLVM Shape width not allowed" n \w ->
        pure (Some (mkKnownReprObj (LLVMShapeRepr w)))
    TyLlvmBlock p n ->
      withPositive p "Zero LLVM Block width not allowed" n \w ->
        pure (Some (mkKnownReprObj (LLVMBlockRepr w)))

    TyStruct _ fs ->
      do fs1 <- traverse tcTypeKnown fs
         let fs2 = foldl structAdd (Some (mkKnownReprObj Ctx.empty)) fs1
         case fs2 of
           Some xs@KnownReprObj -> pure (Some (mkKnownReprObj (StructRepr (unKnownReprObj xs))))

    TyPerm _ x ->
      do Some tp@KnownReprObj <- tcTypeKnown x
         pure (Some (mkKnownReprObj (ValuePermRepr (unKnownReprObj tp))))

-- | Helper function for building struct type lists
structAdd ::
  Some (KnownReprObj (Ctx.Assignment TypeRepr)) ->
  Some (KnownReprObj TypeRepr) ->
  Some (KnownReprObj (Ctx.Assignment TypeRepr))
structAdd (Some acc@KnownReprObj) (Some x@KnownReprObj) =
  Some (mkKnownReprObj (Ctx.extend (unKnownReprObj acc) (unKnownReprObj x)))

----------------------------------------------------------------------
-- * Checking Expressions
----------------------------------------------------------------------

-- | Parse an identifier as an expression variable of a specific type
tcVar ::
  TypeRepr a            {- ^ expected type              -} ->
  Pos                   {- ^ identifier position        -} ->
  String                {- ^ identifier                 -} ->
  Tc (ExprVar a)
tcVar ty p name =
  do Some tn <- tcTypedName p name
     tcCastTyped p ty tn

-- | Check a valid identifier string as an expression variable
tcTypedName ::
  Pos                   {- ^ identifier position        -} ->
  String                {- ^ identifier                 -} ->
  Tc TypedName
tcTypedName p name =
  do env <- tcAsk
     case lookup name (tcEnvExprVars env) of
       Nothing -> tcError p ("Unknown variable:" ++ name)
       Just stn -> pure stn

-- | Check an 'AstExpr' as a 'PermExpr' with a known type.
tcKExpr :: KnownRepr TypeRepr a => AstExpr -> Tc (PermExpr a)
tcKExpr = tcExpr knownRepr

-- | Check an 'AstExpr' as a 'PermExpr' with a given type.
-- This is a top-level entry-point to the checker that will
-- resolve variables.
tcExpr :: TypeRepr a -> AstExpr -> Tc (PermExpr a)
tcExpr ty (ExVar p name Nothing Nothing) = PExpr_Var <$> tcVar ty p name

tcExpr tp@(LLVMShapeRepr w) (ExVar p name (Just args) Nothing) =
  do env <- tcAsk
     case lookupNamedShape (tcEnvPermEnv env) name of
       Just (SomeNamedShape nmsh)
         | Just Refl <- testEquality w (natRepr nmsh) ->
           do sub <- tcExprs p (namedShapeArgs nmsh) args
              pure (PExpr_NamedShape Nothing Nothing nmsh sub)
       Just (SomeNamedShape nmsh) ->
         tcError p $ renderDoc $ sep
         [ pretty "Named shape" <+> pretty name <+>
           pretty "is of incorrect type"
         , pretty "Expected:" <+> permPretty emptyPPInfo tp
         , pretty "Found:" <+>
           permPretty emptyPPInfo (LLVMShapeRepr (natRepr nmsh)) ]
       Nothing -> tcError p ("Unknown shape name: " ++ name)

tcExpr tp@(ValuePermRepr sub_tp) (ExVar p name (Just args) Nothing) =
  do env <- tcAsk
     case lookupNamedPermName (tcEnvPermEnv env) name of
       Just (SomeNamedPermName npn)
         | Just Refl <- testEquality (namedPermNameType npn) sub_tp ->
           do arg_exprs <- tcExprs p (namedPermNameArgs npn) args
              pure (PExpr_ValPerm $ ValPerm_Named npn arg_exprs NoPermOffset)
       Just (SomeNamedPermName npn) ->
         tcError p $ renderDoc $ sep
         [ pretty "Named permission" <+> pretty (namedPermNameName npn) <+>
           pretty "is of incorrect type"
         , pretty "Expected:" <+> permPretty emptyPPInfo tp
         , pretty "Found:" <+> permPretty emptyPPInfo (namedPermNameType npn) ]
       Nothing -> tcError p ("Unknown shape name: " ++ name)

tcExpr _ (ExVar p _ Just{} _) = tcError p "Unexpected variable instantiation"
tcExpr _ (ExVar p _ _ Just{}) = tcError p "Unexpected variable offset"

tcExpr UnitRepr         e = tcUnit e
tcExpr NatRepr          e = tcNat e
tcExpr (BVRepr w)       e = withKnownNat w (normalizeBVExpr <$> tcBV e)
tcExpr (StructRepr fs)  e = tcStruct fs e
tcExpr LifetimeRepr     e = tcLifetimeLit e
tcExpr (LLVMPointerRepr w) e = withKnownNat w (tcLLVMPointer w e)
tcExpr FunctionHandleRepr{} e = tcError (pos e) "Expected functionhandle" -- no literals
tcExpr PermListRepr     e = tcError (pos e) "Expected permlist" -- no literals
tcExpr RWModalityRepr   e = tcRWModality e
tcExpr (ValuePermRepr t) e = permToExpr <$> tcValPerm t e
tcExpr (LLVMShapeRepr w) e = withKnownNat w (tcLLVMShape e)

tcExpr (IntrinsicRepr s _) e = tcError (pos e) ("Expected intrinsic type: " ++ show s)

-- reprs that we explicitly do not support
tcExpr BoolRepr             e = tcError (pos e) "Expected boolean"
tcExpr IntegerRepr          e = tcError (pos e) "Expected integerl"
tcExpr AnyRepr              e = tcError (pos e) "Expected any type"
tcExpr RealValRepr          e = tcError (pos e) "Expected realval"
tcExpr ComplexRealRepr      e = tcError (pos e) "Expected realval"
tcExpr CharRepr             e = tcError (pos e) "Expected char"
tcExpr RecursiveRepr     {} e = tcError (pos e) "Expected recursive-value"
tcExpr FloatRepr         {} e = tcError (pos e) "Expected float"
tcExpr IEEEFloatRepr     {} e = tcError (pos e) "Expected ieeefloat"
tcExpr StringRepr        {} e = tcError (pos e) "Expected string"
tcExpr MaybeRepr         {} e = tcError (pos e) "Expected maybe"
tcExpr VectorRepr        {} e = tcError (pos e) "Expected vector"
tcExpr VariantRepr       {} e = tcError (pos e) "Expected variant"
tcExpr ReferenceRepr     {} e = tcError (pos e) "Expected reference"
tcExpr WordMapRepr       {} e = tcError (pos e) "Expected wordmap"
tcExpr StringMapRepr     {} e = tcError (pos e) "Expected stringmap"
tcExpr SymbolicArrayRepr {} e = tcError (pos e) "Expected symbolicarray"
tcExpr SymbolicStructRepr{} e = tcError (pos e) "Expected symbolicstruct"
tcExpr SequenceRepr      {} e = tcError (pos e) "Expected sequencerepr"

-- | Check for a unit literal
tcUnit :: AstExpr -> Tc (PermExpr UnitType)
tcUnit ExUnit{} = pure PExpr_Unit
tcUnit e        = tcError (pos e) "Expected unit"

-- | Check for a nat literal
tcNat :: AstExpr -> Tc (PermExpr NatType)
tcNat (ExNat _ i) = pure (PExpr_Nat i)
tcNat e           = tcError (pos e) "Expected integer"

-- | Check for a bitvector expression
tcBV :: (KnownNat w, 1 <= w) => AstExpr -> Tc (PermExpr (BVType w))
tcBV (ExAdd _ x y) = bvAdd <$> tcBV x <*> tcBV y
tcBV (ExNeg _ x)   = bvNegate <$> tcBV x
tcBV e             = tcBVFactor e

-- | Check for a bitvector factor. This is limited to
-- variables, constants, and multiplication by a constant.
tcBVFactor :: (KnownNat w, 1 <= w) => AstExpr -> Tc (PermExpr (BVType w))
-- Constants
tcBVFactor (ExNat _ i) = pure (bvInt (fromIntegral i))
-- Multiplication by a constant
tcBVFactor (ExMul _ c (ExVar p name Nothing Nothing)) =
  do c' <- asBVConst c
     Some tn <- tcTypedName p name
     bvMultBV c' . PExpr_Var <$> tcCastTyped p knownRepr tn
tcBVFactor (ExMul _ (ExVar p name Nothing Nothing) c) =
  do c' <- asBVConst c
     Some tn <- tcTypedName p name
     bvMultBV c' . PExpr_Var <$> tcCastTyped p knownRepr tn
-- Variables
tcBVFactor (ExVar p name Nothing Nothing) =
  do Some tn <- tcTypedName p name
     PExpr_Var <$> tcCastTyped p knownRepr tn
tcBVFactor e = tcError (pos e) "Expected BV factor"

-- | Check for an integer literal, which can be negative. If one is found,
-- convert it to a 'BV'. Fail otherwise.
asBVConst :: (KnownNat w, 1 <= w) => AstExpr -> Tc (BV w)
asBVConst (ExNat _ i) =
  pure $ BV.mkBV knownNat $ toInteger i
asBVConst (ExNeg _ (ExNat _ i)) =
  pure $ BV.negate knownNat $ BV.mkBV knownNat $ toInteger i
asBVConst e =
  tcError (pos e) "Expected integer or negated integer"

-- | Check for a struct literal
tcStruct :: CtxRepr fs -> AstExpr -> Tc (PermExpr (StructType fs))
tcStruct ts (ExStruct p es) = PExpr_Struct <$> tcExprs p (mkCruCtx ts) es
tcStruct _ e = tcError (pos e) "Expected struct"

-- | Check a list of expressions. In case of arity issues
-- an arity error is reported at the given position.
tcExprs ::
  Pos                   {- ^ position for arity error   -} ->
  CruCtx fs             {- ^ expected types             -} ->
  [AstExpr]             {- ^ expressions                -} ->
  Tc (PermExprs fs)
tcExprs p tys es = tcExprs' p tys (reverse es)

-- | Helper for 'tcExprs'
tcExprs' :: Pos -> CruCtx fs -> [AstExpr] -> Tc (PermExprs fs)
tcExprs' _ CruCtxNil [] = pure PExprs_Nil
tcExprs' p (CruCtxCons xs x) (y:ys) =
  do zs <- tcExprs' p xs ys
     z  <- tcExpr x y
     pure (zs :>: z)
tcExprs' p _ _ = tcError p "Bad arity"

-- | Parse a sequence of permissions of some given types
tcValuePerms :: Pos -> RAssign TypeRepr tys -> [AstExpr] -> Tc (RAssign ValuePerm tys)
tcValuePerms p tys es = tcValuePerms' p tys (reverse es)

-- | Helper for 'tcValuePerms'
tcValuePerms' :: Pos -> RAssign TypeRepr tps -> [AstExpr] -> Tc (RAssign ValuePerm tps)
tcValuePerms' _ MNil [] = pure MNil
tcValuePerms' p (xs :>: x) (y:ys) =
  do zs <- tcValuePerms' p xs ys
     z  <- tcValPerm x y
     pure (zs :>: z)
tcValuePerms' p _ _ = tcError p "Bad arity"

-- | Check an rwmodality literal
tcRWModality :: AstExpr -> Tc (PermExpr RWModalityType)
tcRWModality ExRead {} = pure PExpr_Read
tcRWModality ExWrite{} = pure PExpr_Write
tcRWModality e         = tcError (pos e) "Expected rwmodality"

-- | Check an optional lifetime expression. Default to @always@ if missing.
tcOptLifetime :: Maybe AstExpr -> Tc (PermExpr LifetimeType)
tcOptLifetime Nothing = pure PExpr_Always
tcOptLifetime (Just e) = tcKExpr e

-- | Check a lifetime literal
tcLifetimeLit :: AstExpr -> Tc (PermExpr LifetimeType)
tcLifetimeLit ExAlways{} = pure PExpr_Always
tcLifetimeLit e          = tcError (pos e) "Expected lifetime"

-- | Check an LLVM shape expression
tcLLVMShape :: (KnownNat w, 1 <= w) => AstExpr -> Tc (PermExpr (LLVMShapeType w))
tcLLVMShape (ExOrSh _ x y) = PExpr_OrShape <$> tcKExpr x <*> tcKExpr y
tcLLVMShape (ExExSh _ var vartype sh) =
  do Some ktp'@KnownReprObj <- tcTypeKnown vartype
     fmap PExpr_ExShape $ mbM $ nu \z ->
       withExprVar var (unKnownReprObj ktp') z (tcKExpr sh)
tcLLVMShape (ExSeqSh _ x y) = PExpr_SeqShape <$> tcKExpr x <*> tcKExpr y
tcLLVMShape ExEmptySh{} = pure PExpr_EmptyShape
tcLLVMShape (ExEqSh _ len v) = PExpr_EqShape <$> tcKExpr len <*> tcKExpr v
tcLLVMShape (ExPtrSh _ maybe_l maybe_rw sh) =
  PExpr_PtrShape
  <$> traverse tcKExpr maybe_l
  <*> traverse tcKExpr maybe_rw
  <*> tcKExpr sh
tcLLVMShape (ExFieldSh _ w fld) = PExpr_FieldShape <$> tcLLVMFieldShape_ w fld
tcLLVMShape (ExArraySh _ len stride sh) =
  PExpr_ArrayShape
  <$> tcKExpr len
  <*> (Bytes . fromIntegral <$> tcNatural stride)
  <*> tcKExpr sh
tcLLVMShape (ExTupleSh _ sh) = PExpr_TupShape <$> tcKExpr sh
tcLLVMShape (ExFalseSh _) = pure PExpr_FalseShape
tcLLVMShape e = tcError (pos e) "Expected shape"

-- | Field and array helper for 'tcLLVMShape'
tcLLVMFieldShape_ ::
  forall w. (KnownNat w, 1 <= w) => Maybe AstExpr -> AstExpr -> Tc (LLVMFieldShape w)
tcLLVMFieldShape_ Nothing e = tcLLVMFieldShape (knownNat :: NatRepr w) e
tcLLVMFieldShape_ (Just w) e =
  do Some (Pair nr LeqProof) <- tcPositive w
     withKnownNat nr (tcLLVMFieldShape nr e)

-- | Check a single field or array element shape
tcLLVMFieldShape ::
  forall (w :: Nat) (v :: Nat).
  (KnownNat w, 1 <= w) =>
  NatRepr w -> AstExpr -> Tc (LLVMFieldShape v)
tcLLVMFieldShape nr e = LLVMFieldShape <$> tcValPerm (LLVMPointerRepr nr) e

-- | Check a LLVM pointer expression
tcLLVMPointer :: (KnownNat w, 1 <= w) => NatRepr w -> AstExpr -> Tc (PermExpr (LLVMPointerType w))
tcLLVMPointer _ (ExLlvmWord _ e) = PExpr_LLVMWord <$> tcKExpr e
tcLLVMPointer w (ExAdd _ (ExVar p name Nothing Nothing) off) = PExpr_LLVMOffset <$> tcVar (LLVMPointerRepr w) p name <*> tcKExpr off
tcLLVMPointer _ e = tcError (pos e) "Expected llvmpointer"

-- | Check a value permission of a known type in a given context
tcValPermInCtx :: ParsedCtx ctx -> TypeRepr a -> AstExpr -> Tc (Mb ctx (ValuePerm a))
tcValPermInCtx ctx tp = inParsedCtxM ctx . const . tcValPerm tp

-- | Parse a value permission of a known type
tcValPerm :: TypeRepr a -> AstExpr -> Tc (ValuePerm a)
tcValPerm _  ExTrue{} = pure ValPerm_True
tcValPerm _  ExFalse{} = pure ValPerm_False
tcValPerm ty (ExOr _ x y) = ValPerm_Or <$> tcValPerm ty x <*> tcValPerm ty y
tcValPerm ty (ExEq _ e) = ValPerm_Eq <$> tcExpr ty e
tcValPerm ty (ExExists _ var vartype e) =
  do Some ktp'@KnownReprObj <- tcTypeKnown vartype
     fmap ValPerm_Exists $ mbM $ nu \z ->
       withExprVar var (unKnownReprObj ktp') z (tcValPerm ty e)
tcValPerm ty (ExVar p n (Just argEs) maybe_off) =
  do env <- tcEnvPermEnv <$> tcAsk
     case lookupNamedPermName env n of
       Just (SomeNamedPermName rpn)
         | Just Refl <- testEquality (namedPermNameType rpn) ty ->
           do args <- tcExprs p (namedPermNameArgs rpn) argEs
              off <- tcPermOffset ty p maybe_off
              pure (ValPerm_Named rpn args off)
       Just (SomeNamedPermName rpn) ->
         tcError p $ renderDoc $ sep
         [ pretty "Named permission" <+> pretty n <+>
           pretty "is of incorrect type"
         , pretty "Expected:" <+> permPretty emptyPPInfo ty
         , pretty "Found:" <+>
           permPretty emptyPPInfo (namedPermNameType rpn) ]
       Nothing ->
         tcError p ("Unknown named permission '" ++ n ++ "'")
tcValPerm ty (ExVar p n Nothing off) =
  ValPerm_Var <$> tcVar (ValuePermRepr ty) p n <*> tcPermOffset ty p off
tcValPerm ty e = ValPerm_Conj <$> tcAtomicPerms ty e

-- | Parse a @*@-separated list of atomic permissions
tcAtomicPerms :: TypeRepr a -> AstExpr -> Tc [AtomicPerm a]
tcAtomicPerms ty (ExMul _ x y) = (++) <$> tcAtomicPerms ty x <*> tcAtomicPerms ty y
tcAtomicPerms ty e = pure <$> tcAtomicPerm ty e

-- | Parse an atomic permission of a specific type
tcAtomicPerm :: TypeRepr a -> AstExpr -> Tc (AtomicPerm a)
tcAtomicPerm ty (ExVar p n (Just argEs) maybe_off) =
  do env <- tcEnvPermEnv <$> tcAsk
     case lookupNamedPermName env n of
       Just (SomeNamedPermName npn)
         | Just Refl <- testEquality (namedPermNameType npn) ty
         , TrueRepr <- nameIsConjRepr npn ->
             do args <- tcExprs p (namedPermNameArgs npn) argEs
                off <- tcPermOffset ty p maybe_off
                return (Perm_NamedConj npn args off)
       Just (SomeNamedPermName npn)
         | Just Refl <- testEquality (namedPermNameType npn) ty ->
         tcError p ("Non-conjoinable permission name '" ++ n
                  ++ "' used in conjunctive context")
       Just (SomeNamedPermName _) ->
         tcError p ("Permission name '" ++ n ++ "' has incorrect type")
       Nothing ->
         tcError p ("Unknown permission name '" ++ n ++ "'")
tcAtomicPerm (LLVMPointerRepr w) e = withKnownNat w (tcPointerAtomic e)
tcAtomicPerm (LLVMFrameRepr w) e = withKnownNat w (tcFrameAtomic e)
tcAtomicPerm (LLVMBlockRepr w) e = withKnownNat w (tcBlockAtomic e)
tcAtomicPerm (StructRepr tys) e = tcStructAtomic tys e
tcAtomicPerm LifetimeRepr e = tcLifetimeAtomic e
tcAtomicPerm _ (ExAny _) = return Perm_Any
tcAtomicPerm _ e = tcError (pos e) "Expected perm"

-- | Build a field permission using an 'LLVMFieldShape'
fieldPermFromShape :: (KnownNat w, 1 <= w) => PermExpr RWModalityType ->
                      PermExpr LifetimeType -> PermExpr (BVType w) ->
                      LLVMFieldShape w -> AtomicPerm (LLVMPointerType w)
fieldPermFromShape rw l off (LLVMFieldShape p) =
  Perm_LLVMField $ LLVMFieldPerm rw l off p

-- | Check an LLVM pointer atomic permission expression
tcPointerAtomic :: (KnownNat w, 1 <= w) => AstExpr -> Tc (AtomicPerm (LLVMPointerType w))
tcPointerAtomic (ExPtr _ l rw off sz c) =
  fieldPermFromShape
  <$> tcKExpr rw
  <*> tcOptLifetime l
  <*> tcKExpr off
  <*> tcLLVMFieldShape_ sz c
tcPointerAtomic (ExArray _ l rw off len stride sh) =
  Perm_LLVMArray <$> tcArrayAtomic l rw off len stride sh
tcPointerAtomic (ExMemblock _ l rw off len sh) = Perm_LLVMBlock <$> tcMemblock l rw off len sh
tcPointerAtomic (ExFree      _ x  ) = Perm_LLVMFree <$> tcKExpr x
tcPointerAtomic (ExLlvmFunPtr _ n w f) = tcFunPtrAtomic n w f
tcPointerAtomic (ExEqual     _ x y) = Perm_BVProp <$> (BVProp_Eq   <$> tcKExpr x <*> tcKExpr y)
tcPointerAtomic (ExNotEqual  _ x y) = Perm_BVProp <$> (BVProp_Neq  <$> tcKExpr x <*> tcKExpr y)
tcPointerAtomic (ExLessThan  _ x y) = Perm_BVProp <$> (BVProp_ULt  <$> tcKExpr x <*> tcKExpr y)
tcPointerAtomic (ExLessEqual _ x y) = Perm_BVProp <$> (BVProp_ULeq <$> tcKExpr x <*> tcKExpr y)
tcPointerAtomic e = tcError (pos e) "Expected pointer perm"

-- | Check a function pointer permission literal
tcFunPtrAtomic ::
  (KnownNat w, 1 <= w) =>
  AstExpr -> AstExpr -> AstFunPerm -> Tc (AtomicPerm (LLVMPointerType w))
tcFunPtrAtomic x y fun =
  do Some args_no            <- mkNatRepr <$> tcNatural x
     Some (Pair w' LeqProof) <- tcPositive y
     Some args               <- pure (cruCtxReplicate args_no (LLVMPointerRepr w'))
     SomeFunPerm fun_perm    <- tcFunPerm args (LLVMPointerRepr w') fun
     pure (mkPermLLVMFunPtr knownNat fun_perm)

-- | Check a memblock permission literal
tcMemblock ::
  (KnownNat w, 1 <= w) =>
  Maybe AstExpr ->
  AstExpr -> AstExpr -> AstExpr -> AstExpr -> Tc (LLVMBlockPerm w)
tcMemblock l rw off len sh =
  do llvmBlockLifetime <- tcOptLifetime l
     llvmBlockRW       <- tcKExpr rw
     llvmBlockOffset   <- tcKExpr off
     llvmBlockLen      <- tcKExpr len
     llvmBlockShape    <- tcKExpr sh
     pure LLVMBlockPerm{..}

-- | Check an atomic array permission literal
tcArrayAtomic ::
  (KnownNat w, 1 <= w) => Maybe AstExpr -> AstExpr -> AstExpr -> AstExpr ->
  AstExpr -> AstExpr -> Tc (LLVMArrayPerm w)
tcArrayAtomic l rw off len stride sh =
  LLVMArrayPerm
  <$> tcKExpr rw
  <*> tcOptLifetime l
  <*> tcKExpr off
  <*> tcKExpr len
  <*> (Bytes . fromIntegral <$> tcNatural stride)
  <*> tcKExpr sh
  <*> pure []

-- | Check a frame permission literal
tcFrameAtomic :: (KnownNat w, 1 <= w) => AstExpr -> Tc (AtomicPerm (LLVMFrameType w))
tcFrameAtomic (ExLlvmFrame _ xs) =
  Perm_LLVMFrame <$> traverse (\(e,i) -> (,) <$> tcKExpr e <*> pure (fromIntegral i)) xs
tcFrameAtomic e = tcError (pos e) "Expected llvmframe perm"

-- | Check a struct permission literal
tcStructAtomic :: CtxRepr tys -> AstExpr -> Tc (AtomicPerm (StructType tys))
tcStructAtomic tys (ExStruct p es) = Perm_Struct <$> tcValuePerms p (assignToRList tys) es
tcStructAtomic _ e = tcError (pos e) "Expected struct perm"

-- | Check a block shape permission literal
tcBlockAtomic :: (KnownNat w, 1 <= w) => AstExpr -> Tc (AtomicPerm (LLVMBlockType w))
tcBlockAtomic (ExShape _ e) = Perm_LLVMBlockShape <$> tcKExpr e
tcBlockAtomic e = tcError (pos e) "Expected llvmblock perm"

-- | Check a lifetime permission literal
tcLifetimeAtomic :: AstExpr -> Tc (AtomicPerm LifetimeType)
tcLifetimeAtomic (ExLOwned _ ls ps_in ps_out) =
  do Some ps_in' <- tcDistPerms ps_in
     Some ps_out' <- tcDistPerms ps_out
     ls' <- mapM tcKExpr ls
     let eps_in = distPermsToExprPerms $ unTypeDistPerms ps_in'
     let eps_out = distPermsToExprPerms $ unTypeDistPerms ps_out'
     pure (Perm_LOwned ls' (typedDistPermsCtx ps_in')
           (typedDistPermsCtx ps_out') eps_in eps_out)
tcLifetimeAtomic (ExLCurrent _ l) = Perm_LCurrent <$> tcOptLifetime l
tcLifetimeAtomic (ExLFinished _) = return Perm_LFinished
tcLifetimeAtomic e = tcError (pos e) "Expected lifetime perm"

-- | Check a sequence @x1:p1, ..., xn:pn@ of variables and permissions
tcDistPerms :: [(Located String,AstExpr)] -> Tc (Some TypedDistPerms)
tcDistPerms [] = pure (Some MNil)
tcDistPerms ((Located p n,e):xs) =
  do Some (Typed tp x) <- tcTypedName p n
     perm <- tcValPerm tp e
     Some ps <- tcDistPerms xs
     pure (Some (ps :>: Typed tp (VarAndPerm x perm)))

-- | Helper for checking permission offsets
tcPermOffset :: TypeRepr a -> Pos -> Maybe AstExpr -> Tc (PermOffset a)
tcPermOffset _ _ Nothing = pure NoPermOffset
tcPermOffset (LLVMPointerRepr w) _ (Just i) = withKnownNat w (LLVMPermOffset <$> tcKExpr i)
tcPermOffset _ p _ = tcError p "Unexpected offset"

-- | Check for a number literal
tcNatural :: AstExpr -> Tc Natural
tcNatural (ExNat _ i) = pure i
tcNatural e = tcError (pos e) "Expected integer literal"

-- | Ensure a natural nubmer is positive
withPositive ::
  Pos                   {- ^ location of literal        -} ->
  String                {- ^ error message              -} ->
  Natural               {- ^ number                     -} ->
  (forall w. (1 <= w, KnownNat w) => NatRepr w -> Tc a)
                        {- ^ continuation               -} ->
  Tc a
withPositive p err n k =
  case someNatGeq1 n of
    Nothing -> tcError p err
    Just (Some (Pair w LeqProof)) -> withKnownNat w (k w)

-- | Check for a positive number literal
tcPositive :: AstExpr -> Tc (Some (Product NatRepr (LeqProof 1)))
tcPositive e =
  do i <- tcNatural e
     withPositive (pos e) "positive required" i \w -> pure (Some (Pair w LeqProof))

-- | Check a typing context @x1:tp1, x2:tp2, ...@
tcCtx :: [(Located String, AstType)] -> Tc (Some ParsedCtx)
tcCtx []         = pure (Some emptyParsedCtx)
tcCtx ((n,t):xs) = preconsSomeParsedCtx (locThing n) <$> tcType t <*> tcCtx xs

-- | Check a sequence @x1:p1, x2:p2, ...@ of variables and their permissions,
-- where each variable occurs at most once. The input list says which variables
-- can occur and which have already been seen. Return a sequence of the
-- permissions in the same order as the input list of variables.
tcSortedValuePerms ::
  VarPermSpecs ctx -> [(Located String, AstExpr)] -> Tc (ValuePerms ctx)
tcSortedValuePerms var_specs [] = pure (varSpecsToPerms var_specs)
tcSortedValuePerms var_specs ((Located p var, x):xs) =
  do Some (Typed tp n) <- tcTypedName p var
     perm              <- tcValPerm tp x
     var_specs'        <- tcSetVarSpecs p var n perm var_specs
     tcSortedValuePerms var_specs' xs

-- | Check a sequence @x1:p1, x2:p2, ...@ of variables and their permissions,
-- and sort the result into a 'ValuePerms' in a multi-binding that is in the
-- same order as the 'ParsedCtx' supplied on input
tcSortedMbValuePerms ::
  ParsedCtx ctx -> [(Located String, AstExpr)] -> Tc (MbValuePerms ctx)
tcSortedMbValuePerms ctx perms =
  inParsedCtxM ctx \ns ->
  tcSortedValuePerms (mkVarPermSpecs ns) perms

-- | Check a function permission of the form
--
-- > (x1:tp1, ...). arg1:p1, ... -o
-- >   (y1:tp1', ..., ym:tpm'). arg1:p1', ..., argn:pn', ret:p_ret
--
-- for some arbitrary context @x1:tp1, ...@ of ghost variables
tcFunPerm :: CruCtx args -> TypeRepr ret -> AstFunPerm -> Tc (SomeFunPerm args ret)
tcFunPerm args ret (AstFunPerm _ untyCtx ins untyCtxOut outs) =
  do Some ghosts_ctx@(ParsedCtx _ ghosts) <- tcCtx untyCtx
     Some gouts_ctx@(ParsedCtx _ gouts) <- tcCtx untyCtxOut
     let args_ctx = mkArgsParsedCtx args
         perms_in_ctx = appendParsedCtx ghosts_ctx args_ctx
         perms_out_ctx =
           appendParsedCtx (appendParsedCtx ghosts_ctx args_ctx)
           (consParsedCtx "ret" ret gouts_ctx)
     perms_in  <- tcSortedMbValuePerms perms_in_ctx ins
     perms_out <- tcSortedMbValuePerms perms_out_ctx outs
     pure (SomeFunPerm (FunPerm ghosts args gouts ret perms_in perms_out))

----------------------------------------------------------------------
-- * Parsing Permission Sets and Function Permissions
----------------------------------------------------------------------

-- | Helper type for 'parseValuePerms' that represents whether a pair @x:p@ has
-- been parsed yet for a specific variable @x@ and, if so, contains that @p@
data VarPermSpec a = VarPermSpec (Name a) (Maybe (ValuePerm a))

-- | A sequence of variables @x@ and what pairs @x:p@ have been parsed so far
type VarPermSpecs = RAssign VarPermSpec

-- | Build a 'VarPermSpecs' from a list of names
mkVarPermSpecs :: RAssign Name ctx -> VarPermSpecs ctx
mkVarPermSpecs = RL.map (\n -> VarPermSpec n Nothing)

-- | Find a 'VarPermSpec' for a particular variable
findVarPermSpec :: Name (a :: CrucibleType) ->
                   VarPermSpecs ctx -> Maybe (Member ctx a)
findVarPermSpec _ MNil = Nothing
findVarPermSpec n (_ :>: VarPermSpec n' _)
  | Just Refl <- testEquality n n'
  = Just Member_Base
findVarPermSpec n (specs :>: _) = Member_Step <$> findVarPermSpec n specs

-- | Try to set the permission for a variable in a 'VarPermSpecs' list, raising
-- a parse error if the variable already has a permission or is one of the
-- expected variables
tcSetVarSpecs ::
  Pos -> String -> Name tp -> ValuePerm tp -> VarPermSpecs ctx ->
  Tc (VarPermSpecs ctx)
tcSetVarSpecs p var n perm var_specs =
  case findVarPermSpec n var_specs of
    Nothing -> tcError p ("Unknown variable: " ++ var)
    Just memb ->
      case RL.get memb var_specs of
        VarPermSpec _ Nothing ->
          pure (RL.modify memb (const (VarPermSpec n (Just perm))) var_specs)
        _ -> tcError p ("Variable " ++ var ++ " occurs more than once!")

-- | Convert a 'VarPermSpecs' sequence to a sequence of permissions, using the
-- @true@ permission for any variables without permissions
varSpecsToPerms :: VarPermSpecs ctx -> ValuePerms ctx
varSpecsToPerms MNil = ValPerms_Nil
varSpecsToPerms (var_specs :>: VarPermSpec _ (Just p)) =
  ValPerms_Cons (varSpecsToPerms var_specs) p
varSpecsToPerms (var_specs :>: VarPermSpec _ Nothing) =
  ValPerms_Cons (varSpecsToPerms var_specs) ValPerm_True

-- | Run a parsing computation inside a name-binding for expressions variables
-- given by a 'ParsedCtx'. Returning the results inside a name-binding.
inParsedCtxM ::
  NuMatching a =>
  ParsedCtx ctx -> (RAssign Name ctx -> Tc a) -> Tc (Mb ctx a)
inParsedCtxM (ParsedCtx ids tps) f =
  mbM (nuMulti (cruCtxProxies tps) \ns -> withExprVars ids tps ns (f ns))
