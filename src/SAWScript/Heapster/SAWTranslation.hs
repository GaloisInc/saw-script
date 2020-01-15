{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module SAWScript.Heapster.SAWTranslation where

import Data.Maybe
import Data.Either
import Data.List
import Data.Kind
import GHC.TypeLits
import qualified Data.Functor.Constant as Constant
import Control.Lens hiding ((:>),Index)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Cont

import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), empty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import Data.Parameterized.Context hiding ((:>), empty, take, view, zipWith)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Arch.X86
import Lang.Crucible.CFG.Expr
import qualified Lang.Crucible.CFG.Expr as Expr
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.Analysis.Fixpoint.Components

import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor

import SAWScript.Heapster.CruUtil
import SAWScript.Heapster.Permissions
import SAWScript.Heapster.Implication
import SAWScript.Heapster.TypedCrucible

import Debug.Trace


-- | FIXME HERE: move to Hobbits!
mapRListTail :: MapRList f (ctx :> a) -> MapRList f ctx
mapRListTail (xs :>: _) = xs


----------------------------------------------------------------------
-- * The Type and Expression Translation Monad
----------------------------------------------------------------------

-- | The result of translating a 'PermExpr' at 'CrucibleType' @a@. This is a
-- form of partially static data in the sense of partial evaluation.
data ExprTrans (a :: CrucibleType) where
  -- | LLVM pointers have their translations dictated by their permissions, so
  -- the translations of their expressions have no computational content
  ETrans_LLVM :: ExprTrans (LLVMPointerType w)

  -- | Frames also have no computational content
  ETrans_LLVMFrame :: ExprTrans (LLVMFrameType w)

  -- | Lifetimes also have no computational content
  ETrans_Lifetime :: ExprTrans LifetimeType

  -- | Permission lists also have no computational content
  ETrans_PermList :: ExprTrans PermListType

  -- | The computational content of functions is in their FunPerms, so functions
  -- themselves have no computational content
  ETrans_Fun :: ExprTrans (FunctionHandleType args ret)

  -- | The translation for every other expression type is just a SAW term. Note
  -- that this construct should not be used for the types handled above.
  ETrans_Term :: OpenTerm -> ExprTrans a


-- | A context mapping bound names to their type-level SAW translations
type ExprTransCtx (ctx :: RList CrucibleType) = MapRList ExprTrans ctx

-- | Map an expression translation result to an 'OpenTerm' or 'Nothing' if it
-- has no pure content, i.e., if it is a splitting or LLVM value
exprTransToTerm :: ExprTrans a -> Maybe OpenTerm
exprTransToTerm ETrans_LLVM = Nothing
exprTransToTerm ETrans_LLVMFrame = Nothing
exprTransToTerm ETrans_Lifetime = Nothing
exprTransToTerm ETrans_PermList = Nothing
exprTransToTerm ETrans_Fun = Nothing
exprTransToTerm (ETrans_Term t) = Just t

-- | Call 'exprTransToTerm' and map 'Nothing' to unit
exprTransToTermForce :: ExprTrans a -> OpenTerm
exprTransToTermForce = maybe unitOpenTerm id . exprTransToTerm

-- | Map a context of expression translations to a list of 'OpenTerm's, dropping
-- the "invisible" ones whose types are translated to 'Nothing'
exprCtxToTerms :: ExprTransCtx tps -> [OpenTerm]
exprCtxToTerms =
  catMaybes . mapRListToList . mapMapRList (Constant.Constant . exprTransToTerm)

-- | Translate a variable to a 'Member' proof, raising an error if the variable
-- is unbound
translateVar :: Mb ctx (ExprVar a) -> Member ctx a
translateVar mb_x | Left memb <- mbNameBoundP mb_x = memb
translateVar _ = error "translateVar: unbound variable!"


-- | The type translation monad = a reader monad for 'ExprTransCtx'
type TypeTransM ctx = Reader (ExprTransCtx ctx)

-- | Run a 'TypeTransM' in an empty context
runTypeTransM :: TypeTransM RNil a -> a
runTypeTransM m = runReader m MNil

-- | Run a 'TypeTransM' computation in an extended context
inExtTypeTransM :: ExprTrans tp -> TypeTransM (ctx :> tp) a ->
                   TypeTransM ctx a
inExtTypeTransM tp_trans = withReader (:>: tp_trans)

-- | Run a 'TypeTransM' computation in the empty context
inEmptyTypeTransM :: TypeTransM RNil a -> TypeTransM ctx a
inEmptyTypeTransM = withReader (const MNil)

-- | Apply the result of a translation to that of another
applyTransM :: Monad m => m OpenTerm -> m OpenTerm -> m OpenTerm
applyTransM m1 m2 = applyOpenTerm <$> m1 <*> m2

-- | Apply the result of a translation to the results of multiple translations
applyMultiTransM :: Monad m => m OpenTerm -> [m OpenTerm] -> m OpenTerm
applyMultiTransM m ms = foldl applyTransM m ms

-- | Build a lambda in a translation monad
lambdaTransM :: String -> OpenTerm -> (OpenTerm -> Reader r OpenTerm) ->
                Reader r OpenTerm
lambdaTransM x tp body_m =
  do r <- ask
     return $ lambdaOpenTerm x tp (\x -> runReader (body_m x) r)

-- | Build a pi in a translation monad
piTransM :: String -> OpenTerm -> (OpenTerm -> Reader r OpenTerm) ->
            Reader r OpenTerm
piTransM x tp body_m =
  do r <- ask
     return $ piOpenTerm x tp (\x -> runReader (body_m x) r)

-- | Build a let-binding in a translation monad
letTransM :: String -> OpenTerm -> Reader r OpenTerm ->
             (OpenTerm -> Reader r OpenTerm) ->
             Reader r OpenTerm
letTransM x tp rhs_m body_m =
  do r <- ask
     return $
       letOpenTerm x tp (runReader rhs_m r) (\x -> runReader (body_m x) r)


----------------------------------------------------------------------
-- * Translating Types and Pure Expressions
----------------------------------------------------------------------

-- | The typeclass for the type-level translation
class TypeTranslate a ctx res | a ctx -> res where
  tptranslate :: Mb ctx a -> TypeTransM ctx res

instance TypeTranslate (NatRepr n) ctx OpenTerm where
  tptranslate mb_n = return $ natOpenTerm $ mbLift $ fmap intValue mb_n

-- | Helper for writing the 'TypeTranslate' instance for 'TypeRepr'
returnType :: OpenTerm -> TypeTransM ctx (Either (ExprTrans a)
                                          (OpenTerm,
                                           OpenTerm -> ExprTrans a))
returnType tp = return $ Right (tp, ETrans_Term)

-- FIXME: explain this translation
instance TypeTranslate (TypeRepr a) ctx (Either (ExprTrans a)
                                         (OpenTerm,
                                          OpenTerm -> ExprTrans a)) where
  tptranslate [nuP| (AnyRepr) |] =
    return $ error "TypeTranslate: Any"
  tptranslate [nuP| (UnitRepr) |] =
    returnType unitTypeOpenTerm
  tptranslate [nuP| (BoolRepr) |] =
    returnType $ dataTypeOpenTerm "Prelude.Bool" []
  tptranslate [nuP| (NatRepr) |] =
    returnType $ dataTypeOpenTerm "Prelude.Nat" []
  tptranslate [nuP| (IntegerRepr) |] =
    return $ error "TypeTranslate: IntegerRepr"
  tptranslate [nuP| (RealValRepr) |] =
    return $ error "TypeTranslate: RealValRepr"
  tptranslate [nuP| (ComplexRealRepr) |] =
    return $ error "TypeTranslate: ComplexRealRepr"
  tptranslate [nuP| (BVRepr w) |] =
    returnType =<<
    (applyOpenTerm (globalOpenTerm "Prelude.bitvector") <$> tptranslate w)

  -- Our special-purpose intrinsic types, whose translations do not have
  -- computational content
  tptranslate [nuP| (LLVMPointerRepr _) |] =
    return $ Left ETrans_LLVM
  tptranslate [nuP| (LLVMFrameRepr _) |] =
    return $ Left ETrans_LLVMFrame
  tptranslate [nuP| LifetimeRepr |] =
    return $ Left ETrans_Lifetime
  tptranslate [nuP| PermListRepr |] =
    return $ Left ETrans_PermList
  tptranslate [nuP| (IntrinsicRepr _ _) |] =
    return $ error "TypeTranslate: IntrinsicRepr"

  tptranslate [nuP| (RecursiveRepr _ _) |] =
    return $ error "TypeTranslate: RecursiveRepr"
  tptranslate [nuP| (FloatRepr _) |] =
    returnType $ dataTypeOpenTerm "Prelude.Float" []
  tptranslate [nuP| (IEEEFloatRepr _) |] =
    return $ error "TypeTranslate: IEEEFloatRepr"
  tptranslate [nuP| (CharRepr) |] =
    return $ error "TypeTranslate: CharRepr"
  tptranslate [nuP| (StringRepr) |] =
    returnType $ dataTypeOpenTerm "Prelude.String" []
  tptranslate [nuP| (FunctionHandleRepr _ _) |] =
    -- NOTE: function permissions translate to the SAW function, but the
    -- function handle itself has no SAW translation
    return $ Left ETrans_Fun
  tptranslate [nuP| (MaybeRepr tp) |] =
    returnType =<<
    (applyOpenTerm (globalOpenTerm "Prelude.Maybe") <$> translateType tp)
  tptranslate [nuP| (VectorRepr _) |] =
    return $ error "TypeTranslate: VectorRepr (can't map to Vec without size)"
  tptranslate [nuP| (StructRepr _) |] =
    return $ error "TypeTranslate: StructRepr"
  tptranslate [nuP| (VariantRepr _) |] =
    return $ error "TypeTranslate: VariantRepr"
  tptranslate [nuP| (ReferenceRepr _) |] =
    return $ error "TypeTranslate: ReferenceRepr"
  tptranslate [nuP| (WordMapRepr _ _) |] =
    return $ error "TypeTranslate: WordMapRepr"
  tptranslate [nuP| (StringMapRepr _) |] =
    return $ error "TypeTranslate: StringMapRepr"
  tptranslate [nuP| (SymbolicArrayRepr _ _) |] =
    return $ error "TypeTranslate: SymbolicArrayRepr"
  tptranslate [nuP| (SymbolicStructRepr _) |] =
    return $ error "TypeTranslate: SymbolicStructRepr"


-- | Translate a Crucible type to a SAW type, converting 'Nothing' to unit
translateType :: Mb ctx (TypeRepr a) -> TypeTransM ctx OpenTerm
translateType mb_t =
  do eith <- tptranslate mb_t
     case eith of
       Left _ -> return unitTypeOpenTerm
       Right (tp, _) -> return tp

-- | Build the correct 'ExprTrans' from an 'OpenTerm' given its type
mkExprTrans :: TypeRepr a -> OpenTerm -> TypeTransM ctx (ExprTrans a)
mkExprTrans tp trm =
  do mb_tp <- nuMultiTransM $ const tp
     eith <- tptranslate mb_tp
     case eith of
       Left etrans -> return etrans
       Right (_, mk_etrans) -> return $ mk_etrans trm

-- | Build a lambda-abstraction for an expression translation if the associated
-- type has any computational content; otherwise, this operation is the identity
lambdaExprTrans :: String -> TypeRepr a -> TypeTransM (ctx :> a) OpenTerm ->
                   TypeTransM ctx OpenTerm
lambdaExprTrans x tp body =
  do mb_tp <- nuMultiTransM $ const tp
     eith <- tptranslate mb_tp
     case eith of
       Left etrans -> inExtTypeTransM etrans body
       Right (tp_term, mk_etrans) ->
         lambdaTransM x tp_term (\z -> inExtTypeTransM (mk_etrans z) body)

-- | Like 'lambdaExprTrans', but always build a lambda-abstraction, even if the
-- type has no computational content and the lambda is over the unit type
lambdaExprTransForce :: String -> TypeRepr a ->
                        TypeTransM (ctx :> a) OpenTerm ->
                        TypeTransM ctx OpenTerm
lambdaExprTransForce x tp body =
  do mb_tp <- nuMultiTransM $ const tp
     eith <- tptranslate mb_tp
     case eith of
       Left etrans ->
         lambdaTransM x unitTypeOpenTerm (\_ -> inExtTypeTransM etrans body)
       Right (tp_term, mk_etrans) ->
         lambdaTransM x tp_term (\z -> inExtTypeTransM (mk_etrans z) body)

piExprTrans :: String -> TypeRepr a -> TypeTransM (ctx :> a) OpenTerm ->
               TypeTransM ctx OpenTerm
piExprTrans x tp body =
  do mb_tp <- nuMultiTransM $ const tp
     eith <- tptranslate mb_tp
     case eith of
       Left etrans -> inExtTypeTransM etrans body
       Right (tp_term, mk_etrans) ->
         piTransM x tp_term (\z -> inExtTypeTransM (mk_etrans z) body)

instance TypeTranslate (ExprVar a) ctx (ExprTrans a) where
  tptranslate mb_x = mapRListLookup (translateVar mb_x) <$> ask

trueOpenTerm :: OpenTerm
trueOpenTerm = ctorOpenTerm "Prelude.True" []

bvNat :: Integer -> Integer -> OpenTerm
bvNat w n =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvNat")
  [natOpenTerm w, natOpenTerm n]

bvAddOpenTerm :: Integer -> OpenTerm -> OpenTerm -> OpenTerm
bvAddOpenTerm n x y =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvAdd")
  [natOpenTerm n, x, y]

bvMulOpenTerm :: Integer -> OpenTerm -> OpenTerm -> OpenTerm
bvMulOpenTerm n x y =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvMul")
  [natOpenTerm n, x, y]

instance TypeTranslate (PermExpr a) ctx (ExprTrans a) where
  tptranslate [nuP| PExpr_Var x |] = tptranslate x
  tptranslate [nuP| PExpr_Unit |] = return $ ETrans_Term unitOpenTerm
  tptranslate [nuP| PExpr_Nat i |] =
    return $ ETrans_Term $ natOpenTerm $ mbLift i
  tptranslate [nuP| PExpr_BV (bvfactors :: [BVFactor w]) off |] =
    do let w = natVal (Proxy :: Proxy w)
       bv_transs <- mapM tptranslate $ mbList bvfactors
       return $ ETrans_Term $
         bvAddOpenTerm w (foldr (bvMulOpenTerm w) (bvNat w 1) bv_transs)
         (bvNat w $ mbLift off)
  tptranslate [nuP| PExpr_Struct _args |] =
    error "FIXME HERE: translate struct expressions!"
  tptranslate [nuP| PExpr_Always |] =
    return ETrans_Lifetime
  tptranslate [nuP| PExpr_LLVMWord _ |] = return ETrans_LLVM
  tptranslate [nuP| PExpr_LLVMOffset _ _ |] = return ETrans_LLVM
  tptranslate [nuP| PExpr_Fun _ |] = return ETrans_Fun
  tptranslate [nuP| PExpr_PermListNil |] = return ETrans_PermList
  tptranslate [nuP| PExpr_PermListCons _ _ _ |] = return ETrans_PermList

instance TypeTranslate (PermExprs as) ctx (ExprTransCtx as) where
  tptranslate [nuP| PExprs_Nil |] = return MNil
  tptranslate [nuP| PExprs_Cons es e |] =
    (:>:) <$> tptranslate es <*> tptranslate e

instance TypeTranslate (BVFactor w) ctx OpenTerm where
  tptranslate [nuP| BVFactor i x :: BVFactor w |] =
    tptranslate x >>= \x_trans ->
    return $
    bvMulOpenTerm (natVal (Proxy :: Proxy w)) (natOpenTerm (mbLift i))
    (exprTransToTermForce x_trans)

-- | Translate a Crucible type to a SAW type, converting 'Nothing' to unit
translateExpr :: Mb ctx (PermExpr a) -> TypeTransM ctx OpenTerm
translateExpr mb_e = exprTransToTermForce <$> tptranslate mb_e


----------------------------------------------------------------------
-- * Translating Permissions to Types
----------------------------------------------------------------------

-- | The result of translating a "proof element" of a permission of type
-- @'ValuePerm' a@. The idea here is that, for a permission implication or typed
-- statement that consumes or emits permission @p@, the translation consumes or
-- emits an element of the SAW type @'tptranslate' p@.
--
-- Another way to look at a @'PermTrans'@ for permission @p@ is that it is a
-- partially static representation (in the sense of the partial evaluation
-- literature) of a SAW expression of type @'tptranslate' p@. Note that we do
-- not include special representations for disjunctions, existentials, or
-- recursive mu permissions, however, because our type-checker does not
-- generally introduce these forms as intermediate values.
data PermTrans ctx (a :: CrucibleType) where
  -- | An @eq(e)@ permission has no computational content
  PTrans_Eq :: Mb ctx (PermExpr a) -> PermTrans ctx a

  -- | A conjuction of atomic permission translations
  PTrans_Conj :: [AtomicPermTrans ctx a] -> PermTrans ctx a

  -- | The translation for disjunctive, existential, and mu permissions
  PTrans_Term :: Mb ctx (ValuePerm a) -> OpenTerm -> PermTrans ctx a


-- | The 'PermTrans' type for atomic permissions
data AtomicPermTrans ctx a where

  -- | The translation of an LLVM field permission is just the translation of
  -- its contents
  APTrans_LLVMField :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMFieldPerm w) ->
                       PermTrans ctx (LLVMPointerType w) ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | The translation of an LLVM array permission is a SAW term of @Vec@ type;
  -- the function argument knows how to convert an term for a single element of
  -- the array into a 'PermTrans' for that element, and is essentially a capture
  -- of the result of 'tptranslate' on the element type
  APTrans_LLVMArray :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMArrayPerm w) ->
                       (OpenTerm ->
                        [AtomicPermTrans ctx (LLVMPointerType w)]) ->
                       OpenTerm ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM free permissions have no computational content
  APTrans_LLVMFree :: (1 <= w, KnownNat w) =>
                      Mb ctx (PermExpr (BVType w)) ->
                      AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM frame permissions have no computational content
  APTrans_LLVMFrame :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMFramePerm w) ->
                       AtomicPermTrans ctx (LLVMFrameType w)

  -- | Lifetime permissions have no computational content
  APTrans_LifetimePerm :: Mb ctx (AtomicPerm LifetimeType) ->
                          AtomicPermTrans ctx LifetimeType

  -- | The translation of functional permission is a SAW term of functional type
  APTrans_Fun :: Mb ctx (FunPerm ghosts (CtxToRList cargs) ret) -> OpenTerm ->
                 AtomicPermTrans ctx (FunctionHandleType cargs ret)

  -- | Propositional permissions are represented by a SAW term
  APTrans_BVProp :: (1 <= w, KnownNat w) => Mb ctx (BVProp w) ->
                    OpenTerm -> AtomicPermTrans ctx (LLVMPointerType w)


-- | The translation of the vacuously true permission
pattern PTrans_True :: PermTrans ctx a
pattern PTrans_True = PTrans_Conj []

-- | Extract the body of a conjunction or raise an error
unPTransConj :: String -> PermTrans ctx a -> [AtomicPermTrans ctx a]
unPTransConj _ (PTrans_Conj ps) = ps
unPTransConj str _ = error (str ++ ": not a conjunction")

-- | Extract the body of a conjunction, which should have exactly one conjunct,
-- or raise an error
unPTransConj1 :: String -> PermTrans ctx a -> AtomicPermTrans ctx a
unPTransConj1 str ptrans =
  case unPTransConj str ptrans of
    [aptrans] -> aptrans
    _ -> error (str ++ ": not a single-element conjunction")

-- | Extract the body of a conjunction of a single field permission
unPTransLLVMField :: String -> PermTrans ctx (LLVMPointerType w) ->
                     (Mb ctx (LLVMFieldPerm w),
                      PermTrans ctx (LLVMPointerType w))
unPTransLLVMField _ (PTrans_Conj [APTrans_LLVMField e ptrans]) = (e, ptrans)
unPTransLLVMField str _ = error (str ++ ": not an LLVM field permission")

-- | Extract the body of a conjunction of a single array permission
unPTransLLVMArray :: String -> PermTrans ctx (LLVMPointerType w) ->
                     (Mb ctx (LLVMArrayPerm w),
                      (OpenTerm -> [AtomicPermTrans ctx (LLVMPointerType w)]),
                      OpenTerm)
unPTransLLVMArray _ (PTrans_Conj [APTrans_LLVMArray e f trm]) = (e, f, trm)
unPTransLLVMArray str _ = error (str ++ ": not an LLVM array permission")

-- | A context mapping bound names to their perm translations
type PermTransCtx ctx ps = MapRList (PermTrans ctx) ps

-- | Build a permission translation context with just @true@ permissions
truePermTransCtx :: CruCtx ps -> PermTransCtx ctx ps
truePermTransCtx CruCtxNil = MNil
truePermTransCtx (CruCtxCons ctx _) = truePermTransCtx ctx :>: PTrans_True

-- | Map a perm translation result to an 'OpenTerm', or to 'Nothing' if it has
-- no computational content
permTransToTerm :: PermTrans ctx a -> Maybe OpenTerm
permTransToTerm (PTrans_Eq _) = Nothing
permTransToTerm (PTrans_Conj aps) =
  case mapMaybe atomicPermTransToTerm aps of
    [] -> Nothing
    ts -> Just $ tupleOpenTerm ts
permTransToTerm (PTrans_Term _ t) = Just t

-- | Map an atomic perm translation result to an 'OpenTerm', or to 'Nothing' if
-- the atomic perm has no computational content
atomicPermTransToTerm :: AtomicPermTrans ctx a -> Maybe OpenTerm
atomicPermTransToTerm (APTrans_LLVMField _ ptrans) = permTransToTerm ptrans
atomicPermTransToTerm (APTrans_LLVMArray _ _ t) = Just t
atomicPermTransToTerm (APTrans_LLVMFree _) = Nothing
atomicPermTransToTerm (APTrans_LLVMFrame _) = Nothing
atomicPermTransToTerm (APTrans_LifetimePerm _) = Nothing
atomicPermTransToTerm (APTrans_Fun _ t) = Just t
atomicPermTransToTerm (APTrans_BVProp _ t) = Just t

-- | Map a perm translation result to an 'OpenTerm', or to a unit if it has no
-- computational content
permTransToTermForce :: PermTrans ctx a -> OpenTerm
permTransToTermForce = maybe unitOpenTerm id . permTransToTerm

-- | Map a context of perm translations to a list of 'OpenTerm's, dropping the
-- "invisible" ones whose permissions are translated to 'Nothing'
permCtxToTerms :: PermTransCtx ctx tps -> [OpenTerm]
permCtxToTerms =
  catMaybes . mapRListToList . mapMapRList (Constant.Constant . permTransToTerm)

-- | Extract out the permission of a permission translation result
permTransPerm :: MapRList Proxy ctx -> PermTrans ctx a -> Mb ctx (ValuePerm a)
permTransPerm _ (PTrans_Eq e) = fmap ValPerm_Eq e
permTransPerm prxs (PTrans_Conj ts) =
  fmap ValPerm_Conj $ foldr (mbMap2 (:)) (nuMulti prxs $ const []) $
  map (atomicPermTransPerm prxs) ts
permTransPerm _ (PTrans_Term p _) = p

atomicPermTransPerm :: MapRList Proxy ctx -> AtomicPermTrans ctx a ->
                       Mb ctx (AtomicPerm a)
atomicPermTransPerm prxs (APTrans_LLVMField fld _) = fmap Perm_LLVMField fld
atomicPermTransPerm prxs (APTrans_LLVMArray ap _ _) = fmap Perm_LLVMArray ap
atomicPermTransPerm prxs (APTrans_LLVMFree e) = fmap Perm_LLVMFree e
atomicPermTransPerm prxs (APTrans_LLVMFrame fp) = fmap Perm_LLVMFrame fp
atomicPermTransPerm prxs (APTrans_LifetimePerm p) = p
atomicPermTransPerm prxs (APTrans_Fun fp _) = fmap Perm_Fun fp
atomicPermTransPerm prxs (APTrans_BVProp prop _) = fmap Perm_BVProp prop

-- | Test that a permission equals that of a permission translation
permTransPermEq :: PermTrans ctx a -> Mb ctx (ValuePerm a) -> Bool
permTransPermEq ptrans mb_p =
  permTransPerm (mbToProxy mb_p) ptrans == mb_p

extMb :: Mb ctx a -> Mb (ctx :> tp) a
extMb = mbCombine . fmap (nu . const)

-- | Extend the context of a permission translation result
extPermTrans :: PermTrans ctx a -> PermTrans (ctx :> tp) a
extPermTrans (PTrans_Eq e) = PTrans_Eq $ extMb e
extPermTrans (PTrans_Conj aps) = PTrans_Conj (map extAtomicPermTrans aps)
extPermTrans (PTrans_Term p t) = PTrans_Term (extMb p) t

-- | Extend the context of an atomic permission translation result
extAtomicPermTrans :: AtomicPermTrans ctx a -> AtomicPermTrans (ctx :> tp) a
extAtomicPermTrans (APTrans_LLVMField fld ptrans) =
  APTrans_LLVMField (extMb fld) (extPermTrans ptrans)
extAtomicPermTrans (APTrans_LLVMArray ap f t) =
  APTrans_LLVMArray (extMb ap) (map extAtomicPermTrans . f) t
extAtomicPermTrans (APTrans_LLVMFree e) = APTrans_LLVMFree $ extMb e
extAtomicPermTrans (APTrans_LLVMFrame fp) = APTrans_LLVMFrame $ extMb fp
extAtomicPermTrans (APTrans_LifetimePerm p) = APTrans_LifetimePerm $ extMb p
extAtomicPermTrans (APTrans_Fun fp t) = APTrans_Fun (extMb fp) t
extAtomicPermTrans (APTrans_BVProp prop t) = APTrans_BVProp (extMb prop) t

-- | Extend the context of a permission translation context
extPermTransCtx :: PermTransCtx ctx ps -> PermTransCtx (ctx :> tp) ps
extPermTransCtx = mapMapRList extPermTrans

-- | Add another permission translation to a permission translation context
consPermTransCtx :: PermTransCtx ctx ps -> PermTrans ctx a ->
                    PermTransCtx ctx (ps :> a)
consPermTransCtx = (:>:)

-- | Apply 'offsetLLVMAtomicPerm' to the permissions associated with an 
offsetLLVMAtomicPermTrans :: Mb ctx (PermExpr (BVType w)) ->
                             AtomicPermTrans ctx (LLVMPointerType w) ->
                             AtomicPermTrans ctx (LLVMPointerType w)
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMField fld ptrans) =
  APTrans_LLVMField (mbMap2 offsetLLVMFieldPerm mb_off fld) ptrans
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMArray ap f t) =
  APTrans_LLVMArray (mbMap2 offsetLLVMArrayPerm mb_off ap) f t
offsetLLVMAtomicPermTrans _ p@(APTrans_LLVMFree _) = p

-- | Put a 'PermTrans' into a lifetime. This is the same as applying
-- 'inLifetime' to the 'permTransPerm' of a 'PermTrans'.
permTransInLifetime :: Mb ctx (PermExpr LifetimeType) ->
                       PermTrans ctx a -> PermTrans ctx a
permTransInLifetime _ p@(PTrans_Eq _) = p
permTransInLifetime l (PTrans_Conj ps) =
  PTrans_Conj $ map (atomicPermTransInLifetime l) ps
permTransInLifetime l (PTrans_Term p t) =
  PTrans_Term (mbMap2 inLifetime l p) t

-- | Like 'permTransInLifetime' but for atomic permission translations
atomicPermTransInLifetime :: Mb ctx (PermExpr LifetimeType) ->
                     AtomicPermTrans ctx a ->
                     AtomicPermTrans ctx a
atomicPermTransInLifetime l (APTrans_LLVMField fld ptrans) =
  APTrans_LLVMField (mbMap2 inLifetime l fld) $
  permTransInLifetime l ptrans
atomicPermTransInLifetime l (APTrans_LLVMArray ap f t) =
  APTrans_LLVMArray (mbMap2 inLifetime l ap)
  (map (atomicPermTransInLifetime l) . f)
  t
atomicPermTransInLifetime _ p@(APTrans_LLVMFree _) = p
atomicPermTransInLifetime _ p@(APTrans_LLVMFrame _) = p
atomicPermTransInLifetime l (APTrans_LifetimePerm p) =
  APTrans_LifetimePerm $ mbMap2 inLifetime l p
atomicPermTransInLifetime _ p@(APTrans_Fun _ _) = p
atomicPermTransInLifetime _ p@(APTrans_BVProp _ _) = p

-- | Map a 'PermTrans' to the permission it should have after a lifetime has
-- ended, undoing 'minLtEndPerms'. The first argument should have associated
-- permissions that equal 'minLtEndPerms' of the second. This operation does not
-- actually modify the translation itself, just changes the associated
-- permissions.
permTransEndLifetime :: PermTrans ctx a -> Mb ctx (ValuePerm a) ->
                        PermTrans ctx a
permTransEndLifetime p@(PTrans_Eq _) _ = p
permTransEndLifetime (PTrans_Conj ptranss) [nuP| ValPerm_Conj ps |] =
  PTrans_Conj $ zipWith atomicPermTransEndLifetime ptranss (mbList ps)
permTransEndLifetime (PTrans_Term _ t) p2 = PTrans_Term p2 t
permTransEndLifetime _ _ =
  error "permTransEndLifetime: permissions don't agree!"

-- | Like 'permTransEndLifetime' but for atomic permission translations
atomicPermTransEndLifetime :: AtomicPermTrans ctx a -> Mb ctx (AtomicPerm a) ->
                              AtomicPermTrans ctx a
atomicPermTransEndLifetime (APTrans_LLVMField
                            _ ptrans) [nuP| Perm_LLVMField fld |] =
  APTrans_LLVMField fld $
  permTransEndLifetime ptrans (fmap llvmFieldContents fld)
atomicPermTransEndLifetime (APTrans_LLVMArray
                            _ f t) [nuP| Perm_LLVMArray ap |] =
  APTrans_LLVMArray ap
  (\trm -> zipWith atomicPermTransEndLifetime (f trm)
           (mbList $ fmap (map Perm_LLVMField . llvmArrayFields) ap))
  t
atomicPermTransEndLifetime p@(APTrans_LLVMFree _) _ = p
atomicPermTransEndLifetime p@(APTrans_LLVMFrame _) _ = p
atomicPermTransEndLifetime p@(APTrans_LifetimePerm _) _ = p
atomicPermTransEndLifetime p@(APTrans_Fun _ _) _ = p
atomicPermTransEndLifetime p@(APTrans_BVProp _ _) _ = p
atomicPermTransEndLifetime _ _ =
  error "atomicPermTransEndLifetime: permissions don't agree!"


-- | Apply 'permTransEndLifetime' to a 'PermTransCtx'
permCtxEndLifetime :: PermTransCtx ctx ps -> Mb ctx (DistPerms ps) ->
                      PermTransCtx ctx ps
permCtxEndLifetime MNil _ = MNil
permCtxEndLifetime (ptranss :>: ptrans) [nuP| DistPermsCons perms _ p |] =
  permCtxEndLifetime ptranss perms :>: permTransEndLifetime ptrans p

-- [| p :: ValuePerm |] = type of the impl translation of reg with perms p
instance TypeTranslate (ValuePerm a) ctx (Either (PermTrans ctx a)
                                          (OpenTerm,
                                           OpenTerm -> PermTrans ctx a)) where
  tptranslate [nuP| ValPerm_Eq e |] = return $ Left $ PTrans_Eq e
  tptranslate p@[nuP| ValPerm_Or p1 p2 |] =
    do tp1 <- translatePerm p1
       tp2 <- translatePerm p2
       return $ Right (dataTypeOpenTerm "Prelude.Either" [tp1, tp2],
                       PTrans_Term p)
  tptranslate p@[nuP| ValPerm_Exists (p1 :: Binding tp (ValuePerm b)) |] =
    do let tp = knownRepr :: TypeRepr tp
       tp_trans <- nuMultiTransM (const tp) >>= translateType
       tp_f <- lambdaExprTransForce "x_ex" tp (translatePerm $ mbCombine p1)
       return $ Right (dataTypeOpenTerm "Prelude.Sigma" [tp_trans, tp_f],
                       PTrans_Term p)
  tptranslate [nuP| ValPerm_Mu _ |] =
    error "FIXME HERE: tptranslate ValPerm_Mu"
  tptranslate [nuP| ValPerm_Var _ |] =
    error "FIXME HERE: tptranslate ValPerm_Var"
  tptranslate [nuP| ValPerm_Conj ps |] =
    mapM tptranslate (mbList ps) >>= \eithers ->
    case partitionEithers eithers of
      (transs, []) -> return $ Left $ PTrans_Conj transs
      (_, [(tp, mk_ptrans)]) ->
        return $ Right (tp, \t -> PTrans_Conj [mk_ptrans t])
      _ ->
        return $ Right (tupleTypeOpenTerm
                        (mapMaybe (\eith -> case eith of
                                      Left _ -> Nothing
                                      Right (tp,_) -> Just tp) eithers),
                        (\t ->
                          PTrans_Conj $ fst $
                          foldl (\(rest, t') eith ->
                                  case eith of
                                    Left ptrans -> (ptrans:rest, t')
                                    Right (_, mk_ptrans) ->
                                      (mk_ptrans (pairLeftOpenTerm t'):rest,
                                       pairRightOpenTerm t'))
                          ([],t) eithers))


instance TypeTranslate (AtomicPerm a) ctx (Either (AtomicPermTrans ctx a)
                                           (OpenTerm,
                                            OpenTerm ->
                                            AtomicPermTrans ctx a)) where
  tptranslate [nuP| Perm_LLVMField fld |] =
    tptranslate (fmap llvmFieldContents fld) >>= \eith ->
    case eith of
      Left ptrans -> return $ Left $ APTrans_LLVMField fld ptrans
      Right (tp_term, mk_ptrans) ->
        return $ Right (tp_term, APTrans_LLVMField fld . mk_ptrans)

  tptranslate ([nuP| Perm_LLVMArray ap@(LLVMArrayPerm _ len _ flds _) |]) =
    do elem_tp <- translateLLVMArrayElemType ap
       len_term <- translateExpr len
       fld_funs <-
         mapM ((either const snd <$>) . tptranslate . fmap Perm_LLVMField)
         (mbList flds)
       let fld_fun elem_trm =
             map (\(f,i) -> f $ projTupleOpenTerm i elem_trm)
             (zip fld_funs [0 ..])
       return $ Right
         (applyOpenTermMulti (globalOpenTerm "Prelude.Vec")
          [len_term, elem_tp],
          APTrans_LLVMArray ap fld_fun)

  tptranslate [nuP| Perm_LLVMFree e |] = return $ Left $ APTrans_LLVMFree e
  tptranslate [nuP| Perm_LLVMFrame fp |] = return $ Left $ APTrans_LLVMFrame fp
  tptranslate p@[nuP| Perm_LOwned _ |] =
    return $ Left $ APTrans_LifetimePerm p
  tptranslate p@[nuP| Perm_LCurrent _ |] =
    return $ Left $ APTrans_LifetimePerm p

  tptranslate ([nuP| Perm_Fun
                   fp@(FunPerm ghosts args ret perms_in perms_out) |]) =
    (piExprCtx (appendCruCtx
                (CruCtxCons (mbLift ghosts) LifetimeRepr)
                (mbLift args)) $
     piPermCtx (mbCombine $ fmap mbCombine perms_in) $ \_ ->
      translateRetType (mbLift ret)
      (mbCombine $ fmap (mbCombine
                         . fmap mbValuePermsToDistPerms) perms_out)) >>= \tp_term ->
    return $ Right (tp_term, APTrans_Fun fp)

  -- The proposition e1 = e2 becomes sort 1 equality in SAW
  -- FIXME: this should use propositional equality
  tptranslate [nuP| Perm_BVProp
                  prop@(BVProp_Eq e1 (e2 :: PermExpr (BVType w))) |] =
    do let w = natVal (Proxy :: Proxy w)
       t1 <- translateExpr e1
       t2 <- translateExpr e2
       return $ Right
         (dataTypeOpenTerm "Prelude.EqP"
          [applyOpenTerm (globalOpenTerm "Prelude.bitvector") (natOpenTerm w),
           t1, t2],
          APTrans_BVProp prop)

  -- The proposition e in [off,off+len) becomes (e-off) < len, which in SAW is
  -- represented as bvslt (e-off) len = True
  tptranslate [nuP| Perm_BVProp
                  prop@(BVProp_InRange (e :: PermExpr (BVType w))
                        (BVRange off len)) |] =
    do let w = natVal (Proxy :: Proxy w)
       t_sub <- translateExpr (mbMap2 bvSub e off)
       t_len <- translateExpr len
       return $ Right
         (dataTypeOpenTerm "Prelude.EqP"
          [globalOpenTerm "Prelude.Bool",
           applyOpenTermMulti (globalOpenTerm "Prelude.bvult")
           [natOpenTerm w, t_sub, t_len],
           trueOpenTerm],
          APTrans_BVProp prop)

  -- The proposition [off1,off1+len1) subset [off2,off2+len2) becomes the
  -- proposition...?
  -- FIXME: must imply (bvToNat (off1 - off2) + bvToNat len1) <= bvToNat len2
  tptranslate [nuP| Perm_BVProp (BVProp_RangeSubset
                  (BVRange (off1 :: PermExpr (BVType w)) len1)
                  (BVRange off2 len2)) |] =
    error "FIXME HERE NOW: translate BVProp_RangeSubset"

  tptranslate [nuP| Perm_BVProp (BVProp_RangesDisjoint
                  (BVRange (off1 :: PermExpr (BVType w)) len1)
                  (BVRange off2 len2)) |] =
    error "FIXME HERE NOW: translate BVProp_RangesDisjoint"


-- | Translate a permission to a SAW type, converting 'Nothing' to unit
translatePerm :: Mb ctx (ValuePerm a) -> TypeTransM ctx OpenTerm
translatePerm mb_p =
  tptranslate mb_p >>= \eith ->
  case eith of
    Left _ -> return unitTypeOpenTerm
    Right (tp_term, _) -> return tp_term

-- | Translate the element type of an array permission
translateLLVMArrayElemType :: Mb ctx (LLVMArrayPerm w) ->
                              TypeTransM ctx OpenTerm
translateLLVMArrayElemType [nuP| LLVMArrayPerm _ _ _ flds _ |] =
  tupleTypeOpenTerm <$>
  mapM (translatePerm . fmap llvmFieldContents) (mbList flds)

-- | Build a lambda-abstraction for a 'PermTrans' if the associated permission
-- has any computational content; otherwise, this operation is the identity
lambdaPermTrans :: String -> Mb ctx (ValuePerm a) ->
                   (PermTrans ctx a -> TypeTransM ctx OpenTerm) ->
                   TypeTransM ctx OpenTerm
lambdaPermTrans _ [nuP| ValPerm_Eq mb_e |] body_f = body_f (PTrans_Eq mb_e)
lambdaPermTrans x mb_p body_f =
  tptranslate mb_p >>= \eith ->
  case eith of
    Left ptrans -> body_f ptrans
    Right (tp_term, mk_ptrans) ->
      lambdaTransM x tp_term (body_f . mk_ptrans)

-- | Like 'lambdaPermTrans', but always build a lambda-abstraction, even if the
-- permission has no computational content and the lambda is over the unit type
lambdaPermTransForce :: String -> Mb ctx (ValuePerm a) ->
                        (PermTrans ctx a -> TypeTransM ctx OpenTerm) ->
                        TypeTransM ctx OpenTerm
lambdaPermTransForce x mb_p body_f =
  tptranslate mb_p >>= \eith ->
  case eith of
    Left ptrans ->
      lambdaTransM x unitTypeOpenTerm (const $ body_f ptrans)
    Right (tp_term, mk_ptrans) ->
      lambdaTransM x tp_term (body_f . mk_ptrans)

-- | FIXME: documentation
lambdaPermCtx :: Mb ctx (ValuePerms ps) ->
                 (PermTransCtx ctx ps -> TypeTransM ctx OpenTerm) ->
                 TypeTransM ctx OpenTerm
lambdaPermCtx [nuP| ValPerms_Nil |] f = f MNil
lambdaPermCtx [nuP| ValPerms_Cons ps p |] f =
  lambdaPermCtx ps $ \pctx -> lambdaPermTrans "p" p $ \ptrans ->
  f (pctx :>: ptrans)

piPermTrans :: String -> Mb ctx (ValuePerm a) ->
               (PermTrans ctx a -> TypeTransM ctx OpenTerm) ->
               TypeTransM ctx OpenTerm
piPermTrans _ [nuP| ValPerm_Eq mb_e |] body_f = body_f (PTrans_Eq mb_e)
piPermTrans x mb_p body_f =
  tptranslate mb_p >>= \eith ->
  case eith of
    Left ptrans -> body_f ptrans
    Right (tp_term, mk_ptrans) ->
      piTransM x tp_term (body_f . mk_ptrans)

piPermCtx :: Mb ctx (ValuePerms ps) ->
             (PermTransCtx ctx ps -> TypeTransM ctx OpenTerm) ->
             TypeTransM ctx OpenTerm
piPermCtx [nuP| ValPerms_Nil |] f = f MNil
piPermCtx [nuP| ValPerms_Cons ps p |] f =
  piPermCtx ps $ \pctx -> piPermTrans "p" p $ \ptrans ->
  f (pctx :>: ptrans)

-- Translate a sequence of permissions into a nested tuple type
instance TypeTranslate (ValuePerms ps) ctx OpenTerm where
  tptranslate ps = tupleTypeOpenTerm <$> helper ps where
    helper :: Mb ctx (ValuePerms ps') -> TypeTransM ctx [OpenTerm]
    helper [nuP| ValPerms_Nil |] = return []
    helper [nuP| ValPerms_Cons ps p |] =
      do rest <- helper ps
         eith <- tptranslate p
         case eith of
           Left _ -> return rest
           Right (tp_term, _) ->
             return (rest ++ [tp_term])

-- Translate a DistPerms into a nested pair type
instance TypeTranslate (DistPerms ps) ctx OpenTerm where
  tptranslate = tptranslate . mbDistPermsToValuePerms

-- | Unpack a SAW nested tuple, whose type is determined by the supplied
-- permissions, into a permission translation context for those permissions
unpackPermCtxTuple :: Mb ctx (ValuePerms ps) -> OpenTerm ->
                      TypeTransM ctx (PermTransCtx ctx ps)
unpackPermCtxTuple top_ps = evalStateT (helper top_ps) where
  helper :: Mb ctx (ValuePerms ps') ->
            StateT OpenTerm (TypeTransM ctx) (PermTransCtx ctx ps')
  helper [nuP| ValPerms_Nil |] = return MNil
  helper [nuP| ValPerms_Cons ps p |] =
    do rest <- helper ps
       eith <- lift $ tptranslate p
       case eith of
         Left ptrans -> return (rest :>: ptrans)
         Right (_, mk_ptrans) ->
           do trm <- get
              put (pairRightOpenTerm trm)
              return (rest :>: mk_ptrans (pairLeftOpenTerm trm))


----------------------------------------------------------------------
-- * The Implication Translation Monad
----------------------------------------------------------------------

-- | A mapping from a block entrypoint to its corresponding SAW variable that is
-- bound to its translation
data TypedEntryTrans ext blocks ret args =
  TypedEntryTrans (TypedEntry ext blocks ret args) OpenTerm

typedEntryTransEntry :: TypedEntryTrans ext blocks ret args ->
                        TypedEntry ext blocks ret args
typedEntryTransEntry (TypedEntryTrans entry _) = entry

-- | A mapping from a block to the SAW functions for each entrypoint
data TypedBlockTrans ext blocks ret args =
  TypedBlockTrans [TypedEntryTrans ext blocks ret args]

-- | A mapping from all block entrypoints to their SAW translations
type TypedBlockMapTrans ext blocks ret =
  MapRList (TypedBlockTrans ext blocks ret) blocks

lookupEntryTrans :: TypedEntryID blocks args ghosts ->
                    TypedBlockMapTrans ext blocks ret ->
                    TypedEntryTrans ext blocks ret args
lookupEntryTrans entryID blkMap =
  let TypedBlockTrans entries = mapRListLookup (entryBlockID entryID) blkMap in
  foldr (\trans rest ->
          case trans of
            TypedEntryTrans (TypedEntry entryID' _ _ _ _ _) _
              | Just Refl <- testEquality entryID entryID' -> trans
            _ -> rest)
  (case find (\(TypedEntryTrans entry _) ->
               typedEntryIndex entry == entryIndex entryID) entries of
      Just entry ->
        error ("lookupEntryTrans: type mismatch on entry "
               ++ show (entryIndex entryID))
      Nothing ->
        error ("lookupEntryTrans: entry " ++ show (entryIndex entryID)
               ++ " not in list: "
               ++ show (map (typedEntryIndex . typedEntryTransEntry) entries)))
  entries

-- | Translate an entrypoint ID by looking up its SAW function
translateTypedEntryID :: TypedEntryID blocks args ghosts ->
                         TypedBlockMapTrans ext blocks ret ->
                         OpenTerm
translateTypedEntryID entryID blkMap =
  case lookupEntryTrans entryID blkMap of
    TypedEntryTrans _ trm -> trm

-- | Contextual info for an implication translation
data ImpTransInfo ext blocks ret ps ctx =
  ImpTransInfo
  {
    itiExprCtx :: ExprTransCtx ctx,
    itiPermCtx :: PermTransCtx ctx ctx,
    itiPermStack :: PermTransCtx ctx ps,
    itiPermStackVars :: MapRList (Member ctx) ps,
    itiBlockMapTrans :: TypedBlockMapTrans ext blocks ret,
    itiCatchHandler :: OpenTerm,
    itiReturnType :: OpenTerm
  }

-- | Return the default catch handler of a given return type, which is just a
-- call to @errorM@ at that type
defaultCatchHandler :: OpenTerm -> OpenTerm
defaultCatchHandler = applyOpenTerm (globalOpenTerm "Prelude.errorM")

-- | Extend the context of an 'ImpTransInfo'
extPermTransInfo :: ExprTrans tp -> PermTrans (ctx :> tp) tp ->
                    ImpTransInfo ext blocks ret ps ctx ->
                    ImpTransInfo ext blocks ret ps (ctx :> tp)
extPermTransInfo tp_trans perm_trans (ImpTransInfo {..}) =
  ImpTransInfo
  { itiExprCtx = itiExprCtx :>: tp_trans
  , itiPermCtx = consPermTransCtx (extPermTransCtx itiPermCtx) perm_trans
  , itiPermStack = extPermTransCtx itiPermStack
  , itiPermStackVars = mapMapRList Member_Step itiPermStackVars
  , .. }

-- | The monad for translating permission implications
type ImpTransM ext blocks ret ps ctx =
  Reader (ImpTransInfo ext blocks ret ps ctx)

-- | Run an 'ImpTransM' computation in a 'TypeTransM' context (FIXME: better
-- documentation; e.g., the pctx starts on top of the stack)
impTransM :: PermTransCtx ctx ctx -> TypedBlockMapTrans ext blocks ret ->
             OpenTerm -> ImpTransM ext blocks ret ctx ctx a ->
             TypeTransM ctx a
impTransM pctx mapTrans retType =
  withReader $ \ectx ->
  ImpTransInfo { itiExprCtx = ectx,
                 itiPermCtx = mapMapRList (const $ PTrans_True) pctx,
                 itiPermStack = pctx,
                 itiPermStackVars = members pctx,
                 itiBlockMapTrans = mapTrans,
                 itiCatchHandler = defaultCatchHandler retType,
                 itiReturnType = retType }

-- | Embed a type translation into an impure translation
tpTransM :: TypeTransM ctx a -> ImpTransM ext blocks ret ps ctx a
tpTransM = withReader itiExprCtx

-- | Run an 'ImpTransM' computation in an extended context
inExtImpTransM :: ExprTrans tp -> PermTrans (ctx :> tp) tp ->
                  ImpTransM ext blocks ret ps (ctx :> tp) a ->
                  ImpTransM ext blocks ret ps ctx a
inExtImpTransM tp_trans perm_trans =
  withReader $ extPermTransInfo tp_trans perm_trans

-- | Get most recently bound variable
getTopVarM :: ImpTransM ext blocks ret ps (ctx :> tp) (ExprTrans tp)
getTopVarM = (\(_ :>: p) -> p) <$> itiExprCtx <$> ask

-- | Get the top permission on the stack
getTopPermM :: ImpTransM ext blocks ret (ps :> tp) ctx (PermTrans ctx tp)
getTopPermM = (\(_ :>: p) -> p) <$> itiPermStack <$> ask

-- | Apply a transformation to the (translation of the) current perm stack
withPermStackM :: (MapRList (Member ctx) ps_in -> MapRList (Member ctx) ps_out) ->
                  (PermTransCtx ctx ps_in -> PermTransCtx ctx ps_out) ->
                  ImpTransM ext blocks ret ps_out ctx a ->
                  ImpTransM ext blocks ret ps_in ctx a
withPermStackM f_vars f_p =
  withReader $ \info ->
  info { itiPermStack = f_p (itiPermStack info),
         itiPermStackVars = f_vars (itiPermStackVars info) }

-- | Assert a property of the current permission stack, raising an 'error' if it
-- fails to hold. The 'String' names the construct being translated.
assertPermStackM :: String -> (MapRList (Member ctx) ps ->
                               PermTransCtx ctx ps -> Bool) ->
                    ImpTransM ext blocks ret ps ctx ()
assertPermStackM nm f =
  ask >>= \info ->
  if f (itiPermStackVars info) (itiPermStack info) then return () else
    error ("translate: " ++ nm)

-- | Assert that the current permission stack equals the given 'DistPerms'
assertPermStackEqM :: String -> Mb ctx (DistPerms ps) ->
                      ImpTransM ext blocks ret ps ctx ()
assertPermStackEqM nm perms =
  assertPermStackM nm (helper perms)
  where
    helper :: Mb ctx (DistPerms ps) -> MapRList (Member ctx) ps ->
              PermTransCtx ctx ps -> Bool
    helper [nuP| DistPermsNil |] _ _ = True
    helper [nuP| DistPermsCons perms x p |] (xs :>: x') (ptranss :>: ptrans) =
      x' == translateVar x && permTransPermEq ptrans p &&
      helper perms xs ptranss

-- | Assert that the top permission is as given by the arguments
assertTopPermM :: String -> Mb ctx (ExprVar a) -> Mb ctx (ValuePerm a) ->
                  ImpTransM ext blocks ret (ps :> a) ctx ()
assertTopPermM nm x p =
  assertPermStackM nm (\(_ :>: x_top) (_ :>: p_top) ->
                        x_top == translateVar x && permTransPermEq p_top p)

-- | Get the (translation of the) perms for a variable
getVarPermM :: Mb ctx (ExprVar tp) ->
               ImpTransM ext blocks ret ps ctx (PermTrans ctx tp)
getVarPermM x = mapRListLookup (translateVar x) <$> itiPermCtx <$> ask

-- | Assert that a variable has a given permission
assertVarPermM :: String -> Mb ctx (ExprVar tp) -> Mb ctx (ValuePerm tp) ->
                  ImpTransM ext blocks ret ps ctx ()
assertVarPermM nm x p =
  getVarPermM x >>= \x_p ->
  if permTransPermEq x_p p then return () else error ("translation: " ++ nm)

-- | Set the (translation of the) perms for a variable in a computation
setVarPermM :: Mb ctx (ExprVar tp) -> PermTrans ctx tp ->
               ImpTransM ext blocks ret ps ctx a ->
               ImpTransM ext blocks ret ps ctx a
setVarPermM x p =
  local $ \info -> info { itiPermCtx =
                            mapRListSet (translateVar x) p $ itiPermCtx info }

-- | Build the monadic return type @CompM ret@, where @ret@ is the current
-- return type in 'itiReturnType'
compReturnTypeM :: ImpTransM ext blocks ret ps_out ctx OpenTerm
compReturnTypeM =
  applyOpenTerm (globalOpenTerm "Prelude.CompM") <$> itiReturnType <$> ask

-- | Run a computation with a new catch handler
withCatchHandlerM :: OpenTerm -> ImpTransM ext blocks ret ps_out ctx a ->
                     ImpTransM ext blocks ret ps_out ctx a
withCatchHandlerM h = local (\info -> info { itiCatchHandler = h })

-- | Run 'lambdaExprTrans' in the 'ImpTransM' monad
lambdaExprTransI ::
  String -> TypeRepr tp ->
  ImpTransM ext blocks ret ps_out (ctx :> tp) OpenTerm ->
  ImpTransM ext blocks ret ps_out ctx OpenTerm
lambdaExprTransI x tp body =
  do eith <- tpTransM (nuMultiTransM (const tp) >>= tptranslate)
     case eith of
       Left etrans -> inExtImpTransM etrans PTrans_True body
       Right (tp_term, mk_etrans) ->
         lambdaTransM x tp_term
         (\z -> inExtImpTransM (mk_etrans z) PTrans_True body)

-- | Run 'lambdaExprTransForce' in the 'ImpTransM' monad
lambdaExprTransForceI ::
  String -> TypeRepr tp ->
  ImpTransM ext blocks ret ps_out (ctx :> tp) OpenTerm ->
  ImpTransM ext blocks ret ps_out ctx OpenTerm
lambdaExprTransForceI x tp body =
  do eith <- tpTransM (nuMultiTransM (const tp) >>= tptranslate)
     case eith of
       Left etrans ->
         lambdaTransM x unitTypeOpenTerm
         (\_ -> inExtImpTransM etrans PTrans_True body)
       Right (tp_term, mk_etrans) ->
         lambdaTransM x tp_term
         (\z -> inExtImpTransM (mk_etrans z) PTrans_True body)

-- | Run 'lambdaPermTrans' in the 'ImpTransM' monad
lambdaPermTransI ::
  String -> Mb ctx (ValuePerm a) ->
  (PermTrans ctx a -> ImpTransM ext blocks ret ps_out ctx OpenTerm) ->
  ImpTransM ext blocks ret ps_out ctx OpenTerm
lambdaPermTransI x p body_f =
  tpTransM (tptranslate p) >>= \eith ->
  case eith of
    Left ptrans -> body_f ptrans
    Right (tp_term, mk_ptrans) ->
      lambdaTransM x tp_term (body_f . mk_ptrans)

-- | Run 'lambdaPermTransForce' in the 'ImpTransM' monad
lambdaPermTransForceI ::
  String -> Mb ctx (ValuePerm a) ->
  (PermTrans ctx a -> ImpTransM ext blocks ret ps_out ctx OpenTerm) ->
  ImpTransM ext blocks ret ps_out ctx OpenTerm
lambdaPermTransForceI x p body_f =
  tpTransM (tptranslate p) >>= \eith ->
  case eith of
    Left ptrans -> lambdaTransM x unitTypeOpenTerm (const $ body_f ptrans)
    Right (tp_term, mk_ptrans) ->
      lambdaTransM x tp_term (body_f . mk_ptrans)


-- | The typeclass for translating permission implications
class ImplTranslate a res ext blocks ret ps ctx | ctx a -> res where
  itranslate :: Mb ctx a -> ImpTransM ext blocks ret ps ctx res

-- | The typeclass for the implication translation of a functor at any
-- permission set inside any binding to an 'OpenTerm'
class NuMatchingAny1 f => ImplTranslateF f ext blocks ret where
  itranslateF :: Mb ctx (f ps) -> ImpTransM ext blocks ret ps ctx OpenTerm


-- Translate a TypeRepr to a SAW type in the implication translation monad,
-- using the unit type in place of 'Nothing'
instance ImplTranslate (TypeRepr a) OpenTerm ext blocks ret ps ctx where
  itranslate tp = tpTransM $ translateType tp

-- Translate a permission to a SAW type in the implication translation monad,
-- using the unit type in place of 'Nothing'
instance ImplTranslate (ValuePerm a) OpenTerm ext blocks ret ps ctx where
  itranslate p = tpTransM $ translatePerm p


----------------------------------------------------------------------
-- * Translating Permission Implication Constructs
----------------------------------------------------------------------

-- | Translate a 'SimplImpl' to a function on translation computations
itranslateSimplImpl :: Proxy ps -> Mb ctx (SimplImpl ps_in ps_out) ->
                       ImpTransM ext blocks ret (ps :++: ps_out) ctx res ->
                       ImpTransM ext blocks ret (ps :++: ps_in) ctx res

itranslateSimplImpl _ [nuP| SImpl_Drop _ _ |] m =
  withPermStackM (\(xs :>: _) -> xs) (\(ps :>: _) -> ps) m

itranslateSimplImpl _ [nuP| SImpl_Swap _ _ _ _ |] m =
  withPermStackM (\(xs :>: x :>: y) -> xs :>: y :>: x)
  (\(pctx :>: px :>: py) -> pctx :>: py :>: px)
  m

itranslateSimplImpl _ [nuP| SImpl_IntroOrL _ p1 p2 |] m =
  do tp1 <- itranslate p1
     tp2 <- itranslate p2
     withPermStackM id
       (\(ps :>: p_top) ->
         ps :>: (PTrans_Term (mbMap2 ValPerm_Or p1 p2)
                 (ctorOpenTerm "Prelude.Left"
                  [tp1, tp2, permTransToTermForce p_top])))
       m

itranslateSimplImpl _ [nuP| SImpl_IntroOrR _ p1 p2 |] m =
  do tp1 <- itranslate p1
     tp2 <- itranslate p2
     withPermStackM id
       (\(ps :>: p_top) ->
         ps :>: (PTrans_Term (mbMap2 ValPerm_Or p1 p2)
                 (ctorOpenTerm "Prelude.Right"
                  [tp1, tp2, permTransToTermForce p_top])))
       m

itranslateSimplImpl _ [nuP| SImpl_IntroExists _ (e :: PermExpr tp) p |] m =
  do let tp :: TypeRepr tp = knownRepr
     tp_trans <- itranslate $ nuMulti (mbToProxy e) $ const tp
     tp_f <- lambdaExprTransForceI "x_introEx" tp $ itranslate $ mbCombine p
     e_trans <- tpTransM (translateExpr e)
     withPermStackM id
       (\(ps :>: p_top) ->
         ps :>: (PTrans_Term (fmap ValPerm_Exists p)
                 (ctorOpenTerm "Prelude.exists"
                  [tp_trans, tp_f, e_trans, permTransToTermForce p_top])))
       m

itranslateSimplImpl _ [nuP| SImpl_Cast _ _ p |] m =
  withPermStackM mapRListTail
  (\(pctx :>: _ :>: ptrans) -> pctx :>: ptrans)
  m

itranslateSimplImpl _ [nuP| SImpl_IntroEqRefl x |] m =
  withPermStackM (:>: translateVar x) (:>: PTrans_Eq (fmap PExpr_Var x)) m
  
itranslateSimplImpl _ [nuP| SImpl_CopyEq _ _ |] m =
  withPermStackM
  (\(vars :>: var) -> (vars :>: var :>: var))
  (\(pctx :>: ptrans) -> (pctx :>: ptrans :>: ptrans))
  m

itranslateSimplImpl _ [nuP| SImpl_IntroConj x |] m =
  withPermStackM (:>: translateVar x) (:>: PTrans_True) m

itranslateSimplImpl _ [nuP| SImpl_ExtractConj x _ i |] m =
  withPermStackM (:>: translateVar x)
  (\(pctx :>: ptrans) ->
    let ps = unPTransConj "itranslateSimplImpl: SImpl_ExtractConj" ptrans in
    pctx :>: PTrans_Conj [ps !! mbLift i]
    :>: PTrans_Conj (take (mbLift i) ps ++ drop (mbLift i +1) ps))
  m

itranslateSimplImpl _ [nuP| SImpl_CopyConj x _ i |] m =
  withPermStackM (:>: translateVar x)
  (\(pctx :>: ptrans) ->
    let ps = unPTransConj "itranslateSimplImpl: SImpl_CopyConj" ptrans in
    pctx :>: PTrans_Conj [ps !! mbLift i] :>: ptrans)
  m

itranslateSimplImpl _ [nuP| SImpl_InsertConj x _ _ i |] m =
  withPermStackM mapRListTail
  (\(pctx :>: ptransi :>: ptrans) ->
    let ps = unPTransConj "itranslateSimplImpl: SImpl_CopyConj" ptrans
        pi = unPTransConj1 "itranslateSimplImpl: SImpl_CopyConj" ptransi in
    pctx :>: PTrans_Conj (take (mbLift i) ps ++ pi : drop (mbLift i) ps))
  m

itranslateSimplImpl _ [nuP| SImpl_CastLLVMWord _ _ e2 |] m =
  withPermStackM mapRListTail
  ((:>: PTrans_Eq (fmap PExpr_LLVMWord e2)) . mapRListTail . mapRListTail)
  m

itranslateSimplImpl _ [nuP| SImpl_CastLLVMPtr _ _ off _ |] m =
  withPermStackM mapRListTail
  (\(pctx :>: _ :>: ptrans) ->
    let ps = unPTransConj "itranslateSimplImpl: SImpl_CastLLVMPtr" ptrans in
    pctx :>: PTrans_Conj (map (offsetLLVMAtomicPermTrans $
                               fmap bvNegate off) ps))
  m

itranslateSimplImpl _ [nuP| SImpl_CastLLVMFree _ _ e2 |] m =
  withPermStackM mapRListTail
  ((:>: PTrans_Conj [APTrans_LLVMFree e2]) . mapRListTail . mapRListTail)
  m

itranslateSimplImpl _ [nuP| SImpl_CastLLVMFieldOffset _ _ mb_off |] m =
  withPermStackM mapRListTail
  (\(pctx :>: _ :>: ptrans) ->
    let (mb_fld,ptrans') =
          unPTransLLVMField "itranslateSimplImpl: SImpl_CastLLVMPtr" ptrans in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (mbMap2 (\fld off -> fld { llvmFieldOffset = off })
                           mb_fld mb_off)
                          ptrans'])
  m

itranslateSimplImpl _ [nuP| SImpl_IntroLLVMFieldContents x _ mb_fld |] m =
  withPermStackM ((:>: translateVar x) . mapRListTail . mapRListTail)
  (\(pctx :>: _ :>: ptrans) ->
    pctx :>: PTrans_Conj [APTrans_LLVMField mb_fld ptrans])
  m

itranslateSimplImpl _ [nuP| SImpl_LLVMFieldLifetimeCurrent _ _ _ mb_l |] m =
  withPermStackM mapRListTail
  (\(pctx :>: ptrans :>: _) ->
    let (mb_fld,ptrans') =
          unPTransLLVMField
          "itranslateSimplImpl: SImpl_LLVMFieldLifetimeCurrent" ptrans in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (mbMap2 (\fp l -> fp { llvmFieldLifetime = l })
                           mb_fld mb_l)
                          ptrans'])
  m

itranslateSimplImpl _ [nuP| SImpl_LLVMFieldLifetimeAlways _ _ mb_l |] m =
  withPermStackM id
  (\(pctx :>: ptrans) ->
    let (mb_fld,ptrans') =
          unPTransLLVMField
          "itranslateSimplImpl: SImpl_LLVMFieldLifetimeCurrent" ptrans in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (mbMap2 (\fp l -> fp { llvmFieldLifetime = l })
                           mb_fld mb_l)
                          ptrans'])
  m

itranslateSimplImpl _ [nuP| SImpl_DemoteLLVMFieldWrite _ _ |] m =
  withPermStackM id
  (\(pctx :>: ptrans) ->
    let (mb_fld,ptrans') =
          unPTransLLVMField
          "itranslateSimplImpl: SImpl_DemoteLLVMFieldWrite" ptrans in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (fmap (\fld -> fld { llvmFieldRW = Read }) mb_fld)
                          ptrans])
  m


itranslateSimplImpl _ [nuP| SImpl_LLVMArrayCopy _ mb_ap mb_rng |] m =
  error "FIXME HERE: itranslateSimplImpl: SImpl_LLVMArrayCopy not yet implemented!"
  -- NOTE: needs a special version of slice, to avoid casts
  --
  -- IDEA: the translation of a BVProp should be a proof of that BVProp, so we
  -- can use it in casting things! Or our special version of slice could take
  -- one of these proofs as input
  {-
  do elem_tp <- tpTransM (translateLLVMArrayElemType mb_ap)
     withPermStackM id
       (\(pctx :>: ptrans :>: _) ->
         let (mb_ap, trm) =
               unPTransLLVMArray
               "itranslateSimplImpl: SImpl_LLVMArrayCopy" ptrans in
         pctx :>: PTrans_Conj [APTrans_LLVMArray ap t] :>:
         PTrans_Conj [APTrans_LLVMArray
                      (mbMap2 $ \ap rng ->
                        ap { llvmArrayOffset = bvRangeOffset rng,
                             llvmArrayLen = bvRangeLength rng })
                      (applyOpenTermMulti
                       (globalOpenTerm "Prelude.slice")
                       [elem_tp, ]
                      )
                     ])
       m -}

itranslateSimplImpl _ [nuP| SImpl_LLVMArrayBorrow _ _ _ |] m =
  error
  "FIXME HERE: itranslateSimplImpl: SImpl_LLVMArrayBorrow not yet implemented!"
  -- NOTE: same issue as for SImpl_LLVMArrayCopy

itranslateSimplImpl _ [nuP| SImpl_LLVMArrayReturn _ _ _ |] m =
  error
  "FIXME HERE: itranslateSimplImpl: SImpl_LLVMArrayReturn not yet implemented!"
  -- NOTE: needs a function to replace a sub-range of a Vec with another one
  -- IDEA: the borrows could translate to proofs of the relevant BVProps, which
  -- could be used when returning

itranslateSimplImpl _ [nuP| SImpl_LLVMArrayIndexCopy x _ mb_i j |] m =
  do ptrans_array <- getTopPermM
     let (mb_ap, f_elem, array_trm) =
           unPTransLLVMArray
           "itranslateSimplImpl: SImpl_LLVMArrayIndexCopy" ptrans_array
     elem_ptrans <-
       (!! mbLift j) <$> f_elem <$>
       tpTransM (applyMultiTransM (return $ globalOpenTerm "Prelude.at")
                 [translateExpr (fmap llvmArrayLen mb_ap),
                  translateLLVMArrayElemType mb_ap,
                  return array_trm, translateExpr mb_i])
     withPermStackM id
       (\(pctx :>: _ :>: _) ->
         pctx :>: PTrans_Conj [elem_ptrans] :>: ptrans_array)
       m

itranslateSimplImpl _ [nuP| SImpl_LLVMArrayIndexBorrow x _ mb_i j |] m =
  do ptrans_array <- getTopPermM
     let (mb_ap, f_elem, array_trm) =
           unPTransLLVMArray
           "itranslateSimplImpl: SImpl_LLVMArrayIndexBorrow" ptrans_array
     elem_ptrans <-
       (!! mbLift j) <$> f_elem <$>
       tpTransM (applyMultiTransM (return $ globalOpenTerm "Prelude.at")
                 [translateExpr (fmap llvmArrayLen mb_ap),
                  translateLLVMArrayElemType mb_ap,
                  return array_trm, translateExpr mb_i])
     withPermStackM id
       (\(pctx :>: _ :>: _) ->
         pctx :>: PTrans_Conj [elem_ptrans] :>:
         PTrans_Conj
         [APTrans_LLVMArray
          (mbMap2 (\i -> llvmArrayAddBorrow
                         (FieldBorrow i (toInteger $ mbLift j) Nothing))
           mb_i mb_ap)
          f_elem array_trm])
       m

itranslateSimplImpl _ [nuP| SImpl_LLVMArrayIndexReturn x _ mb_i j |] m =
  do (_ :>: ptrans_fld :>: ptrans_array) <- itiPermStack <$> ask
     let (mb_ap, f_elem, array_trm) =
           unPTransLLVMArray
           "itranslateSimplImpl: SImpl_LLVMArrayIndexReturn" ptrans_array
     old_elem_trm <-
       tpTransM (applyMultiTransM (return $ globalOpenTerm "Prelude.at")
                 [translateExpr (fmap llvmArrayLen mb_ap),
                  translateLLVMArrayElemType mb_ap,
                  return array_trm, translateExpr mb_i])
     let replace_nth_proj :: Int -> OpenTerm -> OpenTerm -> OpenTerm
         replace_nth_proj 0 _ t_repl = t_repl
         replace_nth_proj i t t_repl =
           pairOpenTerm (pairLeftOpenTerm t)
           (replace_nth_proj (i-1) (pairRightOpenTerm t) t_repl)
     let new_elem_trm =
           replace_nth_proj (mbLift j) old_elem_trm $
           permTransToTermForce ptrans_fld
     new_array_trm <-
       tpTransM (applyMultiTransM (return $ globalOpenTerm "Prelude.upd")
                 [translateExpr (fmap llvmArrayLen mb_ap),
                  translateLLVMArrayElemType mb_ap,
                  return array_trm, translateExpr mb_i,
                  return new_elem_trm])
     withPermStackM mapRListTail
       (\(pctx :>: _ :>: _) ->
         pctx :>:
         PTrans_Conj [APTrans_LLVMArray
                      (mbMap2 (\i ap -> llvmArrayRemIndexBorrow i (mbLift j) ap)
                       mb_i mb_ap)
                      f_elem
                      new_array_trm])
       m


itranslateSimplImpl _ [nuP| SImpl_LLVMArrayContents _ _ _ _ _ |] m =
  error "FIXME HERE: itranslateSimplImpl: SImpl_LLVMArrayContents unhandled"

itranslateSimplImpl _ [nuP| SImpl_SplitLifetime mb_x mb_p mb_l mb_ps |] m =
  withPermStackM id
  (\(pctx :>: ptrans_x :>: ptrans_l) ->
    pctx :>: permTransInLifetime (fmap PExpr_Var mb_l) ptrans_x :>:
    PTrans_Conj
    [APTrans_LifetimePerm
     (fmap
      (\x p ps ->
        Perm_LOwned (PExpr_PermListCons (PExpr_Var x) p ps))
      mb_x `mbApply` mb_p `mbApply` mb_ps)])
  m

itranslateSimplImpl _ [nuP| SImpl_LCurrentRefl l |] m =
  withPermStackM (:>: translateVar l)
  (:>: PTrans_Conj [APTrans_LifetimePerm $ fmap (Perm_LCurrent . PExpr_Var) l])
  m

itranslateSimplImpl _ [nuP| SImpl_LCurrentTrans l1 l2 l3 |] m =
  withPermStackM mapRListTail
  ((:>: PTrans_Conj [APTrans_LifetimePerm $ fmap Perm_LCurrent l3]) .
   mapRListTail . mapRListTail)
  m

itranslateSimplImpl _ [nuP| SImpl_FoldMu _ _ |] m =
  error "FIXME HERE: SImpl_FoldMu: translation not yet implemented"

itranslateSimplImpl _ [nuP| SImpl_UnfoldMu _ _ |] m =
  error "FIXME HERE: SImpl_UnfoldMu: translation not yet implemented"

itranslateSimplImpl _ [nuP| SImpl_Mu _ _ _ _ |] m =
  error "FIXME HERE: SImpl_Mu: translation not yet implemented"


-- | Translate a 'PermImpl1' to a function on translation computations
itranslatePermImpl1 :: ImplTranslateF r ext blocks ret =>
                       Mb ctx (PermImpl1 ps_in ps_outs) ->
                       Mb ctx (MbPermImpls r ps_outs) ->
                       ImpTransM ext blocks ret ps_in ctx OpenTerm

-- A failure translates to a call to the catch handler, which is the most recent
-- Impl1_Catch, if one exists, or the SAW errorM function otherwise
itranslatePermImpl1 [nuP| Impl1_Fail |] _ = itiCatchHandler <$> ask

-- A catch runs the first computation using the second as catch handler
itranslatePermImpl1 [nuP| Impl1_Catch |]
  [nuP| MbPermImpls_Cons (MbPermImpls_Cons _ mb_impl1) mb_impl2 |] =
  do compMType <- compReturnTypeM
     letTransM "catchpoint" compMType
       (itranslate $ mbCombine mb_impl2)
       (\handler -> withCatchHandlerM handler $ itranslate $ mbCombine mb_impl1)

-- A push moves the given permission from x to the top of the perm stack
itranslatePermImpl1 [nuP| Impl1_Push x p |] [nuP| MbPermImpls_Cons _ mb_impl |] =
  assertVarPermM "Impl1_Push" x p >>
  getVarPermM x >>= \ptrans ->
  setVarPermM x (PTrans_True)
  (withPermStackM (:>: translateVar x) (:>: ptrans) $
   itranslate (mbCombine mb_impl))

-- A pop moves the given permission from the top of the perm stack to x
itranslatePermImpl1 [nuP| Impl1_Pop x p |] [nuP| MbPermImpls_Cons _ mb_impl |] =
  assertTopPermM "Impl1_Pop" x p >>
  assertVarPermM "Impl1_Pop" x (nuMulti (mbToProxy p) $ const ValPerm_True) >>
  getTopPermM >>= \ptrans ->
  setVarPermM x ptrans
  (withPermStackM mapRListTail mapRListTail $
   itranslate (mbCombine mb_impl))

-- An or elimination performs a pattern-match on an Either
itranslatePermImpl1 [nuP| Impl1_ElimOr x p1 p2 |]
  [nuP| MbPermImpls_Cons (MbPermImpls_Cons _ mb_impl1) mb_impl2 |] =
  do assertTopPermM "Impl1_ElimOr" x (mbMap2 ValPerm_Or p1 p2)
     tp1 <- itranslate p1
     tp2 <- itranslate p2
     tp_ret <- compReturnTypeM
     top_ptrans <- getTopPermM
     applyMultiTransM (return $ globalOpenTerm "Prelude.either")
       [ return tp1, return tp2, return tp_ret
       , lambdaPermTransForceI "x_left" p1
         (\ptrans ->
           withPermStackM id ((:>: ptrans) . mapRListTail) $
           itranslate $ mbCombine mb_impl1)
       , lambdaPermTransForceI "x_right" p2
         (\ptrans ->
           withPermStackM id ((:>: ptrans) . mapRListTail) $
           itranslate $ mbCombine mb_impl2)
       , return (permTransToTermForce top_ptrans)]

-- An existential elimination performs a pattern-match on a Sigma
itranslatePermImpl1 [nuP| Impl1_ElimExists x (p :: Binding tp (ValuePerm a)) |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  do assertTopPermM "Impl1_ElimExists" x (fmap ValPerm_Exists p)
     let tp :: TypeRepr tp = knownRepr
     tp_trans <- itranslate $ nuMulti (mbToProxy x) $ const tp
     tp_f <- lambdaExprTransForceI "x_elimEx" tp $ itranslate $ mbCombine p
     ret_f <- lambdaTransM "x_elimEx"
       (dataTypeOpenTerm "Prelude.Sigma" [tp_trans, tp_f])
       (const compReturnTypeM)
     top_ptrans <- getTopPermM
     applyMultiTransM (return $ globalOpenTerm "Prelude.Sigma__rec")
       [ return tp_trans, return tp_f, return ret_f
       , lambdaExprTransForceI "x1_elimEx" tp
         (getTopVarM >>= \z1 ->
           lambdaPermTransForceI "x2_elimEx" (mbCombine p) $ \z2 ->
           withPermStackM id ((:>: z2) . mapRListTail) $
           itranslate $ mbCombine mb_impl)
       , return (permTransToTermForce top_ptrans) ]

-- A SimplImpl is translated using itranslateSimplImpl
itranslatePermImpl1 [nuP| Impl1_Simpl simpl prx |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  itranslateSimplImpl (mbLift prx) simpl $ itranslate $ mbCombine mb_impl

itranslatePermImpl1 [nuP| Impl1_ElimLLVMFieldContents
                        _ mb_fld |] [nuP| MbPermImpls_Cons _ mb_impl |] =
  inExtImpTransM ETrans_LLVM PTrans_True $
  withPermStackM (:>: Member_Base)
  (\(pctx :>: ptrans_x) ->
    let (_,ptrans') =
          unPTransLLVMField
          "itranslateSimplImpl: Impl1_ElimLLVMFieldContents" ptrans_x in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (mbCombine $
                           fmap (\fld -> nu $ \y ->
                                  fld { llvmFieldContents =
                                          ValPerm_Eq (PExpr_Var y)})
                           mb_fld) $
                          PTrans_Eq (mbCombine $
                                     fmap (const $ nu PExpr_Var) mb_fld)]
    :>: ptrans') $
  itranslate $ mbCombine mb_impl


itranslatePermImpl1 [nuP| Impl1_TryProveBVProp x
                        prop@(BVProp_Eq e1 (e2 :: PermExpr (BVType w))) |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  let p_prop = fmap (ValPerm_Conj1 . Perm_BVProp) prop in
  applyMultiTransM (return $ globalOpenTerm "Prelude.maybe")
  [ tpTransM (translatePerm p_prop)
  , compReturnTypeM, (itiCatchHandler <$> ask)
  , lambdaPermTransForceI "eq_pf" p_prop
    (\ptrans ->
      withPermStackM (:>: translateVar x) (:>: ptrans)
      (itranslate $ mbCombine mb_impl))
  , applyMultiTransM (return $ globalOpenTerm "Prelude.bvEqWithProof")
    [ return (natOpenTerm $ natVal (Proxy :: Proxy w))
    , tpTransM (translateExpr e1), tpTransM (translateExpr e2)]
  ]

itranslatePermImpl1 [nuP| Impl1_TryProveBVProp x
                        prop@(BVProp_InRange
                              (e :: PermExpr (BVType w)) (BVRange off len)) |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  let p_prop = fmap (ValPerm_Conj1 . Perm_BVProp) prop in
  applyMultiTransM (return $ globalOpenTerm "Prelude.maybe")
  [ tpTransM (translatePerm p_prop)
  , compReturnTypeM, (itiCatchHandler <$> ask)
  , lambdaPermTransForceI "inrange_pf" p_prop
    (\ptrans ->
      withPermStackM (:>: translateVar x) (:>: ptrans)
      (itranslate $ mbCombine mb_impl))
  , applyMultiTransM (return $ globalOpenTerm "Prelude.bvultWithProof")
    [ return (natOpenTerm $ natVal (Proxy :: Proxy w))
    , tpTransM (translateExpr (mbMap2 bvSub e off)),
      tpTransM (translateExpr len)]
  ]

itranslatePermImpl1 [nuP| Impl1_TryProveBVProp _ (BVProp_RangeSubset _ _) |]
  [nuP| MbPermImpls_Cons _ _ |] =
  error "FIXME HERE NOW: translate Impl1_TryProveBVProp (BVProp_RangeSubset)"

itranslatePermImpl1 [nuP| Impl1_TryProveBVProp _ (BVProp_RangesDisjoint _ _) |]
  [nuP| MbPermImpls_Cons _ _ |] =
  error "FIXME HERE NOW: translate Impl1_TryProveBVProp (BVProp_RangesDisjoint)"


instance ImplTranslateF r ext blocks ret =>
         ImplTranslate (PermImpl r ps) OpenTerm ext blocks ret ps ctx where
  itranslate [nuP| PermImpl_Done r |] = itranslateF r
  itranslate [nuP| PermImpl_Step impl1 mb_impls |] =
    itranslatePermImpl1 impl1 mb_impls


----------------------------------------------------------------------
-- * Translating Typed Crucible Expressions
----------------------------------------------------------------------

-- tptranslate for a TypedReg yields an ExprTrans
instance TypeTranslate (TypedReg tp) ctx (ExprTrans tp) where
  tptranslate [nuP| TypedReg x |] = tptranslate x

instance TypeTranslate (RegWithVal tp) ctx (ExprTrans tp) where
  tptranslate [nuP| RegWithVal _ e |] = tptranslate e
  tptranslate [nuP| RegNoVal x |] = tptranslate x

translateRWV :: Mb ctx (RegWithVal a) -> TypeTransM ctx OpenTerm
translateRWV mb_rwv = exprTransToTermForce <$> tptranslate mb_rwv

-- tptranslate for a TypedExpr yields an ExprTrans
instance PermCheckExtC ext =>
         TypeTranslate (App ext RegWithVal tp) ctx (ExprTrans tp) where
  tptranslate [nuP| BaseIsEq BaseBoolRepr e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.boolEq")
    [translateRWV e1, translateRWV e2]
  tptranslate [nuP| BaseIsEq BaseNatRepr e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.equalNat")
    [translateRWV e1, translateRWV e2]

  tptranslate [nuP| EmptyApp |] = return $ ETrans_Term unitOpenTerm

  -- Booleans
  tptranslate [nuP| BoolLit True |] =
    return $ ETrans_Term $ globalOpenTerm "Prelude.True"
  tptranslate [nuP| BoolLit False |] =
    return $ ETrans_Term $ globalOpenTerm "Prelude.False"
  tptranslate [nuP| Not e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.not")
    [translateRWV e]
  tptranslate [nuP| And e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.and")
    [translateRWV e1, translateRWV e2]
  tptranslate [nuP| Or e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.or")
    [translateRWV e1, translateRWV e2]
  tptranslate [nuP| BoolXor e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.xor")
    [translateRWV e1, translateRWV e2]

  -- Natural numbers
  tptranslate [nuP| Expr.NatLit n |] =
    return $ ETrans_Term $ natOpenTerm $ toInteger $ mbLift n
  tptranslate [nuP| NatLt e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.ltNat")
    [translateRWV e1, translateRWV e2]
  -- tptranslate [nuP| NatLe _ _ |] =
  tptranslate [nuP| NatAdd e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.addNat")
    [translateRWV e1, translateRWV e2]
  tptranslate [nuP| NatSub e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.subNat")
    [translateRWV e1, translateRWV e2]
  tptranslate [nuP| NatMul e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.mulNat")
    [translateRWV e1, translateRWV e2]
  tptranslate [nuP| NatDiv e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.divNat")
    [translateRWV e1, translateRWV e2]
  tptranslate [nuP| NatMod e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.modNat")
    [translateRWV e1, translateRWV e2]

  -- Function handles: the expression part of a function handle has no
  -- computational content
  tptranslate [nuP| HandleLit _ |] = return ETrans_Fun

  -- Bitvectors
  tptranslate [nuP| BVLit w i |] =
    return $ ETrans_Term $ bvNat (intValue $ mbLift w) (mbLift i)
  tptranslate [nuP| BVConcat w1 w2 e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.join")
    [tptranslate w1, tptranslate w2, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVTrunc w1 w2 e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.take")
    [return (globalOpenTerm "Prelude.Bool"),
     return (natOpenTerm (intValue (mbLift w2) - intValue (mbLift w1))),
     tptranslate w1,
     translateRWV e]
  tptranslate [nuP| BVZext w1 w2 e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvUExt")
    [tptranslate w1, tptranslate w2, translateRWV e]
  tptranslate [nuP| BVSext w1 w2 e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvSExt")
    [tptranslate w1, tptranslate w2, translateRWV e]
  tptranslate [nuP| BVNot w e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvNot")
    [tptranslate w, translateRWV e]
  tptranslate [nuP| BVAnd w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvAnd")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVOr w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvOr")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVNeg w e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvNeg")
    [tptranslate w, translateRWV e]
  tptranslate [nuP| BVAdd w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvAdd")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVSub w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvSub")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVMul w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvMul")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVUdiv w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvUDiv")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVSdiv w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvSDiv")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVUrem w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvURem")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVSrem w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvSRem")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVUle w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvule")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVUlt w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvult")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVSle w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvsle")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate [nuP| BVSlt w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvslt")
    [tptranslate w, translateRWV e1, translateRWV e2]
  tptranslate mb_e =
    error ("Unhandled expression form: " ++
           (flip displayS "" $ renderPretty 0.8 80 $
            mbLift $ fmap (ppApp (const $ string "_")) mb_e))


-- tptranslate for a TypedExpr yields an ExprTrans
{-
instance PermCheckExtC ext =>
         TypeTranslate (App ext RegWithVal tp) ctx (ExprTrans tp) where
  tptranslate mb_app = tptranslate (fmap (fmapFC regWithValExpr) mb_app)
-}

-- tptranslate for a TypedExpr yields an ExprTrans
instance PermCheckExtC ext =>
         TypeTranslate (TypedExpr ext tp) ctx (ExprTrans tp) where
  tptranslate [nuP| TypedExpr _ (Just e) |] = tptranslate e
  tptranslate [nuP| TypedExpr app Nothing |] = tptranslate app

-- itranslate for a TypedReg yields a PermTrans
instance PermCheckExtC ext =>
         ImplTranslate (TypedReg tp) (PermTrans ctx tp)
         ext blocks ret ps ctx where
  itranslate [nuP| TypedReg x |] = getVarPermM x

-- itranslate for a TypedExpr yields a PermTrans
{-
instance PermCheckExtC ext =>
         ImplTranslate (App ext TypedReg tp) (PermTrans ctx tp)
         ext blocks ret ps ctx where
  itranslate [nuP| EmptyApp |] = return PTrans_True
  itranslate _ = error "FIXME HERE NOW"
-}

-- itranslate for a TypedExpr yields a PermTrans, which is either an eq(e)
-- permission or true
instance PermCheckExtC ext =>
         ImplTranslate (TypedExpr ext tp) (PermTrans ctx tp)
         ext blocks ret ps ctx where
  itranslate [nuP| TypedExpr _ (Just e) |] = return $ PTrans_Eq e
  itranslate [nuP| TypedExpr _ Nothing |] = return $ PTrans_True


----------------------------------------------------------------------
-- * Translating Typed Crucible Jump Targets
----------------------------------------------------------------------

instance ImplTranslate (TypedEntryID blocks args ghosts) OpenTerm
         ext blocks ret ps ctx where
  itranslate mb_entryID =
    translateTypedEntryID (mbLift mb_entryID) <$> itiBlockMapTrans <$> ask

-- | Apply the translation of a function-like construct (i.e., a
-- 'TypedJumpTarget' or 'TypedFnHandle') to the pure plus impure translations of
-- its arguments, given as 'DistPerms', which should match the current
-- stack. The 'String' argument is the name of the construct being applied, for
-- use in error reporting.
translateApply :: String -> OpenTerm -> Mb ctx (DistPerms ps) ->
                  ImpTransM ext blocks ret ps ctx OpenTerm
translateApply nm f perms =
  do assertPermStackEqM nm perms
     expr_ctx <- itiExprCtx <$> ask
     arg_membs <- itiPermStackVars <$> ask
     let e_args = mapMapRList (flip mapRListLookup expr_ctx) arg_membs
     i_args <- itiPermStack <$> ask
     return $
       applyOpenTermMulti f (exprCtxToTerms e_args ++ permCtxToTerms i_args)

-- | Translate a 'TypedEntryID' and call the resulting function
--
-- FIXME: check that the supplied perms match those expected by the entryID
translateCallEntryID :: String -> TypedEntryID blocks args ghosts ->
                        Mb ctx (DistPerms ps) ->
                        ImpTransM ext blocks ret ps ctx OpenTerm
translateCallEntryID nm entryID perms =
  do entry_trans <-
       lookupEntryTrans entryID <$> itiBlockMapTrans <$> ask
     case entry_trans of
       TypedEntryTrans _ f ->
         translateApply nm f perms

instance ImplTranslate (TypedJumpTarget blocks ps) OpenTerm
         ext blocks ret ps ctx where
  itranslate [nuP| TypedJumpTarget entryID _ perms |] =
    translateCallEntryID "TypedJumpTarget" (mbLift entryID) perms

instance ImplTranslateF (TypedJumpTarget blocks) ext blocks ret where
  itranslateF mb_tgt = itranslate mb_tgt


----------------------------------------------------------------------
-- * Translating Typed Crucible Statements
----------------------------------------------------------------------

-- | Translate a 'TypedStmt' to a function on translation computations
itranslateStmt :: PermCheckExtC ext =>
                  Mb ctx (TypedStmt ext rets ps_in ps_out) ->
                  ImpTransM ext blocks ret ps_out (ctx :++: rets) OpenTerm ->
                  ImpTransM ext blocks ret ps_in ctx OpenTerm

itranslateStmt [nuP| TypedSetReg _ e |] m =
  do etrans <- tpTransM $ tptranslate e
     ptrans <- extPermTrans <$> itranslate e
     inExtImpTransM etrans PTrans_True $
       withPermStackM (:>: Member_Base) (:>: ptrans) m

itranslateStmt [nuP| stmt@(TypedCall freg fun_perm ghosts args l ps) |] m =
  do f_trans <- getTopPermM
     let f = case f_trans of
           PTrans_Conj [APTrans_Fun _ f_trm] -> f_trm
           _ -> error "itranslateStmt: TypedCall: unexpected function permission"
     let perms_in = fmap (distPermsSnoc . typedStmtIn) stmt
     let perms_out =
           mbCombine $ fmap (\stmt' -> nu $ \ret ->
                              flip typedStmtOut (MNil :>: ret) stmt') stmt
     let mb_ret_tp = fmap funPermRet fun_perm
     let ret_tp = mbLift $ fmap funPermRet fun_perm
     ret_tp_trm <- itranslate mb_ret_tp
     tp_f <- lambdaExprTransForceI "x_elimCallRet" ret_tp $ tpTransM $
       tptranslate $ mbCombine $
       fmap (\stmt' -> nu $ \ret ->
              typedStmtOut stmt' (MNil :>: ret)) stmt
     ret_f <- lambdaTransM "x_elimCallRet"
       (dataTypeOpenTerm "Prelude.Sigma" [ret_tp_trm, tp_f])
       (const compReturnTypeM)
     fret_trm <-
       withPermStackM mapRListTail mapRListTail $
       translateApply "TypedCall" f perms_in
     applyMultiTransM (return $ globalOpenTerm "Prelude.Sigma__rec")
       [return ret_tp_trm, return tp_f, return ret_f,
        lambdaExprTransForceI "x_elimCallRet" ret_tp $
        lambdaTransM "x_elimCallRet" (dataTypeOpenTerm "Prelude.Sigma"
                                      [ret_tp_trm, tp_f]) $ \z_perms ->
         tpTransM (unpackPermCtxTuple
                   (mbDistPermsToValuePerms perms_out) z_perms) >>= \pctx ->
         withPermStackM
         (\(args :>: l :>: _) -> (args :>: Member_Base :>: l))
         (const $ pctx)
         m
       ]

itranslateStmt stmt@[nuP| BeginLifetime |] m =
  inExtImpTransM ETrans_Lifetime PTrans_True $
  withPermStackM (:>: Member_Base)
  (:>: PTrans_Conj [APTrans_LifetimePerm $ nuMulti (mbToProxy stmt :>: Proxy) $
                    const $ Perm_LOwned PExpr_PermListNil])
  m

itranslateStmt stmt@[nuP| EndLifetime _ ps _ |] m =
  withPermStackM mapRListTail
  (\(pctx :>: _) -> permCtxEndLifetime pctx ps)
  m

itranslateStmt [nuP| TypedAssert e _ |] m =
  applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
  [compReturnTypeM, tpTransM (exprTransToTermForce <$> tptranslate e),
   m, itiCatchHandler <$> ask]

itranslateStmt [nuP| TypedLLVMStmt stmt |] m = itranslateLLVMStmt stmt m


-- | Translate a 'TypedStmt' to a function on translation computations
itranslateLLVMStmt ::
  Mb ctx (TypedLLVMStmt w r ps_in ps_out) ->
  ImpTransM ext blocks ret ps_out (ctx :> r) OpenTerm ->
  ImpTransM ext blocks ret ps_in ctx OpenTerm

itranslateLLVMStmt [nuP| ConstructLLVMWord (TypedReg x) |] m =
  inExtImpTransM ETrans_LLVM PTrans_True $
  withPermStackM (:>: Member_Base) (:>: (PTrans_Eq $ extMb $
                                         fmap (PExpr_LLVMWord . PExpr_Var) x)) m

itranslateLLVMStmt [nuP| AssertLLVMWord reg _ |] m =
  inExtImpTransM (ETrans_Term $ natOpenTerm 0) PTrans_True $
  withPermStackM ((:>: Member_Base) . mapRListTail)
  ((:>: (PTrans_Eq $ fmap (const $ PExpr_Nat 0) $ extMb reg)) . mapRListTail)
  m

itranslateLLVMStmt [nuP| DestructLLVMWord _ e |] m =
  tpTransM (tptranslate e) >>= \etrans ->
  inExtImpTransM etrans PTrans_True $
  withPermStackM ((:>: Member_Base) . mapRListTail)
  ((:>: (PTrans_Eq $ extMb e)) . mapRListTail)
  m

itranslateLLVMStmt [nuP| TypedLLVMLoad _ _ _ e |] m =
  inExtImpTransM ETrans_LLVM PTrans_True $
  withPermStackM ((:>: Member_Base) . mapRListTail)
  ((:>: (PTrans_Eq $ extMb e)) . mapRListTail)
  m

itranslateLLVMStmt [nuP| TypedLLVMStore _ (TypedReg y) |] m =
  inExtImpTransM (ETrans_Term unitOpenTerm) PTrans_True $
  withPermStackM id
  ((:>: PTrans_Conj [APTrans_LLVMField
                     (fmap (llvmFieldWrite0Eq . PExpr_Var) (extMb y))
                     (PTrans_Eq $ fmap PExpr_Var $ extMb y)])
   . mapRListTail)
  m

itranslateLLVMStmt [nuP| TypedLLVMAlloca
                       _ (mb_fperm :: LLVMFramePerm w) mb_sz |] m =
  let sz = mbLift mb_sz
      w :: Proxy w = Proxy in
  inExtImpTransM ETrans_LLVM PTrans_True $
  withPermStackM (:>: Member_Base)
  (\(pctx :>: _) ->
    pctx
    :>: PTrans_Conj [APTrans_LLVMFrame $
                     flip nuMultiWithElim1 (extMb mb_fperm) $
                     \(_ :>: ret) fperm -> (PExpr_Var ret, sz):fperm]
    :>: PTrans_Conj (flip map [0 .. bytesToMachineWords w sz - 1] $ \i ->
                      APTrans_LLVMField
                      (fmap
                       (const $ llvmFieldWrite0True
                        { llvmFieldOffset = bvInt (i * machineWordBytes w) })
                       (extMb mb_fperm))
                      PTrans_True))
  m

itranslateLLVMStmt mb_stmt@[nuP| TypedLLVMCreateFrame |] m =
  inExtImpTransM ETrans_LLVMFrame PTrans_True $
  withPermStackM (:>: Member_Base)
  (:>: PTrans_Conj [APTrans_LLVMFrame $ fmap (const []) (extMb mb_stmt)])
  m

itranslateLLVMStmt mb_stmt@[nuP| TypedLLVMDeleteFrame _ _ _ |] m =
  inExtImpTransM (ETrans_Term unitOpenTerm) PTrans_True $
  withPermStackM (const MNil) (const MNil) m


----------------------------------------------------------------------
-- * Translating Sequences of Typed Crucible Statements
----------------------------------------------------------------------

instance PermCheckExtC ext =>
         ImplTranslate (TypedRet ret ps) OpenTerm ext blocks ret ps ctx where
  itranslate [nuP| TypedRet ret r mb_perms |] =
    do let perms =
             mbMap2
             (\reg mbps -> varSubst (singletonVarSubst $ typedRegVar reg) mbps)
             r mb_perms
       assertPermStackEqM "TypedRet" perms
       r_trans <- exprTransToTermForce <$> tpTransM (tptranslate r)
       ret_trans <- tpTransM $ translateType $ ret
       pctx <- itiPermStack <$> ask
       tp_f <- lambdaExprTransForceI "r" (mbLift ret) $
         tpTransM $ tptranslate $ mbCombine mb_perms
       return $ ctorOpenTerm "Prelude.exists"
         [ret_trans, tp_f, r_trans,
          tupleOpenTerm (permCtxToTerms pctx)]

instance PermCheckExtC ext =>
         ImplTranslateF (TypedRet ret) ext blocks ret where
  itranslateF mb_ret = itranslate mb_ret

instance PermCheckExtC ext =>
         ImplTranslate (TypedTermStmt blocks ret ps) OpenTerm
         ext blocks ret ps ctx where
  itranslate [nuP| TypedJump impl_tgt |] = itranslate impl_tgt
  itranslate [nuP| TypedBr reg impl_tgt1 impl_tgt2 |] =
    applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
    [compReturnTypeM, tpTransM (exprTransToTermForce <$> tptranslate reg),
     itranslate impl_tgt1, itranslate impl_tgt2]
  itranslate [nuP| TypedReturn impl_ret |] = itranslate impl_ret
  itranslate [nuP| TypedErrorStmt _ |] = itiCatchHandler <$> ask

instance PermCheckExtC ext =>
         ImplTranslate (TypedStmtSeq ext blocks ret ps) OpenTerm
         ext blocks ret ps ctx where
  itranslate [nuP| TypedImplStmt impl_seq |] = itranslate impl_seq
  itranslate [nuP| TypedConsStmt _ stmt mb_seq |] =
    itranslateStmt stmt (itranslate $ mbCombine mb_seq)
  itranslate [nuP| TypedTermStmt _ term_stmt |] = itranslate term_stmt

instance PermCheckExtC ext =>
         ImplTranslateF (TypedStmtSeq ext blocks ret) ext blocks ret where
  itranslateF mb_seq = itranslate mb_seq


----------------------------------------------------------------------
-- * Translating CFGs
----------------------------------------------------------------------

-- | Fold a function over all the 'TypedEntry's in a 'TypedBlockMap', visiting
-- the entries in the right-most 'TypedBlock' first
foldBlockMap :: (forall args. TypedEntry ext blocks ret args -> b -> b) ->
                 b -> TypedBlockMap ext blocks ret -> b
foldBlockMap = helper where
  helper :: (forall args. TypedEntry ext blocks ret args -> b -> b) ->
            b -> MapRList (TypedBlock ext blocks ret) bs -> b
  helper _ b MNil = b
  helper f b (bs :>: TypedBlock []) = helper f b bs
  helper f b (bs :>: TypedBlock (entry:entries)) =
    f entry $ helper f b (bs :>: TypedBlock entries)

-- | FIXME: documentation
lambdaExprCtx :: CruCtx ctx -> TypeTransM ctx OpenTerm ->
                 TypeTransM RNil OpenTerm
lambdaExprCtx CruCtxNil m = m
lambdaExprCtx (CruCtxCons ctx tp) m =
  lambdaExprCtx ctx $ lambdaExprTrans "e" tp m

piExprCtx :: CruCtx ctx2 -> TypeTransM (ctx :++: ctx2) OpenTerm ->
             TypeTransM ctx OpenTerm
piExprCtx CruCtxNil m = m
piExprCtx (CruCtxCons ctx tp) m =
  piExprCtx ctx $ piExprTrans "e" tp m

-- | Build the return type for a function; FIXME: documentation
translateRetType :: TypeRepr ret -> Mb (ctx :> ret) (DistPerms ps) ->
                    TypeTransM ctx OpenTerm
translateRetType ret ret_perms =
  do mb_ret <- nuMultiTransM $ const ret
     tp_term <- translateType mb_ret
     tp_f <- lambdaExprTransForce "x" ret (tptranslate ret_perms)
     return $ dataTypeOpenTerm "Prelude.Sigma" [tp_term, tp_f]

nuMultiTransM :: (MapRList Name ctx -> b) -> TypeTransM ctx (Mb ctx b)
nuMultiTransM f =
  do ctx <- ask
     return $ nuMulti ctx f

-- | Build a @LetRecType@ that describes the type of the translation of a
-- 'TypedEntry'
translateEntryLRT :: TypedEntry ext blocks ret args ->
                     TypeTransM ctx OpenTerm
translateEntryLRT (TypedEntry entryID args ret perms_in perms_out _) =
  trace "translateEntryLRT starting..." $
  inEmptyTypeTransM $
  helperExpr (appendCruCtx (entryGhosts entryID) args) $
  helperPerms ret perms_in perms_out
  where
    helperExpr :: CruCtx ctx -> TypeTransM ctx OpenTerm ->
                  TypeTransM RNil OpenTerm
    helperExpr CruCtxNil m = m
    helperExpr (CruCtxCons ctx tp) m =
      helperExpr ctx $
      do mb_tp <- nuMultiTransM $ const tp
         tp_trans <- tptranslate mb_tp
         case tp_trans of
           Left etrans -> inExtTypeTransM etrans m
           Right (tp_term, mk_etrans) ->
             (\lam -> ctorOpenTerm "Prelude.LRT_Fun" [tp_term,lam]) <$>
             lambdaTransM "e" tp_term (\x -> inExtTypeTransM (mk_etrans x) m)

    helperPerms :: TypeRepr ret -> Mb ctx (DistPerms ps_in) ->
                   Mb (ctx :> ret) (DistPerms ps_out) -> TypeTransM ctx OpenTerm
    helperPerms ret [nuP| DistPermsNil |] ret_perms =
      (\retType ->
        trace "translateEntryLRT finished" $
        ctorOpenTerm "Prelude.LRT_Ret" [retType]) <$>
      translateRetType ret ret_perms
    helperPerms ret [nuP| DistPermsCons perms _ p |] ret_perms =
      do eith <- tptranslate p
         case eith of
           Left _ -> helperPerms ret perms ret_perms
           Right (tp_term, _) ->
             (\lam -> ctorOpenTerm "Prelude.LRT_Fun" [tp_term,lam]) <$>
             lambdaTransM "p" tp_term (\_ -> helperPerms ret perms ret_perms)


-- | Build a @LetRecTypes@ list that describes the types of all of the
-- entrypoints in a 'TypedBlockMap'
translateBlockMapLRTs :: TypedBlockMap ext blocks ret ->
                         TypeTransM ctx OpenTerm
translateBlockMapLRTs =
  trace "translateBlockMapLRTs started..." $
  foldBlockMap
  (\entry rest_m ->
    do entryType <- translateEntryLRT entry
       rest <- rest_m
       return $ ctorOpenTerm "Prelude.LRT_Cons" [entryType, rest])
  (trace "translateBlockMapLRTs finished" $
   return $ ctorOpenTerm "Prelude.LRT_Nil" [])


-- | FIXME: documentation
lambdaBlockMap :: TypedBlockMap ext blocks ret ->
                  (TypedBlockMapTrans ext blocks ret ->
                   TypeTransM ctx OpenTerm) ->
                  TypeTransM ctx OpenTerm
lambdaBlockMap = helper where
  helper :: MapRList (TypedBlock ext blocks ret) bs ->
            (MapRList (TypedBlockTrans ext blocks ret) bs ->
             TypeTransM ctx OpenTerm) ->
            TypeTransM ctx OpenTerm
  helper MNil f = f MNil
  helper (bs :>: TypedBlock []) f =
    helper bs (f . (:>: TypedBlockTrans []))
  helper (bs :>: TypedBlock (entry:entries)) f =
    do entryLRT <- translateEntryLRT entry
       lambdaTransM "f" (applyOpenTerm
                          (globalOpenTerm "Prelude.lrtToType")
                          entryLRT) $ \fvar ->
         helper (bs :>: TypedBlock entries)
         (\(bsTrans :>: TypedBlockTrans eTranss) ->
           f (bsTrans :>: TypedBlockTrans (TypedEntryTrans entry fvar:eTranss)))

translateEntryBody :: PermCheckExtC ext =>
                      TypedBlockMapTrans ext blocks ret ->
                      TypedEntry ext blocks ret args ->
                      TypeTransM ctx OpenTerm
translateEntryBody mapTrans (TypedEntry entryID args ret in_perms
                             ret_perms stmts) =
  inEmptyTypeTransM $
  lambdaExprCtx (appendCruCtx (entryGhosts entryID) args) $
  lambdaPermCtx (mbDistPermsToValuePerms in_perms) $ \pctx ->
  do retType <- translateRetType ret ret_perms
     impTransM pctx mapTrans retType $ itranslate stmts


translateBlockMapBodies :: PermCheckExtC ext =>
                           TypedBlockMapTrans ext blocks ret ->
                           TypedBlockMap ext blocks ret ->
                           TypeTransM ctx OpenTerm
translateBlockMapBodies mapTrans =
  trace "translateBlockMapBodies starting..." $
  foldBlockMap
  (\entry restM ->
    pairOpenTerm <$> translateEntryBody mapTrans entry <*> restM)
  (trace "translateBlockMapBodies finished" $ return unitOpenTerm)

-- | Translate a typed CFG to a SAW term
translateCFG :: PermCheckExtC ext => TypedCFG ext blocks ghosts inits ret ->
                OpenTerm
translateCFG cfg =
  let h = tpcfgHandle cfg
      fun_perm = tpcfgFunPerm cfg
      blkMap = tpcfgBlockMap cfg
      ctx = typedFnHandleAllArgs h
      ghosts = typedFnHandleGhosts h
      retType = typedFnHandleRetType h in
  runTypeTransM $ lambdaExprCtx ctx $
  lambdaPermCtx (mbCombine $ funPermIns fun_perm) $ \pctx ->
  lambdaPermTrans "l" (fmap (const $ ValPerm_Conj1 $
                             Perm_LOwned PExpr_PermListNil) $
                       mbCombine $ funPermIns fun_perm) $ \pl ->
  do retTypeTrans <-
       translateRetType retType
       (mbCombine $ fmap mbValuePermsToDistPerms $ tpcfgOutputPerms cfg)
     applyMultiTransM (return $ globalOpenTerm "Prelude.letRecM")
       [
         -- The LetRecTypes describing all the entrypoints of the CFG
         translateBlockMapLRTs blkMap

         -- The return type of the entire function
       , return retTypeTrans

         -- The definitions of the translations of the entrypoints of the CFG
       , lambdaBlockMap blkMap
         (\mapTrans -> translateBlockMapBodies mapTrans blkMap)

         -- The main body, that calls the first function with the input vars
       , lambdaBlockMap blkMap
         (\mapTrans ->
           impTransM (appendMapRList
                      (truePermTransCtx ghosts :>: pl)
                      pctx) mapTrans retTypeTrans $
           translateCallEntryID "CFG" (tpcfgEntryBlockID cfg)
           (funPermToBlockInputs fun_perm)
         )
       ]
