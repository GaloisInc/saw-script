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

module SAWScript.Heapster.SAWTranslation where

import Data.Maybe
import Data.Kind
import GHC.TypeLits
import qualified Data.Functor.Constant as Constant
import Control.Lens hiding ((:>),Index)
import Control.Monad.Reader

import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Data.Parameterized.Context hiding ((:>), empty, take, view)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Arch.X86
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.Analysis.Fixpoint.Components

import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor

import SAWScript.Heapster.CruUtil
import SAWScript.Heapster.Permissions
import SAWScript.Heapster.Implication
import SAWScript.Heapster.TypedCrucible


----------------------------------------------------------------------
-- * The Pure Translation Monad
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

  -- | The default translation of an expression is just a SAW term
  ETrans_Std :: OpenTerm -> ExprTrans a


-- | A context mapping bound names to their type-level SAW translations
type ExprTransCtx (ctx :: RList CrucibleType) = MapRList ExprTrans ctx

-- | Build the correct 'ExprTrans' from an 'OpenTerm' given its type
mkExprTrans :: TypeRepr a -> OpenTerm -> ExprTrans a
mkExprTrans = helper where
  helper :: TypeRepr a -> OpenTerm -> ExprTrans a
  helper (LLVMPointerRepr _) _ = ETrans_LLVM
  helper (LLVMFrameRepr _) _ = ETrans_LLVMFrame
  helper LifetimeRepr _ = ETrans_Lifetime
  helper PermListRepr _ = ETrans_PermList
  helper _ t = ETrans_Std t

-- | Map an expression translation result to an 'OpenTerm' or 'Nothing' if it
-- has no pure content, i.e., if it is a splitting or LLVM value
exprTransToMaybeTerm :: ExprTrans a -> Maybe OpenTerm
exprTransToMaybeTerm ETrans_LLVM = Nothing
exprTransToMaybeTerm ETrans_LLVMFrame = Nothing
exprTransToMaybeTerm ETrans_Lifetime = Nothing
exprTransToMaybeTerm ETrans_PermList = Nothing
exprTransToMaybeTerm (ETrans_Std t) = Just t

exprTransToTerm :: ExprTrans a -> OpenTerm
exprTransToTerm = fromMaybe unitOpenTerm . exprTransToMaybeTerm

-- | Map a context of pure translations to a list of 'OpenTerm's, dropping the
-- "invisible" ones that are always translated to unit
exprCtxToTerms :: ExprTransCtx ctx -> [OpenTerm]
exprCtxToTerms MNil = []
exprCtxToTerms (ctx :>: (exprTransToMaybeTerm -> Just t)) = exprCtxToTerms ctx ++ [t]
exprCtxToTerms (ctx :>: _) = exprCtxToTerms ctx


-- | The type translation monad = a reader monad for 'ExprTransCtx'
type TypeTransM ctx = Reader (ExprTransCtx ctx)


-- | Run a 'TypeTransM' computation in an extended context
inExtTypeTransM :: ExprTrans tp -> TypeTransM (ctx :> tp) a ->
                   TypeTransM ctx a
inExtTypeTransM tp_trans = withReader (:>: tp_trans)

-- | Apply terms inside translation monads
applyTransM :: Reader r OpenTerm -> Reader r OpenTerm -> Reader r OpenTerm
applyTransM m1 m2 = applyOpenTerm <$> m1 <*> m2

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
letTransM :: String -> OpenTerm -> OpenTerm ->
             (OpenTerm -> Reader r OpenTerm) -> Reader r OpenTerm
letTransM x tp rhs body_m =
  do r <- ask
     return $ letOpenTerm x tp rhs (\x -> runReader (body_m x) r)


----------------------------------------------------------------------
-- * The Pure Translation
----------------------------------------------------------------------

-- | The typeclass for the type-level translation
class TypeTranslate a res | a -> res where
  tptranslate :: Mb ctx a -> TypeTransM ctx res

instance TypeTranslate (NatRepr n) OpenTerm where
  tptranslate mb_n = return $ natOpenTerm $ mbLift $ fmap intValue mb_n

-- The Idea: if a type translates to Nothing then its expressions are not
-- represented in our SAW translation
instance TypeTranslate (TypeRepr a) (Maybe OpenTerm) where
  tptranslate [nuP| (AnyRepr) |] =
    return $ error "TypeTranslate: Any"
  tptranslate [nuP| (UnitRepr) |] =
    return $ Just unitTypeOpenTerm
  tptranslate [nuP| (BoolRepr) |] =
    return $ Just $ dataTypeOpenTerm "Prelude.Bool" []
  tptranslate [nuP| (NatRepr) |] =
    return $ Just $ dataTypeOpenTerm "Prelude.Nat" []
  tptranslate [nuP| (IntegerRepr) |] =
    return $ error "TypeTranslate: IntegerRepr"
  tptranslate [nuP| (RealValRepr) |] =
    return $ error "TypeTranslate: RealValRepr"
  tptranslate [nuP| (ComplexRealRepr) |] =
    return $ error "TypeTranslate: ComplexRealRepr"
  tptranslate [nuP| (BVRepr w) |] =
    Just <$>
    applyOpenTerm (globalOpenTerm "Prelude.bitvector") <$> tptranslate w

  -- Our special-purpose intrinsic types, whose translations do not have
  -- computational content
  tptranslate [nuP| (LLVMPointerRepr _) |] =
    return Nothing
  tptranslate [nuP| (LLVMFrameRepr _) |] =
    return Nothing
  tptranslate [nuP| LifetimeRepr |] =
    return Nothing
  tptranslate [nuP| PermListRepr |] =
    return Nothing
  tptranslate [nuP| (IntrinsicRepr _ _) |] =
    return $ error "TypeTranslate: IntrinsicRepr"

  tptranslate [nuP| (RecursiveRepr _ _) |] =
    return $ error "TypeTranslate: RecursiveRepr"
  tptranslate [nuP| (FloatRepr _) |] =
    return $ Just $ dataTypeOpenTerm "Prelude.Float" []
  tptranslate [nuP| (IEEEFloatRepr _) |] =
    return $ error "TypeTranslate: IEEEFloatRepr"
  tptranslate [nuP| (CharRepr) |] =
    return $ error "TypeTranslate: CharRepr"
  tptranslate [nuP| (StringRepr) |] =
    return $ Just $ dataTypeOpenTerm "Prelude.String" []
  tptranslate [nuP| (FunctionHandleRepr _ _) |] =
    -- NOTE: function permissions translate to the SAW function, but the
    -- function handle itself has no SAW translation
    return Nothing
  tptranslate [nuP| (MaybeRepr tp) |] =
    fmap (applyOpenTerm (globalOpenTerm "Prelude.Maybe")) <$> tptranslate tp
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


instance TypeTranslate (ExprVar a) (ExprTrans a) where
  tptranslate mb_x
    | Left memb <- mbNameBoundP mb_x = mapRListLookup memb <$> ask
  tptranslate mb_x = error "tptranslate: unbound variable!"

instance TypeTranslate (PermExpr a) (ExprTrans a) where
  tptranslate = error "FIXME HERE NOW"

instance ress ~ (CtxToRList as) =>
         TypeTranslate (PermExprs as) (ExprTransCtx ress) where
  tptranslate = error "FIXME HERE NOW"

instance TypeTranslate (BVFactor w) OpenTerm where
  tptranslate = error "FIXME HERE NOW"

-- [| p :: ValuePerm |] = type of the impl translation of reg with perms p
instance TypeTranslate (ValuePerm a) (Maybe OpenTerm) where
  tptranslate = error "FIXME HERE NOW"

instance TypeTranslate (ValuePerms a) [OpenTerm] where
  tptranslate = error "FIXME HERE NOW"


----------------------------------------------------------------------
-- * The Translations of Permission Implications
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
  PTrans_Conj :: TypeCtx ctx => [AtomicPermTrans ctx a] -> PermTrans ctx a

  -- | The default translation is a SAW term. Note that this can include LLVM
  -- pointer permissions that have not yet been broken into multiple SAW terms.
  PTrans_Std :: Mb ctx (ValuePerm a) -> OpenTerm -> PermTrans ctx a


-- | The 'PermTrans' type for atomic permissions
data AtomicPermTrans ctx a where

  -- | The translation of an LLVM field permission is just the translation of
  -- its contents
  APTrans_LLVMField :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMFieldPerm w) ->
                       PermTrans ctx (LLVMPointerType w) ->
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

  -- | Propositional permissions have no computational content
  APTrans_BVProp :: (1 <= w, KnownNat w) => Mb ctx (BVProp w) ->
                    AtomicPermTrans ctx (LLVMPointerType w)

  -- | The default translation of an atomic permission is a SAW term
  APTrans_Std :: Mb ctx (AtomicPerm a) -> OpenTerm -> AtomicPermTrans ctx a


-- | A context mapping bound names to their perm translations
type PermTransCtx ctx ps = MapRList (PermTrans ctx) ps

-- | Build a 'PermTrans' from a permission and its term
mkPermTrans :: Mb ctx (ValuePerm a) -> OpenTerm -> PermTrans ctx a
mkPermTrans [nuP| ValPerm_Eq mb_e |] _ = PTrans_Eq mb_e
mkPermTrans mb_p t = PTrans_Std mb_p t

-- | Map a perm translation result to an 'OpenTerm'
permTransToTerm :: PermTrans ctx a -> OpenTerm
permTransToTerm (PTrans_Eq _) = unitOpenTerm
permTransToTerm (PTrans_Conj aps) =
  tupleOpenTerm $ map atomicPermTransToTerm aps
permTransToTerm (PTrans_Std _ t) = t

-- | Map an atomic perm translation result to an 'OpenTerm'
atomicPermTransToTerm :: AtomicPermTrans ctx a -> OpenTerm
atomicPermTransToTerm _ = error "FIXME HERE NOW"

-- | Map a context of perm translations to a list of 'OpenTerm's, dropping the
-- "invisible" ones that are always translated to unit
permCtxToTerms :: PermTransCtx ctx ps -> [OpenTerm]
permCtxToTerms =
  mapRListToList . mapMapRList (Constant.Constant . permTransToTerm)

-- | Extract out the permission of a permission translation result
permTransPerm :: PermTrans ctx a -> Mb ctx (ValuePerm a)
permTransPerm (PTrans_Eq e) = fmap ValPerm_Eq e
permTransPerm (PTrans_Conj ts) =
  fmap ValPerm_Conj $ sequenceA $ map atomicPermTransPerm ts
permTransPerm (PTrans_Std p _) = p

atomicPermTransPerm :: AtomicPermTrans ctx a -> Mb ctx (AtomicPerm a)
atomicPermTransPerm = error "FIXME HERE NOW"

extMb :: Mb ctx a -> Mb (ctx :> tp) a
extMb = mbCombine . fmap (nu . const)

-- | Extend the context of a permission translation result
extPermTrans :: PermTrans ctx a -> PermTrans (ctx :> tp) a
extPermTrans (PTrans_Eq e) = PTrans_Eq $ extMb e
extPermTrans (PTrans_Conj _) = error "FIXME HERE NOW"
extPermTrans (PTrans_Std p t) = PTrans_Std (extMb p) t

-- | Extend the context of a permission translation context
extPermTransCtx :: PermTransCtx ctx ps -> PermTransCtx (ctx :> tp) ps
extPermTransCtx = mapMapRList extPermTrans

-- | Add another permission translation to a permission translation context
consPermTransCtx :: PermTransCtx ctx ps -> PermTrans ctx a ->
                    PermTransCtx ctx (ps :> a)
consPermTransCtx = (:>:)


----------------------------------------------------------------------
-- * The Impure Translation Monad
----------------------------------------------------------------------

-- | A mapping from a block entrypoint to its corresponding SAW variable that is
-- bound to its translation
data TypedEntryTrans ext blocks ret args =
  TypedEntryTrans (TypedEntry ext blocks ret args) OpenTerm

-- | A mapping from a block to the SAW functions for each entrypoint
data TypedBlockTrans ext blocks ret args =
  TypedBlockTrans [TypedEntryTrans ext blocks ret args]

-- | A mapping from all block entrypoints to their SAW translations
type TypedBlockMapTrans ext blocks ret =
  MapRList (TypedBlockTrans ext blocks ret) blocks

-- | Translate an entrypoint ID by looking up its SAW function
translateTypedEntryID :: TypedEntryID blocks args ghosts ->
                         TypedBlockMapTrans ext blocks ret ->
                         OpenTerm
translateTypedEntryID entryID blkMap =
  let TypedBlockTrans entries = mapRListLookup (entryBlockID entryID) blkMap in
  foldr (\(TypedEntryTrans entry trm) rest ->
          case entry of
            TypedEntry entryID' _ _ _
              | Just Refl <- testEquality entryID entryID' -> trm
            _ -> rest)
  (error "translateTypedEntryID")
  entries


-- | Contextual info for a permission-level translation
data ImpTransInfo ext blocks ret args ps ctx =
  ImpTransInfo
  {
    itiExprCtx :: ExprTransCtx ctx,
    itiPermCtx :: PermTransCtx ctx ctx,
    itiPermStack :: PermTransCtx ctx ps,
    itiBlockTrans :: TypedBlockMapTrans ext blocks ret,
    itiCatchHandler :: Maybe OpenTerm,
    itiReturnType :: OpenTerm
  }

extPermTransInfo :: ExprTrans tp -> PermTrans (ctx :> tp) tp ->
                    ImpTransInfo ext blocks ret args ps ctx ->
                    ImpTransInfo ext blocks ret args ps (ctx :> tp)
extPermTransInfo tp_trans perm_trans (ImpTransInfo {..}) =
  ImpTransInfo
  { itiExprCtx = itiExprCtx :>: tp_trans
  , itiPermCtx = consPermTransCtx (extPermTransCtx itiPermCtx) perm_trans
  , itiPermStack = extPermTransCtx itiPermStack
  , .. }

-- | The monad for permission-level translation
type ImpTransM ext blocks ret args ps ctx =
  Reader (ImpTransInfo ext blocks ret args ps ctx)

-- | Embed a pure translation into an impure translation
embedPureM :: TypeTransM ctx a -> ImpTransM ext blocks ret args ps ctx a
embedPureM = withReader itiExprCtx

-- | Run an 'ImpTransM' computation in an extended context
inExtImpTransM :: ExprTrans tp -> PermTrans (ctx :> tp) tp ->
                  ImpTransM ext blocks ret args ps (ctx :> tp) a ->
                  ImpTransM ext blocks ret args ps ctx a
inExtImpTransM tp_trans perm_trans =
  withReader $ extPermTransInfo tp_trans perm_trans

-- | Apply the translation of a function-like construct (i.e., a
-- 'TypedJumpTarget' or 'TypedFnHandle') to the pure plus impure translations of
-- its arguments
translateApply :: OpenTerm -> ExprTransCtx tps -> PermTransCtx ctx tps ->
                  OpenTerm
translateApply f p_args i_args =
  applyOpenTermMulti f (exprCtxToTerms p_args ++ permCtxToTerms i_args)


----------------------------------------------------------------------
-- * Translating Permission Implication Constructs
----------------------------------------------------------------------

{-


-- | FIXME: figure out a better name and move to Hobbits
mbMap2 :: (a -> b -> c) -> Mb ctx a -> Mb ctx b -> Mb ctx c
mbMap2 f mb1 mb2 = fmap f mb1 `mbApply` mb2

-- | Apply left or-introduction to a permission translation by applying the
-- @Left@ constructor in SAW
introOrLTrans :: Mb ctx (ValuePerm a) -> PermTrans ctx a ->
                 ImpTransM ext blocks ret args ps ctx (PermTrans ctx a)
introOrLTrans p1 pt =
  do tp1 <- embedPureM $ tptranslate p1
     tp2 <- embedPureM $ tptranslate (permTransPerm pt)
     return $
       PTrans_Std (mbMap2 ValPerm_Or p1 $ permTransPerm pt)
       (ctorOpenTerm "Prelude.Left" [tp1, tp2, permTransToTerm pt])

-- | Apply right or-introduction to a permission translation by applying the
-- @Right@ constructor in SAW
introOrRTrans :: Mb ctx (ValuePerm a) -> PermTrans ctx a ->
                 ImpTransM ext blocks ret args ps ctx (PermTrans ctx a)
introOrRTrans p2 pt =
  do tp1 <- embedPureM $ tptranslate (permTransPerm pt)
     tp2 <- embedPureM $ tptranslate p2
     return $
       PTrans_Std (mbMap2 ValPerm_Or (permTransPerm pt) p2)
       (ctorOpenTerm "Prelude.Right" [tp1, tp2, permTransToTerm pt])

-- | Translate an or-elimination to the @either@ elimination rule
elimOrTrans :: PermTrans ctx a ->
               (PermTrans ctx a ->
                ImpTransM ext blocks ret args ps ctx OpenTerm) ->
               (PermTrans ctx a ->
                ImpTransM ext blocks ret args ps ctx OpenTerm) ->
               ImpTransM ext blocks ret args ps ctx OpenTerm
elimOrTrans (PTrans_Std mb_p t) f1 f2 =
  do let mb_p1 = fmap orPermLeft mb_p
         mb_p2 = fmap orPermRight mb_p
     tp1 <- embedPureM $ tptranslate mb_p1
     tp2 <- embedPureM $ tptranslate mb_p2
     ret_tp <- itiReturnType <$> ask
     f1trans <- lambdaTransM "x_left" tp1 (f1 . mkPermTrans mb_p1)
     f2trans <- lambdaTransM "x_right" tp2 (f2 . mkPermTrans mb_p2)
     return (applyOpenTermMulti (globalOpenTerm "Prelude.either")
             [tp1, tp2, ret_tp, f1trans, f2trans])
elimOrTrans _ _ _ = error "elimOrTrans"

-- | Translate an exists-introduction to a @Sigma@ introduction
introExistsTrans :: KnownRepr TypeRepr tp => Mb ctx (PermExpr tp) ->
                    Mb ctx (Binding tp (ValuePerm a)) ->
                    PermTrans ctx a ->
                    ImpTransM ext blocks ret args ps ctx (PermTrans ctx a)
introExistsTrans (mb_e :: Mb ctx (PermExpr tp)) mb_p_body pt
  | permTransPerm pt
    == mbMap2 (\e p_body ->
                subst (singletonSubst e) p_body) mb_e mb_p_body =
    do let mb_p = permTransPerm pt
           t = permTransToTerm pt
       let tp = knownRepr :: TypeRepr tp
       tp_trans <- embedPureM $ tptranslate (fmap (const tp) mb_e)
       tp_f <- embedPureM $ lambdaTransM "x_introEx" tp_trans $ \x ->
         inExtTypeTransM (mkExprTrans tp x) (tptranslate $ mbCombine mb_p_body)
       e <- exprTransToTerm <$> embedPureM (tptranslate mb_e)
       return $
         PTrans_Std (fmap ValPerm_Exists mb_p_body) $
         ctorOpenTerm "Prelude.exists" [tp_trans, tp_f, e, t]
introExistsTrans _ _ _ = error "introExistsTrans"

-- | Translate an existential elimination into a @Sigma@ elimination
elimExistsTrans :: KnownRepr TypeRepr tp =>
                   PermTrans ctx a ->
                   (PermTrans (ctx :> tp) a ->
                    ImpTransM ext blocks ret args ps (ctx :> tp) OpenTerm) ->
                   ImpTransM ext blocks ret args ps ctx OpenTerm
elimExistsTrans (PTrans_Std mb_p t) f =
  do let tp1 = knownRepr
         mb_p_body = mbCombine $ fmap (exPermBody tp1) mb_p
     tp1_trans <- embedPureM $ tptranslate $ fmap (const tp1) mb_p
     tp2_trans <- embedPureM $ lambdaTransM "x_fst" tp1_trans $ \x ->
       inExtTypeTransM (mkExprTrans tp1 x) $ tptranslate mb_p_body
     ret_tp <- itiReturnType <$> ask
     let ret_tp_f = lambdaOpenTerm "x_fst" tp1_trans (const ret_tp)
     f_trans <- lambdaTransM "x_fst" tp1_trans $ \x1 ->
       lambdaTransM "x_snd" (applyOpenTerm tp2_trans x1) $ \x2 ->
       inExtImpTransM (mkExprTrans tp1 x1) (PTrans_True (mbToProxy mb_p_body)) $
       f (mkPermTrans mb_p_body x2)
     return $ applyOpenTermMulti (globalOpenTerm "Prelude.Sigma__rec")
       [tp1_trans, tp2_trans, ret_tp_f, f_trans, t]
elimExistsTrans _ _ = error "elimExistsTrans"


----------------------------------------------------------------------
-- * The Impure Translation
----------------------------------------------------------------------

-- | The typeclass for translating permission implications
class ImplTranslate a res ext blocks ret args ps ctx | ctx a -> res where
  itranslate :: Mb ctx a -> ImpTransM ext blocks ret args ps ctx res

-- | The typeclass for the impure translation of a functor at any type to an
-- 'OpenTerm'
class ImplTranslate1 f ext blocks ret args ps ctx where
  itranslate1 :: Mb ctx (f a) -> ImpTransM ext blocks ret args ps ctx OpenTerm

instance ImplTranslate1 f ext blocks ret args ps ctx =>
         ImplTranslate (PermImpl f ps) OpenTerm ext blocks ret args ps ctx where
  itranslate = error "FIXME HERE NOW"

instance ImplTranslate (TypedReg tp) (PermTrans ctx tp)
         ext blocks ret args ps ctx where
  itranslate = error "FIXME HERE NOW"

instance ImplTranslate (TypedExpr ext tp) (PermTrans ctx tp)
         ext blocks ret args ps ctx where
  itranslate = error "FIXME HERE NOW"

instance ImplTranslate (TypedEntryID blocks args' ghosts) OpenTerm
         ext blocks ret args ps ctx where
  itranslate mb_entryID =
    translateTypedEntryID (mbLift mb_entryID) <$> itiBlockTrans <$> ask

-- A sequence of distinguished permissions on variables translates to a list of
-- pure translations of the variables and impure translations of the permissions
-- on them
instance ImplTranslate (DistPerms tps) (ExprTransCtx tps, PermTransCtx ctx tps)
         ext blocks ret args ps ctx where
  itranslate [nuP| DistPermsNil |] = return (MNil, MNil)
  itranslate [nuP| DistPermsCons perms x _ |] =
    do (p_trs,i_trs) <- itranslate perms
       p_tr <- embedPureM $ tptranslate x
       i_tr <- itranslate (fmap TypedReg x)
       return (p_trs :>: p_tr, i_trs :>: i_tr)

instance ImplTranslate (TypedJumpTarget blocks ps) OpenTerm
         ext blocks ret args ps ctx where
  itranslate [nuP| TypedJumpTarget entryID _ perms |] =
    do f <- itranslate entryID
       (p_args, i_args) <- itranslate perms
       return $ translateApply f p_args i_args

{-
FIXME HERE NOW:
- Write the translation for PermImpl and for TypedStmt, to see what prims we need
- Need something special for TypedStmt to bind vars; maybe just do seqs?
- ImpTranslate for statement sequences, blocks / entrypoints, and CFGs
-}
-}
