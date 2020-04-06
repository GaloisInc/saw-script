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
import Data.Text (unpack)
import GHC.TypeLits
import qualified Data.Functor.Constant as Constant
import Control.Applicative
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
-- * Translation Monads
----------------------------------------------------------------------

-- | The result of translating a type-like construct such as a 'TypeRepr' or a
-- permission, parameterized by the (Haskell) type of the translations of the
-- elements of that type. This are translated to 0 or more SAW types, along with
-- a (Haskell) function for mapping elements of those types their translation
-- construct in Haskell.
data TypeTrans tr = TypeTrans
                     { typeTransTypes :: [OpenTerm],
                       typeTransF :: [OpenTerm] -> tr }

instance Functor TypeTrans where
  fmap f (TypeTrans ts tp_f) = TypeTrans ts (f . tp_f)

instance Applicative TypeTrans where
  pure = mkTypeTrans0
  liftA2 f (TypeTrans tps1 f1) (TypeTrans tps2 f2) =
    TypeTrans (tps1 ++ tps2)
    (\ts -> f (f1 $ take (length tps1) ts) (f2 $ drop (length tps1) ts))

-- | Build a 'TypeTrans' represented by 0 SAW types
mkTypeTrans0 :: tr -> TypeTrans tr
mkTypeTrans0 tr = TypeTrans [] (\[] -> tr)

-- | Build a 'TypeTrans' represented by 1 SAW type
mkTypeTrans1 :: OpenTerm -> (OpenTerm -> tr) -> TypeTrans tr
mkTypeTrans1 tp f = TypeTrans [tp] (\[t] -> f t)

-- | Extract out the single SAW type associated with a 'TypeTrans', or the unit
-- type if it has 0 SAW types. It is an error if it has 2 or more SAW types.
typeTransType1 :: TypeTrans tr -> OpenTerm
typeTransType1 (TypeTrans [] _) = unitTypeOpenTerm
typeTransType1 (TypeTrans [tp] _) = tp
typeTransType1 _ = error "typeTransType1"

-- | Map the 'typeTransTypes' field of a 'TypeTrans' to a single type, where a
-- single type is mapped to itself, an empty list of types is mapped to @unit@,
-- and a list of 2 or more types is mapped to a tuple of the types
typeTransTupleType :: TypeTrans tr -> OpenTerm
typeTransTupleType (TypeTrans [] _) = unitTypeOpenTerm
typeTransTupleType (TypeTrans [tp] _) = tp
typeTransTupleType (TypeTrans tps _) = tupleTypeOpenTerm tps

-- | Convert a 'TypeTrans' over 0 or more types to one over 1 type, where 2
-- or more types are converted to a single tuple type
tupleTypeTrans :: TypeTrans tr -> TypeTrans tr
-- tupleTypeTrans ttrans@(TypeTrans [] _) = ttrans
tupleTypeTrans ttrans@(TypeTrans [_] _) = ttrans
tupleTypeTrans ttrans =
  TypeTrans [tupleTypeOpenTerm $ typeTransTypes ttrans]
  (\[t] -> typeTransF ttrans $ map (\i -> projTupleOpenTerm i t) $
           take (length $ typeTransTypes ttrans) [0..])

-- | Build a type translation for a list of translations
listTypeTrans :: [TypeTrans tr] -> TypeTrans [tr]
listTypeTrans [] = pure []
listTypeTrans (trans:transs) = liftA2 (:) trans $ listTypeTrans transs


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
type ExprTransCtx = MapRList ExprTrans


-- | Describes a Haskell type that represents the translation of a term-like
-- construct that corresponds to 0 or more SAW terms
class IsTermTrans tr where
  transTerms :: tr -> [OpenTerm]

-- | Build a tuple of the terms contained in a translation, with 0 terms mapping
-- to the unit term and one term mapping to itself. If @ttrans@ is a 'TypeTrans'
-- describing the SAW types associated with a @tr@ translation, then this
-- function returns an element of the type @'tupleTypeTrans' ttrans@.
transTupleTerm :: IsTermTrans tr => tr -> OpenTerm
transTupleTerm (transTerms -> [t]) = t
transTupleTerm tr = tupleOpenTerm $ transTerms tr

-- | Like 'transTupleTerm' but raise an error if there are more than 1 terms
transTerm1 :: IsTermTrans tr => tr -> OpenTerm
transTerm1 (transTerms -> []) = unitOpenTerm
transTerm1 (transTerms -> [t]) = t
transTerm1 _ = error "transTerm1"


instance IsTermTrans tr => IsTermTrans [tr] where
  transTerms = concatMap transTerms

instance IsTermTrans (TypeTrans tr) where
  transTerms = typeTransTypes

instance IsTermTrans (ExprTrans tp) where
  transTerms ETrans_LLVM = []
  transTerms ETrans_LLVMFrame = []
  transTerms ETrans_Lifetime = []
  transTerms ETrans_PermList = []
  transTerms ETrans_Fun = []
  transTerms (ETrans_Term t) = [t]

instance IsTermTrans (ExprTransCtx ctx) where
  transTerms MNil = []
  transTerms (ctx :>: etrans) = transTerms ctx ++ transTerms etrans


-- | Map a context of expression translations to a list of 'OpenTerm's
exprCtxToTerms :: ExprTransCtx tps -> [OpenTerm]
exprCtxToTerms =
  concat . mapRListToList . mapMapRList (Constant.Constant . transTerms)


-- | Class for valid translation info types, which must contain at least a
-- context of expression translations
class TransInfo info where
  infoCtx :: info ctx -> ExprTransCtx ctx
  infoEnv :: info ctx -> PermEnv
  extTransInfo :: ExprTrans tp -> info ctx -> info (ctx :> tp)

-- | A "translation monad" is a 'Reader' monad with some info type that is
-- parameterized by a translation context
newtype TransM info (ctx :: RList CrucibleType) a =
  TransM { unTransM :: Reader (info ctx) a }
  deriving (Functor, Applicative, Monad)

-- | The run function for the 'TransM' monad
runTransM :: TransM info ctx a -> info ctx -> a
runTransM (TransM m) = runReader m

instance MonadReader (info ctx) (TransM info ctx) where
  ask = TransM ask
  local f (TransM m) = TransM $ local f m

-- | Run a translation computation with a modified info object
withInfoM :: (info ctx -> info' ctx') -> TransM info' ctx' a ->
             TransM info ctx a
withInfoM f (TransM m) = TransM $ withReader f m

-- | Run a translation computation in an extended context
inExtTransM :: TransInfo info => ExprTrans tp -> TransM info (ctx :> tp) a ->
               TransM info ctx a
inExtTransM etrans (TransM m) = TransM $ withReader (extTransInfo etrans) m

-- | Run a translation computation in a context extended with multiple types
inExtMultiTransM :: TransInfo info => ExprTransCtx ctx2 ->
                    TransM info (ctx :++: ctx2) a ->
                    TransM info ctx a
inExtMultiTransM MNil m = m
inExtMultiTransM (ctx :>: etrans) m =
  inExtMultiTransM ctx $ inExtTransM etrans m

-- | Run a translation computation in a specific context
inCtxTransM :: TransInfo info => ExprTransCtx ctx ->
               TransM info ctx a -> TransM info RNil a
inCtxTransM MNil m = m
inCtxTransM (ctx :>: etrans) m = inCtxTransM ctx $ inExtTransM etrans m

-- | Build a multi-binding for the current context
nuMultiTransM :: TransInfo info => (MapRList Name ctx -> b) ->
                 TransM info ctx (Mb ctx b)
nuMultiTransM f =
  do info <- ask
     return $ nuMulti (infoCtx info) f

-- | Apply the result of a translation to that of another
applyTransM :: TransM info ctx OpenTerm -> TransM info ctx OpenTerm ->
               TransM info ctx OpenTerm
applyTransM m1 m2 = applyOpenTerm <$> m1 <*> m2

-- | Apply the result of a translation to the results of multiple translations
applyMultiTransM :: TransM info ctx OpenTerm -> [TransM info ctx OpenTerm] ->
                    TransM info ctx OpenTerm
applyMultiTransM m ms = foldl applyTransM m ms

-- | Build a lambda-abstraction inside the 'TransM' monad
lambdaOpenTermTransM :: String -> OpenTerm ->
                        (OpenTerm -> TransM info ctx OpenTerm) ->
                        TransM info ctx OpenTerm
lambdaOpenTermTransM x tp body_f =
  ask >>= \info ->
  return (lambdaOpenTerm x tp $ \t -> runTransM (body_f t) info)

-- | Build a nested lambda-abstraction
--
-- > \x1:tp1 -> ... -> \xn:tpn -> body
--
-- over the types in a 'TypeTrans' inside a translation monad, using the
-- 'String' as a variable name prefix for the @xi@ variables
lambdaTransM :: String -> TypeTrans tr -> (tr -> TransM info ctx OpenTerm) ->
                TransM info ctx OpenTerm
lambdaTransM x tps body_f =
  ask >>= \info ->
  return (lambdaOpenTermMulti
          (zipWith (\i tp -> (x ++ show i, tp)) [0..] $ typeTransTypes tps)
          (\ts -> runTransM (body_f $ typeTransF tps ts) info))

-- | Build a lambda-abstraction
--
-- > \x1:(tp1, ..., tpn) -> body
--
-- over a tuple of the types in a 'TypeTrans'. Note that this always builds
-- exactly one lambda-abstraction, even if there are 0 types.
lambdaTupleTransM :: String -> TypeTrans tr -> (tr -> TransM info ctx OpenTerm) ->
                     TransM info ctx OpenTerm
lambdaTupleTransM x ttrans body_f =
  lambdaTransM x (tupleTypeTrans ttrans) body_f

-- | Build a pi-abstraction over the types in a 'TypeTrans' inside a
-- translation monad, using the 'String' as a variable name prefix
piTransM :: String -> TypeTrans tr -> (tr -> TransM info ctx OpenTerm) ->
            TransM info ctx OpenTerm
piTransM x tps body_f =
  ask >>= \info ->
  return (piOpenTermMulti
          (zipWith (\i tp -> (x ++ show i, tp)) [0..] $ typeTransTypes tps)
          (\ts -> runTransM (body_f $ typeTransF tps ts) info))

-- | Build a let-binding in a translation monad
letTransM :: String -> OpenTerm -> TransM info ctx OpenTerm ->
             (OpenTerm -> TransM info ctx OpenTerm) ->
             TransM info ctx OpenTerm
letTransM x tp rhs_m body_m =
  do r <- ask
     return $
       letOpenTerm x tp (runTransM rhs_m r) (\x -> runTransM (body_m x) r)

-- | Build an @Either@ type in SAW from the 'typeTransTupleType's of the left
-- and right types
eitherTypeTrans :: TypeTrans trL -> TypeTrans trR -> OpenTerm
eitherTypeTrans tp_l tp_r =
  dataTypeOpenTerm "Prelude.Either"
  [typeTransTupleType tp_l, typeTransTupleType tp_r]

-- | Apply the @Left@ constructor of the @Either@ type in SAW to the
-- 'transTupleTerm' of the input
leftTrans :: IsTermTrans trL => TypeTrans trL -> TypeTrans trR -> trL ->
             OpenTerm
leftTrans tp_l tp_r tr =
  ctorOpenTerm "Prelude.Left"
  [typeTransTupleType tp_l, typeTransTupleType tp_r, transTupleTerm tr]

-- | Apply the @Right@ constructor of the @Either@ type in SAW to the
-- 'transTupleTerm' of the input
rightTrans :: IsTermTrans trR => TypeTrans trL -> TypeTrans trR -> trR ->
              OpenTerm
rightTrans tp_l tp_r tr =
  ctorOpenTerm "Prelude.Right"
  [typeTransTupleType tp_l, typeTransTupleType tp_r, transTupleTerm tr]

-- | Eliminate a SAW @Either@ type
eitherElimTransM :: TypeTrans trL -> TypeTrans trR ->
                    TypeTrans tr -> (trL -> TransM info ctx OpenTerm) ->
                    (trR -> TransM info ctx OpenTerm) -> OpenTerm ->
                    TransM info ctx OpenTerm
eitherElimTransM tp_l tp_r tp_ret fl fr eith =
  do fl_trans <- lambdaTupleTransM "x_left" tp_l fl
     fr_trans <- lambdaTupleTransM "x_right" tp_r fr
     return $ applyOpenTermMulti (globalOpenTerm "Prelude.either")
       [ typeTransTupleType tp_l, typeTransTupleType tp_r,
         typeTransTupleType tp_ret, fl_trans, fr_trans, eith ]

-- | Build the dependent pair type whose first projection type is the
-- 'typeTransTupleType' of the supplied 'TypeTrans' and whose second projection
-- is the 'typeTransTupleType' of the supplied monadic function. As a special
-- case, just return the latter if the 'TypeTrans' contains 0 types.
sigmaTypeTransM :: String -> TypeTrans trL ->
                   (trL -> TransM info ctx (TypeTrans trR)) ->
                   TransM info ctx OpenTerm
sigmaTypeTransM _ ttrans@(typeTransTypes -> []) tp_f =
  typeTransTupleType <$> tp_f (typeTransF ttrans [])
sigmaTypeTransM x ttrans tp_f =
  do tp_f_trm <- lambdaTupleTransM x ttrans (\tr ->
                                              typeTransTupleType <$> tp_f tr)
     return (dataTypeOpenTerm "Prelude.Sigma"
             [typeTransTupleType ttrans, tp_f_trm])

-- | Build a dependent pair of the type returned by 'sigmaTypeTransM'. Note that
-- the 'TypeTrans' returned by the type-level function will in general be in a
-- larger context than that of the right-hand projection argument, so we allow
-- the representation types to be different to allow for this.
sigmaTransM :: (IsTermTrans trL, IsTermTrans trR2) => String -> TypeTrans trL ->
               (trL -> TransM info ctx (TypeTrans trR1)) ->
               trL -> TransM info ctx trR2 ->
               TransM info ctx OpenTerm
sigmaTransM _ (typeTransTypes -> []) _ _ rhs_m = transTupleTerm <$> rhs_m
sigmaTransM x tp_l tp_r lhs rhs_m =
  do tp_r_trm <- lambdaTupleTransM x tp_l ((typeTransTupleType <$>) . tp_r)
     rhs <- transTupleTerm <$> rhs_m
     return (ctorOpenTerm "Prelude.exists"
             [typeTransTupleType tp_l, tp_r_trm, transTupleTerm lhs, rhs])


-- | Eliminate a dependent pair of the type returned by 'sigmaTypeTransM'
sigmaElimTransM :: (IsTermTrans trL, IsTermTrans trR) =>
                   String -> TypeTrans trL ->
                   (trL -> TransM info ctx (TypeTrans trR)) ->
                   TransM info ctx (TypeTrans trRet) ->
                   (trL -> trR -> TransM info ctx OpenTerm) ->
                   OpenTerm ->
                   TransM info ctx OpenTerm
sigmaElimTransM _ tp_l@(typeTransTypes -> []) tp_r _ f sigma =
  do let proj1 = typeTransF tp_l []
     proj2 <- flip typeTransF [sigma] <$> tp_r proj1
     f proj1 proj2
sigmaElimTransM x tp_l tp_r tp_ret_m f sigma =
  do tp_r_trm <- lambdaTupleTransM x tp_l (\tr ->
                                            typeTransTupleType <$> tp_r tr)
     sigma_tp <- sigmaTypeTransM x tp_l tp_r
     tp_ret <- lambdaTransM x (mkTypeTrans1 sigma_tp id)
       (const (typeTransTupleType <$> tp_ret_m))
     f_trm <-
       lambdaTupleTransM (x ++ "_left") tp_l $ \x_l ->
       tp_r x_l >>= \tp_r_app ->
       lambdaTupleTransM (x ++ "_right") tp_r_app (f x_l)
     return (applyOpenTermMulti (globalOpenTerm "Prelude.Sigma__rec")
             [ typeTransTupleType tp_l, tp_r_trm, tp_ret, f_trm, sigma ])


-- | The class for translating to SAW
class Translate info ctx a tr | ctx a -> tr where
  translate :: Mb ctx a -> TransM info ctx tr

-- | Translate to SAW and then convert to a single SAW term using
-- 'transTupleTerm'
translateToTuple :: (IsTermTrans tr, Translate info ctx a tr) =>
                    Mb ctx a -> TransM info ctx OpenTerm
translateToTuple a = transTupleTerm <$> translate a

-- | Translate to SAW and then convert to a single SAW term, raising an error if
-- the result has 0 or more than 1 terms
translate1 :: (IsTermTrans tr, Translate info ctx a tr) =>
              Mb ctx a -> TransM info ctx OpenTerm
translate1 a = translate a >>= \tr -> case transTerms tr of
  [t] -> return t
  ts -> error ("translate1: expected 1 term, found " ++ show (length ts))

-- | Translate a "closed" term, that is not in a binding
translateClosed :: (TransInfo info, Translate info ctx a tr) =>
                   a -> TransM info ctx tr
translateClosed a = nuMultiTransM (const a) >>= translate

{-
-- | Call 'exprTransToTerm' and map 'Nothing' to unit
exprTransToTermForce :: ExprTrans a -> OpenTerm
exprTransToTermForce = maybe unitOpenTerm id . exprTransToTerm

-- | Map a context of expression translations to a list of 'OpenTerm's, dropping
-- the "invisible" ones whose types are translated to 'Nothing'
exprCtxToTerms :: ExprTransCtx tps -> [OpenTerm]
exprCtxToTerms =
  catMaybes . mapRListToList . mapMapRList (Constant.Constant . exprTransToTerm)


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

-}


----------------------------------------------------------------------
-- * Translating Types
----------------------------------------------------------------------

-- | Translation info for translating types and pure expressions
data TypeTransInfo ctx = TypeTransInfo (ExprTransCtx ctx) PermEnv

instance TransInfo TypeTransInfo where
  infoCtx (TypeTransInfo ctx _) = ctx
  infoEnv (TypeTransInfo _ env) = env
  extTransInfo etrans (TypeTransInfo ctx env) =
    TypeTransInfo (ctx :>: etrans) env

-- | The translation monad specific to translating types and pure expressions
type TypeTransM = TransM TypeTransInfo

-- | Run a translation computation in an empty expression translation context
inEmptyCtxTransM :: TypeTransM RNil a -> TypeTransM ctx a
inEmptyCtxTransM =
  withInfoM (\(TypeTransInfo _ env) -> TypeTransInfo MNil env)

instance TransInfo info => Translate info ctx (NatRepr n) OpenTerm where
  translate mb_n = return $ natOpenTerm $ mbLift $ fmap intValue mb_n

{-
-- | The typeclass for the type-level translation
class TypeTranslate a ctx res | a ctx -> res where
  tptranslate :: Mb ctx a -> TypeTransM ctx res

-- | Helper for writing the 'TypeTranslate' instance for 'TypeRepr'
returnType :: OpenTerm -> TypeTransM ctx (Either (ExprTrans a)
                                          (OpenTerm,
                                           OpenTerm -> ExprTrans a))
returnType tp = return $ Right (tp, ETrans_Term)
-}

-- | Helper for writing the 'Translate' instance for 'TypeRepr'
returnType1 :: OpenTerm -> TransM info ctx (TypeTrans (ExprTrans a))
returnType1 tp = return $ mkTypeTrans1 tp ETrans_Term


-- FIXME: explain this translation
instance TransInfo info =>
         Translate info ctx (TypeRepr a) (TypeTrans (ExprTrans a)) where
  translate [nuP| AnyRepr |] =
    return $ error "TypeTranslate: Any"
  translate [nuP| UnitRepr |] =
    returnType1 unitTypeOpenTerm
  translate [nuP| BoolRepr |] =
    returnType1 $ globalOpenTerm "Prelude.Bool"
  translate [nuP| NatRepr |] =
    returnType1 $ dataTypeOpenTerm "Prelude.Nat" []
  translate [nuP| IntegerRepr |] =
    return $ error "TypeTranslate: IntegerRepr"
  translate [nuP| RealValRepr |] =
    return $ error "TypeTranslate: RealValRepr"
  translate [nuP| ComplexRealRepr |] =
    return $ error "TypeTranslate: ComplexRealRepr"
  translate [nuP| BVRepr w |] =
    returnType1 =<<
    (applyOpenTerm (globalOpenTerm "Prelude.bitvector") <$> translate w)

  -- Our special-purpose intrinsic types, whose translations do not have
  -- computational content
  translate [nuP| LLVMPointerRepr _ |] =
    return $ mkTypeTrans0 ETrans_LLVM
  translate [nuP| LLVMFrameRepr _ |] =
    return $ mkTypeTrans0 ETrans_LLVMFrame
  translate [nuP| LifetimeRepr |] =
    return $ mkTypeTrans0 ETrans_Lifetime
  translate [nuP| PermListRepr |] =
    return $ mkTypeTrans0 ETrans_PermList
  translate [nuP| IntrinsicRepr _ _ |] =
    return $ error "TypeTranslate: IntrinsicRepr"

  translate [nuP| RecursiveRepr _ _ |] =
    return $ error "TypeTranslate: RecursiveRepr"
  translate [nuP| FloatRepr _ |] =
    returnType1 $ dataTypeOpenTerm "Prelude.Float" []
  translate [nuP| IEEEFloatRepr _ |] =
    return $ error "TypeTranslate: IEEEFloatRepr"
  translate [nuP| CharRepr |] =
    return $ error "TypeTranslate: CharRepr"
  translate [nuP| StringRepr |] =
    returnType1 $ globalOpenTerm "Prelude.String"
  translate [nuP| FunctionHandleRepr _ _ |] =
    -- NOTE: function permissions translate to the SAW function, but the
    -- function handle itself has no SAW translation
    return $ mkTypeTrans0 ETrans_Fun
  translate [nuP| MaybeRepr tp |] =
    return $ error "TypeTranslate: MaybeRepr"
  translate [nuP| VectorRepr _ |] =
    return $ error "TypeTranslate: VectorRepr (can't map to Vec without size)"
  translate [nuP| StructRepr _ |] =
    return $ error "TypeTranslate: StructRepr"
  translate [nuP| VariantRepr _ |] =
    return $ error "TypeTranslate: VariantRepr"
  translate [nuP| ReferenceRepr _ |] =
    return $ error "TypeTranslate: ReferenceRepr"
  translate [nuP| WordMapRepr _ _ |] =
    return $ error "TypeTranslate: WordMapRepr"
  translate [nuP| StringMapRepr _ |] =
    return $ error "TypeTranslate: StringMapRepr"
  translate [nuP| SymbolicArrayRepr _ _ |] =
    return $ error "TypeTranslate: SymbolicArrayRepr"
  translate [nuP| SymbolicStructRepr _ |] =
    return $ error "TypeTranslate: SymbolicStructRepr"


instance TransInfo info =>
         Translate info ctx (CruCtx as) (TypeTrans (ExprTransCtx as)) where
  translate [nuP| CruCtxNil |] = return $ mkTypeTrans0 MNil
  translate [nuP| CruCtxCons ctx tp |] =
    liftA2 (:>:) <$> translate ctx <*> translate tp

-- | Translate all types in a Crucible context and lambda-abstract over them
lambdaExprCtx :: TransInfo info => CruCtx ctx -> TransM info ctx OpenTerm ->
                 TransM info RNil OpenTerm
lambdaExprCtx ctx m =
  translateClosed ctx >>= \tptrans ->
  lambdaTransM "e" tptrans (\ectx -> inCtxTransM ectx m)

-- | Translate all types in a Crucible context and pi-abstract over them
piExprCtx :: TransInfo info => CruCtx ctx2 ->
             TransM info (ctx :++: ctx2) OpenTerm ->
             TransM info ctx OpenTerm
piExprCtx ctx m =
  translateClosed ctx >>= \tptrans ->
  piTransM "e" tptrans (\ectx -> inExtMultiTransM ectx m)


----------------------------------------------------------------------
-- * Translating Pure Expressions
----------------------------------------------------------------------

-- FIXME HERE: move these OpenTerm operations to OpenTerm.hs
trueOpenTerm :: OpenTerm
trueOpenTerm = globalOpenTerm "Prelude.True"

bvNatOpenTerm :: Integer -> Integer -> OpenTerm
bvNatOpenTerm w n =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvNat")
  [natOpenTerm w, natOpenTerm (n `mod` 2 ^ w)]

bvAddOpenTerm :: Integer -> OpenTerm -> OpenTerm -> OpenTerm
bvAddOpenTerm n x y =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvAdd")
  [natOpenTerm n, x, y]

bvMulOpenTerm :: Integer -> OpenTerm -> OpenTerm -> OpenTerm
bvMulOpenTerm n x y =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvMul")
  [natOpenTerm n, x, y]

-- | Translate a variable to a 'Member' proof, raising an error if the variable
-- is unbound
translateVar :: Mb ctx (ExprVar a) -> Member ctx a
translateVar mb_x | Left memb <- mbNameBoundP mb_x = memb
translateVar _ = error "translateVar: unbound variable!"

-- | A version of 'natVal' that takes a phantom argument with 2 applied type
-- functors instead of 1
natVal2 :: KnownNat w => f (g w) -> Integer
natVal2 (_ :: f (g w)) = natVal (Proxy :: Proxy w)

-- | A version of 'natVal' that takes a phantom argument with 3 applied type
-- functors instead of 1
natVal3 :: KnownNat w => f (g (h w)) -> Integer
natVal3 (_ :: f (g (h w))) = natVal (Proxy :: Proxy w)

-- | A version of 'natVal' that takes a phantom argument with 4 applied type
-- functors instead of 1
natVal4 :: KnownNat w => f (g (h (i w))) -> Integer
natVal4 (_ :: f (g (h (i w)))) = natVal (Proxy :: Proxy w)

-- | Get the 'TypeRepr' of an expression
mbExprType :: KnownRepr TypeRepr a => Mb ctx (PermExpr a) -> TypeRepr a
mbExprType _ = knownRepr

-- | Get the 'TypeRepr' bound by a binding
mbBindingType :: KnownRepr TypeRepr tp => Mb ctx (Binding tp a) -> TypeRepr tp
mbBindingType _ = knownRepr


instance TransInfo info =>
         Translate info ctx (ExprVar a) (ExprTrans a) where
  translate mb_x = mapRListLookup (translateVar mb_x) <$> infoCtx <$> ask

instance TransInfo info =>
         Translate info ctx (PermExpr a) (ExprTrans a) where
  translate [nuP| PExpr_Var x |] = translate x
  translate [nuP| PExpr_Unit |] = return $ ETrans_Term unitOpenTerm
  translate [nuP| PExpr_Nat i |] =
    return $ ETrans_Term $ natOpenTerm $ mbLift i
  translate [nuP| PExpr_BV bvfactors@[] off |] =
    let w = natVal3 bvfactors in
    return $ ETrans_Term $ bvNatOpenTerm w $ mbLift off
  translate [nuP| PExpr_BV bvfactors 0 |] =
    let w = natVal3 bvfactors in
    ETrans_Term <$> foldr1 (bvAddOpenTerm w) <$>
    mapM translate (mbList bvfactors)
  translate [nuP| PExpr_BV bvfactors off |] =
    do let w = natVal3 bvfactors
       bv_transs <- mapM translate $ mbList bvfactors
       return $ ETrans_Term $
         foldr (bvAddOpenTerm w) (bvNatOpenTerm w $ mbLift off) bv_transs
  translate [nuP| PExpr_Struct _args |] =
    error "FIXME HERE: translate struct expressions!"
  translate [nuP| PExpr_Always |] =
    return ETrans_Lifetime
  translate [nuP| PExpr_LLVMWord _ |] = return ETrans_LLVM
  translate [nuP| PExpr_LLVMOffset _ _ |] = return ETrans_LLVM
  translate [nuP| PExpr_Fun _ |] = return ETrans_Fun
  translate [nuP| PExpr_PermListNil |] = return ETrans_PermList
  translate [nuP| PExpr_PermListCons _ _ _ |] = return ETrans_PermList

instance TransInfo info =>
         Translate info ctx (PermExprs as) (ExprTransCtx as) where
  translate [nuP| PExprs_Nil |] = return MNil
  translate [nuP| PExprs_Cons es e |] =
    (:>:) <$> translate es <*> translate e

instance TransInfo info => Translate info ctx (BVFactor w) OpenTerm where
  translate [nuP| BVFactor 1 x |] = translate1 (fmap PExpr_Var x)
  translate [nuP| BVFactor i x |] =
    let w = natVal4 x in
    bvMulOpenTerm w (bvNatOpenTerm w (mbLift i)) <$>
    translate1 (fmap PExpr_Var x)


----------------------------------------------------------------------
-- * Translating Permissions to Types
----------------------------------------------------------------------

-- | The result of translating a "proof element" of a permission of type
-- @'ValuePerm' a@. The idea here is that, for a permission implication or typed
-- statement that consumes or emits permission @p@, the translation consumes or
-- emits an element of the SAW type @'translate' p@.
--
-- Another way to look at a @'PermTrans'@ for permission @p@ is that it is a
-- partially static representation (in the sense of the partial evaluation
-- literature) of a SAW expression of type @'translate' p@. Note that we do
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

  -- | LLVM array permisions are translated to an 'LLVMArrayPermTrans'
  APTrans_LLVMArray :: (1 <= w, KnownNat w) =>
                       LLVMArrayPermTrans ctx w ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM free permissions have no computational content
  APTrans_LLVMFree :: (1 <= w, KnownNat w) =>
                      Mb ctx (PermExpr (BVType w)) ->
                      AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM function pointer permissions have the same computational content as
  -- a function permission
  APTrans_LLVMFunPtr :: (1 <= w, KnownNat w) =>
                        Mb ctx (FunPerm ghosts args ret) -> OpenTerm ->
                        AtomicPermTrans ctx (LLVMPointerType w)

  -- | IsLLVMPtr permissions have no computational content
  APTrans_IsLLVMPtr :: (1 <= w, KnownNat w) =>
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
  APTrans_BVProp :: (1 <= w, KnownNat w) => BVPropTrans ctx w ->
                    AtomicPermTrans ctx (LLVMPointerType w)


-- | The translation of a proof of a 'BVProp'
data BVPropTrans ctx w = BVPropTrans (Mb ctx (BVProp w)) OpenTerm

-- | Build the translation of a 'BVProp' permission from a proof of it
bvPropPerm :: (1 <= w, KnownNat w) => BVPropTrans ctx w ->
              PermTrans ctx (LLVMPointerType w)
bvPropPerm prop = PTrans_Conj [APTrans_BVProp prop]


-- | The translation of an LLVM array permission is a SAW term of @BVVec@ type,
-- along with a type translation for its fields and proof terms stating that all
-- of the borrows are in the array. Note that the type translation for the
-- fields is always a 'tupleTypeTrans', i.e., has at most one SAW type.
data LLVMArrayPermTrans ctx w = LLVMArrayPermTrans {
  llvmArrayTransPerm :: Mb ctx (LLVMArrayPerm w),
  llvmArrayTransLen :: OpenTerm,
  llvmArrayTransFields :: TypeTrans [AtomicPermTrans ctx (LLVMPointerType w)],
  llvmArrayTransBorrows :: [LLVMArrayBorrowTrans ctx w],
  llvmArrayTransTerm :: OpenTerm
  }

-- | The translation of an LLVM array index is the translation of the cell
-- number plus the field number (which is statically known)
data LLVMArrayIndexTrans ctx w =
  LLVMArrayIndexTrans (Mb ctx (PermExpr (BVType w))) OpenTerm Int

-- | The translation of an 'LLVMArrayBorrow' is an element / proof of the
-- translation of the the 'BVProp' returned by 'llvmArrayBorrowInArrayBase'
data LLVMArrayBorrowTrans ctx w =
  LLVMArrayBorrowTrans
  { llvmArrayBorrowTransBorrow :: Mb ctx (LLVMArrayBorrow w),
    llvmArrayBorrowTransProp :: (BVPropTrans ctx w) }

-- | The translation of the vacuously true permission
pattern PTrans_True :: PermTrans ctx a
pattern PTrans_True = PTrans_Conj []

-- | Build a type translation for a disjunctive, existential, or recursive
-- permission that uses the 'PTrans_Term' constructor
mkPermTypeTrans1 :: Mb ctx (ValuePerm a) -> OpenTerm ->
                    TypeTrans (PermTrans ctx a)
mkPermTypeTrans1 mb_p tp = mkTypeTrans1 tp (PTrans_Term mb_p)

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

-- | Extract out a list of proofs of 'BVProp's from a proof of a conjunction
unPTransBVProps :: String -> PermTrans ctx (LLVMPointerType w) ->
                   [BVPropTrans ctx w]
unPTransBVProps _ ptrans
  | PTrans_Conj ps <- ptrans
  , Just transs <- mapM (\ap -> case ap of
                            APTrans_BVProp p -> Just p
                            _ -> Nothing) ps
  = transs
unPTransBVProps str _ = error (str ++ ": not a list of BVProp permissions")

-- | Extract the body of a conjunction of a single field permission
unPTransLLVMField :: String -> PermTrans ctx (LLVMPointerType w) ->
                     (Mb ctx (LLVMFieldPerm w),
                      PermTrans ctx (LLVMPointerType w))
unPTransLLVMField _ (PTrans_Conj [APTrans_LLVMField e ptrans]) = (e, ptrans)
unPTransLLVMField str _ = error (str ++ ": not an LLVM field permission")

-- | Extract the body of a conjunction of a single array permission
unPTransLLVMArray :: String -> PermTrans ctx (LLVMPointerType w) ->
                     LLVMArrayPermTrans ctx w
unPTransLLVMArray _ (PTrans_Conj [APTrans_LLVMArray aptrans]) = aptrans
unPTransLLVMArray str _ = error (str ++ ": not an LLVM array permission")

-- | Add a borrow translation to the translation of an array permission

-- | A context mapping bound names to their perm translations
type PermTransCtx ctx ps = MapRList (PermTrans ctx) ps

-- | Build a permission translation context with just @true@ permissions
truePermTransCtx :: CruCtx ps -> PermTransCtx ctx ps
truePermTransCtx CruCtxNil = MNil
truePermTransCtx (CruCtxCons ctx _) = truePermTransCtx ctx :>: PTrans_True

instance IsTermTrans (PermTrans ctx a) where
  transTerms (PTrans_Eq _) = []
  transTerms (PTrans_Conj aps) = transTerms aps
  transTerms (PTrans_Term _ t) = [t]

instance IsTermTrans (PermTransCtx ctx ps) where
  transTerms MNil = []
  transTerms (ctx :>: ptrans) = transTerms ctx ++ transTerms ptrans

instance IsTermTrans (AtomicPermTrans ctx a) where
  transTerms (APTrans_LLVMField _ ptrans) = transTerms ptrans
  transTerms (APTrans_LLVMArray arr_trans) = transTerms arr_trans
  transTerms (APTrans_LLVMFree _) = []
  transTerms (APTrans_LLVMFunPtr _ t) = [t]
  transTerms APTrans_IsLLVMPtr = []
  transTerms (APTrans_LLVMFrame _) = []
  transTerms (APTrans_LifetimePerm _) = []
  transTerms (APTrans_Fun _ t) = [t]
  transTerms (APTrans_BVProp prop) = transTerms prop

instance IsTermTrans (BVPropTrans ctx w) where
  transTerms (BVPropTrans _ t) = [t]

instance IsTermTrans (LLVMArrayPermTrans ctx a) where
  transTerms arr_trans =
    llvmArrayTransTerm arr_trans : transTerms (llvmArrayTransBorrows arr_trans)

instance IsTermTrans (LLVMArrayBorrowTrans ctx w) where
  transTerms (LLVMArrayBorrowTrans _ prop_trans) = transTerms prop_trans

-- | Map a context of perm translations to a list of 'OpenTerm's, dropping the
-- "invisible" ones whose permissions are translated to 'Nothing'
permCtxToTerms :: PermTransCtx ctx tps -> [OpenTerm]
permCtxToTerms =
  concat . mapRListToList . mapMapRList (Constant.Constant . transTerms)

-- | Extract out the permission of a permission translation result
permTransPerm :: MapRList Proxy ctx -> PermTrans ctx a -> Mb ctx (ValuePerm a)
permTransPerm _ (PTrans_Eq e) = fmap ValPerm_Eq e
permTransPerm prxs (PTrans_Conj ts) =
  fmap ValPerm_Conj $ foldr (mbMap2 (:)) (nuMulti prxs $ const []) $
  map (atomicPermTransPerm prxs) ts
permTransPerm _ (PTrans_Term p _) = p

-- | Extract out the atomic permission of an atomic permission translation result
atomicPermTransPerm :: MapRList Proxy ctx -> AtomicPermTrans ctx a ->
                       Mb ctx (AtomicPerm a)
atomicPermTransPerm prxs (APTrans_LLVMField fld _) = fmap Perm_LLVMField fld
atomicPermTransPerm prxs (APTrans_LLVMArray arr_trans) =
  fmap Perm_LLVMArray $ llvmArrayTransPerm arr_trans
atomicPermTransPerm prxs (APTrans_LLVMFree e) = fmap Perm_LLVMFree e
atomicPermTransPerm prxs (APTrans_LLVMFunPtr fperm _) =
  fmap Perm_LLVMFunPtr fperm
atomicPermTransPerm prxs APTrans_IsLLVMPtr = nuMulti prxs $ const Perm_IsLLVMPtr
atomicPermTransPerm prxs (APTrans_LLVMFrame fp) = fmap Perm_LLVMFrame fp
atomicPermTransPerm prxs (APTrans_LifetimePerm p) = p
atomicPermTransPerm prxs (APTrans_Fun fp _) = fmap Perm_Fun fp
atomicPermTransPerm prxs (APTrans_BVProp (BVPropTrans prop _)) =
  fmap Perm_BVProp prop

-- | Extract out the LLVM borrow from its translation
borrowTransMbBorrow :: LLVMArrayBorrowTrans ctx w -> Mb ctx (LLVMArrayBorrow w)
borrowTransMbBorrow (LLVMArrayBorrowTrans mb_b _) = mb_b

-- | Test that a permission equals that of a permission translation
permTransPermEq :: PermTrans ctx a -> Mb ctx (ValuePerm a) -> Bool
permTransPermEq ptrans mb_p =
  permTransPerm (mbToProxy mb_p) ptrans == mb_p

-- FIXME HERE: move this to Hobbits
extMb :: Mb ctx a -> Mb (ctx :> tp) a
extMb = mbCombine . fmap (nu . const)

-- | Generic function to extend the context of the translation of a permission
class ExtPermTrans f where
  extPermTrans :: f ctx a -> f (ctx :> tp) a

instance ExtPermTrans PermTrans where
  extPermTrans (PTrans_Eq e) = PTrans_Eq $ extMb e
  extPermTrans (PTrans_Conj aps) = PTrans_Conj (map extPermTrans aps)
  extPermTrans (PTrans_Term p t) = PTrans_Term (extMb p) t

instance ExtPermTrans AtomicPermTrans where
  extPermTrans (APTrans_LLVMField fld ptrans) =
    APTrans_LLVMField (extMb fld) (extPermTrans ptrans)
  extPermTrans (APTrans_LLVMArray arr_trans) =
    APTrans_LLVMArray $ extPermTrans arr_trans
  extPermTrans (APTrans_LLVMFree e) = APTrans_LLVMFree $ extMb e
  extPermTrans (APTrans_LLVMFunPtr fperm t) = APTrans_LLVMFunPtr (extMb fperm) t
  extPermTrans APTrans_IsLLVMPtr = APTrans_IsLLVMPtr
  extPermTrans (APTrans_LLVMFrame fp) = APTrans_LLVMFrame $ extMb fp
  extPermTrans (APTrans_LifetimePerm p) = APTrans_LifetimePerm $ extMb p
  extPermTrans (APTrans_Fun fp t) = APTrans_Fun (extMb fp) t
  extPermTrans (APTrans_BVProp prop_trans) =
    APTrans_BVProp $ extPermTrans prop_trans

instance ExtPermTrans LLVMArrayPermTrans where
  extPermTrans (LLVMArrayPermTrans ap len flds bs t) =
    LLVMArrayPermTrans (extMb ap) len (fmap (map extPermTrans) flds)
    (map extPermTrans bs) t

instance ExtPermTrans LLVMArrayBorrowTrans where
  extPermTrans (LLVMArrayBorrowTrans mb_b prop_trans) =
    LLVMArrayBorrowTrans (extMb mb_b) (extPermTrans prop_trans)

instance ExtPermTrans BVPropTrans where
  extPermTrans (BVPropTrans prop t) = BVPropTrans (extMb prop) t

-- | Extend the context of a permission translation context
extPermTransCtx :: PermTransCtx ctx ps -> PermTransCtx (ctx :> tp) ps
extPermTransCtx = mapMapRList extPermTrans

-- | Add another permission translation to a permission translation context
consPermTransCtx :: PermTransCtx ctx ps -> PermTrans ctx a ->
                    PermTransCtx ctx (ps :> a)
consPermTransCtx = (:>:)

-- | Apply 'offsetLLVMAtomicPerm' to the permissions associated with an atomic
-- permission translation, returning 'Nothing' if the offset does not exist
offsetLLVMAtomicPermTrans :: Mb ctx (PermExpr (BVType w)) ->
                             AtomicPermTrans ctx (LLVMPointerType w) ->
                             Maybe (AtomicPermTrans ctx (LLVMPointerType w))
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMField fld ptrans) =
  Just $ APTrans_LLVMField (mbMap2 offsetLLVMFieldPerm mb_off fld) ptrans
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMArray
                                  (LLVMArrayPermTrans ap len flds bs t)) =
  Just $ APTrans_LLVMArray $
  LLVMArrayPermTrans (mbMap2 offsetLLVMArrayPerm mb_off ap) len flds bs t
offsetLLVMAtomicPermTrans _ (APTrans_LLVMFree _) = Nothing
offsetLLVMAtomicPermTrans _ (APTrans_LLVMFunPtr _ _) = Nothing
offsetLLVMAtomicPermTrans _ p@APTrans_IsLLVMPtr = Just p

-- | Get the SAW type of the cells (= lists of fields) of the translation of an
-- LLVM array permission
llvmArrayTransCellType :: LLVMArrayPermTrans ctx w -> OpenTerm
llvmArrayTransCellType = typeTransType1 . llvmArrayTransFields

-- | Add a borrow to an LLVM array permission translation
llvmArrayTransAddBorrow :: LLVMArrayBorrowTrans ctx w ->
                           LLVMArrayPermTrans ctx w ->
                           LLVMArrayPermTrans ctx w
llvmArrayTransAddBorrow b arr_trans =
  arr_trans { llvmArrayTransPerm =
                mbMap2 llvmArrayAddBorrow (llvmArrayBorrowTransBorrow b)
                (llvmArrayTransPerm arr_trans)
            , llvmArrayTransBorrows = b : llvmArrayTransBorrows arr_trans }

-- | Find the index in the list of borrows of a specific borrow
llvmArrayTransFindBorrowIx :: Mb ctx (LLVMArrayBorrow w) ->
                             LLVMArrayPermTrans ctx w -> Int
llvmArrayTransFindBorrowIx b arr_trans =
  mbLift $ mbMap2 llvmArrayFindBorrow b (llvmArrayTransPerm arr_trans)

-- | Find the index in the list of borrows of a specific borrow
llvmArrayTransFindBorrow :: Mb ctx (LLVMArrayBorrow w) ->
                            LLVMArrayPermTrans ctx w ->
                            LLVMArrayBorrowTrans ctx w
llvmArrayTransFindBorrow b arr_trans =
  llvmArrayTransBorrows arr_trans !! llvmArrayTransFindBorrowIx b arr_trans

-- | Remove a borrow from an LLVM array permission translation
llvmArrayTransRemBorrow :: LLVMArrayBorrowTrans ctx w ->
                           LLVMArrayPermTrans ctx w ->
                           LLVMArrayPermTrans ctx w
llvmArrayTransRemBorrow b_trans arr_trans =
  let b = llvmArrayBorrowTransBorrow b_trans in
  arr_trans { llvmArrayTransPerm =
                mbMap2 llvmArrayRemBorrow b (llvmArrayTransPerm arr_trans)
            , llvmArrayTransBorrows =
                deleteNth (llvmArrayTransFindBorrowIx b arr_trans)
                (llvmArrayTransBorrows arr_trans) }

-- | Read an array cell (= list of fields) of the translation of an LLVM array
-- permission at a given index, given proofs of the propositions that the index
-- is in the array
getLLVMArrayTransCell :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                         LLVMArrayIndexTrans ctx w -> BVPropTrans ctx w ->
                         [AtomicPermTrans ctx (LLVMPointerType w)]
getLLVMArrayTransCell arr_trans (LLVMArrayIndexTrans _ i_trans _)
  (BVPropTrans _ in_rng_term) =
  let w = natVal arr_trans in
  mapMaybe (offsetLLVMAtomicPermTrans $
            fmap llvmArrayOffset $ llvmArrayTransPerm arr_trans) $
  typeTransF (llvmArrayTransFields arr_trans)
  [applyOpenTermMulti (globalOpenTerm "Prelude.atBVVec")
   [natOpenTerm w, llvmArrayTransLen arr_trans,
    llvmArrayTransCellType arr_trans, llvmArrayTransTerm arr_trans,
    i_trans, in_rng_term]]

-- | Write an array cell (= list of fields) of the translation of an LLVM array
-- permission at a given index, given proofs of the propositions that the index
-- is in the array
setLLVMArrayTransCell :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                         LLVMArrayIndexTrans ctx w -> BVPropTrans ctx w ->
                         [AtomicPermTrans ctx (LLVMPointerType w)] ->
                         LLVMArrayPermTrans ctx w
setLLVMArrayTransCell arr_trans (LLVMArrayIndexTrans _ i_trans _)
  (BVPropTrans _ in_rng_term) cell =
  let w = natVal arr_trans in
  arr_trans {
    llvmArrayTransTerm =
        applyOpenTermMulti (globalOpenTerm "Prelude.updBVVec")
        [natOpenTerm w, llvmArrayTransLen arr_trans,
         llvmArrayTransCellType arr_trans, llvmArrayTransTerm arr_trans,
         i_trans, in_rng_term, transTupleTerm cell] }

-- | Read a field (= element of a cell) of the translation of an LLVM array
-- permission at a given index, given proopfs of the propositions that the index
-- is in the array
getLLVMArrayTransField :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          LLVMArrayIndexTrans ctx w -> BVPropTrans ctx w ->
                          AtomicPermTrans ctx (LLVMPointerType w)
getLLVMArrayTransField arr_trans ix_trans@(LLVMArrayIndexTrans
                                           _ _ j) prop_trans =
  getLLVMArrayTransCell arr_trans ix_trans prop_trans !! j

-- | Write a field (= element of a cell) of the translation of an LLVM array
-- permission at a given index, given a proof of the proposition that the index
-- is in the array
setLLVMArrayTransField :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          LLVMArrayIndexTrans ctx w -> BVPropTrans ctx w ->
                          AtomicPermTrans ctx (LLVMPointerType w) ->
                          LLVMArrayPermTrans ctx w
setLLVMArrayTransField arr_trans ix_trans@(LLVMArrayIndexTrans
                                           _ _ j) prop_trans fld' =
  let flds = getLLVMArrayTransCell arr_trans ix_trans prop_trans in
  setLLVMArrayTransCell arr_trans ix_trans prop_trans
  (replaceNth j fld' flds)


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
atomicPermTransInLifetime l (APTrans_LLVMArray
                             (LLVMArrayPermTrans ap len flds bs t)) =
  APTrans_LLVMArray $
  LLVMArrayPermTrans (mbMap2 inLifetime l ap) len
  (fmap (map (atomicPermTransInLifetime l)) flds)
  bs
  t
atomicPermTransInLifetime _ p@(APTrans_LLVMFree _) = p
atomicPermTransInLifetime _ p@(APTrans_LLVMFunPtr _ _) = p
atomicPermTransInLifetime _ p@APTrans_IsLLVMPtr = p
atomicPermTransInLifetime _ p@(APTrans_LLVMFrame _) = p
atomicPermTransInLifetime l (APTrans_LifetimePerm p) =
  APTrans_LifetimePerm $ mbMap2 inLifetime l p
atomicPermTransInLifetime _ p@(APTrans_Fun _ _) = p
atomicPermTransInLifetime _ p@(APTrans_BVProp _) = p

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
                            (LLVMArrayPermTrans _ len flds bs t))
  [nuP| Perm_LLVMArray ap |] =
  APTrans_LLVMArray $ LLVMArrayPermTrans ap len
  (fmap (\aps ->
          zipWith atomicPermTransEndLifetime aps
          (mbList $ fmap (map Perm_LLVMField . llvmArrayFields) ap)) flds)
  bs t
atomicPermTransEndLifetime p@(APTrans_LLVMFree _) _ = p
atomicPermTransEndLifetime p@(APTrans_LLVMFunPtr _ _) _ = p
atomicPermTransEndLifetime p@APTrans_IsLLVMPtr _ = p
atomicPermTransEndLifetime p@(APTrans_LLVMFrame _) _ = p
atomicPermTransEndLifetime p@(APTrans_LifetimePerm _) _ = p
atomicPermTransEndLifetime p@(APTrans_Fun _ _) _ = p
atomicPermTransEndLifetime p@(APTrans_BVProp _) _ = p
atomicPermTransEndLifetime _ _ =
  error "atomicPermTransEndLifetime: permissions don't agree!"


-- | Apply 'permTransEndLifetime' to a 'PermTransCtx'
permCtxEndLifetime :: PermTransCtx ctx ps -> Mb ctx (DistPerms ps) ->
                      PermTransCtx ctx ps
permCtxEndLifetime MNil _ = MNil
permCtxEndLifetime (ptranss :>: ptrans) [nuP| DistPermsCons perms _ p |] =
  permCtxEndLifetime ptranss perms :>: permTransEndLifetime ptrans p


instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (BVProp w) (TypeTrans (BVPropTrans ctx w)) where
  translate prop@[nuP| BVProp_Eq e1 e2 |] =
    do let w = natVal4 e1
       t1 <- translate1 e1
       t2 <- translate1 e2
       return $ flip mkTypeTrans1 (BVPropTrans prop) $
         (dataTypeOpenTerm "Prelude.EqP"
          [applyOpenTerm (globalOpenTerm "Prelude.bitvector") (natOpenTerm w),
           t1, t2])

  translate prop@[nuP| BVProp_Neq _ _ |] =
    -- NOTE: we don't need a proof object for not equal proofs, because we don't
    -- actually use them for anything, but it is easier to just have all BVProps
    -- be represented as something, so we use the unit type
    return $ mkTypeTrans1 unitTypeOpenTerm (BVPropTrans prop)

  -- The proposition e in [off,off+len) becomes (e-off) < len, which in SAW is
  -- represented as bvslt (e-off) len = True
  translate prop@[nuP| BVProp_InRange e (BVRange off len) |] =
    do let w = natVal4 e
       t_sub <- translate1 (mbMap2 bvSub e off)
       t_len <- translate1 len
       return $ flip mkTypeTrans1 (BVPropTrans prop)
         (dataTypeOpenTerm "Prelude.EqP"
          [globalOpenTerm "Prelude.Bool",
           applyOpenTermMulti (globalOpenTerm "Prelude.bvult")
           [natOpenTerm w, t_sub, t_len],
           trueOpenTerm])

  translate prop@[nuP| BVProp_NotInRange _ _ |] =
    -- NOTE: we don't need a proof object for not in range proofs, because we
    -- don't actually use them for anything, but it is easier to just have all
    -- BVProps be represented as something, so we use the unit type
    return $ mkTypeTrans1 unitTypeOpenTerm (BVPropTrans prop)

  -- The proposition [off1,off1+len1) subset [off2,off2+len2) becomes the
  -- proposition...?
  -- FIXME: must imply (bvToNat (off1 - off2) + bvToNat len1) <= bvToNat len2
  translate prop@[nuP| BVProp_RangeSubset (BVRange off1 len1)
                     (BVRange off2 len2) |] =
    error "FIXME HERE NOW: translate BVProp_RangeSubset"

  translate prop@[nuP| BVProp_RangesDisjoint _ _ |] =
    -- NOTE: we don't need a proof object for negative proofs, because we don't
    -- actually use them for anything, but it is easier to just have all BVProps
    -- be represented as something, so we use the unit type
    return $ mkTypeTrans1 unitTypeOpenTerm (BVPropTrans prop)


instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (LLVMArrayIndex w) (LLVMArrayIndexTrans ctx w) where
  translate [nuP| LLVMArrayIndex mb_i mb_j |] =
    LLVMArrayIndexTrans mb_i <$> translate1 mb_i <*> return (mbLift mb_j)

-- [| p :: ValuePerm |] = type of the impl translation of reg with perms p
instance TransInfo info =>
         Translate info ctx (ValuePerm a) (TypeTrans (PermTrans ctx a)) where
  translate [nuP| ValPerm_Eq e |] = return $ mkTypeTrans0 $ PTrans_Eq e
  translate p@[nuP| ValPerm_Or p1 p2 |] =
    do tp1 <- translate p1
       tp2 <- translate p2
       return $ mkPermTypeTrans1 p (eitherTypeTrans tp1 tp2)
  translate p@[nuP| ValPerm_Exists p1 |] =
    do let tp = mbBindingType p1
       tp_trans <- translateClosed tp
       mkPermTypeTrans1 p <$>
         sigmaTypeTransM "x_ex" tp_trans (\x -> inExtTransM x $
                                                translate $ mbCombine p1)
  translate p@[nuP| ValPerm_Rec rpn _ |] =
    do env <- infoEnv <$> ask
       let rp = case lookupRecPerm env (mbLift rpn) of
             Just rp -> rp
             Nothing -> error "Unknown recursive permission name!"
       return $ mkPermTypeTrans1 p (dataTypeOpenTerm (recPermDataType rp) [])
  translate [nuP| ValPerm_Conj ps |] =
    fmap PTrans_Conj <$> listTypeTrans <$> mapM translate (mbList ps)


instance TransInfo info =>
         Translate info ctx (AtomicPerm a) (TypeTrans
                                            (AtomicPermTrans ctx a)) where
  translate [nuP| Perm_LLVMField fld |] =
    fmap (APTrans_LLVMField fld) <$> translate (fmap llvmFieldContents fld)

  translate ([nuP| Perm_LLVMArray ap |]) =
    fmap APTrans_LLVMArray <$> translate ap

  translate [nuP| Perm_LLVMFree e |] =
    return $ mkTypeTrans0 $ APTrans_LLVMFree e
  translate [nuP| Perm_LLVMFunPtr fun_perm |] =
    translate fun_perm >>= \tp_term ->
    return $ mkTypeTrans1 tp_term (APTrans_LLVMFunPtr fun_perm)
  translate [nuP| Perm_IsLLVMPtr |] =
    return $ mkTypeTrans0 APTrans_IsLLVMPtr
  translate [nuP| Perm_LLVMFrame fp |] =
    return $ mkTypeTrans0 $ APTrans_LLVMFrame fp
  translate p@[nuP| Perm_LOwned _ |] =
    return $ mkTypeTrans0 $ APTrans_LifetimePerm p
  translate p@[nuP| Perm_LCurrent _ |] =
    return $ mkTypeTrans0 $ APTrans_LifetimePerm p
  translate ([nuP| Perm_Fun fun_perm |]) =
    translate fun_perm >>= \tp_term ->
    return $ mkTypeTrans1 tp_term (APTrans_Fun fun_perm)


instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (LLVMArrayPerm w) (TypeTrans
                                               (LLVMArrayPermTrans ctx w)) where
  translate ap@[nuP| LLVMArrayPerm _ len _ flds bs |] =
    do let w = natVal4 len
       flds_trans <-
         tupleTypeTrans <$> listTypeTrans <$>
         mapM (translate . fmap Perm_LLVMField) (mbList flds)
       let elem_tp = typeTransType1 flds_trans
       len_term <- translate1 len
       bs_trans <-
         listTypeTrans <$> mapM (translateLLVMArrayBorrow ap) (mbList bs)
       let arr_tp =
             applyOpenTermMulti (globalOpenTerm "Prelude.BVVec")
             [natOpenTerm w, len_term, elem_tp]
       return (mkTypeTrans1 arr_tp (flip $
                                    LLVMArrayPermTrans ap len_term flds_trans)
               <*> bs_trans)

-- | Translate an 'LLVMArrayBorrow' into an 'LLVMArrayBorrowTrans'. This
-- requires a special-purpose function, instead of the 'Translate' class,
-- because it requires the array permission.
translateLLVMArrayBorrow :: (1 <= w, KnownNat w, TransInfo info) =>
                            Mb ctx (LLVMArrayPerm w) ->
                            Mb ctx (LLVMArrayBorrow w) ->
                            TransM info ctx (TypeTrans
                                             (LLVMArrayBorrowTrans ctx w))
translateLLVMArrayBorrow mb_ap mb_b =
  do let mb_prop = mbMap2 llvmArrayBorrowInArrayBase mb_ap mb_b
     prop_trans <- translate mb_prop
     return (LLVMArrayBorrowTrans mb_b <$> prop_trans)

instance TransInfo info =>
         Translate info ctx (ValuePerms ps) (TypeTrans
                                             (PermTransCtx ctx ps)) where
  translate [nuP| ValPerms_Nil |] = return $ mkTypeTrans0 MNil
  translate [nuP| ValPerms_Cons ps p |] =
    liftA2 (:>:) <$> translate ps <*> translate p

-- Translate a DistPerms by translating its corresponding ValuePerms
instance TransInfo info =>
         Translate info ctx (DistPerms ps) (TypeTrans
                                            (PermTransCtx ctx ps)) where
  translate = translate . mbDistPermsToValuePerms

-- Translate a FunPerm to a pi-abstraction (FIXME: more documentation!)
instance TransInfo info =>
         Translate info ctx (FunPerm ghosts args ret) OpenTerm where
  translate ([nuP| FunPerm ghosts args ret perms_in perms_out |]) =
    piExprCtx (appendCruCtx
               (CruCtxCons (mbLift ghosts) LifetimeRepr)
               (mbLift args)) $
    piPermCtx (mbCombine $ fmap mbCombine perms_in) $ \_ ->
    translateRetType (mbLift ret) $
    mbCombine $ fmap (mbCombine . fmap mbValuePermsToDistPerms) perms_out


-- | Lambda-abstraction over a permission
lambdaPermTrans :: TransInfo info => String -> Mb ctx (ValuePerm a) ->
                   (PermTrans ctx a -> TransM info ctx OpenTerm) ->
                   TransM info ctx OpenTerm
lambdaPermTrans str p f =
  translate p >>= \tptrans -> lambdaTransM str tptrans f

-- | Lambda-abstraction over a sequence of permissions
lambdaPermCtx :: TransInfo info => Mb ctx (ValuePerms ps) ->
                 (PermTransCtx ctx ps -> TransM info ctx OpenTerm) ->
                 TransM info ctx OpenTerm
lambdaPermCtx ps f =
  translate ps >>= \tptrans -> lambdaTransM "p" tptrans f

-- | Pi-abstraction over a sequence of permissions
piPermCtx :: TransInfo info => Mb ctx (ValuePerms ps) ->
             (PermTransCtx ctx ps -> TransM info ctx OpenTerm) ->
             TransM info ctx OpenTerm
piPermCtx ps f =
  translate ps >>= \tptrans -> piTransM "p" tptrans f


-- | Build the return type for a function; FIXME: documentation
translateRetType :: TransInfo info => TypeRepr ret ->
                    Mb (ctx :> ret) (DistPerms ps) ->
                    TransM info ctx OpenTerm
translateRetType ret ret_perms =
  do tptrans <- translateClosed ret
     sigmaTypeTransM "ret" tptrans (\etrans ->
                                     inExtTransM etrans $ translate ret_perms)


{-
-- | Translate a permission to a single SAW type using 'transTupleTerm'
translatePerm :: Mb ctx (ValuePerm a) -> TypeTransM ctx OpenTerm
translatePerm mb_p =
  translate mb_p >>= \eith ->
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
  translate mb_p >>= \eith ->
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
  translate mb_p >>= \eith ->
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
  translate mb_p >>= \eith ->
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
  translate ps = tupleTypeOpenTerm <$> helper ps where
    helper :: Mb ctx (ValuePerms ps') -> TypeTransM ctx [OpenTerm]
    helper [nuP| ValPerms_Nil |] = return []
    helper [nuP| ValPerms_Cons ps p |] =
      do rest <- helper ps
         eith <- translate p
         case eith of
           Left _ -> return rest
           Right (tp_term, _) ->
             return (rest ++ [tp_term])

-- Translate a DistPerms into a nested pair type
instance TypeTranslate (DistPerms ps) ctx OpenTerm where
  translate = translate . mbDistPermsToValuePerms

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
       eith <- lift $ translate p
       case eith of
         Left ptrans -> return (rest :>: ptrans)
         Right (_, mk_ptrans) ->
           do trm <- get
              put (pairRightOpenTerm trm)
              return (rest :>: mk_ptrans (pairLeftOpenTerm trm))
-}


----------------------------------------------------------------------
-- * The Implication Translation Monad
----------------------------------------------------------------------

-- | A mapping from a block entrypoint to a corresponding SAW variable that is
-- bound to its translation if it has one: only those entrypoints marked as the
-- heads of strongly-connect components have translations as letrec-bound
-- variables
data TypedEntryTrans ext blocks ret args =
  TypedEntryTrans (TypedEntry ext blocks ret args) (Maybe OpenTerm)

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
            TypedEntryTrans (TypedEntry entryID' _ _ _ _ _ _) _
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

{- FIXME: unused
-- | Translate an entrypoint ID by looking up its SAW function, if it has one
translateTypedEntryID :: TypedEntryID blocks args ghosts ->
                         TypedBlockMapTrans ext blocks ret ->
                         Maybe OpenTerm
translateTypedEntryID entryID blkMap =
  case lookupEntryTrans entryID blkMap of
    TypedEntryTrans _ maybe_trm -> maybe_trm
-}

-- | Contextual info for an implication translation
data ImpTransInfo ext blocks ret ps ctx =
  ImpTransInfo
  {
    itiExprCtx :: ExprTransCtx ctx,
    itiPermCtx :: PermTransCtx ctx ctx,
    itiPermStack :: PermTransCtx ctx ps,
    itiPermStackVars :: MapRList (Member ctx) ps,
    itiPermEnv :: PermEnv,
    itiBlockMapTrans :: TypedBlockMapTrans ext blocks ret,
    itiCatchHandler :: OpenTerm,
    itiReturnType :: OpenTerm
  }

instance TransInfo (ImpTransInfo ext blocks ret ps) where
  infoCtx = itiExprCtx
  infoEnv = itiPermEnv
  extTransInfo etrans (ImpTransInfo {..}) =
    ImpTransInfo
    { itiExprCtx = itiExprCtx :>: etrans
    , itiPermCtx = consPermTransCtx (extPermTransCtx itiPermCtx) PTrans_True
    , itiPermStack = extPermTransCtx itiPermStack
    , itiPermStackVars = mapMapRList Member_Step itiPermStackVars
    , .. }

-- | Return the default catch handler of a given return type, which is just a
-- call to @errorM@ at that type
defaultCatchHandler :: OpenTerm -> OpenTerm
defaultCatchHandler = applyOpenTerm (globalOpenTerm "Prelude.errorM")

-- | The monad for translating permission implications
type ImpTransM ext blocks ret ps = TransM (ImpTransInfo ext blocks ret ps)

-- | Run an 'ImpTransM' computation in a 'TypeTransM' context (FIXME: better
-- documentation; e.g., the pctx starts on top of the stack)
impTransM :: PermTransCtx ctx ctx -> TypedBlockMapTrans ext blocks ret ->
             OpenTerm -> ImpTransM ext blocks ret ctx ctx a ->
             TypeTransM ctx a
impTransM pctx mapTrans retType =
  withInfoM $ \(TypeTransInfo ectx env) ->
  ImpTransInfo { itiExprCtx = ectx,
                 itiPermCtx = mapMapRList (const $ PTrans_True) pctx,
                 itiPermStack = pctx,
                 itiPermStackVars = members pctx,
                 itiPermEnv = env,
                 itiBlockMapTrans = mapTrans,
                 itiCatchHandler = defaultCatchHandler retType,
                 itiReturnType = retType }

-- | Embed a type translation into an impure translation
-- FIXME: should no longer need this...
tpTransM :: TypeTransM ctx a -> ImpTransM ext blocks ret ps ctx a
tpTransM =
  withInfoM (\info -> TypeTransInfo (itiExprCtx info) (itiPermEnv info))

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
  withInfoM $ \info ->
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

-- | The current non-monadic return type
returnTypeM :: ImpTransM ext blocks ret ps_out ctx OpenTerm
returnTypeM = itiReturnType <$> ask

-- | Build the monadic return type @CompM ret@, where @ret@ is the current
-- return type in 'itiReturnType'
compReturnTypeM :: ImpTransM ext blocks ret ps_out ctx OpenTerm
compReturnTypeM =
  applyOpenTerm (globalOpenTerm "Prelude.CompM") <$> returnTypeM

-- | Like 'compReturnTypeM' but build a 'TypeTrans'
compReturnTypeTransM :: ImpTransM ext blocks ret ps_out ctx (TypeTrans OpenTerm)
compReturnTypeTransM = 
  flip mkTypeTrans1 id <$> compReturnTypeM

-- | Run a computation with a new catch handler
withCatchHandlerM :: OpenTerm -> ImpTransM ext blocks ret ps_out ctx a ->
                     ImpTransM ext blocks ret ps_out ctx a
withCatchHandlerM h = local (\info -> info { itiCatchHandler = h })

{-
-- | Run 'lambdaExprTrans' in the 'ImpTransM' monad
lambdaExprTransI ::
  String -> TypeRepr tp ->
  ImpTransM ext blocks ret ps_out (ctx :> tp) OpenTerm ->
  ImpTransM ext blocks ret ps_out ctx OpenTerm
lambdaExprTransI x tp body =
  do eith <- tpTransM (nuMultiTransM (const tp) >>= translate)
     case eith of
       Left etrans -> inExtTransM etrans PTrans_True body
       Right (tp_term, mk_etrans) ->
         lambdaTransM x tp_term
         (\z -> inExtTransM (mk_etrans z) PTrans_True body)

-- | Run 'lambdaExprTransForce' in the 'ImpTransM' monad
lambdaExprTransForceI ::
  String -> TypeRepr tp ->
  ImpTransM ext blocks ret ps_out (ctx :> tp) OpenTerm ->
  ImpTransM ext blocks ret ps_out ctx OpenTerm
lambdaExprTransForceI x tp body =
  do eith <- tpTransM (nuMultiTransM (const tp) >>= translate)
     case eith of
       Left etrans ->
         lambdaTransM x unitTypeOpenTerm
         (\_ -> inExtTransM etrans PTrans_True body)
       Right (tp_term, mk_etrans) ->
         lambdaTransM x tp_term
         (\z -> inExtTransM (mk_etrans z) PTrans_True body)

-- | Run 'lambdaPermTrans' in the 'ImpTransM' monad
lambdaPermTransI ::
  String -> Mb ctx (ValuePerm a) ->
  (PermTrans ctx a -> ImpTransM ext blocks ret ps_out ctx OpenTerm) ->
  ImpTransM ext blocks ret ps_out ctx OpenTerm
lambdaPermTransI x p body_f =
  tpTransM (translate p) >>= \eith ->
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
  tpTransM (translate p) >>= \eith ->
  case eith of
    Left ptrans -> lambdaTransM x unitTypeOpenTerm (const $ body_f ptrans)
    Right (tp_term, mk_ptrans) ->
      lambdaTransM x tp_term (body_f . mk_ptrans)


-- | The typeclass for translating permission implications
class ImplTranslate a res ext blocks ret ps ctx | ctx a -> res where
  translate :: Mb ctx a -> ImpTransM ext blocks ret ps ctx res

-- | The typeclass for the implication translation of a functor at any
-- permission set inside any binding to an 'OpenTerm'
class NuMatchingAny1 f => ImplTranslateF f ext blocks ret where
  translateF :: Mb ctx (f ps) -> ImpTransM ext blocks ret ps ctx OpenTerm


-- Translate a TypeRepr to a SAW type in the implication translation monad,
-- using the unit type in place of 'Nothing'
instance ImplTranslate (TypeRepr a) OpenTerm ext blocks ret ps ctx where
  translate tp = tpTransM $ translateType tp

-- Translate a permission to a SAW type in the implication translation monad,
-- using the unit type in place of 'Nothing'
instance ImplTranslate (ValuePerm a) OpenTerm ext blocks ret ps ctx where
  translate p = tpTransM $ translatePerm p
-}

-- | The typeclass for the implication translation of a functor at any
-- permission set inside any binding to an 'OpenTerm'
class NuMatchingAny1 f => ImplTranslateF f ext blocks ret where
  translateF :: Mb ctx (f ps) -> ImpTransM ext blocks ret ps ctx OpenTerm


----------------------------------------------------------------------
-- * Translating Permission Implication Constructs
----------------------------------------------------------------------

-- | Translate a 'SimplImpl' to a function on translation computations
translateSimplImpl :: Proxy ps -> Mb ctx (SimplImpl ps_in ps_out) ->
                      ImpTransM ext blocks ret (ps :++: ps_out) ctx res ->
                      ImpTransM ext blocks ret (ps :++: ps_in) ctx res

translateSimplImpl _ [nuP| SImpl_Drop _ _ |] m =
  withPermStackM (\(xs :>: _) -> xs) (\(ps :>: _) -> ps) m

translateSimplImpl _ [nuP| SImpl_Copy x _ |] m =
  withPermStackM (:>: translateVar x) (\(ps :>: p) -> ps :>: p :>: p) m

translateSimplImpl _ [nuP| SImpl_Swap _ _ _ _ |] m =
  withPermStackM (\(xs :>: x :>: y) -> xs :>: y :>: x)
  (\(pctx :>: px :>: py) -> pctx :>: py :>: px)
  m

translateSimplImpl _ [nuP| SImpl_IntroOrL _ p1 p2 |] m =
  do tp1 <- translate p1
     tp2 <- translate p2
     withPermStackM id
       (\(ps :>: p_top) ->
         ps :>: PTrans_Term (mbMap2 ValPerm_Or p1 p2) (leftTrans tp1 tp2 p_top))
       m

translateSimplImpl _ [nuP| SImpl_IntroOrR _ p1 p2 |] m =
  do tp1 <- translate p1
     tp2 <- translate p2
     withPermStackM id
       (\(ps :>: p_top) ->
         ps :>: PTrans_Term (mbMap2 ValPerm_Or p1 p2) (rightTrans tp1 tp2 p_top))
       m

translateSimplImpl _ [nuP| SImpl_IntroExists _ e p |] m =
  do let tp = mbExprType e
     tp_trans <- translateClosed tp
     etrans <- translate e
     sigma_trm <-
       sigmaTransM "x_ex" tp_trans (flip inExtTransM $ translate $ mbCombine p)
       etrans getTopPermM
     withPermStackM id
       ((:>: PTrans_Term (fmap ValPerm_Exists p) sigma_trm) . mapRListTail)
       m

translateSimplImpl _ [nuP| SImpl_Cast _ _ p |] m =
  withPermStackM mapRListTail
  (\(pctx :>: _ :>: ptrans) -> pctx :>: ptrans)
  m

translateSimplImpl _ [nuP| SImpl_IntroEqRefl x |] m =
  withPermStackM (:>: translateVar x) (:>: PTrans_Eq (fmap PExpr_Var x)) m
  
translateSimplImpl _ [nuP| SImpl_InvertEq x y |] m =
  withPermStackM ((:>: translateVar y) . mapRListTail)
  ((:>: PTrans_Eq (fmap PExpr_Var x)) . mapRListTail)
  m

translateSimplImpl _ [nuP| SImpl_CopyEq _ _ |] m =
  withPermStackM
  (\(vars :>: var) -> (vars :>: var :>: var))
  (\(pctx :>: ptrans) -> (pctx :>: ptrans :>: ptrans))
  m

translateSimplImpl _ [nuP| SImpl_IntroConj x |] m =
  withPermStackM (:>: translateVar x) (:>: PTrans_True) m

translateSimplImpl _ [nuP| SImpl_ExtractConj x _ i |] m =
  withPermStackM (:>: translateVar x)
  (\(pctx :>: ptrans) ->
    let ps = unPTransConj "translateSimplImpl: SImpl_ExtractConj" ptrans in
    pctx :>: PTrans_Conj [ps !! mbLift i]
    :>: PTrans_Conj (deleteNth (mbLift i) ps))
  m

translateSimplImpl _ [nuP| SImpl_CopyConj x _ i |] m =
  withPermStackM (:>: translateVar x)
  (\(pctx :>: ptrans) ->
    let ps = unPTransConj "translateSimplImpl: SImpl_CopyConj" ptrans in
    pctx :>: PTrans_Conj [ps !! mbLift i] :>: ptrans)
  m

translateSimplImpl _ [nuP| SImpl_InsertConj x _ _ i |] m =
  withPermStackM mapRListTail
  (\(pctx :>: ptransi :>: ptrans) ->
    let ps = unPTransConj "translateSimplImpl: SImpl_CopyConj" ptrans
        pi = unPTransConj1 "translateSimplImpl: SImpl_CopyConj" ptransi in
    pctx :>: PTrans_Conj (take (mbLift i) ps ++ pi : drop (mbLift i) ps))
  m

translateSimplImpl _ [nuP| SImpl_ConstFunPerm x _ mb_fun_perm ident |] m =
  withPermStackM ((:>: translateVar x) . mapRListTail)
  ((:>: PTrans_Term (fmap (ValPerm_Conj1
                           . Perm_Fun) mb_fun_perm) (globalOpenTerm $
                                                     mbLift ident))
   . mapRListTail)
  m

translateSimplImpl _ [nuP| SImpl_CastLLVMWord _ _ e2 |] m =
  withPermStackM mapRListTail
  ((:>: PTrans_Eq (fmap PExpr_LLVMWord e2)) . mapRListTail . mapRListTail)
  m

translateSimplImpl _ [nuP| SImpl_InvertLLVMOffsetEq mb_x mb_off mb_y |] m =
  withPermStackM
  ((:>: translateVar mb_y) . mapRListTail)
  ((:>: PTrans_Eq (mbMap2 (\x off -> PExpr_LLVMOffset x $
                                     bvNegate off) mb_x mb_off)) . mapRListTail)
  m

translateSimplImpl _ [nuP| SImpl_OffsetLLVMWord _ mb_e mb_off mb_x |] m =
  withPermStackM
  ((:>: translateVar mb_x) . mapRListTail . mapRListTail)
  ((:>: PTrans_Eq (mbMap2 (\e off -> PExpr_LLVMWord $ bvAdd e off)
                   mb_e mb_off)) . mapRListTail . mapRListTail)
  m

translateSimplImpl _ [nuP| SImpl_CastLLVMPtr _ _ off _ |] m =
  withPermStackM mapRListTail
  (\(pctx :>: _ :>: ptrans) ->
    let ps = unPTransConj "translateSimplImpl: SImpl_CastLLVMPtr" ptrans in
    pctx :>: PTrans_Conj (mapMaybe (offsetLLVMAtomicPermTrans $
                                    fmap bvNegate off) ps))
  m

translateSimplImpl _ [nuP| SImpl_CastLLVMFree _ _ e2 |] m =
  withPermStackM mapRListTail
  ((:>: PTrans_Conj [APTrans_LLVMFree e2]) . mapRListTail . mapRListTail)
  m

translateSimplImpl _ [nuP| SImpl_CastLLVMFieldOffset _ _ mb_off |] m =
  withPermStackM mapRListTail
  (\(pctx :>: _ :>: ptrans) ->
    let (mb_fld,ptrans') =
          unPTransLLVMField "translateSimplImpl: SImpl_CastLLVMPtr" ptrans in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (mbMap2 (\fld off -> fld { llvmFieldOffset = off })
                           mb_fld mb_off)
                          ptrans'])
  m

translateSimplImpl _ [nuP| SImpl_IntroLLVMFieldContents x _ mb_fld |] m =
  withPermStackM ((:>: translateVar x) . mapRListTail . mapRListTail)
  (\(pctx :>: _ :>: ptrans) ->
    pctx :>: PTrans_Conj [APTrans_LLVMField mb_fld ptrans])
  m

translateSimplImpl _ [nuP| SImpl_LLVMFieldLifetimeCurrent _ _ _ mb_l |] m =
  withPermStackM mapRListTail
  (\(pctx :>: ptrans :>: _) ->
    let (mb_fld,ptrans') =
          unPTransLLVMField
          "translateSimplImpl: SImpl_LLVMFieldLifetimeCurrent" ptrans in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (mbMap2 (\fp l -> fp { llvmFieldLifetime = l })
                           mb_fld mb_l)
                          ptrans'])
  m

translateSimplImpl _ [nuP| SImpl_LLVMFieldLifetimeAlways _ _ mb_l |] m =
  withPermStackM id
  (\(pctx :>: ptrans) ->
    let (mb_fld,ptrans') =
          unPTransLLVMField
          "translateSimplImpl: SImpl_LLVMFieldLifetimeCurrent" ptrans in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (mbMap2 (\fp l -> fp { llvmFieldLifetime = l })
                           mb_fld mb_l)
                          ptrans'])
  m

translateSimplImpl _ [nuP| SImpl_DemoteLLVMFieldWrite _ _ |] m =
  withPermStackM id
  (\(pctx :>: ptrans) ->
    let (mb_fld,ptrans') =
          unPTransLLVMField
          "translateSimplImpl: SImpl_DemoteLLVMFieldWrite" ptrans in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (fmap (\fld -> fld { llvmFieldRW = PExpr_Read }) mb_fld)
                          ptrans])
  m


translateSimplImpl _ [nuP| SImpl_LLVMArrayCopy _ mb_ap mb_rng |] m =
  error "FIXME HERE: translateSimplImpl: SImpl_LLVMArrayCopy not yet implemented!"
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
               "translateSimplImpl: SImpl_LLVMArrayCopy" ptrans in
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

translateSimplImpl _ [nuP| SImpl_LLVMArrayBorrow _ _ _ |] m =
  error
  "FIXME HERE: translateSimplImpl: SImpl_LLVMArrayBorrow not yet implemented!"
  -- NOTE: same issue as for SImpl_LLVMArrayCopy

translateSimplImpl _ [nuP| SImpl_LLVMArrayReturn _ _ _ |] m =
  error
  "FIXME HERE: translateSimplImpl: SImpl_LLVMArrayReturn not yet implemented!"
  -- NOTE: needs a function to replace a sub-range of a Vec with another one
  -- IDEA: the borrows could translate to proofs of the relevant BVProps, which
  -- could be used when returning

translateSimplImpl _ [nuP| SImpl_LLVMArrayIndexCopy _ _ ix |] m =
  do let w = natVal2 ix
     (_ :>: ptrans_props :>: ptrans_array) <- itiPermStack <$> ask
     let arr_trans =
           unPTransLLVMArray
           "translateSimplImpl: SImpl_LLVMArrayIndexCopy" ptrans_array
     let prop_trans =
           head $ unPTransBVProps
           "translateSimplImpl: SImpl_LLVMArrayIndexCopy" ptrans_props
     ix_trans <- translate ix
     let fld_ptrans = getLLVMArrayTransField arr_trans ix_trans prop_trans
     withPermStackM id
       (\(pctx :>: _ :>: _) ->
         pctx :>: PTrans_Conj [fld_ptrans] :>: ptrans_array)
       m

translateSimplImpl _ [nuP| SImpl_LLVMArrayIndexBorrow x _ ix |] m =
  do let w = natVal2 ix
     (_ :>: ptrans_props :>: ptrans_array) <- itiPermStack <$> ask
     let arr_trans =
           unPTransLLVMArray
           "translateSimplImpl: SImpl_LLVMArrayIndexCopy" ptrans_array
     let prop_trans =
           head $ unPTransBVProps
           "translateSimplImpl: SImpl_LLVMArrayIndexCopy" ptrans_props
     ix_trans <- translate ix
     let fld_ptrans = getLLVMArrayTransField arr_trans ix_trans prop_trans
     let b = LLVMArrayBorrowTrans (fmap FieldBorrow ix) prop_trans
     withPermStackM id
       (\(pctx :>: _ :>: _) ->
         pctx :>: PTrans_Conj [fld_ptrans] :>:
         PTrans_Conj [APTrans_LLVMArray $ llvmArrayTransAddBorrow b arr_trans])
       m

translateSimplImpl _ [nuP| SImpl_LLVMArrayIndexReturn x _ ix |] m =
  do let w = natVal2 ix
     (_ :>: ptrans_fld :>: ptrans_array) <- itiPermStack <$> ask
     let aptrans_fld = case ptrans_fld of
           PTrans_Conj [ap] -> ap
           _ -> error ("translateSimplImpl: SImpl_LLVMArrayIndexReturn: "
                       ++ "found non-field perm where field perm was expected")
     let arr_trans =
           unPTransLLVMArray
           "translateSimplImpl: SImpl_LLVMArrayIndexCopy" ptrans_array
     let b_trans = llvmArrayTransFindBorrow (fmap FieldBorrow ix) arr_trans
     ix_trans <- translate ix
     let arr_trans' =
           setLLVMArrayTransField arr_trans ix_trans
           (llvmArrayBorrowTransProp b_trans) aptrans_fld
     withPermStackM mapRListTail
       (\(pctx :>: _ :>: _) ->
         pctx :>:
         PTrans_Conj [APTrans_LLVMArray $
                      llvmArrayTransRemBorrow b_trans arr_trans'])
       m

translateSimplImpl _ [nuP| SImpl_LLVMArrayContents _ _ _ _ _ |] m =
  error "FIXME HERE: translateSimplImpl: SImpl_LLVMArrayContents unhandled"

translateSimplImpl _ [nuP| SImpl_LLVMFieldIsPtr x _ |] m =
  withPermStackM (:>: translateVar x)
  (\(pctx :>: ptrans_fld) ->
    pctx :>: PTrans_Conj [APTrans_IsLLVMPtr] :>: ptrans_fld)
  m

translateSimplImpl _ [nuP| SImpl_LLVMArrayIsPtr x _ |] m =
  withPermStackM (:>: translateVar x)
  (\(pctx :>: ptrans_array) ->
    pctx :>: PTrans_Conj [APTrans_IsLLVMPtr] :>: ptrans_array)
  m

translateSimplImpl _ [nuP| SImpl_SplitLifetime mb_x mb_p mb_l mb_ps |] m =
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

translateSimplImpl _ [nuP| SImpl_LCurrentRefl l |] m =
  withPermStackM (:>: translateVar l)
  (:>: PTrans_Conj [APTrans_LifetimePerm $ fmap (Perm_LCurrent . PExpr_Var) l])
  m

translateSimplImpl _ [nuP| SImpl_LCurrentTrans l1 l2 l3 |] m =
  withPermStackM mapRListTail
  ((:>: PTrans_Conj [APTrans_LifetimePerm $ fmap Perm_LCurrent l3]) .
   mapRListTail . mapRListTail)
  m

translateSimplImpl _ [nuP| SImpl_FoldRec x rp args |] m =
  do ttrans <-
       translate $ mbMap2 ValPerm_Rec (fmap recPermName rp) args
     let fold_ident = mbLift $ fmap recPermFoldFun rp
     withPermStackM id
       (\(pctx :>: ptrans_x) ->
         pctx :>: typeTransF ttrans [applyOpenTermMulti
                                     (globalOpenTerm fold_ident)
                                     (transTerms ptrans_x)])
       m

translateSimplImpl _ [nuP| SImpl_UnfoldRec x rp args |] m =
  do ttrans <- translate $ mbMap2 unfoldRecPerm rp args
     let unfold_ident = mbLift $ fmap recPermUnfoldFun rp
     withPermStackM id
       (\(pctx :>: ptrans_x) ->
         pctx :>:
         typeTransF (tupleTypeTrans ttrans) [applyOpenTerm
                                             (globalOpenTerm unfold_ident)
                                             (transTerm1 ptrans_x)])
       m

{-
translateSimplImpl _ [nuP| SImpl_Mu _ _ _ _ |] m =
  error "FIXME HERE: SImpl_Mu: translation not yet implemented"
-}

translateSimplImpl _ mb_simpl@[nuP| SImpl_RecArgAlways _ _ _ _ _ |] m =
  withPermStackM id
  (\(pctx :>: PTrans_Term _ t) ->
    pctx :>: PTrans_Term (fmap (distPermsHeadPerm . simplImplOut) mb_simpl) t)
  m

translateSimplImpl _ mb_simpl@[nuP| SImpl_RecArgCurrent _ _ _ _ _ |] m =
  withPermStackM mapRListTail
  (\(pctx :>: PTrans_Term _ t :>: _) ->
    pctx :>: PTrans_Term (fmap (distPermsHeadPerm . simplImplOut) mb_simpl) t)
  m

translateSimplImpl _ mb_simpl@[nuP| SImpl_RecArgWrite _ _ _ _ _ |] m =
  withPermStackM id
  (\(pctx :>: PTrans_Term _ t) ->
    pctx :>: PTrans_Term (fmap (distPermsHeadPerm . simplImplOut) mb_simpl) t)
  m

translateSimplImpl _ mb_simpl@[nuP| SImpl_RecArgRead _ _ _ _ |] m =
  withPermStackM id
  (\(pctx :>: PTrans_Term _ t) ->
    pctx :>: PTrans_Term (fmap (distPermsHeadPerm . simplImplOut) mb_simpl) t)
  m


-- | Translate a 'PermImpl1' to a function on translation computations
translatePermImpl1 :: ImplTranslateF r ext blocks ret =>
                      Mb ctx (PermImpl1 ps_in ps_outs) ->
                      Mb ctx (MbPermImpls r ps_outs) ->
                      ImpTransM ext blocks ret ps_in ctx OpenTerm

-- A failure translates to a call to the catch handler, which is the most recent
-- Impl1_Catch, if one exists, or the SAW errorM function otherwise
translatePermImpl1 [nuP| Impl1_Fail |] _ = itiCatchHandler <$> ask

-- A catch runs the first computation using the second as catch handler
translatePermImpl1 [nuP| Impl1_Catch |]
  [nuP| MbPermImpls_Cons (MbPermImpls_Cons _ mb_impl1) mb_impl2 |] =
  do compMType <- compReturnTypeM
     letTransM "catchpoint" compMType
       (translate $ mbCombine mb_impl2)
       (\handler -> withCatchHandlerM handler $ translate $ mbCombine mb_impl1)

-- A push moves the given permission from x to the top of the perm stack
translatePermImpl1 [nuP| Impl1_Push x p |] [nuP| MbPermImpls_Cons _ mb_impl |] =
  assertVarPermM "Impl1_Push" x p >>
  getVarPermM x >>= \ptrans ->
  setVarPermM x (PTrans_True)
  (withPermStackM (:>: translateVar x) (:>: ptrans) $
   translate (mbCombine mb_impl))

-- A pop moves the given permission from the top of the perm stack to x
translatePermImpl1 [nuP| Impl1_Pop x p |] [nuP| MbPermImpls_Cons _ mb_impl |] =
  assertTopPermM "Impl1_Pop" x p >>
  assertVarPermM "Impl1_Pop" x (nuMulti (mbToProxy p) $ const ValPerm_True) >>
  getTopPermM >>= \ptrans ->
  setVarPermM x ptrans
  (withPermStackM mapRListTail mapRListTail $
   translate (mbCombine mb_impl))

-- An or elimination performs a pattern-match on an Either
translatePermImpl1 [nuP| Impl1_ElimOr x p1 p2 |]
  [nuP| MbPermImpls_Cons (MbPermImpls_Cons _ mb_impl1) mb_impl2 |] =
  do assertTopPermM "Impl1_ElimOr" x (mbMap2 ValPerm_Or p1 p2)
     tp1 <- translate p1
     tp2 <- translate p2
     tp_ret <- compReturnTypeTransM
     top_ptrans <- getTopPermM
     eitherElimTransM tp1 tp2 tp_ret
       (\ptrans ->
         withPermStackM id ((:>: ptrans) . mapRListTail) $
         translate $ mbCombine mb_impl1)
       (\ptrans ->
         withPermStackM id ((:>: ptrans) . mapRListTail) $
         translate $ mbCombine mb_impl2)
       (transTupleTerm top_ptrans)

-- An existential elimination performs a pattern-match on a Sigma
translatePermImpl1 [nuP| Impl1_ElimExists x p |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  do assertTopPermM "Impl1_ElimExists" x (fmap ValPerm_Exists p)
     let tp = mbBindingType p
     top_ptrans <- getTopPermM
     tp_trans <- translateClosed tp
     sigmaElimTransM "x_elimEx" tp_trans
       (flip inExtTransM $ translate $ mbCombine p)
       compReturnTypeTransM
       (\etrans ptrans ->
         inExtTransM etrans $
         withPermStackM id ((:>: ptrans) . mapRListTail) $
         translate $ mbCombine mb_impl)
       (transTerm1 top_ptrans)

-- A SimplImpl is translated using translateSimplImpl
translatePermImpl1 [nuP| Impl1_Simpl simpl prx |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  translateSimplImpl (mbLift prx) simpl $ translate $ mbCombine mb_impl

translatePermImpl1 [nuP| Impl1_ElimLLVMFieldContents
                        _ mb_fld |] [nuP| MbPermImpls_Cons _ mb_impl |] =
  inExtTransM ETrans_LLVM $
  withPermStackM (:>: Member_Base)
  (\(pctx :>: ptrans_x) ->
    let (_,ptrans') =
          unPTransLLVMField
          "translateSimplImpl: Impl1_ElimLLVMFieldContents" ptrans_x in
    pctx :>: PTrans_Conj [APTrans_LLVMField
                          (mbCombine $
                           fmap (\fld -> nu $ \y ->
                                  fld { llvmFieldContents =
                                          ValPerm_Eq (PExpr_Var y)})
                           mb_fld) $
                          PTrans_Eq (mbCombine $
                                     fmap (const $ nu PExpr_Var) mb_fld)]
    :>: ptrans') $
  translate $ mbCombine mb_impl

-- If e1 and e2 are already equal, short-circuit the proof construction and then
-- elimination
translatePermImpl1 [nuP| Impl1_TryProveBVProp x prop@(BVProp_Eq e1 e2) |]
  [nuP| MbPermImpls_Cons _ mb_impl |]
  | mbLift (mbMap2 bvEq e1 e2) =
    do bv_tp <- typeTransType1 <$> translateClosed (mbExprType e1)
       e1_trans <- translate1 e1
       let pf = ctorOpenTerm "Prelude.ReflP" [bv_tp, e1_trans]
       withPermStackM (:>: translateVar x)
         (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop pf)])
         (translate $ mbCombine mb_impl)

translatePermImpl1 [nuP| Impl1_TryProveBVProp x prop@(BVProp_Eq e1 e2) |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  do prop_tp_trans <- translate prop
     applyMultiTransM (return $ globalOpenTerm "Prelude.maybe")
       [ return (typeTransType1 prop_tp_trans), compReturnTypeM
       , (itiCatchHandler <$> ask)
       , lambdaTransM "eq_pf" prop_tp_trans
         (\prop_trans ->
           withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans)
           (translate $ mbCombine mb_impl))
       , applyMultiTransM (return $ globalOpenTerm "Prelude.bvEqWithProof")
         [ return (natOpenTerm $ natVal2 prop) , translate1 e1, translate1 e2]]

translatePermImpl1 [nuP| Impl1_TryProveBVProp x prop@(BVProp_Neq e1 e2) |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  let w = natVal2 prop in
  applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
  [ compReturnTypeM
  , applyMultiTransM (return $ globalOpenTerm "Prelude.bvEq")
    [ return (natOpenTerm w), translate1 e1, translate1 e2 ]
  , (itiCatchHandler <$> ask)
  , withPermStackM (:>: translateVar x)
    (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop unitOpenTerm)])
    (translate $ mbCombine mb_impl)]


translatePermImpl1 [nuP| Impl1_TryProveBVProp x
                        prop@(BVProp_InRange e (BVRange off len)) |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  do prop_tp_trans <- translate prop
     applyMultiTransM (return $ globalOpenTerm "Prelude.maybe")
       [ return (typeTransType1 prop_tp_trans), compReturnTypeM
       , (itiCatchHandler <$> ask)
       , lambdaTransM "inrange_pf" prop_tp_trans
         (\prop_trans ->
           withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans)
           (translate $ mbCombine mb_impl))
       , applyMultiTransM (return $ globalOpenTerm "Prelude.bvultWithProof")
         [ return (natOpenTerm $ natVal2 prop)
         , translate1 (mbMap2 bvSub e off), translate1 len]
       ]

translatePermImpl1 [nuP| Impl1_TryProveBVProp x
                        prop@(BVProp_NotInRange e (BVRange off len)) |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  let w = natVal2 prop in
  applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
  [ compReturnTypeM
  , applyMultiTransM (return $ globalOpenTerm "Prelude.bvult")
    [ return (natOpenTerm w), translate1 (mbMap2 bvSub e off), translate1 len ]
  , (itiCatchHandler <$> ask)
  , withPermStackM (:>: translateVar x)
    (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop unitOpenTerm)])
    (translate $ mbCombine mb_impl)]

translatePermImpl1 [nuP| Impl1_TryProveBVProp _ (BVProp_RangeSubset _ _) |]
  [nuP| MbPermImpls_Cons _ _ |] =
  error "FIXME HERE NOW: translate Impl1_TryProveBVProp (BVProp_RangeSubset)"

translatePermImpl1 [nuP| Impl1_TryProveBVProp _ (BVProp_RangesDisjoint _ _) |]
  [nuP| MbPermImpls_Cons _ _ |] =
  error "FIXME HERE NOW: translate Impl1_TryProveBVProp (BVProp_RangesDisjoint)"


instance ImplTranslateF r ext blocks ret =>
         Translate (ImpTransInfo
                    ext blocks ret ps) ctx (PermImpl r ps) OpenTerm where
  translate [nuP| PermImpl_Done r |] = translateF r
  translate [nuP| PermImpl_Step impl1 mb_impls |] =
    translatePermImpl1 impl1 mb_impls


----------------------------------------------------------------------
-- * Translating Typed Crucible Expressions
----------------------------------------------------------------------

-- translate for a TypedReg yields an ExprTrans
instance TransInfo info =>
         Translate info ctx (TypedReg tp) (ExprTrans tp) where
  translate [nuP| TypedReg x |] = translate x

instance TransInfo info =>
         Translate info ctx (RegWithVal tp) (ExprTrans tp) where
  translate [nuP| RegWithVal _ e |] = translate e
  translate [nuP| RegNoVal x |] = translate x

-- | Translate a 'RegWithVal' to exactly one SAW term via 'transTerm1'
translateRWV :: TransInfo info => Mb ctx (RegWithVal a) ->
                TransM info ctx OpenTerm
translateRWV mb_rwv = transTerm1 <$> translate mb_rwv

-- translate for a TypedExpr yields an ExprTrans
instance (PermCheckExtC ext, TransInfo info) =>
         Translate info ctx (App ext RegWithVal tp) (ExprTrans tp) where
  translate [nuP| BaseIsEq BaseBoolRepr e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.boolEq")
    [translateRWV e1, translateRWV e2]
  translate [nuP| BaseIsEq BaseNatRepr e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.equalNat")
    [translateRWV e1, translateRWV e2]
  translate [nuP| BaseIsEq (BaseBVRepr w) e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvEq")
    [translate w, translateRWV e1, translateRWV e2]

  translate [nuP| EmptyApp |] = return $ ETrans_Term unitOpenTerm

  -- Booleans
  translate [nuP| BoolLit True |] =
    return $ ETrans_Term $ globalOpenTerm "Prelude.True"
  translate [nuP| BoolLit False |] =
    return $ ETrans_Term $ globalOpenTerm "Prelude.False"
  translate [nuP| Not e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.not")
    [translateRWV e]
  translate [nuP| And e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.and")
    [translateRWV e1, translateRWV e2]
  translate [nuP| Or e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.or")
    [translateRWV e1, translateRWV e2]
  translate [nuP| BoolXor e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.xor")
    [translateRWV e1, translateRWV e2]

  -- Natural numbers
  translate [nuP| Expr.NatLit n |] =
    return $ ETrans_Term $ natOpenTerm $ toInteger $ mbLift n
  translate [nuP| NatLt e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.ltNat")
    [translateRWV e1, translateRWV e2]
  -- translate [nuP| NatLe _ _ |] =
  translate [nuP| NatAdd e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.addNat")
    [translateRWV e1, translateRWV e2]
  translate [nuP| NatSub e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.subNat")
    [translateRWV e1, translateRWV e2]
  translate [nuP| NatMul e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.mulNat")
    [translateRWV e1, translateRWV e2]
  translate [nuP| NatDiv e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.divNat")
    [translateRWV e1, translateRWV e2]
  translate [nuP| NatMod e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.modNat")
    [translateRWV e1, translateRWV e2]

  -- Function handles: the expression part of a function handle has no
  -- computational content
  translate [nuP| HandleLit _ |] = return ETrans_Fun

  -- Bitvectors
  translate [nuP| BVLit w i |] =
    return $ ETrans_Term $ bvNatOpenTerm (intValue $ mbLift w) (mbLift i)
  translate [nuP| BVConcat w1 w2 e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.join")
    [translate w1, translate w2, translateRWV e1, translateRWV e2]
  translate [nuP| BVTrunc w1 w2 e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.take")
    [return (globalOpenTerm "Prelude.Bool"),
     return (natOpenTerm (intValue (mbLift w2) - intValue (mbLift w1))),
     translate w1,
     translateRWV e]
  translate [nuP| BVZext w1 w2 e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvUExt")
    [return (natOpenTerm (intValue (mbLift w1) - intValue (mbLift w2))),
     translate w2, translateRWV e]
  translate [nuP| BVSext w1 w2 e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvSExt")
    [return (natOpenTerm (intValue (mbLift w1) - intValue (mbLift w2))),
     -- NOTE: bvSExt adds 1 to the 2ns arg
     return (natOpenTerm (intValue (mbLift w2) - 1)),
     translateRWV e]
  translate [nuP| BVNot w e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvNot")
    [translate w, translateRWV e]
  translate [nuP| BVAnd w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvAnd")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVOr w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvOr")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVXor w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvXor")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVNeg w e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvNeg")
    [translate w, translateRWV e]
  translate [nuP| BVAdd w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvAdd")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVSub w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvSub")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVMul w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvMul")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVUdiv w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvUDiv")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVSdiv w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvSDiv")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVUrem w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvURem")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVSrem w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvSRem")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVUle w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvule")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVUlt w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvult")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVSle w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvsle")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BVSlt w e1 e2 |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvslt")
    [translate w, translateRWV e1, translateRWV e2]
  translate [nuP| BoolToBV w e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
    [applyTransM (return $ globalOpenTerm "Prelude.bitvector") (translate w),
     translateRWV e,
     return (bvNatOpenTerm (intValue $ mbLift w) 1),
     return (bvNatOpenTerm (intValue $ mbLift w) 0)]
  translate [nuP| BVNonzero w e |] =
    ETrans_Term <$>
    applyMultiTransM (return $ globalOpenTerm "Prelude.bvEq")
    [translate w, translateRWV e,
     return (bvNatOpenTerm (intValue $ mbLift w) 0)]

  -- Strings
  translate [nuP| TextLit text |] =
    return $ ETrans_Term $ flatOpenTerm $ StringLit $
    mbLift $ fmap unpack text

  -- Everything else is an error
  translate mb_e =
    error ("Unhandled expression form: " ++
           (flip displayS "" $ renderPretty 0.8 80 $
            mbLift $ fmap (ppApp (const $ string "_")) mb_e))


-- translate for a TypedExpr yields an ExprTrans
{-
instance PermCheckExtC ext =>
         TypeTranslate (App ext RegWithVal tp) ctx (ExprTrans tp) where
  translate mb_app = translate (fmap (fmapFC regWithValExpr) mb_app)
-}

-- translate for a TypedExpr yields an ExprTrans
instance (PermCheckExtC ext, TransInfo info) =>
         Translate info ctx (TypedExpr ext tp) (ExprTrans tp) where
  translate [nuP| TypedExpr _ (Just e) |] = translate e
  translate [nuP| TypedExpr app Nothing |] = translate app

-- translate for a TypedReg yields a PermTrans
{-
instance PermCheckExtC ext =>
         ImplTranslate (TypedReg tp) (PermTrans ctx tp)
         ext blocks ret ps ctx where
  translate [nuP| TypedReg x |] = getVarPermM x
-}

-- translate for a TypedExpr yields a PermTrans
{-
instance PermCheckExtC ext =>
         ImplTranslate (App ext TypedReg tp) (PermTrans ctx tp)
         ext blocks ret ps ctx where
  translate [nuP| EmptyApp |] = return PTrans_True
  translate _ = error "FIXME HERE NOW"
-}

-- | Get the output permission on the return value of a 'TypedExpr'
exprOutPerm :: PermCheckExtC ext => Mb ctx (TypedExpr ext tp) ->
               PermTrans ctx tp
exprOutPerm [nuP| TypedExpr _ (Just e) |] = PTrans_Eq e
exprOutPerm [nuP| TypedExpr _ Nothing |] = PTrans_True


----------------------------------------------------------------------
-- * Translating Typed Crucible Jump Targets
----------------------------------------------------------------------

{- FIXME: unused
instance Translate (ImpTransInfo ext blocks ret ps) ctx
         (TypedEntryID blocks args ghosts) (Maybe OpenTerm) where
  translate mb_entryID =
    translateTypedEntryID (mbLift mb_entryID) <$> itiBlockMapTrans <$> ask
-}

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

-- | Look up the 'TypedEntryTrans' for a 'TypedEntryID' and test if it has a
-- letrec-bound variable. If so, call that, otherwise translate the body of the
-- corresponding 'TypedEntry'
--
-- FIXME: check that the supplied perms match those expected by the entryID
translateCallEntryID :: (PermCheckExtC ext, ps ~ (ghosts :++: args)) =>
                        String -> TypedEntryID blocks args ghosts ->
                        Mb ctx (DistPerms ps) ->
                        ImpTransM ext blocks ret ps ctx OpenTerm
translateCallEntryID nm entryID mb_perms =
  do entry_trans <-
       lookupEntryTrans entryID <$> itiBlockMapTrans <$> ask
     case entry_trans of
       TypedEntryTrans _ (Just f) ->
         translateApply nm f mb_perms
       TypedEntryTrans entry Nothing ->
         translate $
         fmap (\perms ->
                varSubst (PermVarSubst $ distPermsVars perms) $
                typedEntryBody entryID entry) mb_perms

instance PermCheckExtC ext =>
         Translate (ImpTransInfo ext blocks ret ps) ctx
         (TypedJumpTarget blocks ps) OpenTerm where
  translate [nuP| TypedJumpTarget entryID _ perms |] =
    translateCallEntryID "TypedJumpTarget" (mbLift entryID) perms

instance PermCheckExtC ext =>
         ImplTranslateF (TypedJumpTarget blocks) ext blocks ret where
  translateF mb_tgt = translate mb_tgt


----------------------------------------------------------------------
-- * Translating Typed Crucible Statements
----------------------------------------------------------------------

-- | Translate a 'TypedStmt' to a function on translation computations
translateStmt :: PermCheckExtC ext =>
                 Mb ctx (TypedStmt ext rets ps_in ps_out) ->
                 ImpTransM ext blocks ret ps_out (ctx :++: rets) OpenTerm ->
                 ImpTransM ext blocks ret ps_in ctx OpenTerm

translateStmt [nuP| TypedSetReg _ e |] m =
  do etrans <- tpTransM $ translate e
     let ptrans = exprOutPerm e
     inExtTransM etrans $
       withPermStackM (:>: Member_Base) (:>: extPermTrans ptrans) m

translateStmt [nuP| stmt@(TypedCall freg fun_perm ghosts args l ps) |] m =
  do f_trans <- getTopPermM
     let f = case f_trans of
           PTrans_Conj [APTrans_Fun _ f_trm] -> f_trm
           _ -> error "translateStmt: TypedCall: unexpected function permission"
     let perms_in = fmap (distPermsSnoc . typedStmtIn) stmt
     let perms_out = mbCombine $ fmap (\stmt' -> nu $ \ret ->
                                        typedStmtOut stmt' (MNil :>: ret)) stmt
     ret_tp <- translate $ fmap funPermRet fun_perm
     fret_trm <-
       withPermStackM mapRListTail mapRListTail $
       translateApply "TypedCall" f perms_in
     sigmaElimTransM "x_elimCalRet" ret_tp
       (flip inExtTransM (translate perms_out)) compReturnTypeTransM
       (\ret_trans pctx ->
         inExtTransM ret_trans $
         withPermStackM
         (\(args :>: l :>: _) -> (args :>: Member_Base :>: l))
         (const pctx)
         m)
       fret_trm

translateStmt stmt@[nuP| BeginLifetime |] m =
  inExtTransM ETrans_Lifetime $
  withPermStackM (:>: Member_Base)
  (:>: PTrans_Conj [APTrans_LifetimePerm $ nuMulti (mbToProxy stmt :>: Proxy) $
                    const $ Perm_LOwned PExpr_PermListNil])
  m

translateStmt stmt@[nuP| EndLifetime _ ps _ end_perms |] m =
  let end_prx = mbDistPermsToProxies end_perms
      ps_l_prx = mbDistPermsToProxies ps :>: (Proxy :: Proxy LifetimeType) in
  withPermStackM
  (\pvars_all ->
    let ((pvars :>: _), _) = splitMapRList ps_l_prx end_prx pvars_all in
    pvars)
  (\pctx_all ->
    let ((pctx :>: _), _) = splitMapRList ps_l_prx end_prx pctx_all in
    permCtxEndLifetime pctx ps)
  m

-- FIXME HERE: figure out why these asserts always translate to ite True
translateStmt [nuP| TypedAssert e _ |] m =
  applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
  [compReturnTypeM, translate1 e, m, itiCatchHandler <$> ask]

translateStmt [nuP| TypedLLVMStmt stmt |] m = translateLLVMStmt stmt m


-- | Translate a 'TypedStmt' to a function on translation computations
translateLLVMStmt ::
  Mb ctx (TypedLLVMStmt w r ps_in ps_out) ->
  ImpTransM ext blocks ret ps_out (ctx :> r) OpenTerm ->
  ImpTransM ext blocks ret ps_in ctx OpenTerm

translateLLVMStmt [nuP| ConstructLLVMWord (TypedReg x) |] m =
  inExtTransM ETrans_LLVM $
  withPermStackM (:>: Member_Base) (:>: (PTrans_Eq $ extMb $
                                         fmap (PExpr_LLVMWord . PExpr_Var) x)) m

translateLLVMStmt [nuP| AssertLLVMWord reg _ |] m =
  inExtTransM (ETrans_Term $ natOpenTerm 0) $
  withPermStackM ((:>: Member_Base) . mapRListTail)
  ((:>: (PTrans_Eq $ fmap (const $ PExpr_Nat 0) $ extMb reg)) . mapRListTail)
  m

translateLLVMStmt [nuP| AssertLLVMPtr _ |] m =
  inExtTransM (ETrans_Term unitOpenTerm) $
  withPermStackM mapRListTail mapRListTail m

translateLLVMStmt [nuP| DestructLLVMWord _ e |] m =
  translate e >>= \etrans ->
  inExtTransM etrans $
  withPermStackM ((:>: Member_Base) . mapRListTail)
  ((:>: (PTrans_Eq $ extMb e)) . mapRListTail)
  m

translateLLVMStmt [nuP| OffsetLLVMValue x off |] m =
  inExtTransM ETrans_LLVM $
  withPermStackM (:>: Member_Base)
  (:>: (PTrans_Eq $ extMb $
        mbMap2 PExpr_LLVMOffset (fmap typedRegVar x) off))
  m

translateLLVMStmt [nuP| TypedLLVMLoad _ (mb_fp :: LLVMFieldPerm w)
                       (_ :: DistPerms ps) cur_perms |] m =
  let prx_l = mbLifetimeCurrentPermsProxies cur_perms
      prx_ps :: Proxy (ps :> LLVMPointerType w) = Proxy in
  inExtTransM ETrans_LLVM $
  withPermStackM
  (\(splitMapRList prx_ps prx_l -> (vars, vars_l)) ->
    appendMapRList (vars :>: Member_Base) vars_l)
  (\(splitMapRList prx_ps prx_l -> (pctx :>: p_ptr, pctx_l)) ->
    let (_, p_ret) =
          unPTransLLVMField
          "translateLLVMStmt: TypedLLVMLoad: expected field perm" p_ptr in
    appendMapRList
    (pctx :>: PTrans_Conj [APTrans_LLVMField
                           (mbCombine $
                            fmap (\fp -> nu $ \ret ->
                                   fp { llvmFieldContents =
                                          ValPerm_Eq (PExpr_Var ret)}) mb_fp)
                           (PTrans_Eq $ mbCombine $
                            fmap (const $ nu $ \ret -> PExpr_Var ret) mb_fp)]
     :>: p_ret) pctx_l)
  m

translateLLVMStmt [nuP| TypedLLVMStore _ (mb_fp :: LLVMFieldPerm w) mb_e
                      (_ :: DistPerms ps) cur_perms |] m =
  let prx_l = mbLifetimeCurrentPermsProxies cur_perms
      prx_ps :: Proxy (ps :> LLVMPointerType w) = Proxy in
  inExtTransM (ETrans_Term unitOpenTerm) $
  withPermStackM id
  (\(splitMapRList prx_ps prx_l -> (pctx :>: p_ptr, pctx_l)) ->
    appendMapRList
    (pctx :>: PTrans_Conj [APTrans_LLVMField
                           (extMb $ mbMap2 (\fp e ->
                                             fp { llvmFieldContents =
                                                    ValPerm_Eq e })
                            mb_fp mb_e)
                           (PTrans_Eq $ extMb mb_e)])
    pctx_l)
  m

translateLLVMStmt [nuP| TypedLLVMAlloca
                       _ (mb_fperm :: LLVMFramePerm w) mb_sz |] m =
  let sz = mbLift mb_sz
      w :: Proxy w = Proxy in
  inExtTransM ETrans_LLVM $
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

translateLLVMStmt mb_stmt@[nuP| TypedLLVMCreateFrame |] m =
  inExtTransM ETrans_LLVMFrame $
  withPermStackM (:>: Member_Base)
  (:>: PTrans_Conj [APTrans_LLVMFrame $ fmap (const []) (extMb mb_stmt)])
  m

translateLLVMStmt [nuP| TypedLLVMDeleteFrame _ _ _ |] m =
  inExtTransM (ETrans_Term unitOpenTerm) $
  withPermStackM (const MNil) (const MNil) m

translateLLVMStmt [nuP| TypedLLVMLoadHandle _ mb_fun_perm |] m =
  inExtTransM ETrans_Fun $
  withPermStackM ((:>: Member_Base) . mapRListTail)
  (\(pctx :>: PTrans_Conj [APTrans_LLVMFunPtr mb_fun_perm' t]) ->
    case mbMap2 funPermEq3 (extMb mb_fun_perm) mb_fun_perm' of
      [nuP| Just (Refl, Refl, Refl) |] ->
        pctx :>: PTrans_Conj [APTrans_Fun (extMb mb_fun_perm) t]
      _ -> error ("translateLLVMStmt: TypedLLVMLoadHandle: "
                  ++ "unexpected function permission type"))
  m

translateLLVMStmt [nuP| TypedLLVMResolveGlobal gsym
                      (p :: ValuePerm (LLVMPointerType w))|] m =
  inExtTransM ETrans_LLVM $
  do env <- infoEnv <$> ask
     ptrans <- translate $ extMb p
     let w :: NatRepr w = knownRepr
     case lookupGlobalSymbol env (mbLift gsym) w of
       Nothing -> error ("translateLLVMStmt: TypedLLVMResolveGlobal: "
                         ++ " no translation of symbol " ++ show (mbLift gsym))
       Just (_, ts) ->
         withPermStackM (:>: Member_Base) (:>: typeTransF ptrans ts) m


----------------------------------------------------------------------
-- * Translating Sequences of Typed Crucible Statements
----------------------------------------------------------------------

instance PermCheckExtC ext =>
         Translate (ImpTransInfo ext blocks ret ps) ctx
         (TypedRet ret ps) OpenTerm where
  translate [nuP| TypedRet tp r mb_perms |] =
    do let perms =
             mbMap2
             (\reg mbps -> varSubst (singletonVarSubst $ typedRegVar reg) mbps)
             r mb_perms
       assertPermStackEqM "TypedRet" perms
       r_trans <- translate r
       tp_trans <- translate tp
       ret_tp <- returnTypeM
       sigma_trm <-
         sigmaTransM "r" tp_trans (flip inExtTransM $
                                   translate $ mbCombine mb_perms)
         r_trans (itiPermStack <$> ask)
       return $
         applyOpenTermMulti (globalOpenTerm "Prelude.returnM")
         [ret_tp, sigma_trm]

instance PermCheckExtC ext =>
         ImplTranslateF (TypedRet ret) ext blocks ret where
  translateF mb_ret = translate mb_ret

instance PermCheckExtC ext =>
         Translate (ImpTransInfo ext blocks ret ps) ctx
         (TypedTermStmt blocks ret ps) OpenTerm where
  translate [nuP| TypedJump impl_tgt |] = translate impl_tgt
  translate [nuP| TypedBr reg impl_tgt1 impl_tgt2 |] =
    applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
    [compReturnTypeM, translate1 reg,
     translate impl_tgt1, translate impl_tgt2]
  translate [nuP| TypedReturn impl_ret |] = translate impl_ret
  translate [nuP| TypedErrorStmt _ |] = itiCatchHandler <$> ask


instance PermCheckExtC ext =>
         Translate (ImpTransInfo ext blocks ret ps) ctx
         (TypedStmtSeq ext blocks ret ps) OpenTerm where
  translate [nuP| TypedImplStmt impl_seq |] = translate impl_seq
  translate [nuP| TypedConsStmt _ stmt mb_seq |] =
    translateStmt stmt (translate $ mbCombine mb_seq)
  translate [nuP| TypedTermStmt _ term_stmt |] = translate term_stmt

instance PermCheckExtC ext =>
         ImplTranslateF (TypedStmtSeq ext blocks ret) ext blocks ret where
  translateF mb_seq = translate mb_seq


----------------------------------------------------------------------
-- * Translating CFGs
----------------------------------------------------------------------

-- | Fold a function over each 'TypedEntry' in a 'TypedBlockMap' that is marked
-- as being the head of a strongly-connected component, visiting the entries in
-- the right-most 'TypedBlock' first
foldBlockMapSCC :: (forall args. TypedEntry ext blocks ret args -> b -> b) ->
                   b -> TypedBlockMap ext blocks ret -> b
foldBlockMapSCC = helper where
  helper :: (forall args. TypedEntry ext blocks ret args -> b -> b) ->
            b -> MapRList (TypedBlock ext blocks ret) bs -> b
  helper _ b MNil = b
  helper f b (bs :>: TypedBlock []) = helper f b bs
  helper f b (bs :>: TypedBlock (entry:entries))
    | typedEntryIsSCC entry =
      f entry $ helper f b (bs :>: TypedBlock entries)
  helper f b (bs :>: TypedBlock (_:entries)) =
    helper f b (bs :>: TypedBlock (entries))

{-
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
     tp_f <- lambdaExprTransForce "x" ret (translate ret_perms)
     return $ dataTypeOpenTerm "Prelude.Sigma" [tp_term, tp_f]

nuMultiTransM :: (MapRList Name ctx -> b) -> TypeTransM ctx (Mb ctx b)
nuMultiTransM f =
  do ctx <- ask
     return $ nuMulti ctx f
-}

-- FIXME: documentation
lambdaLRTTransM :: String -> TypeTrans tr -> (tr -> TransM info ctx OpenTerm) ->
                   TransM info ctx OpenTerm
lambdaLRTTransM x tps body_f =
  foldr (\(i,tp) rest_f xs ->
          (\t -> ctorOpenTerm "Prelude.LRT_Fun" [tp, t]) <$>
          lambdaOpenTermTransM (x ++ show i) tp (rest_f . (:xs)))
  (body_f . typeTransF tps) (zip [0..] $ typeTransTypes tps) []

-- | Build a @LetRecType@ that describes the type of the translation of a
-- 'TypedEntry'
translateEntryLRT :: TypedEntry ext blocks ret args ->
                     TypeTransM ctx OpenTerm
translateEntryLRT (TypedEntry entryID args ret is_scc perms_in perms_out _) =
  trace "translateEntryLRT starting..." $ inEmptyCtxTransM $
  translateClosed (appendCruCtx (entryGhosts entryID) args) >>= \arg_tps ->
  lambdaLRTTransM "arg" arg_tps $ \ectx ->
  inCtxTransM ectx $
  translate perms_in >>= \perms_in_tps ->
  lambdaLRTTransM "p" perms_in_tps $ \_ ->
  translateRetType ret perms_out >>= \retType ->
  trace "translateEntryLRT finished" $
  return $ ctorOpenTerm "Prelude.LRT_Ret" [retType]

{-
  helperExpr (appendCruCtx (entryGhosts entryID) args) $
  helperPerms ret perms_in perms_out
  where
    helperExpr :: CruCtx ctx -> TypeTransM ctx OpenTerm ->
                  TypeTransM RNil OpenTerm
    helperExpr CruCtxNil m = m
    helperExpr (CruCtxCons ctx tp) m =
      helperExpr ctx $
      do mb_tp <- nuMultiTransM $ const tp
         tp_trans <- translate mb_tp
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
      do eith <- translate p
         case eith of
           Left _ -> helperPerms ret perms ret_perms
           Right (tp_term, _) ->
             (\lam -> ctorOpenTerm "Prelude.LRT_Fun" [tp_term,lam]) <$>
             lambdaTransM "p" tp_term (\_ -> helperPerms ret perms ret_perms)
-}


-- | Build a @LetRecTypes@ list that describes the types of all of the
-- entrypoints in a 'TypedBlockMap'
translateBlockMapLRTs :: TypedBlockMap ext blocks ret ->
                         TypeTransM ctx OpenTerm
translateBlockMapLRTs =
  trace "translateBlockMapLRTs started..." $
  foldBlockMapSCC
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
  helper (bs :>: TypedBlock (entry:entries)) f
    | typedEntryIsSCC entry =
      do entryLRT <- translateEntryLRT entry
         lambdaOpenTermTransM "f" (applyOpenTerm
                                   (globalOpenTerm "Prelude.lrtToType")
                                   entryLRT) $ \fvar ->
           helper (bs :>: TypedBlock entries)
           (\(bsTrans :>: TypedBlockTrans eTranss) ->
             f (bsTrans :>:
                TypedBlockTrans (TypedEntryTrans entry (Just fvar):eTranss)))
  helper (bs :>: TypedBlock (entry:entries)) f =
    helper (bs :>: TypedBlock entries)
           (\(bsTrans :>: TypedBlockTrans eTranss) ->
             f (bsTrans :>:
                TypedBlockTrans (TypedEntryTrans entry Nothing:eTranss)))

translateEntryBody :: PermCheckExtC ext =>
                      TypedBlockMapTrans ext blocks ret ->
                      TypedEntry ext blocks ret args ->
                      TypeTransM ctx OpenTerm
translateEntryBody mapTrans (TypedEntry entryID args ret _ in_perms
                             ret_perms stmts) =
  inEmptyCtxTransM $
  lambdaExprCtx (appendCruCtx (entryGhosts entryID) args) $
  lambdaPermCtx (mbDistPermsToValuePerms in_perms) $ \pctx ->
  do retType <- translateRetType ret ret_perms
     impTransM pctx mapTrans retType $ translate stmts


translateBlockMapBodies :: PermCheckExtC ext =>
                           TypedBlockMapTrans ext blocks ret ->
                           TypedBlockMap ext blocks ret ->
                           TypeTransM ctx OpenTerm
translateBlockMapBodies mapTrans =
  trace "translateBlockMapBodies starting..." $
  foldBlockMapSCC
  (\entry restM ->
    pairOpenTerm <$> translateEntryBody mapTrans entry <*> restM)
  (trace "translateBlockMapBodies finished" $ return unitOpenTerm)

-- | Translate a typed CFG to a SAW term
translateCFG :: PermCheckExtC ext => PermEnv ->
                TypedCFG ext blocks ghosts inits ret ->
                OpenTerm
translateCFG env cfg =
  let h = tpcfgHandle cfg
      fun_perm = tpcfgFunPerm cfg
      blkMap = tpcfgBlockMap cfg
      ctx = typedFnHandleAllArgs h
      ghosts = typedFnHandleGhosts h
      retType = typedFnHandleRetType h in
  flip runTransM (TypeTransInfo MNil env) $ lambdaExprCtx ctx $
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
