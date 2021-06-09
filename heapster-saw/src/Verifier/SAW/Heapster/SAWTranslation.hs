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
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}

module Verifier.SAW.Heapster.SAWTranslation where

import Prelude hiding (pi)

import Numeric (showHex)
import Data.Char
import Data.Maybe
import Numeric.Natural
import Data.List hiding (inits)
import Data.Text (pack)
import GHC.TypeLits
import Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import Data.Functor.Compose
import Control.Applicative
import Control.Lens hiding ((:>), Index, ix, op)
import Control.Monad.Reader hiding (ap)
import Control.Monad.Writer hiding (ap)
import Control.Monad.Trans.Maybe
import qualified Data.Vector as V

import What4.ProgramLoc
import What4.Interface (StringLiteral(..))

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits hiding (sym, trans)
import Data.Binding.Hobbits.Liftable ()

import Prettyprinter as PP
import Prettyprinter.Render.String

import Data.Parameterized.TraversableF

import Lang.Crucible.Types
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.DataLayout
import Lang.Crucible.CFG.Expr
import qualified Lang.Crucible.CFG.Expr as Expr
import Lang.Crucible.CFG.Core

import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor
import Verifier.SAW.Module
import Verifier.SAW.SharedTerm

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.Implication
import Verifier.SAW.Heapster.TypedCrucible

import GHC.Stack
import Debug.Trace

scInsertDef :: SharedContext -> ModuleName -> Ident -> Term -> Term -> IO ()
scInsertDef sc mnm ident def_tp def_tm =
  do t <- scConstant' sc (ModuleIdentifier ident) def_tm def_tp
     scRegisterGlobal sc ident t
     scModifyModule sc mnm $ \m ->
       insDef m $ Def { defIdent = ident,
                        defQualifier = NoQualifier,
                        defType = def_tp,
                        defBody = Just def_tm }


----------------------------------------------------------------------
-- * Translation Monads
----------------------------------------------------------------------

-- | Call 'prettyCallStack' and insert a newline in front
nlPrettyCallStack :: CallStack -> String
nlPrettyCallStack = ("\n" ++) . prettyCallStack

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
typeTransType1 :: HasCallStack => TypeTrans tr -> OpenTerm
typeTransType1 (TypeTrans [] _) = unitTypeOpenTerm
typeTransType1 (TypeTrans [tp] _) = tp
typeTransType1 _ = error ("typeTransType1" ++ nlPrettyCallStack callStack)

-- | Build the tuple of @N@ types, with the special case that a single type is
-- just converted to itself
tupleOfTypes :: [OpenTerm] -> OpenTerm
tupleOfTypes [] = unitTypeOpenTerm
tupleOfTypes [tp] = tp
tupleOfTypes tps = tupleTypeOpenTerm tps

-- | Map the 'typeTransTypes' field of a 'TypeTrans' to a single type, where a
-- single type is mapped to itself, an empty list of types is mapped to @unit@,
-- and a list of 2 or more types is mapped to a tuple of the types
typeTransTupleType :: TypeTrans tr -> OpenTerm
typeTransTupleType = tupleOfTypes . typeTransTypes

-- | Convert a 'TypeTrans' over 0 or more types to one over 1 type, where 2
-- or more types are converted to a single tuple type
tupleTypeTrans :: TypeTrans tr -> TypeTrans tr
-- tupleTypeTrans ttrans@(TypeTrans [] _) = ttrans
tupleTypeTrans ttrans@(TypeTrans [_] _) = ttrans
tupleTypeTrans ttrans =
  TypeTrans [tupleTypeOpenTerm $ typeTransTypes ttrans]
  (\[t] -> typeTransF ttrans $ map (\i -> projTupleOpenTerm i t) $
           take (length $ typeTransTypes ttrans) [0..])

-- | Convert a 'TypeTrans' over 0 or more types to one over 1 type of the form
-- @#(tp1, #(tp2, ... #(tpn, #()) ...))@. This is "strict" in the sense that
-- even a single type is tupled.
strictTupleTypeTrans :: TypeTrans tr -> TypeTrans tr
strictTupleTypeTrans ttrans =
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

  -- | LLVM blocks also have no computational content
  ETrans_LLVMBlock :: ExprTrans (LLVMBlockType w)

  -- | Frames also have no computational content
  ETrans_LLVMFrame :: ExprTrans (LLVMFrameType w)

  -- | Lifetimes also have no computational content
  ETrans_Lifetime :: ExprTrans LifetimeType

  -- | Read-write modalities also have no computational content
  ETrans_RWModality :: ExprTrans RWModalityType

  -- | Structs are translated as a sequence of translations of the fields
  ETrans_Struct :: ExprTransCtx (CtxToRList ctx) -> ExprTrans (StructType ctx)

  -- | The computational content of functions is in their FunPerms, so functions
  -- themselves have no computational content
  ETrans_Fun :: ExprTrans (FunctionHandleType args ret)

  -- | The unit type has no computational content
  ETrans_Unit :: ExprTrans UnitType

  -- | The translation for every other expression type is just a SAW term. Note
  -- that this construct should not be used for the types handled above.
  ETrans_Term :: OpenTerm -> ExprTrans a


-- | A context mapping bound names to their type-level SAW translations
type ExprTransCtx = RAssign ExprTrans


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

-- | Build a tuple of the terms contained in a translation. This is "strict" in
-- that it always makes a tuple, even for a single type, unlike
-- 'transTupleTerm'.  If @ttrans@ is a 'TypeTrans' describing the SAW types
-- associated with a @tr@ translation, then this function returns an element of
-- the type @'strictTupleTypeTrans' ttrans@.
strictTransTupleTerm :: IsTermTrans tr => tr -> OpenTerm
strictTransTupleTerm tr = tupleOpenTerm $ transTerms tr

-- | Like 'transTupleTerm' but raise an error if there are more than 1 terms
transTerm1 :: HasCallStack => IsTermTrans tr => tr -> OpenTerm
transTerm1 (transTerms -> []) = unitOpenTerm
transTerm1 (transTerms -> [t]) = t
transTerm1 _ = error ("transTerm1" ++ nlPrettyCallStack callStack)


instance IsTermTrans tr => IsTermTrans [tr] where
  transTerms = concatMap transTerms

instance IsTermTrans (TypeTrans tr) where
  transTerms = typeTransTypes

instance IsTermTrans (ExprTrans tp) where
  transTerms ETrans_LLVM = []
  transTerms ETrans_LLVMBlock = []
  transTerms ETrans_LLVMFrame = []
  transTerms ETrans_Lifetime = []
  transTerms ETrans_RWModality = []
  transTerms (ETrans_Struct etranss) =
    concat $ RL.mapToList transTerms etranss
  transTerms ETrans_Fun = []
  transTerms ETrans_Unit = []
  transTerms (ETrans_Term t) = [t]

instance IsTermTrans (ExprTransCtx ctx) where
  transTerms MNil = []
  transTerms (ctx :>: etrans) = transTerms ctx ++ transTerms etrans


-- | Map a context of expression translations to a list of 'OpenTerm's
exprCtxToTerms :: ExprTransCtx tps -> [OpenTerm]
exprCtxToTerms = concat . RL.mapToList transTerms


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

instance MonadFail (TransM info ctx) where
  fail = error

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

-- | Run a translation computation in context @(ctx1 :++: ctx2) :++: ctx2@ by
-- copying the @ctx2@ portion of the current context
inExtMultiTransCopyLastM :: TransInfo info => prx ctx1 -> RAssign any ctx2 ->
                            TransM info ((ctx1 :++: ctx2) :++: ctx2) a ->
                            TransM info (ctx1 :++: ctx2) a
inExtMultiTransCopyLastM ctx1 ctx2 m =
  do ectx <- infoCtx <$> ask
     let (_,ectx2) = RL.split ctx1 ctx2 ectx
     inExtMultiTransM ectx2 m

-- | Run a translation computation in a specific context
inCtxTransM :: TransInfo info => ExprTransCtx ctx ->
               TransM info ctx a -> TransM info RNil a
inCtxTransM MNil m = m
inCtxTransM (ctx :>: etrans) m = inCtxTransM ctx $ inExtTransM etrans m

-- | Build a multi-binding for the current context
nuMultiTransM :: TransInfo info => (RAssign Name ctx -> b) ->
                 TransM info ctx (Mb ctx b)
nuMultiTransM f =
  do info <- ask
     return $ nuMulti (RL.map (\_ -> Proxy) (infoCtx info)) f

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
  return (lambdaOpenTerm (pack x) tp $ \t -> runTransM (body_f t) info)

-- | Build a nested lambda-abstraction
--
-- > \x1:tp1 -> ... -> \xn:tpn -> body
--
-- over the types in a 'TypeTrans' inside a translation monad, using the
-- 'String' as a variable name prefix for the @xi@ variables
lambdaTrans :: String -> TypeTrans tr -> (tr -> OpenTerm) -> OpenTerm
lambdaTrans x tps body_f =
  lambdaOpenTermMulti
  (zipWith (\i tp -> (pack (x ++ show (i :: Integer)), tp)) [0..] $ typeTransTypes tps)
  (body_f . typeTransF tps)

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
          (zipWith (\i tp -> (pack (x ++ show (i :: Integer)), tp)) [0..] $ typeTransTypes tps)
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
          (zipWith (\i tp -> (pack (x ++ show (i :: Integer)), tp)) [0..] $ typeTransTypes tps)
          (\ts -> runTransM (body_f $ typeTransF tps ts) info))

-- | Build a let-binding in a translation monad
letTransM :: String -> OpenTerm -> TransM info ctx OpenTerm ->
             (OpenTerm -> TransM info ctx OpenTerm) ->
             TransM info ctx OpenTerm
letTransM x tp rhs_m body_m =
  do r <- ask
     return $
       letOpenTerm (pack x) tp (runTransM rhs_m r) (\x' -> runTransM (body_m x') r)

-- | Build a bitvector type in a translation monad
bitvectorTransM :: TransM info ctx OpenTerm -> TransM info ctx OpenTerm
bitvectorTransM m =
  applyMultiTransM (return $ globalOpenTerm "Prelude.Vec")
  [m, return $ globalOpenTerm "Prelude.Bool"]

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
     proj2 <- flip (typeTransF . tupleTypeTrans) [sigma] <$> tp_r proj1
     f proj1 proj2
sigmaElimTransM x tp_l tp_r _tp_ret_m f sigma =
  do let tp_l_trm = typeTransTupleType tp_l
     tp_r_trm <- lambdaTupleTransM x tp_l (\tr ->
                                            typeTransTupleType <$> tp_r tr)
     let proj_l_trm =
           applyOpenTermMulti (globalOpenTerm "Prelude.Sigma_proj1")
           [tp_l_trm, tp_r_trm, sigma]
     let proj_l = typeTransF (tupleTypeTrans tp_l) [proj_l_trm]
     tp_r_app <- tp_r proj_l
     let proj_r_trm =
           applyOpenTermMulti (globalOpenTerm "Prelude.Sigma_proj2")
           [tp_l_trm, tp_r_trm, sigma]
     let proj_r = typeTransF (tupleTypeTrans tp_r_app) [proj_r_trm]
     f proj_l proj_r

{- NOTE: the following is the version that inserts a Sigma__rec
sigmaElimTransM x tp_l tp_r tp_ret_m f sigma =
  do tp_r_trm <- lambdaTupleTransM x tp_l (\tr ->
                                            typeTransTupleType <$> tp_r tr)
     sigma_tp <- sigmaTypeTransM x tp_l tp_r
     tp_ret <- lambdaTransM x (mkTypeTrans1 sigma_tp id)
       (const (typeTransTupleType <$> tp_ret_m))
     f_trm <-
       lambdaTupleTransM (x ++ "_proj1") tp_l $ \x_l ->
       tp_r x_l >>= \tp_r_app ->
       lambdaTupleTransM (x ++ "_proj2") tp_r_app (f x_l)
     return (applyOpenTermMulti (globalOpenTerm "Prelude.Sigma__rec")
             [ typeTransTupleType tp_l, tp_r_trm, tp_ret, f_trm, sigma ])
-}


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
translate1 :: (IsTermTrans tr, Translate info ctx a tr, HasCallStack) =>
              Mb ctx a -> TransM info ctx OpenTerm
translate1 a = translate a >>= \tr -> case transTerms tr of
  [t] -> return t
  ts -> error ("translate1: expected 1 term, found " ++ show (length ts)
               ++ nlPrettyCallStack callStack)

-- | Translate a "closed" term, that is not in a binding
translateClosed :: (TransInfo info, Translate info ctx a tr) =>
                   a -> TransM info ctx tr
translateClosed a = nuMultiTransM (const a) >>= translate


----------------------------------------------------------------------
-- * Translating Types
----------------------------------------------------------------------

-- | Translation info for translating types and pure expressions
data TypeTransInfo ctx = TypeTransInfo (ExprTransCtx ctx) PermEnv

-- | Build an empty 'TypeTransInfo' from a 'PermEnv'
emptyTypeTransInfo :: PermEnv -> TypeTransInfo RNil
emptyTypeTransInfo = TypeTransInfo MNil

instance TransInfo TypeTransInfo where
  infoCtx (TypeTransInfo ctx _) = ctx
  infoEnv (TypeTransInfo _ env) = env
  extTransInfo etrans (TypeTransInfo ctx env) =
    TypeTransInfo (ctx :>: etrans) env

-- | The translation monad specific to translating types and pure expressions
type TypeTransM = TransM TypeTransInfo

-- | Run a 'TypeTransM' computation in the empty translation context
runNilTypeTransM :: TypeTransM RNil a -> PermEnv -> a
runNilTypeTransM m env = runTransM m (emptyTypeTransInfo env)

-- | Run a translation computation in an empty expression translation context
inEmptyCtxTransM :: TypeTransM RNil a -> TypeTransM ctx a
inEmptyCtxTransM =
  withInfoM (\(TypeTransInfo _ env) -> TypeTransInfo MNil env)

instance TransInfo info => Translate info ctx (NatRepr n) OpenTerm where
  translate mb_n = return $ natOpenTerm $ mbLift $ fmap natValue mb_n

-- | Helper for writing the 'Translate' instance for 'TypeRepr'
returnType1 :: OpenTerm -> TransM info ctx (TypeTrans (ExprTrans a))
returnType1 tp = return $ mkTypeTrans1 tp ETrans_Term


-- FIXME: explain this translation
instance TransInfo info =>
         Translate info ctx (TypeRepr a) (TypeTrans (ExprTrans a)) where
  translate mb_tp = case mbMatch mb_tp of
    [nuMP| AnyRepr |] ->
      return $ error "Translate: Any"
    [nuMP| UnitRepr |] ->
      return $ mkTypeTrans0 ETrans_Unit
    [nuMP| BoolRepr |] ->
      returnType1 $ globalOpenTerm "Prelude.Bool"
    [nuMP| NatRepr |] ->
      returnType1 $ dataTypeOpenTerm "Prelude.Nat" []
    [nuMP| IntegerRepr |] ->
      return $ error "translate: IntegerRepr"
    [nuMP| RealValRepr |] ->
      return $ error "translate: RealValRepr"
    [nuMP| ComplexRealRepr |] ->
      return $ error "translate: ComplexRealRepr"
    [nuMP| BVRepr w |] ->
      returnType1 =<< bitvectorTransM (translate w)

    -- Our special-purpose intrinsic types, whose translations do not have
    -- computational content
    [nuMP| LLVMPointerRepr _ |] ->
      return $ mkTypeTrans0 ETrans_LLVM
    [nuMP| LLVMBlockRepr _ |] ->
      return $ mkTypeTrans0 ETrans_LLVMBlock
    [nuMP| LLVMFrameRepr _ |] ->
      return $ mkTypeTrans0 ETrans_LLVMFrame
    [nuMP| LifetimeRepr |] ->
      return $ mkTypeTrans0 ETrans_Lifetime
    [nuMP| PermListRepr |] ->
      returnType1 (sortOpenTerm $ mkSort 0)
    [nuMP| RWModalityRepr |] ->
      return $ mkTypeTrans0 ETrans_RWModality

    -- Permissions and LLVM shapes translate to types
    [nuMP| ValuePermRepr _ |] ->
      returnType1 (sortOpenTerm $ mkSort 0)
    [nuMP| LLVMShapeRepr _ |] ->
      returnType1 (sortOpenTerm $ mkSort 0)

    -- We can't handle any other special-purpose types
    [nuMP| IntrinsicRepr _ _ |] ->
      return $ error "translate: IntrinsicRepr"

    [nuMP| RecursiveRepr _ _ |] ->
      return $ error "translate: RecursiveRepr"
    [nuMP| FloatRepr _ |] ->
      returnType1 $ dataTypeOpenTerm "Prelude.Float" []
    [nuMP| IEEEFloatRepr _ |] ->
      return $ error "translate: IEEEFloatRepr"
    [nuMP| CharRepr |] ->
      return $ error "translate: CharRepr"
    [nuMP| StringRepr UnicodeRepr |] ->
      returnType1 stringTypeOpenTerm
    [nuMP| StringRepr _ |] ->
      return $ error "translate: StringRepr non-unicode"
    [nuMP| FunctionHandleRepr _ _ |] ->
      -- NOTE: function permissions translate to the SAW function, but the
      -- function handle itself has no SAW translation
      return $ mkTypeTrans0 ETrans_Fun
    [nuMP| MaybeRepr _ |] ->
      return $ error "translate: MaybeRepr"
    [nuMP| VectorRepr _ |] ->
      return $ error "translate: VectorRepr (can't map to Vec without size)"
    [nuMP| StructRepr tps |] ->
      fmap ETrans_Struct <$> translate (fmap mkCruCtx tps)
    [nuMP| VariantRepr _ |] ->
      return $ error "translate: VariantRepr"
    [nuMP| ReferenceRepr _ |] ->
      return $ error "translate: ReferenceRepr"
    [nuMP| WordMapRepr _ _ |] ->
      return $ error "translate: WordMapRepr"
    [nuMP| StringMapRepr _ |] ->
      return $ error "translate: StringMapRepr"
    [nuMP| SymbolicArrayRepr _ _ |] ->
      return $ error "translate: SymbolicArrayRepr"
    [nuMP| SymbolicStructRepr _ |] ->
      return $ error "translate: SymbolicStructRepr"


instance TransInfo info =>
         Translate info ctx (CruCtx as) (TypeTrans (ExprTransCtx as)) where
  translate mb_ctx = case mbMatch mb_ctx of
    [nuMP| CruCtxNil |] -> return $ mkTypeTrans0 MNil
    [nuMP| CruCtxCons ctx tp |] ->
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

boolOpenTerm :: Bool -> OpenTerm
boolOpenTerm True = globalOpenTerm "Prelude.True"
boolOpenTerm False = globalOpenTerm "Prelude.False"

-- | Create a SAW core term for a bitvector literal
bvLitOpenTerm :: NatRepr w -> BV w -> OpenTerm
bvLitOpenTerm w bv =
  flatOpenTerm $ ArrayValue (globalOpenTerm "Prelude.Bool") $
  V.fromList (map boolOpenTerm $ BV.asBitsBE w bv)

bvNatOpenTerm :: Natural -> Natural -> OpenTerm
bvNatOpenTerm w n =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvNat")
  [natOpenTerm w, natOpenTerm (n `mod` 2 ^ w)]

bvAddOpenTerm :: Natural -> OpenTerm -> OpenTerm -> OpenTerm
bvAddOpenTerm n x y =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvAdd")
  [natOpenTerm n, x, y]

bvMulOpenTerm :: Natural -> OpenTerm -> OpenTerm -> OpenTerm
bvMulOpenTerm n x y =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvMul")
  [natOpenTerm n, x, y]

-- | Translate a variable to a 'Member' proof, raising an error if the variable
-- is unbound
translateVar :: Mb ctx (ExprVar a) -> Member ctx a
translateVar mb_x | Left memb <- mbNameBoundP mb_x = memb
translateVar _ = error "translateVar: unbound variable!"

-- | Get the 'TypeRepr' of an expression
mbExprType :: KnownRepr TypeRepr a => Mb ctx (PermExpr a) -> TypeRepr a
mbExprType _ = knownRepr

-- | Get the 'TypeRepr' bound by a binding
mbBindingType :: KnownRepr TypeRepr tp => Mb ctx (Binding tp a) -> TypeRepr tp
mbBindingType _ = knownRepr


instance TransInfo info =>
         Translate info ctx (ExprVar a) (ExprTrans a) where
  translate mb_x = RL.get (translateVar mb_x) <$> infoCtx <$> ask

instance TransInfo info =>
         Translate info ctx (PermExpr a) (ExprTrans a) where
  translate mb_tr = case mbMatch mb_tr of
    [nuMP| PExpr_Var x |] -> translate x
    [nuMP| PExpr_Unit |] -> return ETrans_Unit
    [nuMP| PExpr_Bool True |] ->
      return $ ETrans_Term $ globalOpenTerm "Prelude.True"
    [nuMP| PExpr_Bool False |] ->
      return $ ETrans_Term $ globalOpenTerm "Prelude.False"
    [nuMP| PExpr_Nat i |] ->
      return $ ETrans_Term $ natOpenTerm $ mbLift i
    [nuMP| PExpr_String str |] ->
      return $ ETrans_Term $ stringLitOpenTerm $ pack $ mbLift str
    [nuMP| PExpr_BV bvfactors@[] off |] ->
      let w = natRepr3 bvfactors in
      return $ ETrans_Term $ bvLitOpenTerm w $ mbLift off
    [nuMP| PExpr_BV bvfactors (BV.BV 0) |] ->
      let w = natVal3 bvfactors in
      ETrans_Term <$> foldr1 (bvAddOpenTerm w) <$>
      mapM translate (mbList bvfactors)
    [nuMP| PExpr_BV bvfactors off |] ->
      do let w = natRepr3 bvfactors
         bv_transs <- mapM translate $ mbList bvfactors
         return $ ETrans_Term $
           foldr (bvAddOpenTerm $ natValue w) (bvLitOpenTerm w $ mbLift off) bv_transs
    [nuMP| PExpr_Struct args |] ->
      ETrans_Struct <$> translate args
    [nuMP| PExpr_Always |] ->
      return ETrans_Lifetime
    [nuMP| PExpr_LLVMWord _ |] -> return ETrans_LLVM
    [nuMP| PExpr_LLVMOffset _ _ |] -> return ETrans_LLVM
    [nuMP| PExpr_Fun _ |] -> return ETrans_Fun
    [nuMP| PExpr_PermListNil |] -> return $ ETrans_Term unitTypeOpenTerm
    [nuMP| PExpr_PermListCons _ _ p l |] ->
      ETrans_Term <$> (pairTypeOpenTerm <$>
                       (typeTransTupleType <$> translate p) <*>
                       (translate1 l))
    [nuMP| PExpr_RWModality _ |] -> return ETrans_RWModality

    -- LLVM shapes are translated to types
    [nuMP| PExpr_EmptyShape |] -> return $ ETrans_Term unitTypeOpenTerm
    [nuMP| PExpr_NamedShape _ _ nmsh args |] ->
      case mbMatch $ fmap namedShapeBody nmsh of
        [nuMP| DefinedShapeBody _ |] ->
          translate (mbMap2 unfoldNamedShape nmsh args)
        [nuMP| OpaqueShapeBody _ trans_id |] ->
          ETrans_Term <$> applyOpenTermMulti (globalOpenTerm $ mbLift trans_id) <$>
          transTerms <$> translate args
        [nuMP| RecShapeBody _ trans_id _ _ |] ->
          ETrans_Term <$> applyOpenTermMulti (globalOpenTerm $ mbLift trans_id) <$>
          transTerms <$> translate args
    [nuMP| PExpr_EqShape _ |] -> return $ ETrans_Term unitTypeOpenTerm
    [nuMP| PExpr_PtrShape _ _ sh |] -> translate sh
    [nuMP| PExpr_FieldShape fsh |] ->
      ETrans_Term <$> tupleOfTypes <$> translate fsh
    [nuMP| PExpr_ArrayShape mb_len _ mb_fshs |] ->
      do let w = natVal4 mb_len
         let w_term = natOpenTerm w
         len_term <- translate1 mb_len
         elem_tp <- tupleOfTypes <$> concat <$> mapM translate (mbList mb_fshs)
         return $ ETrans_Term $
           applyOpenTermMulti (globalOpenTerm "Prelude.BVVec")
           [w_term, len_term, elem_tp]
    [nuMP| PExpr_SeqShape sh1 sh2 |] ->
      ETrans_Term <$> (pairTypeOpenTerm <$> translate1 sh1 <*> translate1 sh2)
    [nuMP| PExpr_OrShape sh1 sh2 |] ->
      ETrans_Term <$>
      ((\t1 t2 -> dataTypeOpenTerm "Prelude.Either" [t1,t2])
       <$> translate1 sh1 <*> translate1 sh2)
    [nuMP| PExpr_ExShape mb_sh |] ->
      do tp_trans <- translate $ fmap bindingType mb_sh
         tp_f_trm <- lambdaTupleTransM "x_exsh" tp_trans $ \e ->
           transTupleTerm <$> inExtTransM e (translate $ mbCombine RL.typeCtxProxies mb_sh)
         return $ ETrans_Term (dataTypeOpenTerm "Prelude.Sigma"
                               [typeTransTupleType tp_trans, tp_f_trm])

    [nuMP| PExpr_ValPerm p |] ->
      ETrans_Term <$> typeTransTupleType <$> translate p

-- LLVM field shapes translate to the types that the permission they contain
-- translates to
instance TransInfo info =>
         Translate info ctx (LLVMFieldShape w) [OpenTerm] where
  translate (mbMatch -> [nuMP| LLVMFieldShape p |]) = typeTransTypes <$> translate p

instance TransInfo info =>
         Translate info ctx (PermExprs as) (ExprTransCtx as) where
  translate mb_exprs = case mbMatch mb_exprs of
    [nuMP| PExprs_Nil |] -> return MNil
    [nuMP| PExprs_Cons es e |] ->
      (:>:) <$> translate es <*> translate e

instance TransInfo info => Translate info ctx (BVFactor w) OpenTerm where
  translate mb_f = case mbMatch mb_f of
    [nuMP| BVFactor (BV.BV 1) x |] -> translate1 (fmap PExpr_Var x)
    [nuMP| BVFactor i x |] ->
      let w = natRepr4 x in
      bvMulOpenTerm (natValue w) (bvLitOpenTerm w $ mbLift i) <$>
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
-- recursive permissions, however, because our type-checker does not
-- generally introduce these forms as intermediate values.
data PermTrans (ctx :: RList CrucibleType) (a :: CrucibleType) where
  -- | An @eq(e)@ permission has no computational content
  PTrans_Eq :: Mb ctx (PermExpr a) -> PermTrans ctx a

  -- | A conjuction of atomic permission translations
  PTrans_Conj :: [AtomicPermTrans ctx a] -> PermTrans ctx a

  -- | The translation of a defined permission is a wrapper around the
  -- translation of what it is defined as
  PTrans_Defined :: NamedPermName (DefinedSort b) args a ->
                    Mb ctx (PermExprs args) -> Mb ctx (PermOffset a) ->
                    PermTrans ctx a -> PermTrans ctx a

  -- | The translation for disjunctive, existential, and named permissions
  PTrans_Term :: Mb ctx (ValuePerm a) -> OpenTerm -> PermTrans ctx a


-- | The 'PermTrans' type for atomic permissions
data AtomicPermTrans ctx a where

  -- | The translation of an LLVM field permission is just the translation of
  -- its contents
  APTrans_LLVMField :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                       Mb ctx (LLVMFieldPerm w sz) ->
                       PermTrans ctx (LLVMPointerType sz) ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM array permisions are translated to an 'LLVMArrayPermTrans'
  APTrans_LLVMArray :: (1 <= w, KnownNat w) =>
                       LLVMArrayPermTrans ctx w ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | The translation of an LLVM block permission is an element of the
  -- translation of its shape to a type
  APTrans_LLVMBlock :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMBlockPerm w) -> OpenTerm ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM free permissions have no computational content
  APTrans_LLVMFree :: (1 <= w, KnownNat w) =>
                      Mb ctx (PermExpr (BVType w)) ->
                      AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM function pointer permissions have the same computational content as
  -- a function permission
  APTrans_LLVMFunPtr :: (1 <= w, KnownNat w) =>
                        TypeRepr (FunctionHandleType cargs ret) ->
                        PermTrans ctx (FunctionHandleType cargs ret) ->
                        AtomicPermTrans ctx (LLVMPointerType w)

  -- | IsLLVMPtr permissions have no computational content
  APTrans_IsLLVMPtr :: (1 <= w, KnownNat w) =>
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | The translation of an LLVMBlockShape permission is an element of the
  -- translation of its shape to a type
  APTrans_LLVMBlockShape :: (1 <= w, KnownNat w) =>
                            Mb ctx (PermExpr (LLVMShapeType w)) -> OpenTerm ->
                            AtomicPermTrans ctx (LLVMBlockType w)

  -- | Perm_NamedConj permissions are a permission + a term
  APTrans_NamedConj :: NameSortIsConj ns ~ 'True =>
                       NamedPermName ns args a -> Mb ctx (PermExprs args) ->
                       Mb ctx (PermOffset a) -> OpenTerm ->
                       AtomicPermTrans ctx a

  -- | Defined Perm_NamedConj permissions are just a wrapper around the
  -- translation of the permission definition
  APTrans_DefinedNamedConj :: NamedPermName (DefinedSort 'True) args a ->
                              Mb ctx (PermExprs args) ->
                              Mb ctx (PermOffset a) ->
                              PermTrans ctx a ->
                              AtomicPermTrans ctx a

  -- | LLVM frame permissions have no computational content
  APTrans_LLVMFrame :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMFramePerm w) ->
                       AtomicPermTrans ctx (LLVMFrameType w)

  -- | LOwned permissions translate to a monadic function from (the translation
  -- of) the input permissions to the output permissions
  APTrans_LOwned :: Mb ctx (LOwnedPerms ps_in) ->
                    Mb ctx (LOwnedPerms ps_out) ->
                    OpenTerm -> AtomicPermTrans ctx LifetimeType

  -- | LCurrent permissions have no computational content
  APTrans_LCurrent :: Mb ctx (PermExpr LifetimeType) ->
                      AtomicPermTrans ctx LifetimeType

  -- | The translation of a struct permission is sequence of the translations of
  -- the permissions in the struct permission
  APTrans_Struct :: PermTransCtx ctx (CtxToRList args) ->
                    AtomicPermTrans ctx (StructType args)

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

-- | The translation of a 'BVRange' is the translation of its two elements
data BVRangeTrans ctx w =
  BVRangeTrans (Mb ctx (BVRange w))
  (ExprTrans (BVType w)) (ExprTrans (BVType w))

-- | Extract the translation of the offset from the translation of a 'BVRange'
bvRangeTransOff :: BVRangeTrans ctx w -> ExprTrans (BVType w)
bvRangeTransOff (BVRangeTrans _ off _) = off

-- | Extract the translation of the length from the translation of a 'BVRange'
bvRangeTransLen :: BVRangeTrans ctx w -> ExprTrans (BVType w)
bvRangeTransLen (BVRangeTrans _ _ len) = len

-- | The translation of an LLVM array permission is a SAW term of @BVVec@ type,
-- along with a type translation for its fields and proof terms stating that all
-- of the borrows are in the array. Note that the type translation for the
-- fields is always a 'tupleTypeTrans', i.e., has at most one SAW type.
data LLVMArrayPermTrans ctx w = LLVMArrayPermTrans {
  llvmArrayTransPerm :: Mb ctx (LLVMArrayPerm w),
  llvmArrayTransLen :: OpenTerm,
  llvmArrayTransFields :: TypeTrans [AtomicPermTrans ctx (LLVMPointerType w)],
  -- llvmArrayTransBorrows :: [LLVMArrayBorrowTrans ctx w],
  llvmArrayTransTerm :: OpenTerm
  }

-- | The translation of an LLVM array index is the translation of the cell
-- number plus the field number (which is statically known)
data LLVMArrayIndexTrans ctx w =
  LLVMArrayIndexTrans (Mb ctx (PermExpr (BVType w))) OpenTerm Int

-- | Get back the 'LLVMArrayIndex' from an 'LLVMArrayIndexTrans'
llvmArrayIndexUnTrans :: LLVMArrayIndexTrans ctx w -> Mb ctx (LLVMArrayIndex w)
llvmArrayIndexUnTrans (LLVMArrayIndexTrans mb_i _ j) =
  fmap (flip LLVMArrayIndex j) mb_i

-- | The translation of an 'LLVMArrayBorrow' is an element / proof of the
-- translation of the the 'BVProp' returned by 'llvmArrayBorrowInArrayBase'
{-
data LLVMArrayBorrowTrans ctx w =
  LLVMArrayBorrowTrans
  { llvmArrayBorrowTransBorrow :: Mb ctx (LLVMArrayBorrow w),
    llvmArrayBorrowTransProps :: [BVPropTrans ctx w] }
-}

-- | The translation of the vacuously true permission
pattern PTrans_True :: PermTrans ctx a
pattern PTrans_True = PTrans_Conj []

-- | Build a type translation for a disjunctive, existential, or named
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
unPTransLLVMField :: String -> NatRepr sz ->
                     PermTrans ctx (LLVMPointerType w) ->
                     (Mb ctx (LLVMFieldPerm w sz),
                      PermTrans ctx (LLVMPointerType sz))
unPTransLLVMField _ sz (PTrans_Conj [APTrans_LLVMField mb_fp ptrans])
  | Just Refl <- testEquality sz (mbLift $ fmap llvmFieldSize mb_fp)
  = (mb_fp, ptrans)
unPTransLLVMField str _ _ =
  error (str ++ ": not an LLVM field permission of the required size")

-- | Extract the body of a conjunction of a single array permission
unPTransLLVMArray :: String -> PermTrans ctx (LLVMPointerType w) ->
                     LLVMArrayPermTrans ctx w
unPTransLLVMArray _ (PTrans_Conj [APTrans_LLVMArray aptrans]) = aptrans
unPTransLLVMArray str _ = error (str ++ ": not an LLVM array permission")

-- | Add a borrow translation to the translation of an array permission

-- | A context mapping bound names to their perm translations
type PermTransCtx ctx ps = RAssign (PermTrans ctx) ps

-- | Build a permission translation context with just @true@ permissions
truePermTransCtx :: CruCtx ps -> PermTransCtx ctx ps
truePermTransCtx CruCtxNil = MNil
truePermTransCtx (CruCtxCons ctx _) = truePermTransCtx ctx :>: PTrans_True

-- | Build a permission translation context with equality permissions
eqPermTransCtx :: forall (ctx :: RList CrucibleType) (ps :: RList CrucibleType) any.
                  RAssign any ctx -> RAssign (Member ctx) ps ->
                  PermTransCtx ctx ps
eqPermTransCtx ns =
  RL.map (\memb -> PTrans_Eq $ nuMulti (RL.map (\_-> Proxy) ns) (PExpr_Var . RL.get memb))


instance IsTermTrans (PermTrans ctx a) where
  transTerms (PTrans_Eq _) = []
  transTerms (PTrans_Conj aps) = transTerms aps
  transTerms (PTrans_Defined _ _ _ ptrans) = transTerms ptrans
  transTerms (PTrans_Term _ t) = [t]

instance IsTermTrans (PermTransCtx ctx ps) where
  transTerms MNil = []
  transTerms (ctx :>: ptrans) = transTerms ctx ++ transTerms ptrans

instance IsTermTrans (AtomicPermTrans ctx a) where
  transTerms (APTrans_LLVMField _ ptrans) = transTerms ptrans
  transTerms (APTrans_LLVMArray arr_trans) = transTerms arr_trans
  transTerms (APTrans_LLVMBlock _ t) = [t]
  transTerms (APTrans_LLVMFree _) = []
  transTerms (APTrans_LLVMFunPtr _ trans) = transTerms trans
  transTerms APTrans_IsLLVMPtr = []
  transTerms (APTrans_LLVMBlockShape _ t) = [t]
  transTerms (APTrans_NamedConj _ _ _ t) = [t]
  transTerms (APTrans_DefinedNamedConj _ _ _ ptrans) = transTerms ptrans
  transTerms (APTrans_LLVMFrame _) = []
  transTerms (APTrans_LOwned _ _ t) = [t]
  transTerms (APTrans_LCurrent _) = []
  transTerms (APTrans_Struct pctx) = transTerms pctx
  transTerms (APTrans_Fun _ t) = [t]
  transTerms (APTrans_BVProp prop) = transTerms prop

instance IsTermTrans (BVPropTrans ctx w) where
  transTerms (BVPropTrans _ t) = [t]

instance IsTermTrans (BVRangeTrans ctx w) where
  transTerms (BVRangeTrans _ trans1 trans2) =
    transTerms trans1 ++ transTerms trans2

instance IsTermTrans (LLVMArrayPermTrans ctx a) where
  transTerms arr_trans =
    [llvmArrayTransTerm arr_trans] -- : transTerms (llvmArrayTransBorrows arr_trans)

{-
instance IsTermTrans (LLVMArrayBorrowTrans ctx w) where
  transTerms (LLVMArrayBorrowTrans _ prop_transs) = transTerms prop_transs
-}

-- | Map a context of perm translations to a list of 'OpenTerm's, dropping the
-- "invisible" ones whose permissions are translated to 'Nothing'
permCtxToTerms :: PermTransCtx ctx tps -> [OpenTerm]
permCtxToTerms = concat . RL.mapToList transTerms

-- | Extract out the permission of a permission translation result
permTransPerm :: RAssign Proxy ctx -> PermTrans ctx a -> Mb ctx (ValuePerm a)
permTransPerm _ (PTrans_Eq e) = fmap ValPerm_Eq e
permTransPerm prxs (PTrans_Conj ts) =
  fmap ValPerm_Conj $ foldr (mbMap2 (:)) (nuMulti prxs $ const []) $
  map (atomicPermTransPerm prxs) ts
permTransPerm _ (PTrans_Defined npn mb_args mb_off _) =
  mbMap2 (ValPerm_Named npn) mb_args mb_off
permTransPerm _ (PTrans_Term p _) = p

-- | Extract out the atomic permission of an atomic permission translation result
atomicPermTransPerm :: RAssign Proxy ctx -> AtomicPermTrans ctx a ->
                       Mb ctx (AtomicPerm a)
atomicPermTransPerm _ (APTrans_LLVMField fld _) = fmap Perm_LLVMField fld
atomicPermTransPerm _ (APTrans_LLVMArray arr_trans) =
  fmap Perm_LLVMArray $ llvmArrayTransPerm arr_trans
atomicPermTransPerm _ (APTrans_LLVMBlock mb_bp _) = fmap Perm_LLVMBlock mb_bp
atomicPermTransPerm _ (APTrans_LLVMFree e) = fmap Perm_LLVMFree e
atomicPermTransPerm prxs (APTrans_LLVMFunPtr tp ptrans) =
  fmap (Perm_LLVMFunPtr tp) (permTransPerm prxs ptrans)
atomicPermTransPerm prxs APTrans_IsLLVMPtr = nuMulti prxs $ const Perm_IsLLVMPtr
atomicPermTransPerm _ (APTrans_LLVMBlockShape mb_sh _) =
  fmap Perm_LLVMBlockShape mb_sh
atomicPermTransPerm _ (APTrans_NamedConj npn args off _) =
  mbMap2 (Perm_NamedConj npn) args off
atomicPermTransPerm _ (APTrans_DefinedNamedConj npn args off _) =
  mbMap2 (Perm_NamedConj npn) args off
atomicPermTransPerm _ (APTrans_LLVMFrame fp) = fmap Perm_LLVMFrame fp
atomicPermTransPerm _ (APTrans_LOwned ps_in ps_out _) =
  mbMap2 Perm_LOwned ps_in ps_out
atomicPermTransPerm _ (APTrans_LCurrent l) = fmap Perm_LCurrent l
atomicPermTransPerm prxs (APTrans_Struct ps) =
  fmap Perm_Struct $ permTransCtxPerms prxs ps
atomicPermTransPerm _ (APTrans_Fun fp _) = fmap Perm_Fun fp
atomicPermTransPerm _ (APTrans_BVProp (BVPropTrans prop _)) =
  fmap Perm_BVProp prop

-- | Extract out the permissions from a context of permission translations
permTransCtxPerms :: RAssign Proxy ctx -> PermTransCtx ctx ps ->
                     Mb ctx (ValuePerms ps)
permTransCtxPerms prxs MNil = nuMulti prxs $ const ValPerms_Nil
permTransCtxPerms prxs (ptranss :>: ptrans) =
  mbMap2 ValPerms_Cons (permTransCtxPerms prxs ptranss) (permTransPerm prxs ptrans)

-- | Extract out the LLVM borrow from its translation
{-
borrowTransMbBorrow :: LLVMArrayBorrowTrans ctx w -> Mb ctx (LLVMArrayBorrow w)
borrowTransMbBorrow (LLVMArrayBorrowTrans mb_b _) = mb_b
-}

-- | Test that a permission equals that of a permission translation
permTransPermEq :: PermTrans ctx a -> Mb ctx (ValuePerm a) -> Bool
permTransPermEq ptrans mb_p =
  permTransPerm (mbToProxy mb_p) ptrans == mb_p


extsMb :: CruCtx ctx2 -> Mb ctx a -> Mb (ctx :++: ctx2) a
extsMb ctx = mbCombine proxies . fmap (nus proxies . const)
  where
    proxies = cruCtxProxies ctx

-- | Generic function to extend the context of the translation of a permission
class ExtPermTrans f where
  extPermTrans :: f ctx a -> f (ctx :> tp) a

instance ExtPermTrans PermTrans where
  extPermTrans (PTrans_Eq e) = PTrans_Eq $ extMb e
  extPermTrans (PTrans_Conj aps) = PTrans_Conj (map extPermTrans aps)
  extPermTrans (PTrans_Defined n args a ptrans) =
    PTrans_Defined n (extMb args) (extMb a) (extPermTrans ptrans)
  extPermTrans (PTrans_Term p t) = PTrans_Term (extMb p) t

instance ExtPermTrans AtomicPermTrans where
  extPermTrans (APTrans_LLVMField fld ptrans) =
    APTrans_LLVMField (extMb fld) (extPermTrans ptrans)
  extPermTrans (APTrans_LLVMArray arr_trans) =
    APTrans_LLVMArray $ extPermTrans arr_trans
  extPermTrans (APTrans_LLVMBlock mb_bp t) = APTrans_LLVMBlock (extMb mb_bp) t
  extPermTrans (APTrans_LLVMFree e) = APTrans_LLVMFree $ extMb e
  extPermTrans (APTrans_LLVMFunPtr tp ptrans) =
    APTrans_LLVMFunPtr tp (extPermTrans ptrans)
  extPermTrans APTrans_IsLLVMPtr = APTrans_IsLLVMPtr
  extPermTrans (APTrans_LLVMBlockShape mb_sh t) =
    APTrans_LLVMBlockShape (extMb mb_sh) t
  extPermTrans (APTrans_NamedConj npn args off t) =
    APTrans_NamedConj npn (extMb args) (extMb off) t
  extPermTrans (APTrans_DefinedNamedConj npn args off ptrans) =
    APTrans_DefinedNamedConj npn (extMb args) (extMb off) (extPermTrans ptrans)
  extPermTrans (APTrans_LLVMFrame fp) = APTrans_LLVMFrame $ extMb fp
  extPermTrans (APTrans_LOwned ps_in ps_out t) =
    APTrans_LOwned (extMb ps_in) (extMb ps_out) t
  extPermTrans (APTrans_LCurrent p) = APTrans_LCurrent $ extMb p
  extPermTrans (APTrans_Struct ps) = APTrans_Struct $ RL.map extPermTrans ps
  extPermTrans (APTrans_Fun fp t) = APTrans_Fun (extMb fp) t
  extPermTrans (APTrans_BVProp prop_trans) =
    APTrans_BVProp $ extPermTrans prop_trans

instance ExtPermTrans LLVMArrayPermTrans where
  extPermTrans (LLVMArrayPermTrans ap len flds {- bs -} t) =
    LLVMArrayPermTrans (extMb ap) len (fmap (map extPermTrans) flds)
    {- (map extPermTrans bs) -} t

{-
instance ExtPermTrans LLVMArrayBorrowTrans where
  extPermTrans (LLVMArrayBorrowTrans mb_b prop_transs) =
    LLVMArrayBorrowTrans (extMb mb_b) (map extPermTrans prop_transs)
-}

instance ExtPermTrans BVPropTrans where
  extPermTrans (BVPropTrans prop t) = BVPropTrans (extMb prop) t

instance ExtPermTrans BVRangeTrans where
  extPermTrans (BVRangeTrans rng t1 t2) = BVRangeTrans (extMb rng) t1 t2

-- | Extend the context of a permission translation context
extPermTransCtx :: PermTransCtx ctx ps -> PermTransCtx (ctx :> tp) ps
extPermTransCtx = RL.map extPermTrans

-- | Add another permission translation to a permission translation context
consPermTransCtx :: PermTransCtx ctx ps -> PermTrans ctx a ->
                    PermTransCtx ctx (ps :> a)
consPermTransCtx = (:>:)

-- | Apply 'offsetLLVMAtomicPerm' to the permissions associated with an atomic
-- permission translation, returning 'Nothing' if the offset does not exist
offsetLLVMAtomicPermTrans :: (1 <= w, KnownNat w) => Mb ctx (PermExpr (BVType w)) ->
                             AtomicPermTrans ctx (LLVMPointerType w) ->
                             Maybe (AtomicPermTrans ctx (LLVMPointerType w))
offsetLLVMAtomicPermTrans mb_off ptrans
  | [nuMP| Just 0 |] <- mbMatch $ fmap bvMatchConstInt mb_off = Just ptrans
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMField fld ptrans) =
  Just $ APTrans_LLVMField (mbMap2 offsetLLVMFieldPerm mb_off fld) ptrans
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMArray
                                  (LLVMArrayPermTrans ap len flds {- bs -} t)) =
  Just $ APTrans_LLVMArray $
  LLVMArrayPermTrans (mbMap2 offsetLLVMArrayPerm mb_off ap) len flds {- bs -} t
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMBlock mb_bp t) =
  Just $ APTrans_LLVMBlock
  (mbMap2 (\off bp ->
            bp { llvmBlockOffset =
                   bvAdd (llvmBlockOffset bp) off } ) mb_off mb_bp)
  t
offsetLLVMAtomicPermTrans _ (APTrans_LLVMFree _) = Nothing
offsetLLVMAtomicPermTrans _ (APTrans_LLVMFunPtr _ _) = Nothing
offsetLLVMAtomicPermTrans _ p@APTrans_IsLLVMPtr = Just p
offsetLLVMAtomicPermTrans off (APTrans_NamedConj npn args off' t) =
  Just $ APTrans_NamedConj npn args (mbMap2 addPermOffsets off' $
                                     fmap mkLLVMPermOffset off) t
offsetLLVMAtomicPermTrans off (APTrans_DefinedNamedConj npn args off' ptrans) =
  Just $ APTrans_DefinedNamedConj npn args (mbMap2 addPermOffsets off' $
                                            fmap mkLLVMPermOffset off)
  (offsetLLVMPermTrans off ptrans)
offsetLLVMAtomicPermTrans _ _ = Nothing

-- | Apply 'offsetLLVMPerm' to the permissions associated with a permission
-- translation
offsetLLVMPermTrans :: (1 <= w, KnownNat w) => Mb ctx (PermExpr (BVType w)) ->
                       PermTrans ctx (LLVMPointerType w) ->
                       PermTrans ctx (LLVMPointerType w)
offsetLLVMPermTrans mb_off (PTrans_Eq mb_e) =
  PTrans_Eq $ mbMap2 (\off e -> addLLVMOffset e (bvNegate off)) mb_off mb_e
offsetLLVMPermTrans mb_off (PTrans_Conj ps) =
  PTrans_Conj $ mapMaybe (offsetLLVMAtomicPermTrans mb_off) ps
offsetLLVMPermTrans mb_off (PTrans_Defined n args off ptrans) =
  PTrans_Defined n args (mbMap2 addPermOffsets off
                         (fmap mkLLVMPermOffset mb_off)) ptrans
offsetLLVMPermTrans mb_off (PTrans_Term mb_p t) =
  PTrans_Term (mbMap2 offsetLLVMPerm mb_off mb_p) t

-- | Apply 'offsetPerm' to the permissions associated with a permission
-- translation
offsetPermTrans :: Mb ctx (PermOffset a) -> PermTrans ctx a -> PermTrans ctx a
offsetPermTrans mb_off = case mbMatch mb_off of
  [nuMP| NoPermOffset |] -> id
  [nuMP| LLVMPermOffset off |] -> offsetLLVMPermTrans off

-- | Get the SAW type of the cells (= lists of fields) of the translation of an
-- LLVM array permission
llvmArrayTransCellType :: LLVMArrayPermTrans ctx w -> OpenTerm
llvmArrayTransCellType = typeTransType1 . llvmArrayTransFields

{-
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
-}

-- | Read an array cell (= list of fields) of the translation of an LLVM array
-- permission at a given index, given proofs of the propositions that the index
-- is in the array as returned by 'llvmArrayIndexInArray'. Note that the first
-- proposition should always be that the cell number is <= the array length.
getLLVMArrayTransCell :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                         LLVMArrayIndexTrans ctx w -> [BVPropTrans ctx w] ->
                         [AtomicPermTrans ctx (LLVMPointerType w)]
getLLVMArrayTransCell arr_trans ix@(LLVMArrayIndexTrans _ i_trans _)
  (BVPropTrans _ in_rng_term:_) =
  let w = fromInteger $ natVal arr_trans in
  mapMaybe (offsetLLVMAtomicPermTrans $
            mbMap2 (\ap ix' ->
                     bvAdd (llvmArrayOffset ap) (llvmArrayIndexByteOffset ap ix'))
            (llvmArrayTransPerm arr_trans) (llvmArrayIndexUnTrans ix)) $
  typeTransF (llvmArrayTransFields arr_trans)
  [applyOpenTermMulti (globalOpenTerm "Prelude.atBVVec")
   [natOpenTerm w, llvmArrayTransLen arr_trans,
    llvmArrayTransCellType arr_trans, llvmArrayTransTerm arr_trans,
    i_trans, in_rng_term]]
getLLVMArrayTransCell _ _ [] =
  error "getLLVMArrayTransCell: first proposition is not a BVProp"

{-
-- | Write an array cell (= list of fields) of the translation of an LLVM array
-- permission at a given index, given proofs of the propositions that the index
-- is in the array
setLLVMArrayTransCell :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                         LLVMArrayIndexTrans ctx w -> [BVPropTrans ctx w] ->
                         [AtomicPermTrans ctx (LLVMPointerType w)] ->
                         LLVMArrayPermTrans ctx w
setLLVMArrayTransCell arr_trans (LLVMArrayIndexTrans _ i_trans _)
  (BVPropTrans _ in_rng_term:_) cell =
  let w = fromInteger $ natVal arr_trans in
  arr_trans {
    llvmArrayTransTerm =
        applyOpenTermMulti (globalOpenTerm "Prelude.updBVVec")
        [natOpenTerm w, llvmArrayTransLen arr_trans,
         llvmArrayTransCellType arr_trans, llvmArrayTransTerm arr_trans,
         i_trans, in_rng_term, transTupleTerm cell] }
-}

-- | Adjust an array cell (= list of fields) of the translation of an LLVM array
-- permission at a given index by applying a function to it
adjustLLVMArrayTransCell :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                            OpenTerm ->  LLVMArrayIndexTrans ctx w ->
                            LLVMArrayPermTrans ctx w
adjustLLVMArrayTransCell arr_trans f_trm (LLVMArrayIndexTrans _ i_trans _) =
  let w = fromInteger $ natVal arr_trans in
  arr_trans {
    llvmArrayTransTerm =
        applyOpenTermMulti (globalOpenTerm "Prelude.adjustBVVec")
        [natOpenTerm w, llvmArrayTransLen arr_trans,
         llvmArrayTransCellType arr_trans, llvmArrayTransTerm arr_trans,
         f_trm, i_trans] }

-- | Read a field (= element of a cell) of the translation of an LLVM array
-- permission at a given index, given proofs of the propositions that the index
-- is in the array
getLLVMArrayTransField :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          LLVMArrayIndexTrans ctx w -> [BVPropTrans ctx w] ->
                          AtomicPermTrans ctx (LLVMPointerType w)
getLLVMArrayTransField arr_trans ix_trans@(LLVMArrayIndexTrans
                                           _ _ j) prop_transs =
  let cell = getLLVMArrayTransCell arr_trans ix_trans prop_transs in
  if j < length cell then cell !! j else
    error "getLLVMArrayTransField: index too large"

-- | Write a field (= element of a cell) of the translation of an LLVM array
-- permission at a given index
setLLVMArrayTransField :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          LLVMArrayIndexTrans ctx w ->
                          AtomicPermTrans ctx (LLVMPointerType w) ->
                          LLVMArrayPermTrans ctx w
setLLVMArrayTransField arr_trans ix_trans fld =
  let LLVMArrayIndexTrans _ _ j = ix_trans in
  let f_trm =
        lambdaTrans "fld" (llvmArrayTransFields arr_trans)
        (transTupleTerm . replaceNth j fld) in
  adjustLLVMArrayTransCell arr_trans f_trm ix_trans

{-
-- | Write a field (= element of a cell) of the translation of an LLVM array
-- permission at a given index, given proofs of the propositions that the index
-- is in the array
setLLVMArrayTransField :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          LLVMArrayIndexTrans ctx w -> [BVPropTrans ctx w] ->
                          AtomicPermTrans ctx (LLVMPointerType w) ->
                          LLVMArrayPermTrans ctx w
setLLVMArrayTransField arr_trans ix_trans@(LLVMArrayIndexTrans
                                           _ _ j) prop_transs fld' =
  let flds = getLLVMArrayTransCell arr_trans ix_trans prop_transs in
  setLLVMArrayTransCell arr_trans ix_trans prop_transs
  (replaceNth j fld' flds)
-}

-- | Read a slice (= a sub-array) of the translation of an LLVM array permission
-- for the supplied 'BVRange', given the translation of the sub-array permission
-- and proofs of the propositions that the 'BVRange' is in the array as returned
-- by 'llvmArrayCellsInArray'. Note that the first two of these propositions are
-- those returned by 'bvPropRangeSubset'.
getLLVMArrayTransSlice :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          TypeTrans (LLVMArrayPermTrans ctx w) ->
                          BVRangeTrans ctx w -> [BVPropTrans ctx w] ->
                          LLVMArrayPermTrans ctx w
getLLVMArrayTransSlice arr_trans sub_arr_tp rng_trans prop_transs =
  let w = fromInteger $ natVal arr_trans
      _mb_ap = llvmArrayTransPerm arr_trans
      elem_tp = llvmArrayTransCellType arr_trans
      len_tm = llvmArrayTransLen arr_trans
      v_tm = llvmArrayTransTerm arr_trans
      off_tm = transTerm1 $ bvRangeTransOff rng_trans
      len'_tm = transTerm1 $ bvRangeTransLen rng_trans
      p1_trans:p2_trans:_ = prop_transs
      BVPropTrans _ p1_tm = p1_trans
      BVPropTrans _ p2_tm = p2_trans in
  typeTransF sub_arr_tp
  [applyOpenTermMulti
   (globalOpenTerm "Prelude.sliceBVVec")
   [natOpenTerm w, len_tm, elem_tp, off_tm, len'_tm, p1_tm, p2_tm, v_tm]]

-- | Write a slice (= a sub-array) of the translation of an LLVM array
-- permission given the translation of the slice and of the offset of that slice
-- in the larger array
setLLVMArrayTransSlice :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          LLVMArrayPermTrans ctx w -> OpenTerm ->
                          LLVMArrayPermTrans ctx w
setLLVMArrayTransSlice arr_trans sub_arr_trans off_tm =
  let w = fromInteger $ natVal arr_trans
      _mb_ap = llvmArrayTransPerm arr_trans
      elem_tp = llvmArrayTransCellType arr_trans
      len_tm = llvmArrayTransLen arr_trans
      arr_tm = llvmArrayTransTerm arr_trans
      len'_tm = llvmArrayTransLen sub_arr_trans
      sub_arr_tm = llvmArrayTransTerm sub_arr_trans in
  arr_trans
  { llvmArrayTransTerm =
      applyOpenTermMulti
      (globalOpenTerm "Prelude.updSliceBVVec")
      [natOpenTerm w, len_tm, elem_tp, arr_tm, off_tm, len'_tm, sub_arr_tm] }


instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (BVProp w) (TypeTrans (BVPropTrans ctx w)) where
  translate prop = case mbMatch prop of
    [nuMP| BVProp_Eq e1 e2 |] ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         return $ flip mkTypeTrans1 (BVPropTrans prop) $
           (dataTypeOpenTerm "Prelude.Eq"
            [applyOpenTermMulti (globalOpenTerm "Prelude.Vec")
              [natOpenTerm w,
               globalOpenTerm "Prelude.Bool"],
             t1, t2])

    [nuMP| BVProp_Neq _ _ |] ->
      -- NOTE: we don't need a proof object for not equal proofs, because we don't
      -- actually use them for anything, but it is easier to just have all BVProps
      -- be represented as something, so we use the unit type
      return $ mkTypeTrans1 unitTypeOpenTerm (BVPropTrans prop)

    [nuMP| BVProp_ULt e1 e2 |] ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         return $ flip mkTypeTrans1 (BVPropTrans prop)
           (dataTypeOpenTerm "Prelude.Eq"
            [globalOpenTerm "Prelude.Bool",
             applyOpenTermMulti (globalOpenTerm "Prelude.bvult")
             [natOpenTerm w, t1, t2],
             trueOpenTerm])

    [nuMP| BVProp_ULeq e1 e2 |] ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         return $ flip mkTypeTrans1 (BVPropTrans prop)
           (dataTypeOpenTerm "Prelude.Eq"
            [globalOpenTerm "Prelude.Bool",
             applyOpenTermMulti (globalOpenTerm "Prelude.bvule")
             [natOpenTerm w, t1, t2],
             trueOpenTerm])

    [nuMP| BVProp_ULeq_Diff e1 e2 e3 |] ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         t3 <- translate1 e3
         return $ flip mkTypeTrans1 (BVPropTrans prop)
           (dataTypeOpenTerm "Prelude.Eq"
            [globalOpenTerm "Prelude.Bool",
             applyOpenTermMulti (globalOpenTerm "Prelude.bvule")
             [natOpenTerm w, t1,
              applyOpenTermMulti (globalOpenTerm "Prelude.bvSub")
              [natOpenTerm w, t2, t3]],
             trueOpenTerm])

instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (BVRange w) (BVRangeTrans ctx w) where
  translate rng@(mbMatch -> [nuMP| BVRange off len |]) =
    do off_tm <- translate off
       len_tm <- translate len
       return $ BVRangeTrans rng off_tm len_tm

instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (LLVMArrayIndex w) (LLVMArrayIndexTrans ctx w) where
  translate (mbMatch -> [nuMP| LLVMArrayIndex mb_i mb_j |]) =
    LLVMArrayIndexTrans mb_i <$> translate1 mb_i <*> return (mbLift mb_j)

-- [| p :: ValuePerm |] = type of the impl translation of reg with perms p
instance TransInfo info =>
         Translate info ctx (ValuePerm a) (TypeTrans (PermTrans ctx a)) where
  translate p = case mbMatch p of
    [nuMP| ValPerm_Eq e |] -> return $ mkTypeTrans0 $ PTrans_Eq e
    [nuMP| ValPerm_Or p1 p2 |] ->
      do tp1 <- translate p1
         tp2 <- translate p2
         return $ mkPermTypeTrans1 p (eitherTypeTrans tp1 tp2)
    [nuMP| ValPerm_Exists p1 |] ->
      do let tp = mbBindingType p1
         tp_trans <- translateClosed tp
         mkPermTypeTrans1 p <$>
           sigmaTypeTransM "x_ex" tp_trans (\x -> inExtTransM x $
                                                  translate $ mbCombine RL.typeCtxProxies p1)
    [nuMP| ValPerm_Named npn args off |] ->
      do env <- infoEnv <$> ask
         args_trans <- translate args
         case lookupNamedPerm env (mbLift npn) of
           Just (NamedPerm_Opaque op) ->
             return $ mkPermTypeTrans1 p (applyOpenTermMulti
                                          (globalOpenTerm $ opaquePermTrans op)
                                          (transTerms args_trans))
           Just (NamedPerm_Rec rp) ->
             return $ mkPermTypeTrans1 p (applyOpenTermMulti
                                          (globalOpenTerm $ recPermTransType rp)
                                          (transTerms args_trans))
           Just (NamedPerm_Defined dp) ->
             fmap (PTrans_Defined (mbLift npn) args off) <$>
             translate (mbMap2 (unfoldDefinedPerm dp) args off)
           Nothing -> error "Unknown permission name!"
    [nuMP| ValPerm_Conj ps |] ->
      fmap PTrans_Conj <$> listTypeTrans <$> mapM translate (mbList ps)
    [nuMP| ValPerm_Var x _ |] ->
      mkPermTypeTrans1 p <$> translate1 x

instance TransInfo info =>
         Translate info ctx (AtomicPerm a) (TypeTrans
                                            (AtomicPermTrans ctx a)) where
  translate mb_p = case mbMatch mb_p of
    [nuMP| Perm_LLVMField fld |] ->
      fmap (APTrans_LLVMField fld) <$> translate (fmap llvmFieldContents fld)

    [nuMP| Perm_LLVMArray ap |] ->
      fmap APTrans_LLVMArray <$> translate ap

    [nuMP| Perm_LLVMBlock bp |] ->
      do tp <- translate1 (fmap llvmBlockShape bp)
         return $ mkTypeTrans1 tp (APTrans_LLVMBlock bp)

    [nuMP| Perm_LLVMFree e |] ->
      return $ mkTypeTrans0 $ APTrans_LLVMFree e
    [nuMP| Perm_LLVMFunPtr tp p |] ->
      translate p >>= \tp_ptrans ->
      return $ fmap (APTrans_LLVMFunPtr $ mbLift tp) tp_ptrans
    [nuMP| Perm_IsLLVMPtr |] ->
      return $ mkTypeTrans0 APTrans_IsLLVMPtr
    [nuMP| Perm_LLVMBlockShape sh |] ->
      do tp <- translate1 sh
         return $ mkTypeTrans1 tp (APTrans_LLVMBlockShape sh)
    [nuMP| Perm_NamedConj npn args off |]
      | [nuMP| DefinedSortRepr _ |] <- mbMatch $ fmap namedPermNameSort npn ->
        -- To translate P<args>@off as an atomic permission, we translate it as a
        -- normal permission and map the resulting PermTrans to an AtomicPermTrans
        do tptrans <- translate $ mbMap2 (ValPerm_Named $ mbLift npn) args off
           return $ fmap (APTrans_DefinedNamedConj (mbLift npn) args off) tptrans
    [nuMP| Perm_NamedConj npn args off |] ->
      -- To translate P<args>@off as an atomic permission, we translate it as a
      -- normal permission and map the resulting PermTrans to an AtomicPermTrans
      do ptrans <- translate $ mbMap2 (ValPerm_Named $ mbLift npn) args off
         return $ fmap (\(PTrans_Term _ t) ->
                         APTrans_NamedConj (mbLift npn) args off t) ptrans
    [nuMP| Perm_LLVMFrame fp |] ->
      return $ mkTypeTrans0 $ APTrans_LLVMFrame fp
    [nuMP| Perm_LOwned ps_in ps_out |] ->
      do tp_in <- translate1 ps_in
         tp_out <- translate1 ps_out
         let tp = arrowOpenTerm "ps" tp_in (applyOpenTerm
                                            (globalOpenTerm "Prelude.CompM")
                                            tp_out)
         return $ mkTypeTrans1 tp (APTrans_LOwned ps_in ps_out)
    [nuMP| Perm_LCurrent l |] ->
      return $ mkTypeTrans0 $ APTrans_LCurrent l
    [nuMP| Perm_Struct ps |] ->
      fmap APTrans_Struct <$> translate ps
    [nuMP| Perm_Fun fun_perm |] ->
      translate fun_perm >>= \tp_term ->
      return $ mkTypeTrans1 tp_term (APTrans_Fun fun_perm)
    [nuMP| Perm_BVProp prop |] ->
      fmap APTrans_BVProp <$> translate prop

-- | Translate an array permission to a 'TypeTrans' for an array permission
-- translation, also returning the translations of the bitvector width as a
-- natural, the length of the array as a bitvector, and the type of the elements
-- of the translation of the array
translateLLVMArrayPerm :: (1 <= w, KnownNat w, TransInfo info) =>
                          Mb ctx (LLVMArrayPerm w) ->
                          TransM info ctx (OpenTerm,OpenTerm,OpenTerm,
                                           TypeTrans (LLVMArrayPermTrans ctx w))
translateLLVMArrayPerm mb_ap =
  do let w = natVal2 mb_ap
     let w_term = natOpenTerm w
     let mb_len = fmap llvmArrayLen mb_ap
     let mb_flds = fmap llvmArrayFields mb_ap
     flds_trans <-
       tupleTypeTrans <$> listTypeTrans <$>
       mapM (translate . fmap llvmArrayFieldToAtomicPerm) (mbList mb_flds)
     len_term <- translate1 mb_len
     let elem_tp = typeTransType1 flds_trans
     {-
     bs_trans <-
       listTypeTrans <$> mapM (translateLLVMArrayBorrow ap) (mbList bs) -}
     let arr_tp =
           applyOpenTermMulti (globalOpenTerm "Prelude.BVVec")
           [w_term, len_term, elem_tp]
     return (w_term, len_term, elem_tp,
             mkTypeTrans1 arr_tp ({- flip $ -}
                                  LLVMArrayPermTrans mb_ap len_term flds_trans)
             {- <*> bs_trans -} )

instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (LLVMArrayPerm w) (TypeTrans
                                               (LLVMArrayPermTrans ctx w)) where
  translate mb_ap =
    (\(_,_,_,tp_trans) -> tp_trans) <$> translateLLVMArrayPerm mb_ap

{-
-- | Translate an 'LLVMArrayBorrow' into an 'LLVMArrayBorrowTrans'. This
-- requires a special-purpose function, instead of the 'Translate' class,
-- because it requires the array permission.
translateLLVMArrayBorrow :: (1 <= w, KnownNat w, TransInfo info) =>
                            Mb ctx (LLVMArrayPerm w) ->
                            Mb ctx (LLVMArrayBorrow w) ->
                            TransM info ctx (TypeTrans
                                             (LLVMArrayBorrowTrans ctx w))
translateLLVMArrayBorrow mb_ap mb_b =
  do let mb_props = mbMap2 llvmArrayBorrowInArrayBase mb_ap mb_b
     prop_trans <- mapM translate $ mbList mb_props
     return (LLVMArrayBorrowTrans mb_b <$> listTypeTrans prop_trans)
-}

instance TransInfo info =>
         Translate info ctx (ValuePerms ps) (TypeTrans
                                             (PermTransCtx ctx ps)) where
  translate mb_ps = case mbMatch mb_ps of
    [nuMP| ValPerms_Nil |] -> return $ mkTypeTrans0 MNil
    [nuMP| ValPerms_Cons ps p |] ->
      liftA2 (:>:) <$> translate ps <*> translate p

-- Translate a DistPerms by translating its corresponding ValuePerms
instance TransInfo info =>
         Translate info ctx (DistPerms ps) (TypeTrans
                                            (PermTransCtx ctx ps)) where
  translate = translate . mbDistPermsToValuePerms

instance TransInfo info =>
         Translate info ctx (TypedDistPerms ps) (TypeTrans
                                                 (PermTransCtx ctx ps)) where
  translate = translate . mbDistPermsToValuePerms . fmap unTypeDistPerms

-- LOwnedPerms translate to a single tuple type, because lowned permissions
-- translate to functions with one argument and one return value
instance TransInfo info =>
         Translate info ctx (LOwnedPerms ps) (TypeTrans
                                              (PermTransCtx ctx ps)) where
  translate =
    fmap strictTupleTypeTrans . translate . fmap (RL.map lownedPermPerm)

-- Translate a FunPerm to a pi-abstraction (FIXME: more documentation!)
instance TransInfo info =>
         Translate info ctx (FunPerm ghosts args ret) OpenTerm where
  translate (mbMatch -> [nuMP| FunPerm ghosts args ret perms_in perms_out |]) =
    let ctx = appendCruCtx (mbLift ghosts) (mbLift args)
        pxys = cruCtxProxies ctx in
    piExprCtx ctx $
    piPermCtx (mbCombine pxys perms_in) $ \_ ->
    applyTransM (return $ globalOpenTerm "Prelude.CompM") $
    translateRetType (mbLift ret) $ mbCombine (pxys :>: Proxy) perms_out

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
                    Mb (ctx :> ret) (ValuePerms ps) ->
                    TransM info ctx OpenTerm
translateRetType ret ret_perms =
  do tptrans <- translateClosed ret
     sigmaTypeTransM "ret" tptrans (\etrans ->
                                     inExtTransM etrans $ translate ret_perms)

-- | Build the return type for the function resulting from an entrypoint
translateEntryRetType :: TransInfo info =>
                         TypedEntry phase ext blocks tops ret args ghosts ->
                         TransM info ((tops :++: args) :++: ghosts) OpenTerm
translateEntryRetType (TypedEntry {..}) =
  let mb_perms_out =
        mbCombine RL.typeCtxProxies $
        extMbMulti (cruCtxProxies typedEntryGhosts) $
        extMbMulti (cruCtxProxies typedEntryArgs) $
        mbSeparate (MNil :>: Proxy) typedEntryPermsOut in
  translateRetType typedEntryRet mb_perms_out


----------------------------------------------------------------------
-- * The Implication Translation Monad
----------------------------------------------------------------------

-- | A mapping from a block entrypoint to a corresponding SAW variable that is
-- bound to its translation if it has one: only those entrypoints marked as the
-- heads of strongly-connect components have translations as letrec-bound
-- variables
data TypedEntryTrans ext blocks tops ret args ghosts =
  TypedEntryTrans { typedEntryTransEntry ::
                      TypedEntry TransPhase ext blocks tops ret args ghosts,
                    typedEntryTransFun :: Maybe OpenTerm }

-- | A mapping from a block to the SAW functions for each entrypoint
data TypedBlockTrans ext blocks tops ret args =
  TypedBlockTrans { typedBlockTransEntries ::
                      [Some (TypedEntryTrans ext blocks tops ret args)] }

-- | A mapping from all block entrypoints to their SAW translations
type TypedBlockMapTrans ext blocks tops ret =
  RAssign (TypedBlockTrans ext blocks tops ret) blocks

-- | Look up the translation of an entry by entry ID
lookupEntryTrans :: TypedEntryID blocks args ->
                    TypedBlockMapTrans ext blocks tops ret ->
                    Some (TypedEntryTrans ext blocks tops ret args)
lookupEntryTrans entryID blkMap =
  typedBlockTransEntries (RL.get (entryBlockID entryID) blkMap) !!
  entryIndex entryID

-- | Look up the translation of an entry by entry ID and make sure that it has
-- the supplied ghost arguments
lookupEntryTransCast :: TypedEntryID blocks args -> CruCtx ghosts ->
                        TypedBlockMapTrans ext blocks tops ret ->
                        TypedEntryTrans ext blocks tops ret args ghosts
lookupEntryTransCast entryID ghosts blkMap
  | Some entry_trans <- lookupEntryTrans entryID blkMap
  , Just Refl <- testEquality ghosts (typedEntryGhosts $
                                      typedEntryTransEntry entry_trans)
  = entry_trans
lookupEntryTransCast _ _ _ =
  error "lookupEntryTransCast: incorrect ghosts argument"

-- | A 'TypedCallSite' with existentially quantified ghost variables
data SomeTypedCallSite blocks tops args vars =
  forall ghosts.
  SomeTypedCallSite (TypedCallSite TransPhase blocks tops args ghosts vars)

-- | Look up a call site by id in a 'TypedBlockMapTrans'
lookupCallSite :: TypedCallSiteID blocks args vars ->
                  TypedBlockMapTrans ext blocks tops ret ->
                  SomeTypedCallSite blocks tops args vars
lookupCallSite siteID blkMap
  | Some entry_trans <- lookupEntryTrans (callSiteDest siteID) blkMap
  , Just site <- typedEntryCallerSite siteID (typedEntryTransEntry entry_trans)
  = SomeTypedCallSite site
lookupCallSite siteID blkMap
  | Some entry_trans <- lookupEntryTrans (callSiteDest siteID) blkMap =
    error ("lookupCallSite: no call site for site ID: " ++ show siteID ++
           "\n" ++ "call sites for entrypoint: " ++
           show (map (\(Some site) -> show $ typedCallSiteID site)
                 (typedEntryCallers $ typedEntryTransEntry entry_trans)))


-- | Contextual info for an implication translation
data ImpTransInfo ext blocks tops ret ps ctx =
  ImpTransInfo
  {
    itiExprCtx :: ExprTransCtx ctx,
    itiPermCtx :: PermTransCtx ctx ctx,
    itiPermStack :: PermTransCtx ctx ps,
    itiPermStackVars :: RAssign (Member ctx) ps,
    itiPermEnv :: PermEnv,
    itiBlockMapTrans :: TypedBlockMapTrans ext blocks tops ret,
    itiReturnType :: OpenTerm
  }

instance TransInfo (ImpTransInfo ext blocks tops ret ps) where
  infoCtx = itiExprCtx
  infoEnv = itiPermEnv
  extTransInfo etrans (ImpTransInfo {..}) =
    ImpTransInfo
    { itiExprCtx = itiExprCtx :>: etrans
    , itiPermCtx = consPermTransCtx (extPermTransCtx itiPermCtx) PTrans_True
    , itiPermStack = extPermTransCtx itiPermStack
    , itiPermStackVars = RL.map Member_Step itiPermStackVars
    , .. }


-- | The monad for translating permission implications
type ImpTransM ext blocks tops ret ps =
  TransM (ImpTransInfo ext blocks tops ret ps)

-- | Run an 'ImpTransM' computation in a 'TypeTransM' context (FIXME: better
-- documentation; e.g., the pctx starts on top of the stack)
impTransM :: forall ctx ps ext blocks tops ret a.
             RAssign (Member ctx) ps -> PermTransCtx ctx ps ->
             TypedBlockMapTrans ext blocks tops ret ->
             OpenTerm -> ImpTransM ext blocks tops ret ps ctx a ->
             TypeTransM ctx a
impTransM pvars pctx mapTrans retType =
  withInfoM $ \(TypeTransInfo ectx env) ->
  ImpTransInfo { itiExprCtx = ectx,
                 itiPermCtx = RL.map (const $ PTrans_True) ectx,
                 itiPermStack = pctx,
                 itiPermStackVars = pvars,
                 itiPermEnv = env,
                 itiBlockMapTrans = mapTrans,
                 itiReturnType = retType }

-- | Embed a type translation into an impure translation
-- FIXME: should no longer need this...
tpTransM :: TypeTransM ctx a -> ImpTransM ext blocks tops ret ps ctx a
tpTransM =
  withInfoM (\info -> TypeTransInfo (itiExprCtx info) (itiPermEnv info))

-- | Get most recently bound variable
getTopVarM :: ImpTransM ext blocks tops ret ps (ctx :> tp) (ExprTrans tp)
getTopVarM = (\(_ :>: p) -> p) <$> itiExprCtx <$> ask

-- | Get the top permission on the stack
getTopPermM :: ImpTransM ext blocks tops ret (ps :> tp) ctx (PermTrans ctx tp)
getTopPermM = (\(_ :>: p) -> p) <$> itiPermStack <$> ask

-- | Helper to disambiguate the @ext@ type variable
getExtReprM :: PermCheckExtC ext =>
               ImpTransM ext blocks tops ret ps ctx (ExtRepr ext)
getExtReprM = return knownRepr

-- | Apply a transformation to the (translation of the) current perm stack
withPermStackM :: (RAssign (Member ctx) ps_in -> RAssign (Member ctx) ps_out) ->
                  (PermTransCtx ctx ps_in -> PermTransCtx ctx ps_out) ->
                  ImpTransM ext blocks tops ret ps_out ctx a ->
                  ImpTransM ext blocks tops ret ps_in ctx a
withPermStackM f_vars f_p =
  withInfoM $ \info ->
  info { itiPermStack = f_p (itiPermStack info),
         itiPermStackVars = f_vars (itiPermStackVars info) }

-- | Get the current permission stack as a 'DistPerms' in context
getPermStackDistPerms :: ImpTransM ext blocks tops ret ps ctx
                         (Mb ctx (DistPerms ps))
getPermStackDistPerms =
  do stack <- itiPermStack <$> ask
     stack_vars <- itiPermStackVars <$> ask
     prxs <- RL.map (const Proxy) <$> itiPermCtx <$> ask
     return $
       (nuMulti prxs $ \ns ->
         valuePermsToDistPerms (RL.map (flip RL.get ns) stack_vars))
       `mbApply`
       permTransCtxPerms prxs stack

-- | Assert a property of the current permission stack, raising an 'error' if it
-- fails to hold. The 'String' names the construct being translated.
assertPermStackM :: HasCallStack => String ->
                    (RAssign (Member ctx) ps -> PermTransCtx ctx ps -> Bool) ->
                    ImpTransM ext blocks tops ret ps ctx ()
assertPermStackM nm f =
  ask >>= \info ->
  if f (itiPermStackVars info) (itiPermStack info) then return () else
    error ("translate: " ++ nm ++ nlPrettyCallStack callStack)

-- | Assert that the top portion of the current permission stack equals the
-- given 'DistPerms'
assertPermStackTopEqM :: HasCallStack => ps ~ (ps1 :++: ps2) =>
                         String -> f ps1 -> Mb ctx (DistPerms ps2) ->
                         ImpTransM ext blocks tops ret ps ctx ()
assertPermStackTopEqM nm prx expected =
  getPermStackDistPerms >>= \perms ->
  let actuals =
        fmap (snd . splitDistPerms prx (mbDistPermsToProxies expected)) perms in
  if expected == actuals then return () else
    error ("assertPermStackEqM (" ++ nm ++ "): expected permission stack:\n" ++
           permPrettyString emptyPPInfo expected ++
           "\nFound permission stack:\n" ++
           permPrettyString emptyPPInfo actuals ++
           nlPrettyCallStack callStack)

-- | Assert that the current permission stack equals the given 'DistPerms'
assertPermStackEqM :: HasCallStack => String -> Mb ctx (DistPerms ps) ->
                      ImpTransM ext blocks tops ret ps ctx ()
assertPermStackEqM nm perms =
  -- FIXME: unify this function with assertPermStackTopEqM
  getPermStackDistPerms >>= \stack_perms ->
  if perms == stack_perms then return () else
    error ("assertPermStackEqM (" ++ nm ++ "): expected permission stack:\n" ++
           permPrettyString emptyPPInfo perms ++
           "\nFound permission stack:\n" ++
           permPrettyString emptyPPInfo stack_perms ++
           nlPrettyCallStack callStack)

-- | Assert that the top permission is as given by the arguments
assertTopPermM :: HasCallStack => String -> Mb ctx (ExprVar a) ->
                  Mb ctx (ValuePerm a) ->
                  ImpTransM ext blocks tops ret (ps :> a) ctx ()
assertTopPermM nm x p =
  getPermStackDistPerms >>= \stack_perms ->
  case mbMatch stack_perms of
    [nuMP| DistPermsCons _ x' p' |] | x == x' && p == p' -> return ()
    [nuMP| DistPermsCons _ x' p' |] ->
      error ("assertTopPermM (" ++ nm ++ "): expected top permissions:\n" ++
             permPrettyString emptyPPInfo (mbMap2 distPerms1 x p) ++
             "\nFound top permissions:\n" ++
             permPrettyString emptyPPInfo (mbMap2 distPerms1 x' p') ++
             nlPrettyCallStack callStack ++
             "\nCurrent perm stack:\n" ++
             permPrettyString emptyPPInfo stack_perms)

-- | Get the (translation of the) perms for a variable
getVarPermM :: Mb ctx (ExprVar tp) ->
               ImpTransM ext blocks tops ret ps ctx (PermTrans ctx tp)
getVarPermM x = RL.get (translateVar x) <$> itiPermCtx <$> ask

-- | Assert that a variable has a given permission
assertVarPermM :: HasCallStack => String -> Mb ctx (ExprVar tp) ->
                  Mb ctx (ValuePerm tp) ->
                  ImpTransM ext blocks tops ret ps ctx ()
assertVarPermM nm x p =
  do x_p <- permTransPerm (mbToProxy p) <$> getVarPermM x
     if x_p == p then return () else
       error ("assertVarPermM (" ++ nm ++ "):\n" ++
              "expected: " ++ permPrettyString emptyPPInfo p ++ "\n" ++
              "found:" ++ permPrettyString emptyPPInfo x_p ++
              nlPrettyCallStack callStack)

-- | Set the (translation of the) perms for a variable in a computation
setVarPermM :: Mb ctx (ExprVar tp) -> PermTrans ctx tp ->
               ImpTransM ext blocks tops ret ps ctx a ->
               ImpTransM ext blocks tops ret ps ctx a
setVarPermM x p =
  local $ \info -> info { itiPermCtx =
                            RL.set (translateVar x) p $ itiPermCtx info }

-- | Clear all permissions in the permission variable map in a sub-computation,
-- leaving only those permissions on the top of the stack
clearVarPermsM :: ImpTransM ext blocks tops ret ps ctx a ->
                  ImpTransM ext blocks tops ret ps ctx a
clearVarPermsM =
  local $ \info -> info { itiPermCtx =
                            RL.map (const PTrans_True) $ itiPermCtx info }

-- | The current non-monadic return type
returnTypeM :: ImpTransM ext blocks tops ret ps_out ctx OpenTerm
returnTypeM = itiReturnType <$> ask

-- | Build the monadic return type @CompM ret@, where @ret@ is the current
-- return type in 'itiReturnType'
compReturnTypeM :: ImpTransM ext blocks tops ret ps_out ctx OpenTerm
compReturnTypeM =
  applyOpenTerm (globalOpenTerm "Prelude.CompM") <$> returnTypeM

-- | Like 'compReturnTypeM' but build a 'TypeTrans'
compReturnTypeTransM :: ImpTransM ext blocks tops ret ps_out ctx (TypeTrans OpenTerm)
compReturnTypeTransM =
  flip mkTypeTrans1 id <$> compReturnTypeM

-- | Build an @errorM@ computation with the given error message
mkErrorCompM :: String -> ImpTransM ext blocks tops ret ps_out ctx OpenTerm
mkErrorCompM msg =
  applyMultiTransM (return $ globalOpenTerm "Prelude.errorM")
  [returnTypeM, return $ stringLitOpenTerm $ pack msg]

-- | The typeclass for the implication translation of a functor at any
-- permission set inside any binding to an 'OpenTerm'
class NuMatchingAny1 f => ImplTranslateF f ext blocks tops ret where
  translateF :: Mb ctx (f ps) -> ImpTransM ext blocks tops ret ps ctx OpenTerm


----------------------------------------------------------------------
-- * Translating Permission Implication Constructs
----------------------------------------------------------------------

-- | Translate a 'SimplImpl' to a function on translation computations
translateSimplImpl :: Proxy ps -> Mb ctx (SimplImpl ps_in ps_out) ->
                      ImpTransM ext blocks tops ret (ps :++: ps_out) ctx OpenTerm ->
                      ImpTransM ext blocks tops ret (ps :++: ps_in) ctx OpenTerm
translateSimplImpl (ps0 :: Proxy ps0) mb_simpl m = case mbMatch mb_simpl of
  [nuMP| SImpl_Drop _ _ |] ->
    withPermStackM (\(xs :>: _) -> xs) (\(ps :>: _) -> ps) m
  
  [nuMP| SImpl_Copy x _ |] ->
    withPermStackM (:>: translateVar x) (\(ps :>: p) -> ps :>: p :>: p) m
  
  [nuMP| SImpl_Swap _ _ _ _ |] ->
    withPermStackM (\(xs :>: x :>: y) -> xs :>: y :>: x)
    (\(pctx :>: px :>: py) -> pctx :>: py :>: px)
    m
  
  [nuMP| SImpl_MoveUp (mb_ps1 :: DistPerms ps1) (_mb_x :: ExprVar a) _
                      (mb_ps2 :: DistPerms ps2) |] ->
    let ps1 = mbRAssignProxies mb_ps1
        ps2 = mbRAssignProxies mb_ps2
        prxa = Proxy :: Proxy a
        prx0a = Proxy :: Proxy (ps0 :> a) in
    case (RL.appendRNilConsEq ps0 prxa (RL.append ps1 ps2)) of
      Refl ->
        withPermStackM
        (\xs ->
          let ((xs0 :>: x), xs12) = RL.split prx0a (RL.append ps1 ps2) xs
              (xs1, xs2) = RL.split ps1 ps2 xs12 in
          RL.append xs0 $ RL.append (xs1 :>: x) xs2)
        (\pctx ->
          let ((pctx0 :>: ptrans), pctx12) =
                RL.split prx0a (RL.append ps1 ps2) pctx
              (pctx1, pctx2) = RL.split ps1 ps2 pctx12 in
          RL.append pctx0 $ RL.append (pctx1 :>: ptrans) pctx2)
        m
  
  [nuMP| SImpl_MoveDown mb_ps1 (mb_x :: ExprVar a) _ mb_ps2 |]
    | prx_a <- mbLift $ fmap (const (Proxy :: Proxy a)) mb_x
    , ps1 <- mbRAssignProxies mb_ps1
    , ps1a <- ps1 :>: prx_a
    , ps2 <- mbRAssignProxies mb_ps2
    , Refl <- RL.appendRNilConsEq ps0 prx_a (RL.append ps1 ps2) ->
      withPermStackM
      (\xs ->
        let (xs0, xs1a2) = RL.split ps0 (RL.append ps1a ps2) xs
            ((xs1 :>: x), xs2) = RL.split ps1a ps2 xs1a2 in
        RL.append xs0 (RL.append (MNil :>: x) $ RL.append xs1 xs2))
      (\pctx ->
        let (pctx0, pctx1a2) = RL.split ps0 (RL.append ps1a ps2) pctx
            ((pctx1 :>: ptrans), pctx2) = RL.split ps1a ps2 pctx1a2 in
        RL.append pctx0 (RL.append (MNil :>: ptrans) $ RL.append pctx1 pctx2))
      m

  [nuMP| SImpl_IntroOrL _ p1 p2 |] ->
    do tp1 <- translate p1
       tp2 <- translate p2
       withPermStackM id
         (\(ps :>: p_top) ->
           ps :>: PTrans_Term (mbMap2 ValPerm_Or p1 p2) (leftTrans tp1 tp2 p_top))
         m
  
  [nuMP| SImpl_IntroOrR _ p1 p2 |] ->
    do tp1 <- translate p1
       tp2 <- translate p2
       withPermStackM id
         (\(ps :>: p_top) ->
           ps :>: PTrans_Term (mbMap2 ValPerm_Or p1 p2) (rightTrans tp1 tp2 p_top))
         m
  
  [nuMP| SImpl_IntroExists _ e p |] ->
    do let tp = mbExprType e
       tp_trans <- translateClosed tp
       etrans <- translate e
       sigma_trm <-
         sigmaTransM "x_ex" tp_trans (flip inExtTransM $ translate $ mbCombine RL.typeCtxProxies p)
         etrans getTopPermM
       withPermStackM id
         ((:>: PTrans_Term (fmap ValPerm_Exists p) sigma_trm) . RL.tail)
         m
  
  [nuMP| SImpl_Cast _ _ _ |] ->
    withPermStackM RL.tail
    (\(pctx :>: _ :>: ptrans) -> pctx :>: ptrans)
    m
  
  [nuMP| SImpl_CastPerm (x::ExprVar a) eqp |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       let prxs_a = MNil :>: (Proxy :: Proxy a)
       let prxs1 = mbLift $ fmap (distPermsToProxies . eqProofPerms) eqp
       let prxs = RL.append prxs_a prxs1
       withPermStackM
         (\vars -> fst (RL.split ps0 prxs vars) :>: translateVar x)
         (\pctx ->
           let (pctx1, pctx2) = RL.split ps0 prxs pctx
               (_ :>: ptrans, _) = RL.split prxs_a prxs1 pctx2 in
           pctx1 :>: typeTransF ttrans (transTerms ptrans))
         m
  
  [nuMP| SImpl_IntroEqRefl x |] ->
    withPermStackM (:>: translateVar x) (:>: PTrans_Eq (fmap PExpr_Var x)) m
  
  [nuMP| SImpl_InvertEq x y |] ->
    withPermStackM ((:>: translateVar y) . RL.tail)
    ((:>: PTrans_Eq (fmap PExpr_Var x)) . RL.tail)
    m
  
  [nuMP| SImpl_InvTransEq _ mb_y _ |] ->
    withPermStackM RL.tail
    ((:>: PTrans_Eq (fmap PExpr_Var mb_y)) . RL.tail . RL.tail)
    m
  
  [nuMP| SImpl_CopyEq _ _ |] ->
    withPermStackM
    (\(vars :>: var) -> (vars :>: var :>: var))
    (\(pctx :>: ptrans) -> (pctx :>: ptrans :>: ptrans))
    m
  
  [nuMP| SImpl_LLVMWordEq _ _ e |] ->
    withPermStackM RL.tail
    (\(pctx :>: _ :>: _) -> (pctx :>: PTrans_Eq (fmap PExpr_LLVMWord e)))
    m
  
  [nuMP| SImpl_IntroConj x |] ->
    withPermStackM (:>: translateVar x) (:>: PTrans_True) m
  
  [nuMP| SImpl_ExtractConj x _ mb_i |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans) ->
      let ps = unPTransConj "translateSimplImpl: SImpl_ExtractConj" ptrans
          i = mbLift mb_i in
      if i < length ps then
        pctx :>: PTrans_Conj [ps !! i]
        :>: PTrans_Conj (deleteNth i ps)
      else
        error "translateSimplImpl: SImpl_ExtractConj: index out of bounds")
    m
  
  [nuMP| SImpl_CopyConj x _ mb_i |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans) ->
      let ps = unPTransConj "translateSimplImpl: SImpl_CopyConj" ptrans
          i = mbLift mb_i in
      if i < length ps then pctx :>: PTrans_Conj [ps !! i] :>: ptrans else
        error "translateSimplImpl: SImpl_CopyConj: index out of bounds")
    m
  
  [nuMP| SImpl_InsertConj _ _ _ i |] ->
    withPermStackM RL.tail
    (\(pctx :>: ptransi :>: ptrans) ->
      let ps = unPTransConj "translateSimplImpl: SImpl_InsertConj" ptrans
          pi = unPTransConj1 "translateSimplImpl: SImpl_InsertConj" ptransi in
      pctx :>: PTrans_Conj (take (mbLift i) ps ++ pi : drop (mbLift i) ps))
    m
  
  [nuMP| SImpl_AppendConjs _ _ _ |] ->
    withPermStackM RL.tail
    (\(pctx :>: ptrans1 :>: ptrans2) ->
      let ps1 = unPTransConj "translateSimplImpl: SImpl_AppendConjs" ptrans1
          ps2 = unPTransConj "translateSimplImpl: SImpl_AppendConjs" ptrans2 in
      pctx :>: PTrans_Conj (ps1 ++ ps2))
    m
  
  [nuMP| SImpl_SplitConjs x _ mb_i |] ->
    let i = mbLift mb_i in
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans) ->
      let ps = unPTransConj "translateSimplImpl: SImpl_SplitConjs" ptrans in
      pctx :>: PTrans_Conj (take i ps) :>: PTrans_Conj (drop i ps))
    m
  
  [nuMP| SImpl_IntroStructTrue x prxs |] ->
    withPermStackM (:>: translateVar x)
    (\pctx -> pctx :>: PTrans_Conj [APTrans_Struct $
                                    RL.map (const PTrans_True) (mbRAssign prxs)])
    m
  
  [nuMP| SImpl_StructEqToPerm _ exprs |] ->
    withPermStackM id
    (\(pctx :>: _) ->
      pctx :>: PTrans_Conj [APTrans_Struct $
                            RL.map (PTrans_Eq . getCompose)
                            (mbRAssign $ fmap exprsToRAssign exprs)])
    m
  
  [nuMP| SImpl_StructPermToEq _ exprs |] ->
    withPermStackM id
    (\(pctx :>: _) -> pctx :>: PTrans_Eq (fmap PExpr_Struct exprs))
    m
  
  [nuMP| SImpl_IntroStructField _ _ memb _ |] ->
    withPermStackM RL.tail
    (\(pctx :>: PTrans_Conj [APTrans_Struct pctx_str] :>: ptrans) ->
      pctx :>: PTrans_Conj [APTrans_Struct $
                            RL.set (mbLift memb) ptrans pctx_str])
    m
  
  [nuMP| SImpl_ConstFunPerm x _ mb_fun_perm ident |] ->
    withPermStackM ((:>: translateVar x) . RL.tail)
    ((:>: PTrans_Term (fmap (ValPerm_Conj1
                             . Perm_Fun) mb_fun_perm) (globalOpenTerm $
                                                       mbLift ident))
     . RL.tail)
    m
  
  [nuMP| SImpl_CastLLVMWord _ _ e2 |] ->
    withPermStackM RL.tail
    ((:>: PTrans_Eq (fmap PExpr_LLVMWord e2)) . RL.tail . RL.tail)
    m
  
  [nuMP| SImpl_InvertLLVMOffsetEq mb_x mb_off mb_y |] ->
    withPermStackM
    ((:>: translateVar mb_y) . RL.tail)
    ((:>: PTrans_Eq (mbMap2 (\x off -> PExpr_LLVMOffset x $
                                       bvNegate off) mb_x mb_off)) . RL.tail)
    m
  
  [nuMP| SImpl_OffsetLLVMWord _ mb_e mb_off mb_x |] ->
    withPermStackM
    ((:>: translateVar mb_x) . RL.tail . RL.tail)
    ((:>: PTrans_Eq (mbMap2 (\e off -> PExpr_LLVMWord $ bvAdd e off)
                     mb_e mb_off)) . RL.tail . RL.tail)
    m
  
  [nuMP| SImpl_CastLLVMPtr _ _ off _ |] ->
    withPermStackM RL.tail
    (\(pctx :>: _ :>: ptrans) ->
      pctx :>: offsetLLVMPermTrans (fmap bvNegate off) ptrans)
    m
  
  [nuMP| SImpl_CastLLVMFree _ _ e2 |] ->
    withPermStackM RL.tail
    ((:>: PTrans_Conj [APTrans_LLVMFree e2]) . RL.tail . RL.tail)
    m
  
  [nuMP| SImpl_CastLLVMFieldOffset _ mb_fld mb_off |] ->
    withPermStackM RL.tail
    (\(pctx :>: _ :>: ptrans) ->
      let (_,ptrans') =
            unPTransLLVMField "translateSimplImpl: SImpl_CastLLVMFieldOffset"
            knownNat ptrans in
      pctx :>: PTrans_Conj [APTrans_LLVMField
                            (mbMap2 (\fld off -> fld { llvmFieldOffset = off })
                             mb_fld mb_off)
                            ptrans'])
    m
  
  [nuMP| SImpl_IntroLLVMFieldContents x _ mb_fld |] ->
    withPermStackM ((:>: translateVar x) . RL.tail . RL.tail)
    (\(pctx :>: _ :>: ptrans) ->
      pctx :>: PTrans_Conj [APTrans_LLVMField mb_fld ptrans])
    m
  
  [nuMP| SImpl_DemoteLLVMFieldRW _ mb_fld |] ->
    withPermStackM id
    (\(pctx :>: ptrans) ->
      let (_,ptrans') =
            unPTransLLVMField
            "translateSimplImpl: SImpl_DemoteLLVMFieldRW"
            knownNat ptrans in
      pctx :>: PTrans_Conj [APTrans_LLVMField
                            (fmap (\fld -> fld { llvmFieldRW = PExpr_Read }) mb_fld)
                            ptrans'])
    m
  
  [nuMP| SImpl_LLVMArrayCopy _ mb_ap mb_sub_ap |] ->
    do let _w = natVal2 mb_ap
       sub_ap_tp_trans <- translate mb_sub_ap
       rng_trans <- translate $ mbMap2 llvmSubArrayRange mb_ap mb_sub_ap
       -- let mb_sub_borrows = fmap llvmArrayBorrows mb_sub_ap
       withPermStackM id
         (\(pctx :>: ptrans_array :>: ptrans_props) ->
           let array_trans =
                 unPTransLLVMArray
                 "translateSimplImpl: SImpl_LLVMArrayCopy" ptrans_array
               prop_transs =
                 unPTransBVProps
                 "translateSimplImpl: SImpl_LLVMArrayCopy" ptrans_props in
           pctx :>:
           PTrans_Conj [APTrans_LLVMArray $
                        getLLVMArrayTransSlice array_trans sub_ap_tp_trans
                        rng_trans {- mb_sub_borrows -} prop_transs]
           :>: ptrans_array)
         m
  
  [nuMP| SImpl_LLVMArrayBorrow _ mb_ap mb_sub_ap |] ->
    do sub_ap_tp_trans <- translate mb_sub_ap
       let mb_rng = mbMap2 llvmSubArrayRange mb_ap mb_sub_ap
       rng_trans <- translate mb_rng
       -- let mb_sub_borrows = fmap llvmArrayBorrows mb_sub_ap
       withPermStackM id
         (\(pctx :>: ptrans_array :>: ptrans_props) ->
           let array_trans =
                 unPTransLLVMArray
                 "translateSimplImpl: SImpl_LLVMArrayBorrow" ptrans_array
               prop_transs =
                 unPTransBVProps
                 "translateSimplImpl: SImpl_LLVMArrayBorrow" ptrans_props
               {- borrow_trans =
                 LLVMArrayBorrowTrans (fmap RangeBorrow mb_rng) prop_transs -}
               sub_array_trans =
                 APTrans_LLVMArray $
                 getLLVMArrayTransSlice array_trans sub_ap_tp_trans rng_trans
                 {- mb_sub_borrows -} prop_transs
               array_trans' =
                 array_trans {
                 llvmArrayTransPerm =
                     mbMap2 (\ap sub_ap ->
                              llvmArrayAddBorrow (llvmSubArrayBorrow ap sub_ap) $
                              llvmArrayRemArrayBorrows ap sub_ap)
                     mb_ap mb_sub_ap } in
           pctx :>:
           PTrans_Conj [sub_array_trans]
           :>: PTrans_Conj [APTrans_LLVMArray array_trans'])
         m
  
  [nuMP| SImpl_LLVMArrayReturn _ mb_ap mb_ret_ap |] ->
    do (_ :>: ptrans_sub_array :>: ptrans_array) <- itiPermStack <$> ask
       let mb_cell =
             fmap fromJust $ mbMap2 llvmArrayIsOffsetArray mb_ap mb_ret_ap
       cell_tm <- translate1 mb_cell
       let array_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayReturn" ptrans_array
       let sub_array_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayReturn" ptrans_sub_array
           {- borrow_i =
             mbLift $ mbMap2 llvmArrayFindBorrow (fmap
                                                  RangeBorrow mb_rng) mb_ap
           borrow_trans = llvmArrayTransBorrows array_trans !! borrow_i -}
       let array_trans' =
             (setLLVMArrayTransSlice array_trans sub_array_trans cell_tm)
             { llvmArrayTransPerm =
                 mbMap2 (\ap ret_ap ->
                          llvmArrayRemBorrow (llvmSubArrayBorrow ap ret_ap) $
                          llvmArrayAddArrayBorrows ap ret_ap) mb_ap mb_ret_ap }
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [APTrans_LLVMArray array_trans'])
         m
  
  [nuMP| SImpl_LLVMArrayAppend _ mb_ap1 mb_ap2 |] ->
    withPermStackM RL.tail
    (\(pctx :>: ptrans_array1 :>: ptrans_array2) ->
       let w = natVal2 mb_ap1
           array_trans1 =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayAppend" ptrans_array1
           array_trans2 =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayAppend" ptrans_array2
           len1 = llvmArrayTransLen array_trans1
           len2 = llvmArrayTransLen array_trans2
           mb_ap_out =
             mbMap2 (\ap1 ap2 ->
                      llvmArrayAddArrayBorrows
                      (ap1 { llvmArrayLen =
                             bvAdd (llvmArrayLen ap1) (llvmArrayLen ap2) })
                      ap2) mb_ap1 mb_ap2
           array_trans_out =
             LLVMArrayPermTrans
             { llvmArrayTransPerm = mb_ap_out
             , llvmArrayTransLen = bvAddOpenTerm w len1 len2
             , llvmArrayTransFields = llvmArrayTransFields array_trans1
             , llvmArrayTransTerm =
               applyOpenTermMulti (globalOpenTerm "Prelude.appendBVVec")
               [natOpenTerm w, len1, len2, llvmArrayTransTerm array_trans1,
                llvmArrayTransTerm array_trans2] } in
       pctx :>: PTrans_Conj [APTrans_LLVMArray array_trans_out])
    m
  
  
  [nuMP| SImpl_LLVMArrayRearrange _ _ mb_ap2 |] ->
    do ap2_tp_trans <- translate mb_ap2
       withPermStackM id
         (\(pctx :>: ptrans_array) ->
           pctx :>:
           PTrans_Conj [APTrans_LLVMArray $
                        typeTransF ap2_tp_trans [transTerm1 ptrans_array]])
         m
  
  [nuMP| SImpl_LLVMArrayToField _ _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans [])
         m
  
  [nuMP| SImpl_LLVMArrayEmpty x mb_ap |] ->
    do (w_term, _, elem_tp, ap_tp_trans) <- translateLLVMArrayPerm mb_ap
       let arr_term =
             applyOpenTermMulti (globalOpenTerm "Prelude.emptyBVVec")
             [w_term, elem_tp]
       withPermStackM (:>: translateVar x)
         (\pctx ->
           pctx :>:
           PTrans_Conj [APTrans_LLVMArray $ typeTransF ap_tp_trans [arr_term]])
         m
  
  [nuMP| SImpl_LLVMArrayOneCell _ mb_ap |] ->
    do (w_term, len_term, elem_tp, ap_tp_trans) <- translateLLVMArrayPerm mb_ap
       withPermStackM id
         (\(pctx :>: ptrans_flds) ->
           let arr_term =
                 applyOpenTermMulti (globalOpenTerm "Prelude.repeatBVVec")
                 [w_term, len_term, elem_tp, transTupleTerm ptrans_flds] in
           pctx :>:
           PTrans_Conj [APTrans_LLVMArray $ typeTransF ap_tp_trans [arr_term]])
         m
  
  
  [nuMP| SImpl_LLVMArrayIndexCopy _ _ mb_ix |] ->
    do (_ :>: ptrans_array :>: ptrans_props) <- itiPermStack <$> ask
       let arr_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayIndexCopy" ptrans_array
       let prop_transs =
             unPTransBVProps
             "translateSimplImpl: SImpl_LLVMArrayIndexCopy" ptrans_props
       ix_trans <- translate mb_ix
       let fld_ptrans = getLLVMArrayTransField arr_trans ix_trans prop_transs
       withPermStackM id
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [fld_ptrans] :>: ptrans_array)
         m
  
  [nuMP| SImpl_LLVMArrayIndexBorrow _ mb_ap mb_ix |] ->
    do (_ :>: ptrans_array :>: ptrans_props) <- itiPermStack <$> ask
       let arr_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayIndexBorrow" ptrans_array
       let prop_transs =
             unPTransBVProps
             "translateSimplImpl: SImpl_LLVMArrayIndexBorrow" ptrans_props
       ix_trans <- translate mb_ix
       let fld_ptrans = getLLVMArrayTransField arr_trans ix_trans prop_transs
       {- let b = LLVMArrayBorrowTrans (fmap FieldBorrow ix) prop_transs -}
       let arr_trans' =
             arr_trans { llvmArrayTransPerm =
                           mbMap2 (\ap ix ->
                                    llvmArrayAddBorrow (FieldBorrow ix) ap)
                           mb_ap mb_ix }
       withPermStackM id
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [fld_ptrans] :>:
           PTrans_Conj [APTrans_LLVMArray arr_trans'])
         m
  
  [nuMP| SImpl_LLVMArrayIndexReturn _ mb_ap mb_ix |] ->
    do (_ :>: ptrans_fld :>: ptrans_array) <- itiPermStack <$> ask
       let aptrans_fld = case ptrans_fld of
             PTrans_Conj [ap] -> ap
             _ -> error ("translateSimplImpl: SImpl_LLVMArrayIndexReturn: "
                         ++ "found non-field perm where field perm was expected")
       let arr_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayIndexCopy" ptrans_array
       {- let b_trans = llvmArrayTransFindBorrow (fmap FieldBorrow ix) arr_trans -}
       ix_trans <- translate mb_ix
       let arr_trans' =
             (setLLVMArrayTransField arr_trans ix_trans
              {- (llvmArrayBorrowTransProps b_trans) -} aptrans_fld)
             { llvmArrayTransPerm =
                 mbMap2 (\ap ix ->
                          llvmArrayRemBorrow (FieldBorrow ix) ap) mb_ap mb_ix }
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [APTrans_LLVMArray arr_trans'])
         m
  
  [nuMP| SImpl_LLVMArrayContents _ _ _ _ _ |] ->
    error "FIXME HERE: translateSimplImpl: SImpl_LLVMArrayContents unhandled"
  
  [nuMP| SImpl_LLVMFieldIsPtr x _ |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans_fld) ->
      pctx :>: PTrans_Conj [APTrans_IsLLVMPtr] :>: ptrans_fld)
    m
  
  [nuMP| SImpl_LLVMArrayIsPtr x _ |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans_array) ->
      pctx :>: PTrans_Conj [APTrans_IsLLVMPtr] :>: ptrans_array)
    m
  
  [nuMP| SImpl_LLVMBlockIsPtr x _ |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans) ->
      pctx :>: PTrans_Conj [APTrans_IsLLVMPtr] :>: ptrans)
    m
  
  [nuMP| SImpl_SplitLifetime _ f args l _ ps_in ps_out |] ->
    do pctx_out_trans <- translate $ fmap simplImplOut mb_simpl
       ps_in_tp <- translate1 ps_in
       ps_out_tp <- translate1 ps_out
       x_tp_trans <- translate (mbMap3 ltFuncApply f args l)
       withPermStackM
         (\(ns :>: x :>: _ :>: l2) -> ns :>: x :>: l2)
         (\(pctx :>: ptrans_x :>: _ :>: ptrans_l) ->
           -- The permission for x does not change type, just its lifetime; the
           -- permission for l has the (tupled) type of x added as a new input and
           -- output with tupleCompMFunBoth
           let (f_tm,_,_) =
                 foldr (\x_tp (f_term,f_in_tp,f_out_tp) ->
                         ( applyOpenTermMulti
                           (globalOpenTerm "Prelude.tupleCompMFunBoth")
                           [f_in_tp, f_out_tp, x_tp, f_term]
                         , pairTypeOpenTerm x_tp f_in_tp
                         , pairTypeOpenTerm x_tp f_out_tp))
                 (transTerm1 ptrans_l, ps_in_tp, ps_out_tp)
                 (transTerms x_tp_trans) in
           RL.append pctx $
           typeTransF pctx_out_trans (transTerms ptrans_x ++ [f_tm]))
         m
  
  [nuMP| SImpl_SubsumeLifetime _ _ ps_in1 ps_out1 ps_in2 ps_out2 |] ->
    do pctx_out_trans <- translate $ fmap simplImplOut mb_simpl
       ps_in1_tp <- translate1 ps_in1
       ps_out1_tp <- translate1 ps_out1
       ps_in2_tp <- translate1 ps_in2
       ps_out2_tp <- translate1 ps_out2
       let fun_tp1 = arrowOpenTerm "ps" ps_in1_tp (applyOpenTerm
                                                   (globalOpenTerm "Prelude.CompM")
                                                   ps_out1_tp)
       withPermStackM id
         (\(pctx :>: ptrans_l1 :>: ptrans_l2) ->
           -- The output permissions are an lcurrent permission, which has no term
           -- translation, and the updated lowned permission, which is the result
           -- of adding the translation of the lowned permission for l1 to the
           -- return value of that for l2
           RL.append pctx $
           typeTransF pctx_out_trans [applyOpenTermMulti
                                      (globalOpenTerm "Prelude.tupleCompMFunOut")
                                      [ps_in2_tp, ps_out2_tp, fun_tp1,
                                       transTerm1 ptrans_l1,
                                       transTerm1 ptrans_l2]])
         m
  
  [nuMP| SImpl_WeakenLifetime _ _ _ _ _ |] ->
    do pctx_out_trans <- translate $ fmap simplImplOut mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans_x :>: _) ->
           -- NOTE: lcurrent permissions have no term translations, so we can
           -- construct the output PermTransCtx by just passing the terms in
           -- ptrans_x to pctx_out_trans
           RL.append pctx (typeTransF pctx_out_trans $ transTerms ptrans_x))
         m
  
  [nuMP| SImpl_MapLifetime l ps_in ps_out
                                  ps_in' ps_out' ps1 ps2 impl_in impl_out |] ->
    -- First, translate the output permissions and all of the perm lists
    do pctx_out_trans <- translate $ fmap simplImplOut mb_simpl
       ps_in_trans <- translate ps_in
       ps_out_trans <- translate ps_out
       ps_in'_trans <- translate ps_in'
       ps_out'_trans <- translate ps_out'
       -- ps1_trans <- translate ps1
       -- ps2_trans <- translate ps2
  
       -- Next, split out the various input permissions from the rest of the pctx
       let prxs1 = mbRAssignProxies ps1
       let prxs2 = mbRAssignProxies ps2
       let prxs_in = RL.append prxs1 prxs2 :>: Proxy
       pctx <- itiPermStack <$> ask
       let (pctx_ps, pctx12 :>: ptrans_l) = RL.split ps0 prxs_in pctx
       let (pctx1, pctx2) = RL.split prxs1 prxs2 pctx12
  
       -- Also split out the input variables and replace them with the ps_out vars
       pctx_vars <- itiPermStackVars <$> ask
       let (vars_ps, vars12 :>: _) = RL.split ps0 prxs_in pctx_vars
       let (vars1, vars2) = RL.split prxs1 prxs2 vars12
       let vars_out = vars_ps :>: translateVar l
  
       -- Now build the output lowned function by composing the input lowned
       -- function with the translations of the implications on inputs and outputs
       let fromJustOrError (Just x) = x
           fromJustOrError Nothing = error "translateSimplImpl: SImpl_MapLifetime"
           ps_in'_vars =
             RL.map (translateVar . getCompose) $ mbRAssign $ 
             fmap (fromJustOrError . lownedPermsVars) ps_in'
           ps_out_vars =
             RL.map (translateVar . getCompose) $ mbRAssign $ 
             fmap (fromJustOrError . lownedPermsVars) ps_out
       impl_in_tm <-
         translateCurryLocalPermImpl "Error mapping lifetime input perms:" impl_in
         pctx1 vars1 ps_in'_trans ps_in'_vars ps_in_trans
       impl_out_tm <-
         translateCurryLocalPermImpl "Error mapping lifetime output perms:" impl_out
         pctx2 vars2 ps_out_trans ps_out_vars ps_out'_trans
       let l_res_tm =
             applyOpenTermMulti
             (globalOpenTerm "Prelude.composeM")
             [transTerm1 ps_in'_trans, transTerm1 ps_in_trans,
              transTerm1 ps_out'_trans, impl_in_tm,
              applyOpenTermMulti
              (globalOpenTerm "Prelude.composeM")
              [transTerm1 ps_in_trans, transTerm1 ps_out_trans,
               transTerm1 ps_out'_trans, transTerm1 ptrans_l, impl_out_tm]]
  
       -- Finally, update the permissions
       withPermStackM
         (\_ -> vars_out)
         (\_ -> RL.append pctx_ps $ typeTransF pctx_out_trans [l_res_tm])
         m
  
  [nuMP| SImpl_EndLifetime _ ps_in ps_out |] ->
    -- First, translate the output permissions and the input and output types of
    -- the monadic function for the lifeime ownership permission
    do ps_out_trans <- translate ps_out
       let prxs_in = mbRAssignProxies ps_in :>: Proxy
  
       -- Next, split out the ps_in permissions from the rest of the pctx
       pctx <- itiPermStack <$> ask
       let (pctx_ps, pctx_in :>: ptrans_l) = RL.split ps0 prxs_in pctx
  
       -- Also split out the ps_in variables and replace them with the ps_out vars
       pctx_vars <- itiPermStackVars <$> ask
       let (ps_vars, _ :>: _) = RL.split ps0 prxs_in pctx_vars
       let fromJustHelper (Just x) = x
           fromJustHelper _ = error "translateSimplImpl: SImpl_EndLifetime"
       let vars_out =
             RL.append ps_vars $ RL.map (translateVar . getCompose) $
             mbRAssign $ fmap (fromJustHelper . lownedPermsVars) ps_out
  
       -- Now we apply the lifetime ownerhip function to ps_in and bind its output
       -- in the rest of the computation
       applyMultiTransM (return $ globalOpenTerm "Prelude.bindM")
         [return (transTerm1 ps_out_trans), returnTypeM,
          return (applyOpenTerm (transTerm1 ptrans_l)
                  (strictTransTupleTerm pctx_in)),
          lambdaTransM "endl_ps" ps_out_trans $ \pctx_out ->
           withPermStackM
           (\_ -> vars_out)
           (\_ -> RL.append pctx_ps pctx_out)
           m]
  
  [nuMP| SImpl_LCurrentRefl l |] ->
    withPermStackM (:>: translateVar l)
    (:>: PTrans_Conj [APTrans_LCurrent $ fmap PExpr_Var l])
    m
  
  [nuMP| SImpl_LCurrentTrans _l1 _l2 l3 |] ->
    withPermStackM RL.tail
    ((:>: PTrans_Conj [APTrans_LCurrent l3]) .
     RL.tail . RL.tail)
    m
  
  [nuMP| SImpl_DemoteLLVMBlockRW _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans (transTerms ptrans))
         m
  
  [nuMP| SImpl_IntroLLVMBlockEmpty x _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF ttrans [unitOpenTerm])
         m
  
  [nuMP| SImpl_CoerceLLVMBlockEmpty _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans [unitOpenTerm])
         m
  
  [nuMP| SImpl_ElimLLVMBlockToBytes _ mb_bp |] ->
    do let w = natVal2 mb_bp
       let w_term = natOpenTerm w
       len_term <- translate1 $ fmap llvmBlockLen mb_bp
       ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           let arr_term =
                 applyOpenTermMulti (globalOpenTerm "Prelude.repeatBVVec")
                 [w_term, len_term, unitTypeOpenTerm, unitOpenTerm] in
           pctx :>: typeTransF ttrans [arr_term])
         m
  
  [nuMP| SImpl_IntroLLVMBlockSeqEmpty _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [pairOpenTerm (transTerm1 ptrans)
                                       unitOpenTerm])
         m
  
  [nuMP| SImpl_ElimLLVMBlockSeqEmpty _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [pairLeftOpenTerm (transTerm1 ptrans)])
         m
  
  -- Intro for a recursive named shape applies the fold function
  [nuMP| SImpl_IntroLLVMBlockNamed _ bp nmsh |]
    | [nuMP| RecShapeBody _ _ fold_id _ |] <- mbMatch $ fmap namedShapeBody nmsh
    , [nuMP| PExpr_NamedShape _ _ _ args |] <- mbMatch $ fmap llvmBlockShape bp ->
      do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
         args_trans <- translate args
         let t = applyOpenTermMulti (globalOpenTerm $
                                     mbLift fold_id) (transTerms args_trans)
         withPermStackM id
           (\(pctx :>: _) -> pctx :>: typeTransF ttrans [t])
           m
  
  -- Intro for a defined named shape (the other case) is a no-op
    | [nuMP| DefinedShapeBody _ |] <- mbMatch $ fmap namedShapeBody nmsh ->
      do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
         withPermStackM id
           (\(pctx :>: ptrans) ->
             pctx :>: typeTransF ttrans [transTerm1 ptrans])
           m

    | otherwise -> fail "translateSimplImpl: SImpl_IntroLLVMBlockNamed, unknown named shape"
  
  [nuMP| SImpl_ElimLLVMBlockNamed _ bp nmsh |]
  -- Elim for a recursive named shape applies the fold function
    | [nuMP| RecShapeBody _ _ _ unfold_id |] <- mbMatch $ fmap namedShapeBody nmsh
    , [nuMP| PExpr_NamedShape _ _ _ args |] <- mbMatch $ fmap llvmBlockShape bp ->
      do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
         args_trans <- translate args
         let t = applyOpenTermMulti (globalOpenTerm $
                                     mbLift unfold_id) (transTerms args_trans)
         withPermStackM id
           (\(pctx :>: _) -> pctx :>: typeTransF ttrans [t])
           m
  
  -- Intro for a defined named shape (the other case) is a no-op
    | [nuMP| DefinedShapeBody _ |] <- mbMatch $ fmap namedShapeBody nmsh ->
      do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
         withPermStackM id
           (\(pctx :>: ptrans) ->
             pctx :>: typeTransF ttrans [transTerm1 ptrans])
           m

    | otherwise -> fail "translateSimplImpl: ElimLLVMBlockNamed, unknown named shape"
  
  [nuMP| SImpl_IntroLLVMBlockFromEq _ _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m
  
  [nuMP| SImpl_IntroLLVMBlockPtr _ _ _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m
  
  [nuMP| SImpl_ElimLLVMBlockPtr _ _ _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m
  
  [nuMP| SImpl_IntroLLVMBlockField _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTupleTerm ptrans])
         m
  
  [nuMP| SImpl_ElimLLVMBlockField _ _ _ |] ->
    do let mb_ps = fmap ((\case ValPerm_Conj ps -> ps
                                _ -> error "translateSimplImpl: SImpl_ElimLLVMBlockField, VPerm_Conj required"
                         ). distPermsHeadPerm . simplImplOut) mb_simpl
       ttrans1 <- translate $ fmap (!!0) mb_ps
       ttrans2 <- translate $ fmap (!!1) mb_ps
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>:
           PTrans_Conj [typeTransF (tupleTypeTrans ttrans1) [transTerm1 ptrans],
                        typeTransF ttrans2 [unitOpenTerm]])
         m
  
  [nuMP| SImpl_IntroLLVMBlockArray _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m
  
  [nuMP| SImpl_ElimLLVMBlockArray _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m
  
  [nuMP| SImpl_IntroLLVMBlockSeq _ _ _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans1 :>: ptrans2) ->
           let pair_term =
                 pairOpenTerm (transTerm1 ptrans1) (transTerm1 ptrans2) in
           pctx :>: typeTransF ttrans [pair_term])
         m
  
  [nuMP| SImpl_ElimLLVMBlockSeq _ _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [pairLeftOpenTerm (transTerm1 ptrans),
                                       pairRightOpenTerm (transTerm1 ptrans)])
         m
  
  [nuMP| SImpl_IntroLLVMBlockOr _ _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m
  
  [nuMP| SImpl_ElimLLVMBlockOr _ _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m
  
  [nuMP| SImpl_IntroLLVMBlockEx _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m
  
  [nuMP| SImpl_ElimLLVMBlockEx _ _ |] ->
    do ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m
  
  [nuMP| SImpl_FoldNamed _ (NamedPerm_Rec rp) args _ |] ->
    do args_trans <- translate args
       ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       let fold_ident = mbLift $ fmap recPermFoldFun rp
       withPermStackM id
         (\(pctx :>: ptrans_x) ->
           pctx :>: typeTransF ttrans [applyOpenTermMulti
                                       (globalOpenTerm fold_ident)
                                       (transTerms args_trans
                                        ++ transTerms ptrans_x)])
         m
  
  [nuMP| SImpl_UnfoldNamed _ (NamedPerm_Rec rp) args _ |] ->
    do args_trans <- translate args
       ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       let unfold_ident = mbLift $ fmap recPermUnfoldFun rp
       withPermStackM id
         (\(pctx :>: ptrans_x) ->
           pctx :>:
           typeTransF (tupleTypeTrans ttrans) [applyOpenTermMulti
                                               (globalOpenTerm unfold_ident)
                                               (transTerms args_trans
                                                ++ [transTerm1 ptrans_x])])
         m
  
  [nuMP| SImpl_FoldNamed _ (NamedPerm_Defined dp) args off |] ->
    do folded_trans <-
         translate (mbMap2 ValPerm_Named (fmap definedPermName dp) args
                    `mbApply` off)
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF folded_trans (transTerms ptrans))
         m
  
  [nuMP| SImpl_UnfoldNamed _ (NamedPerm_Defined dp) args off |] ->
    do unfolded_trans <-
         translate (mbMap2 unfoldDefinedPerm dp args `mbApply` off)
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF unfolded_trans (transTerms ptrans))
         m
  
  {-
  [nuMP| SImpl_Mu _ _ _ _ |] ->
    error "FIXME HERE: SImpl_Mu: translation not yet implemented"
  -}
  
  [nuMP| SImpl_NamedToConj _ _ _ _ |] ->
    do tp_trans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m
  
  [nuMP| SImpl_NamedFromConj _ _ _ _ |] ->
    do tp_trans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m
  
  [nuMP| SImpl_NamedArgAlways _ _ _ _ _ _ |] ->
    do tp_trans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m
  
  [nuMP| SImpl_NamedArgCurrent _ _ _ _ _ _ |] ->
    do tp_trans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans :>: _) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m
  
  [nuMP| SImpl_NamedArgWrite _ _ _ _ _ _ |] ->
    do tp_trans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m
  
  [nuMP| SImpl_NamedArgRead _ _ _ _ _ |] ->
    do tp_trans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m
  
  [nuMP| SImpl_ReachabilityTrans _ rp args _ y e |] ->
    do args_trans <- translate $ mbMap2 PExprs_Cons args e
       y_trans <- translate y
       e_trans <- translate e
       ttrans <- translate $ fmap (distPermsHeadPerm . simplImplOut) mb_simpl
       let trans_ident = mbLift $ fmap recPermTransMethod rp
       withPermStackM RL.tail
         (\(pctx :>: ptrans_x :>: ptrans_y) ->
           pctx :>:
           typeTransF (tupleTypeTrans ttrans) [applyOpenTermMulti
                                               (globalOpenTerm trans_ident)
                                               (transTerms args_trans
                                                ++ transTerms y_trans
                                                ++ transTerms e_trans
                                                ++ [transTerm1 ptrans_x,
                                                    transTerm1 ptrans_y])])
         m


-- | The monad for translating 'PermImpl's, which accumulates all failure
-- messages in all branches of a 'PermImpl' and either returns a result or
-- results in only failures
type PermImplTransM = MaybeT (Writer [String])

-- | Run a 'PermImplTransM' computation
runPermImplTransM :: PermImplTransM a -> (Maybe a, [String])
runPermImplTransM = runWriter . runMaybeT

-- | Catch any failures in a 'PermImplTransM' computation
pitmCatching :: PermImplTransM a -> PermImplTransM (Maybe a)
pitmCatching m = lift $ runMaybeT m

-- | Return or fail depending on whether the input is present or 'Nothing'
pitmMaybeRet :: Maybe a -> PermImplTransM a
pitmMaybeRet (Just a) = return a
pitmMaybeRet Nothing = mzero

-- | A failure continuation represents any catch that is around the current
-- 'PermImpl', and can either be a term to jump to / call (meaning that there is
-- a catch) or an error message (meaning there is not)
data ImplFailCont
     -- | A continuation that calls a term on failure
  = ImplFailContTerm OpenTerm
    -- | An error message to print on failure
  | ImplFailContMsg String

-- | "Force" the translation of a possibly failing computation to always return
-- a computation, even if it is just the failing computation
forceImplTrans :: Maybe (ImplFailCont ->
                         ImpTransM ext blocks tops ret ps ctx OpenTerm) ->
                  ImplFailCont ->
                  ImpTransM ext blocks tops ret ps ctx OpenTerm
forceImplTrans (Just trans) k = trans k
forceImplTrans Nothing (ImplFailContTerm errM) = return errM
forceImplTrans Nothing (ImplFailContMsg str) =
  returnTypeM >>= \tp ->
  return (applyOpenTermMulti (globalOpenTerm "Prelude.errorM")
          [tp, stringLitOpenTerm (pack str)])

-- | Perform a failure by jumping to a failure continuation or signaling an
-- error, using an alternate error message in the latter case
implTransAltErr :: String -> ImplFailCont ->
                   ImpTransM ext blocks tops ret ps ctx OpenTerm
implTransAltErr _ (ImplFailContTerm errM) = return errM
implTransAltErr str (ImplFailContMsg _) =
  returnTypeM >>= \tp ->
  return (applyOpenTermMulti (globalOpenTerm "Prelude.errorM")
          [tp, stringLitOpenTerm (pack str)])

-- | Translate a normal unary 'PermImpl1' rule that succeeds and applies the
-- translation function if the argument succeeds and fails if the translation of
-- the argument fails
translatePermImplUnary ::
  RL.TypeCtx bs =>
  ImplTranslateF r ext blocks tops ret =>
  Mb ctx (MbPermImpls r (RNil :> '(bs,ps_out))) ->
  (ImpTransM ext blocks tops ret ps_out (ctx :++: bs) OpenTerm ->
   ImpTransM ext blocks tops ret ps ctx OpenTerm) ->
  PermImplTransM
    (ImplFailCont -> ImpTransM ext blocks tops ret ps ctx OpenTerm)
translatePermImplUnary (mbMatch -> [nuMP| MbPermImpls_Cons _ _ mb_impl |]) f =
  translatePermImpl Proxy (mbCombine RL.typeCtxProxies mb_impl) >>= \trans ->
  return $ \k -> f $ trans k


-- | Translate a 'PermImpl1' to a function on translation computations
translatePermImpl1 :: ImplTranslateF r ext blocks tops ret =>
                      Proxy '(ext, blocks, tops, ret) ->
                      Mb ctx (PermImpl1 ps ps_outs) ->
                      Mb ctx (MbPermImpls r ps_outs) ->
                      PermImplTransM
                      (ImplFailCont ->
                       ImpTransM ext blocks tops ret ps ctx OpenTerm)
translatePermImpl1 prx mb_impl mb_impls = case (mbMatch mb_impl, mbMatch mb_impls) of
  -- A failure translates to a call to the catch handler, which is the most recent
  -- Impl1_Catch, if one exists, or the SAW errorM function otherwise
  ([nuMP| Impl1_Fail str |], _) ->
    tell [mbLift str] >> mzero
  
  ([nuMP| Impl1_Catch |],
   [nuMP| (MbPermImpls_Cons _ (MbPermImpls_Cons _ _ mb_impl1) mb_impl2) |]) ->
    pitmCatching (translatePermImpl prx $ mbCombine RL.typeCtxProxies mb_impl1) >>= \maybe_trans1 ->
    pitmCatching (translatePermImpl prx $ mbCombine RL.typeCtxProxies mb_impl2) >>= \maybe_trans2 ->
    case (maybe_trans1, maybe_trans2) of
      (Just trans1, Just trans2) ->
        return $ \k ->
        compReturnTypeM >>= \ret_tp ->
        letTransM "catchpoint" ret_tp (trans2 k)
        (\catchpoint -> trans1 $ ImplFailContTerm catchpoint)
      (Nothing, Just trans2) -> return trans2
      (_, Nothing) -> pitmMaybeRet maybe_trans1
  
  -- A push moves the given permission from x to the top of the perm stack
  ([nuMP| Impl1_Push x p |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do () <- assertVarPermM "Impl1_Push" x p
       ptrans <- getVarPermM x
       setVarPermM x (PTrans_True)
         (withPermStackM (:>: translateVar x) (:>: ptrans) m)
  
  -- A pop moves the given permission from the top of the perm stack to x
  ([nuMP| Impl1_Pop x p |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do () <- assertTopPermM "Impl1_Pop 1" x p
       () <- assertVarPermM "Impl1_Pop 2" x (nuMulti (mbToProxy p) $
                                             const ValPerm_True)
       ptrans <- getTopPermM
       setVarPermM x ptrans (withPermStackM RL.tail RL.tail m)
  
  -- If both branches of an or elimination fail, the whole thing fails; otherwise,
  -- an or elimination performs a pattern-match on an Either
  ([nuMP| Impl1_ElimOr x p1 p2 |],
   [nuMP| (MbPermImpls_Cons _ (MbPermImpls_Cons _ _ mb_impl1) mb_impl2) |]) ->
    pitmCatching (translatePermImpl prx $ mbCombine RL.typeCtxProxies mb_impl1) >>= \maybe_trans1 ->
    pitmCatching (translatePermImpl prx $ mbCombine RL.typeCtxProxies mb_impl2) >>= \maybe_trans2 ->
    case (maybe_trans1, maybe_trans2) of
      (Nothing, Nothing) -> mzero
      _ ->
        return $ \k ->
        do () <- assertTopPermM "Impl1_ElimOr" x (mbMap2 ValPerm_Or p1 p2)
           tp1 <- translate p1
           tp2 <- translate p2
           tp_ret <- compReturnTypeTransM
           top_ptrans <- getTopPermM
           eitherElimTransM tp1 tp2 tp_ret
             (\ptrans ->
               withPermStackM id ((:>: ptrans) . RL.tail) $
               forceImplTrans maybe_trans1 k)
             (\ptrans ->
               withPermStackM id ((:>: ptrans) . RL.tail) $
               forceImplTrans maybe_trans2 k)
             (transTupleTerm top_ptrans)
  
  -- An existential elimination performs a pattern-match on a Sigma
  ([nuMP| Impl1_ElimExists x p |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do () <- assertTopPermM "Impl1_ElimExists" x (fmap ValPerm_Exists p)
       let tp = mbBindingType p
       top_ptrans <- getTopPermM
       tp_trans <- translateClosed tp
       sigmaElimTransM "x_elimEx" tp_trans
         (flip inExtTransM $ translate $ mbCombine RL.typeCtxProxies p)
         compReturnTypeTransM
         (\etrans ptrans ->
           inExtTransM etrans $
           withPermStackM id ((:>: ptrans) . RL.tail) m)
         (transTerm1 top_ptrans)
  
  -- A SimplImpl is translated using translateSimplImpl
  ([nuMP| Impl1_Simpl simpl mb_prx |], _) ->
    let prx' = mbLift mb_prx in
    translatePermImplUnary mb_impls $ \m ->
    assertPermStackTopEqM "SimplImpl in" prx' (fmap simplImplIn simpl) >>= \() ->
    translateSimplImpl prx' simpl $
    do () <- assertPermStackTopEqM "SimplImpl out" prx' (fmap simplImplOut simpl)
       m
  
  -- A let binding becomes a let binding
  ([nuMP| Impl1_LetBind _ e |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do etrans <- translate e
       inExtTransM etrans $
         withPermStackM (:>: Member_Base) (:>: PTrans_Eq (extMb e)) m
  
  ([nuMP| Impl1_ElimStructField x _ _ memb |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do etrans_x <- translate x
       let etrans_y = case etrans_x of
             ETrans_Struct flds -> RL.get (mbLift memb) flds
             _ -> error "translatePermImpl1: Impl1_ElimStructField"
       let mb_y = mbCombine RL.typeCtxProxies $ fmap (const $ nu $ \y -> PExpr_Var y) x
       inExtTransM etrans_y $
         withPermStackM (:>: Member_Base)
         (\(pctx :>: PTrans_Conj [APTrans_Struct pctx_str]) ->
           pctx :>: PTrans_Conj [APTrans_Struct $
                                 RL.set (mbLift memb) (PTrans_Eq mb_y) pctx_str]
           :>: RL.get (mbLift memb) pctx_str)
         m
  
  ([nuMP| Impl1_ElimLLVMFieldContents _ mb_fld |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    inExtTransM ETrans_LLVM $
    withPermStackM (:>: Member_Base)
    (\(pctx :>: ptrans_x) ->
      let (_,ptrans') =
            unPTransLLVMField "translatePermImpl1: Impl1_ElimLLVMFieldContents"
            knownNat ptrans_x in
      pctx :>: PTrans_Conj [APTrans_LLVMField
                            (mbCombine RL.typeCtxProxies $
                             fmap (\fld -> nu $ \y ->
                                    fld { llvmFieldContents =
                                            ValPerm_Eq (PExpr_Var y)})
                             mb_fld) $
                            PTrans_Eq (mbCombine RL.typeCtxProxies $
                                       fmap (const $ nu PExpr_Var) mb_fld)]
      :>: ptrans')
    m
  
  ([nuMP| Impl1_ElimLLVMBlockToEq _ mb_bp |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    inExtTransM ETrans_LLVMBlock $
    do tp_trans1 <-
         translate (mbMap2 (\bp y ->
                             ValPerm_Conj1 $ Perm_LLVMBlock $
                             bp { llvmBlockShape = PExpr_EqShape $ PExpr_Var y })
                    (extMb mb_bp) $
                    nuMulti (mbToProxy mb_bp :>: Proxy) (\(_ :>: y) -> y))
       tp_trans2 <-
         translate $ fmap (ValPerm_Conj1 .
                           Perm_LLVMBlockShape . modalizeBlockShape) (extMb mb_bp)
       withPermStackM (:>: Member_Base)
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans1 [unitOpenTerm] :>:
           typeTransF tp_trans2 [transTerm1 ptrans])
         m
  
  ([nuMP| Impl1_BeginLifetime |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    inExtTransM ETrans_Lifetime $
    do tp_trans <- translateClosed $ ValPerm_LOwned MNil MNil
       let id_fun =
             lambdaOpenTerm "ps_empty" unitTypeOpenTerm $ \x ->
             applyOpenTermMulti (globalOpenTerm "Prelude.returnM")
             [unitTypeOpenTerm, x]
       withPermStackM (:>: Member_Base) (:>: typeTransF tp_trans [id_fun]) m
  
  -- If e1 and e2 are already equal, short-circuit the proof construction and then
  -- elimination
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_Eq e1 e2) _ |], _)
    | mbLift (mbMap2 bvEq e1 e2) ->
      translatePermImplUnary mb_impls $ \m ->
      do bv_tp <- typeTransType1 <$> translateClosed (mbExprType e1)
         e1_trans <- translate1 e1
         let pf = ctorOpenTerm "Prelude.Refl" [bv_tp, e1_trans]
         withPermStackM (:>: translateVar x)
           (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop pf)])
           m
  
  -- If e1 and e2 are definitely not equal, treat this as a fail
  ([nuMP| Impl1_TryProveBVProp _ (BVProp_Eq e1 e2) prop_str |], _)
    | not $ mbLift (mbMap2 bvCouldEqual e1 e2) ->
      tell [mbLift prop_str] >> mzero
  
  -- Otherwise, insert an equality test with proof construction. Note that, as
  -- with all TryProveBVProps, if the test fails and there is no failure
  -- continuation, we insert just the proposition failure string using
  -- implTransAltErr, not the entire type-checking error message, because this is
  -- considered just an assertion and not a failure
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_Eq e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl prx (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ \k ->
    do prop_tp_trans <- translate prop
       applyMultiTransM (return $ globalOpenTerm "Prelude.maybe")
         [ return (typeTransType1 prop_tp_trans), compReturnTypeM
         , implTransAltErr (mbLift prop_str) k
         , lambdaTransM "eq_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             trans k)
         , applyMultiTransM (return $ globalOpenTerm "Prelude.bvEqWithProof")
           [ return (natOpenTerm $ natVal2 prop) , translate1 e1, translate1 e2]]
  
  -- For an inequality test, we don't need a proof, so just insert an if
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_Neq e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl prx (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ \k ->
    let w = natVal2 prop in
    applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
    [ compReturnTypeM
    , applyMultiTransM (return $ globalOpenTerm "Prelude.bvEq")
      [ return (natOpenTerm w), translate1 e1, translate1 e2 ]
    , implTransAltErr (mbLift prop_str) k
    , withPermStackM (:>: translateVar x)
      (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop unitOpenTerm)]) $
      trans k]
  
  {-
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULt e1 e2) _ |],
   [nuMP| MbPermImpls_Cons _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      withPermStackM (:>: translateVar x)
      (:>: bvPropPerm (BVPropTrans prop
                       (ctorOpenTerm "Prelude.Refl" [globalOpenTerm "Prelude.Bool",
                                                     globalOpenTerm "Prelude.True"])))
      (translate $ mbCombine mb_impl')
  -}
  
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULt e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl prx (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ \k ->
    do prop_tp_trans <- translate prop
       applyMultiTransM (return $ globalOpenTerm "Prelude.maybe")
         [ return (typeTransType1 prop_tp_trans), compReturnTypeM
         , implTransAltErr (mbLift prop_str) k
         , lambdaTransM "ult_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             trans k)
         , applyMultiTransM (return $ globalOpenTerm "Prelude.bvultWithProof")
           [ return (natOpenTerm $ natVal2 prop), translate1 e1, translate1 e2]
         ]
  
  {-
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq e1 e2) _ |],
   [nuMP| MbPermImpls_Cons _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      withPermStackM (:>: translateVar x)
      (:>: bvPropPerm (BVPropTrans prop
                       (ctorOpenTerm "Prelude.Refl" [globalOpenTerm "Prelude.Bool",
                                                     globalOpenTerm "Prelude.True"])))
      (translate $ mbCombine mb_impl')
  -}
  
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl prx (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ \k ->
    do prop_tp_trans <- translate prop
       applyMultiTransM (return $ globalOpenTerm "Prelude.maybe")
         [ return (typeTransType1 prop_tp_trans), compReturnTypeM
         , implTransAltErr (mbLift prop_str) k
         , lambdaTransM "ule_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             trans k)
         , applyMultiTransM (return $ globalOpenTerm "Prelude.bvuleWithProof")
           [ return (natOpenTerm $ natVal2 prop), translate1 e1, translate1 e2]
         ]
  
  
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq_Diff e1 e2 e3) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl prx (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ \k ->
    do prop_tp_trans <- translate prop
       applyMultiTransM (return $ globalOpenTerm "Prelude.maybe")
         [ return (typeTransType1 prop_tp_trans), compReturnTypeM
         , implTransAltErr (mbLift prop_str) k
         , lambdaTransM "ule_diff_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             trans k)
         , applyMultiTransM (return $ globalOpenTerm "Prelude.bvuleWithProof")
           [ return (natOpenTerm $ natVal2 prop), translate1 e1,
             applyMultiTransM (return $ globalOpenTerm "Prelude.bvSub")
             [return (natOpenTerm $ natVal2 prop), translate1 e2, translate1 e3]]
         ]

  ([nuMP| Impl1_TryProveBVProp _ _ _ |], _) ->
    tell ["translatePermImpl1: Unhandled BVProp case"] >> mzero


-- | Translate a 'PermImpl' in the 'PermImplTransM' monad to a function that
-- takes a failure continuation and returns a monadic computation to generate
-- the translation as a term
translatePermImpl :: ImplTranslateF r ext blocks tops ret =>
                     Proxy '(ext, blocks, tops, ret) ->
                     Mb ctx (PermImpl r ps) ->
                     PermImplTransM
                     (ImplFailCont ->
                      ImpTransM ext blocks tops ret ps ctx OpenTerm)
translatePermImpl prx mb_impl = case mbMatch mb_impl of
  [nuMP| PermImpl_Done r |] ->
    return $ const $ translateF r
  [nuMP| PermImpl_Step impl1 mb_impls |] ->
    translatePermImpl1 prx impl1 mb_impls


instance ImplTranslateF r ext blocks tops ret =>
         Translate (ImpTransInfo
                    ext blocks tops ret ps) ctx (AnnotPermImpl r ps) OpenTerm where
  translate (mbMatch -> [nuMP| AnnotPermImpl err impl |]) =
    let (transF, errs) = runPermImplTransM $ translatePermImpl Proxy impl in
    forceImplTrans transF $
    ImplFailContMsg (mbLift err ++ "\n\n"
                     ++ concat (intersperse
                                "\n\n--------------------\n\n" errs))

-- We translate a LocalImplRet to a term that returns all current permissions
instance ImplTranslateF (LocalImplRet ps) ext blocks ps_in ret where
  translateF _ =
    do pctx <- itiPermStack <$> ask
       ret_tp <- returnTypeM
       return $ applyOpenTermMulti (globalOpenTerm "Prelude.returnM")
         [ret_tp, strictTransTupleTerm pctx]

-- | Translate a local implication to its output, adding an error message
translateLocalPermImpl :: String -> Mb ctx (LocalPermImpl ps_in ps_out) ->
                          ImpTransM ext blocks tops ret ps_in ctx OpenTerm
translateLocalPermImpl err (mbMatch -> [nuMP| LocalPermImpl impl |]) =
  clearVarPermsM $ translate $ fmap (AnnotPermImpl err) impl

-- | Translate a local implication over two sequences of permissions (already
-- translated to types) to a monadic function with the first sequence of
-- permissions as free variables and that takes in the second permissions as
-- arguments. Note that the translations of the second input permissions and the
-- output permissions must have exactly one type, i.e., already be tupled.
translateCurryLocalPermImpl ::
  String -> Mb ctx (LocalPermImpl (ps1 :++: ps2) ps_out) ->
  PermTransCtx ctx ps1 -> RAssign (Member ctx) ps1 ->
  TypeTrans (PermTransCtx ctx ps2) -> RAssign (Member ctx) ps2 ->
  TypeTrans (PermTransCtx ctx ps_out) ->
  ImpTransM ext blocks tops ret ps ctx OpenTerm
translateCurryLocalPermImpl err impl pctx1 vars1 tp_trans2 vars2 tp_trans_out =
  lambdaTransM "x_local" tp_trans2 $ \pctx2 ->
  local (\info -> info { itiReturnType = transTerm1 tp_trans_out }) $
  withPermStackM
    (const (RL.append vars1 vars2))
    (const (RL.append pctx1 pctx2))
    (translateLocalPermImpl err impl)


----------------------------------------------------------------------
-- * Translating Typed Crucible Expressions
----------------------------------------------------------------------

-- translate for a TypedReg yields an ExprTrans
instance TransInfo info =>
         Translate info ctx (TypedReg tp) (ExprTrans tp) where
  translate (mbMatch -> [nuMP| TypedReg x |]) = translate x

instance TransInfo info =>
         Translate info ctx (TypedRegs tps) (ExprTransCtx tps) where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedRegsNil |] -> return MNil
    [nuMP| TypedRegsCons rs r |] ->
      (:>:) <$> translate rs <*> translate r

instance TransInfo info =>
         Translate info ctx (RegWithVal tp) (ExprTrans tp) where
  translate mb_x = case mbMatch mb_x of
    [nuMP| RegWithVal _ e |] -> translate e
    [nuMP| RegNoVal x |] -> translate x

-- | Translate a 'RegWithVal' to exactly one SAW term via 'transTerm1'
translateRWV :: TransInfo info => Mb ctx (RegWithVal a) ->
                TransM info ctx OpenTerm
translateRWV mb_rwv = transTerm1 <$> translate mb_rwv

-- translate for a TypedExpr yields an ExprTrans
instance (PermCheckExtC ext, TransInfo info) =>
         Translate info ctx (App ext RegWithVal tp) (ExprTrans tp) where
  translate mb_e = case mbMatch mb_e of
    [nuMP| BaseIsEq BaseBoolRepr e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.boolEq")
      [translateRWV e1, translateRWV e2]
  --  [nuMP| BaseIsEq BaseNatRepr e1 e2 |] ->
  --    ETrans_Term <$>
  --    applyMultiTransM (return $ globalOpenTerm "Prelude.equalNat")
  --    [translateRWV e1, translateRWV e2]
    [nuMP| BaseIsEq (BaseBVRepr w) e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvEq")
      [translate w, translateRWV e1, translateRWV e2]
  
    [nuMP| EmptyApp |] -> return ETrans_Unit
  
    -- Booleans
    [nuMP| BoolLit True |] ->
      return $ ETrans_Term $ globalOpenTerm "Prelude.True"
    [nuMP| BoolLit False |] ->
      return $ ETrans_Term $ globalOpenTerm "Prelude.False"
    [nuMP| Not e |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.not")
      [translateRWV e]
    [nuMP| And e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.and")
      [translateRWV e1, translateRWV e2]
    [nuMP| Or e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.or")
      [translateRWV e1, translateRWV e2]
    [nuMP| BoolXor e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.xor")
      [translateRWV e1, translateRWV e2]
  
    -- Natural numbers
    [nuMP| Expr.NatLit n |] ->
      return $ ETrans_Term $ natOpenTerm $ mbLift n
    [nuMP| NatLt e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.ltNat")
      [translateRWV e1, translateRWV e2]
    -- [nuMP| NatLe _ _ |] ->
    [nuMP| NatEq e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.equalNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatAdd e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.addNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatSub e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.subNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatMul e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.mulNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatDiv e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.divNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatMod e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.modNat")
      [translateRWV e1, translateRWV e2]
  
    -- Function handles: the expression part of a function handle has no
    -- computational content
    [nuMP| HandleLit _ |] -> return ETrans_Fun
  
    -- Bitvectors
    [nuMP| BVLit w mb_bv |] ->
      return $ ETrans_Term $ bvLitOpenTerm (mbLift w) $ mbLift mb_bv
    [nuMP| BVConcat w1 w2 e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.join")
      [translate w1, translate w2, translateRWV e1, translateRWV e2]
    [nuMP| BVTrunc w1 w2 e |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvTrunc")
      [return (natOpenTerm (natValue (mbLift w2) - natValue (mbLift w1))),
       translate w1,
       translateRWV e]
    [nuMP| BVZext w1 w2 e |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvUExt")
      [return (natOpenTerm (natValue (mbLift w1) - natValue (mbLift w2))),
       translate w2, translateRWV e]
    [nuMP| BVSext w1 w2 e |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvSExt")
      [return (natOpenTerm (natValue (mbLift w1) - natValue (mbLift w2))),
       -- NOTE: bvSExt adds 1 to the 2nd arg
       return (natOpenTerm (natValue (mbLift w2) - 1)),
       translateRWV e]
    [nuMP| BVNot w e |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvNot")
      [translate w, translateRWV e]
    [nuMP| BVAnd w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvAnd")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVOr w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvOr")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVXor w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvXor")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVNeg w e |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvNeg")
      [translate w, translateRWV e]
    [nuMP| BVAdd w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvAdd")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSub w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvSub")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVMul w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvMul")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUdiv w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvUDiv")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSdiv w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvSDiv")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUrem w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvURem")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSrem w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvSRem")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUle w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvule")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUlt w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvult")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSle w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvsle")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSlt w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvslt")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVCarry w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvCarry")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSCarry w e1 e2 |] ->
      -- NOTE: bvSCarry adds 1 to the bitvector length
      let w_minus_1 = natOpenTerm (natValue (mbLift w) - 1) in
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvSCarry")
      [return w_minus_1, translateRWV e1, translateRWV e2]
    [nuMP| BVSBorrow w e1 e2 |] ->
      -- NOTE: bvSBorrow adds 1 to the bitvector length
      let w_minus_1 = natOpenTerm (natValue (mbLift w) - 1) in
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvSBorrow")
      [return w_minus_1, translateRWV e1, translateRWV e2]
    [nuMP| BVShl w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvShiftL")
      [translate w, return (globalOpenTerm "Prelude.Bool"), translate w,
       return (globalOpenTerm "Prelude.False"), translateRWV e1, translateRWV e2]
    [nuMP| BVLshr w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvShiftR")
      [translate w, return (globalOpenTerm "Prelude.Bool"), translate w,
       return (globalOpenTerm "Prelude.False"), translateRWV e1, translateRWV e2]
    [nuMP| BVAshr w e1 e2 |] ->
      let w_minus_1 = natOpenTerm (natValue (mbLift w) - 1) in
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.bvSShiftR")
      [return w_minus_1, return (globalOpenTerm "Prelude.Bool"), translate w,
       translateRWV e1, translateRWV e2]
    [nuMP| BoolToBV mb_w e |] ->
      let w = mbLift mb_w in
      ETrans_Term <$>
      applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
      [bitvectorTransM (translate mb_w),
       translateRWV e,
       return (bvLitOpenTerm w (BV.one w)),
       return (bvLitOpenTerm w (BV.zero w))]
    [nuMP| BVNonzero mb_w e |] ->
      let w = mbLift mb_w in
      ETrans_Term <$>
      applyTransM (return $ globalOpenTerm "Prelude.not")
      (applyMultiTransM (return $ globalOpenTerm "Prelude.bvEq")
       [translate mb_w, translateRWV e,
        return (bvLitOpenTerm w (BV.zero w))])
  
    -- Strings
    [nuMP| Expr.StringLit (UnicodeLiteral text) |] ->
      return $ ETrans_Term $ stringLitOpenTerm $
      mbLift text
  
    -- Everything else is an error
    _ ->
      error ("Unhandled expression form: " ++
              (renderString (layoutSmart opts (mbLift $ fmap (ppApp (const $ pretty ("_" :: String))) mb_e))))
        where opts = PP.LayoutOptions (PP.AvailablePerLine 80 0.8)


-- translate for a TypedExpr yields an ExprTrans
instance (PermCheckExtC ext, TransInfo info) =>
         Translate info ctx (TypedExpr ext tp) (ExprTrans tp) where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedExpr _ (Just e) |] -> translate e
    [nuMP| TypedExpr app Nothing |] -> translate app

-- | Get the output permission on the return value of a 'TypedExpr'
exprOutPerm :: PermCheckExtC ext => Mb ctx (TypedExpr ext tp) ->
               PermTrans ctx tp
exprOutPerm mb_x = case mbMatch mb_x of
  [nuMP| TypedExpr _ (Just e) |] -> PTrans_Eq e
  [nuMP| TypedExpr _ Nothing |] -> PTrans_True


----------------------------------------------------------------------
-- * Translating Typed Crucible Jump Targets
----------------------------------------------------------------------

{-
debugPrettyPermCtx :: RAssign Proxy ctx -> PermTransCtx ctx ps -> [Doc]
debugPrettyPermCtx _ MNil = []
debugPrettyPermCtx prxs (ptranss :>: ptrans) =
  debugPrettyPermCtx prxs ptranss ++
  [permPretty emptyPPInfo (permTransPerm prxs ptrans) <+>
   string ("(" ++ show (length $ transTerms ptrans) ++ " terms)")]
-}

-- | Apply the translation of a function-like construct (i.e., a
-- 'TypedJumpTarget' or 'TypedFnHandle') to the pure plus impure translations of
-- its arguments, given as 'DistPerms', which should match the current
-- stack. The 'String' argument is the name of the construct being applied, for
-- use in error reporting.
translateApply :: String -> OpenTerm -> Mb ctx (DistPerms ps) ->
                  ImpTransM ext blocks tops ret ps ctx OpenTerm
translateApply nm f perms =
  do expr_ctx <- itiExprCtx <$> ask
     arg_membs <- itiPermStackVars <$> ask
     let e_args = RL.map (flip RL.get expr_ctx) arg_membs
     i_args <- itiPermStack <$> ask
     return $
       trace ("translateApply for " ++ nm ++ " with perm arguments:\n" ++
              -- renderDoc (list $ debugPrettyPermCtx (mbToProxy perms) i_args)
              -- permPrettyString emptyPPInfo (permTransCtxPerms (mbToProxy perms) i_args)
              permPrettyString emptyPPInfo perms
             ) $
       applyOpenTermMulti f (exprCtxToTerms e_args ++ permCtxToTerms i_args)

-- | Translate a call to (the translation of) an entrypoint, by either calling
-- the letrec-bound variable for the entrypoint, if it has one, or by just
-- translating the body of the entrypoint if it does not.
translateCallEntry :: forall ext tops args ghosts blocks ctx ret.
                      PermCheckExtC ext => String ->
                      TypedEntryTrans ext blocks tops ret args ghosts ->
                      Mb ctx (RAssign ExprVar (tops :++: args)) ->
                      Mb ctx (RAssign ExprVar ghosts) ->
                      ImpTransM ext blocks tops ret
                      ((tops :++: args) :++: ghosts) ctx OpenTerm
translateCallEntry nm entry_trans mb_tops_args mb_ghosts =
  -- First test that the stack == the required perms for entryID
  do let entry = typedEntryTransEntry entry_trans
     let mb_s =
           mbMap2 (\tops_args ghosts ->
                    permVarSubstOfNames $ RL.append tops_args ghosts)
           mb_tops_args mb_ghosts
     let mb_perms = fmap (\s -> varSubst s $ mbValuePermsToDistPerms $
                                typedEntryPermsIn entry) mb_s
     () <- assertPermStackEqM nm mb_perms

     -- Now check if entryID has an associated letRec-bound function
     case typedEntryTransFun entry_trans of
       Just f ->
         -- If so, call the letRec-bound function
         translateApply nm f mb_perms
       Nothing ->
         -- If not, continue by translating entry, setting the variable
         -- permission map to empty (as in the beginning of a block)
         clearVarPermsM $ translate $
         fmap (\s -> varSubst s $ typedEntryBody entry) mb_s


instance PermCheckExtC ext =>
         Translate (ImpTransInfo ext blocks tops ret ps) ctx
         (CallSiteImplRet blocks tops args ghosts ps) OpenTerm where
  translate (mbMatch ->
             [nuMP| CallSiteImplRet entryID ghosts Refl mb_tavars mb_gvars |]) =
    do entry_trans <-
         lookupEntryTransCast (mbLift entryID) (mbLift ghosts) <$>
         itiBlockMapTrans <$> ask
       translateCallEntry "CallSiteImplRet" entry_trans mb_tavars mb_gvars

instance PermCheckExtC ext =>
         ImplTranslateF (CallSiteImplRet blocks tops args ghosts)
         ext blocks tops ret where
  translateF mb_tgt = translate mb_tgt


instance PermCheckExtC ext =>
         Translate (ImpTransInfo ext blocks tops ret ps) ctx
         (TypedJumpTarget blocks tops ps) OpenTerm where
  translate (mbMatch -> [nuMP| TypedJumpTarget siteID _ _ mb_perms_in |]) =
    do SomeTypedCallSite site <-
         lookupCallSite (mbLift siteID) <$> itiBlockMapTrans <$> ask
       let CallSiteImpl mb_impl = typedCallSiteImpl site
       translate $ flip fmap mb_perms_in $ \perms_in ->
         varSubst (permVarSubstOfNames $ distPermsVars perms_in) mb_impl

instance PermCheckExtC ext =>
         ImplTranslateF (TypedJumpTarget blocks tops) ext blocks tops ret where
  translateF mb_tgt = translate mb_tgt


----------------------------------------------------------------------
-- * Translating Typed Crucible Statements
----------------------------------------------------------------------

-- | Translate a 'TypedStmt' to a function on translation computations
translateStmt :: PermCheckExtC ext =>
                 ProgramLoc -> Mb ctx (TypedStmt ext rets ps_in ps_out) ->
                 ImpTransM ext blocks tops ret ps_out (ctx :++: rets) OpenTerm ->
                 ImpTransM ext blocks tops ret ps_in ctx OpenTerm
translateStmt loc mb_stmt m = case mbMatch mb_stmt of
  [nuMP| TypedSetReg _ e |] ->
    do etrans <- tpTransM $ translate e
       let ptrans = exprOutPerm e
       inExtTransM etrans $
         withPermStackM (:>: Member_Base) (:>: extPermTrans ptrans) m
  
  [nuMP| TypedSetRegPermExpr _ e |] ->
    do etrans <- tpTransM $ translate e
       inExtTransM etrans $
         withPermStackM (:>: Member_Base) (:>: PTrans_Eq (extMb e)) m
  
  [nuMP| stmt@(TypedCall _freg fun_perm _ gexprs args) |] ->
    do f_trans <- getTopPermM
       let f = case f_trans of
             PTrans_Conj [APTrans_Fun _ f_trm] -> f_trm
             _ -> error "translateStmt: TypedCall: unexpected function permission"
       -- let perms_in = fmap (distPermsSnoc . typedStmtIn) stmt
       let perms_out = mbCombine RL.typeCtxProxies
                     $ fmap (\stmt' -> nu $ \ret ->
                                          typedStmtOut stmt' (MNil :>: ret)) stmt
       ret_tp <- translate $ fmap funPermRet fun_perm
       ectx_gexprs <- translate gexprs
       ectx_args <- translate args
       pctx_in <- RL.tail <$> itiPermStack <$> ask
       let (pctx_ghosts_args, _) =
             RL.split (RL.append ectx_gexprs ectx_args) ectx_gexprs pctx_in
       let fret_trm =
             applyOpenTermMulti f (exprCtxToTerms ectx_gexprs
                                   ++ exprCtxToTerms ectx_args
                                   ++ permCtxToTerms pctx_ghosts_args)
       fret_tp <- sigmaTypeTransM "ret" ret_tp (flip inExtTransM
                                                (translate perms_out))
       applyMultiTransM (return $ globalOpenTerm "Prelude.bindM")
         [return fret_tp, returnTypeM, return fret_trm,
          lambdaOpenTermTransM "call_ret_val" fret_tp $ \ret_val ->
           sigmaElimTransM "elim_call_ret_val" ret_tp
           (flip inExtTransM (translate perms_out)) compReturnTypeTransM
           (\ret_trans pctx ->
             inExtTransM ret_trans $
             withPermStackM
             (\(vars :>: _) ->
               (fst (RL.split Proxy ectx_gexprs vars) :>: Member_Base))
             (const pctx)
             m)
           ret_val]
  
  -- FIXME HERE: figure out why these asserts always translate to ite True
  [nuMP| TypedAssert e _ |] ->
    applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
    [compReturnTypeM, translate1 e, m,
     mkErrorCompM ("Failed Assert at " ++
                   renderDoc (ppShortFileName (plSourceLoc loc)))]
  
  [nuMP| TypedLLVMStmt stmt |] -> translateLLVMStmt stmt m


-- | Translate a 'TypedStmt' to a function on translation computations
translateLLVMStmt ::
  Mb ctx (TypedLLVMStmt r ps_in ps_out) ->
  ImpTransM ext blocks tops ret ps_out (ctx :> r) OpenTerm ->
  ImpTransM ext blocks tops ret ps_in ctx OpenTerm
translateLLVMStmt mb_stmt m = case mbMatch mb_stmt of
  [nuMP| ConstructLLVMWord (TypedReg x) |] ->
    inExtTransM ETrans_LLVM $
    withPermStackM (:>: Member_Base) (:>: (PTrans_Eq $ extMb $
                                           fmap (PExpr_LLVMWord . PExpr_Var) x)) m
  
  [nuMP| AssertLLVMWord reg _ |] ->
    inExtTransM (ETrans_Term $ natOpenTerm 0) $
    withPermStackM ((:>: Member_Base) . RL.tail)
    ((:>: (PTrans_Eq $ fmap (const $ PExpr_Nat 0) $ extMb reg)) . RL.tail)
    m
  
  [nuMP| AssertLLVMPtr _ |] ->
    inExtTransM ETrans_Unit $
    withPermStackM RL.tail RL.tail m
  
  [nuMP| DestructLLVMWord _ e |] ->
    translate e >>= \etrans ->
    inExtTransM etrans $
    withPermStackM ((:>: Member_Base) . RL.tail)
    ((:>: (PTrans_Eq $ extMb e)) . RL.tail)
    m
  
  [nuMP| OffsetLLVMValue x off |] ->
    inExtTransM ETrans_LLVM $
    withPermStackM (:>: Member_Base)
    (:>: (PTrans_Eq $ extMb $
          mbMap2 PExpr_LLVMOffset (fmap typedRegVar x) off))
    m
  
  [nuMP| TypedLLVMLoad _ (mb_fp :: LLVMFieldPerm w sz)
                       (_ :: DistPerms ps) cur_perms |] ->
    let prx_l = mbLifetimeCurrentPermsProxies cur_perms
        prx_ps :: Proxy (ps :> LLVMPointerType w) = Proxy in
    inExtTransM ETrans_LLVM $
    withPermStackM
    (\(RL.split prx_ps prx_l -> (vars, vars_l)) ->
      RL.append (vars :>: Member_Base) vars_l)
    (\(RL.split prx_ps prx_l -> (pctx :>: p_ptr, pctx_l)) ->
      let (_, p_ret) =
            unPTransLLVMField "translateLLVMStmt: TypedLLVMLoad: expected field perm"
            (knownNat @sz) p_ptr in
      withKnownNat ?ptrWidth $
      RL.append
      (pctx :>: PTrans_Conj [APTrans_LLVMField
                             (mbCombine RL.typeCtxProxies $
                              fmap (\fp -> nu $ \ret ->
                                     fp { llvmFieldContents =
                                            ValPerm_Eq (PExpr_Var ret)}) mb_fp)
                             (PTrans_Eq $ mbCombine RL.typeCtxProxies $
                              fmap (const $ nu $ \ret -> PExpr_Var ret) mb_fp)]
       :>: p_ret) pctx_l)
    m
  
  [nuMP| TypedLLVMStore _ (mb_fp :: LLVMFieldPerm w sz) mb_e
                        (_ :: DistPerms ps) cur_perms |] ->
    let prx_l = mbLifetimeCurrentPermsProxies cur_perms
        prx_ps :: Proxy (ps :> LLVMPointerType w) = Proxy in
    withKnownNat ?ptrWidth $
    inExtTransM ETrans_Unit $
    withPermStackM id
    (\(RL.split prx_ps prx_l -> (pctx :>: _p_ptr, pctx_l)) ->
      RL.append
      (pctx :>: PTrans_Conj [APTrans_LLVMField
                             (extMb $ mbMap2 (\fp e ->
                                               fp { llvmFieldContents =
                                                      ValPerm_Eq e })
                              mb_fp mb_e)
                             (PTrans_Eq $ extMb mb_e)])
      pctx_l)
    m
  
  [nuMP| TypedLLVMAlloca _ (mb_fperm :: LLVMFramePerm w) mb_sz |] ->
    let sz = mbLift mb_sz
        w :: Proxy w = Proxy in
    withKnownNat ?ptrWidth $
    inExtTransM ETrans_LLVM $
    translateClosed (llvmFieldsPermOfSize w sz) >>= \ptrans_tp ->
    withPermStackM (:>: Member_Base)
    (\(pctx :>: _) ->
      pctx
      :>: PTrans_Conj [APTrans_LLVMFrame $
                       flip nuMultiWithElim1 (extMb mb_fperm) $
                       \(_ :>: ret) fperm -> (PExpr_Var ret, sz):fperm]
      :>: typeTransF ptrans_tp [])
    m
  
  [nuMP| TypedLLVMCreateFrame |] ->
    withKnownNat ?ptrWidth $
    inExtTransM ETrans_LLVMFrame $
    withPermStackM (:>: Member_Base)
    (:>: PTrans_Conj [APTrans_LLVMFrame $ fmap (const []) (extMb mb_stmt)])
    m
  
  [nuMP| TypedLLVMDeleteFrame _ _ _ |] ->
    inExtTransM ETrans_Unit $
    withPermStackM (const MNil) (const MNil) m
  
  [nuMP| TypedLLVMLoadHandle _ tp _ |] ->
    inExtTransM ETrans_Fun $
    withPermStackM ((:>: Member_Base) . RL.tail)
    (\(pctx :>: PTrans_Conj [APTrans_LLVMFunPtr tp' ptrans]) ->
      case testEquality (mbLift tp) tp' of
        Just Refl -> pctx :>: ptrans
        _ -> error ("translateLLVMStmt: TypedLLVMLoadHandle: "
                    ++ "unexpected function permission type"))
    m
  
  [nuMP| TypedLLVMResolveGlobal gsym (p :: ValuePerm (LLVMPointerType w))|] ->
    withKnownNat ?ptrWidth $
    inExtTransM ETrans_LLVM $
    do env <- infoEnv <$> ask
       ptrans <- translate $ extMb p
       let w :: NatRepr w = knownRepr
       case lookupGlobalSymbol env (mbLift gsym) w of
         Nothing -> error ("translateLLVMStmt: TypedLLVMResolveGlobal: "
                           ++ " no translation of symbol "
                           ++ globalSymbolName (mbLift gsym))
         Just (_, ts) ->
           withPermStackM (:>: Member_Base) (:>: typeTransF ptrans ts) m
  
  [nuMP| TypedLLVMIte _ mb_r1 _ _ |] ->
    inExtTransM ETrans_LLVM $
    do b <- translate1 $ extMb mb_r1
       tptrans <-
         translate $ mbCombine RL.typeCtxProxies $ flip fmap mb_stmt $ \stmt -> nu $ \ret ->
         distPermsHeadPerm $ typedLLVMStmtOut stmt ret
       let t = applyOpenTerm (globalOpenTerm "Prelude.boolToEither") b
       withPermStackM (:>: Member_Base) (:>: typeTransF tptrans [t]) m


----------------------------------------------------------------------
-- * Translating Sequences of Typed Crucible Statements
----------------------------------------------------------------------

instance PermCheckExtC ext =>
         Translate (ImpTransInfo ext blocks tops ret ps) ctx
         (TypedRet tops ret ps) OpenTerm where
  translate (mbMatch -> [nuMP| TypedRet Refl tp r mb_perms |]) =
    do let perms =
             mbMap2
             (\reg mbps -> varSubst (singletonVarSubst $ typedRegVar reg) mbps)
             r mb_perms
       () <- assertPermStackEqM "TypedRet" perms
       r_trans <- translate r
       tp_trans <- translate tp
       ret_tp <- returnTypeM
       sigma_trm <-
         sigmaTransM "r" tp_trans (flip inExtTransM $
                                   translate $ mbCombine RL.typeCtxProxies mb_perms)
         r_trans (itiPermStack <$> ask)
       return $
         applyOpenTermMulti (globalOpenTerm "Prelude.returnM")
         [ret_tp, sigma_trm]

instance PermCheckExtC ext =>
         ImplTranslateF (TypedRet tops ret) ext blocks tops ret where
  translateF mb_ret = translate mb_ret

instance PermCheckExtC ext =>
         Translate (ImpTransInfo ext blocks tops ret ps) ctx
         (TypedTermStmt blocks tops ret ps) OpenTerm where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedJump impl_tgt |] -> translate impl_tgt
    [nuMP| TypedBr reg impl_tgt1 impl_tgt2 |] ->
      applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
      [compReturnTypeM, translate1 reg,
       translate impl_tgt1, translate impl_tgt2]
    [nuMP| TypedReturn impl_ret |] -> translate impl_ret
    [nuMP| TypedErrorStmt (Just str) _ |] ->
      mkErrorCompM ("Error: " ++ mbLift str)
    [nuMP| TypedErrorStmt Nothing _ |] ->
      mkErrorCompM "Error (unknown message)"


instance PermCheckExtC ext =>
         Translate (ImpTransInfo ext blocks tops ret ps) ctx
         (TypedStmtSeq ext blocks tops ret ps) OpenTerm where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedImplStmt impl_seq |] -> translate impl_seq
    [nuMP| TypedConsStmt loc stmt pxys mb_seq |] ->
      translateStmt (mbLift loc) stmt (translate $ mbCombine (mbLift pxys) mb_seq)
    [nuMP| TypedTermStmt _ term_stmt |] -> translate term_stmt

instance PermCheckExtC ext =>
         ImplTranslateF (TypedStmtSeq
                         ext blocks tops ret) ext blocks tops ret where
  translateF mb_seq = translate mb_seq


----------------------------------------------------------------------
-- * Translating CFGs
----------------------------------------------------------------------

-- | An entrypoint over some regular and ghost arguments
data SomeTypedEntry ext blocks tops ret =
  forall ghosts args.
  SomeTypedEntry (TypedEntry TransPhase ext blocks tops ret args ghosts)

-- | Get all entrypoints in a block map that will be translated to letrec-bound
-- variables, which is all entrypoints with in-degree > 1
--
-- FIXME: consider whether we want let and not letRec for entrypoints that have
-- in-degree > 1 but are not the heads of loops
typedBlockLetRecEntries :: TypedBlockMap TransPhase ext blocks tops ret ->
                           [SomeTypedEntry ext blocks tops ret]
typedBlockLetRecEntries =
  concat . RL.mapToList (map (\(Some entry) ->
                               SomeTypedEntry entry)
                         . filter (anyF typedEntryHasMultiInDegree)
                         . (^. typedBlockEntries))

-- | Fold a function over each 'TypedEntry' in a 'TypedBlockMap' that
-- corresponds to a letrec-bound variable
foldBlockMapLetRec ::
  (forall args ghosts.
   TypedEntry TransPhase ext blocks tops ret args ghosts -> b -> b) ->
  b -> TypedBlockMap TransPhase ext blocks tops ret -> b
foldBlockMapLetRec f r =
  foldr (\(SomeTypedEntry entry) -> f entry) r . typedBlockLetRecEntries

-- | Construct a @LetRecType@ inductive description
--
-- > LRT_Fun tp1 \(x1 : tp1) -> ... -> LRT_Fun tpn \(xn : tpn) -> body x1 ... xn
--
-- of a pi abstraction over the types @tpi@ in a 'TypeTrans', passing the
-- abstracted variables to the supplied @body@ function
piLRTTransM :: String -> TypeTrans tr -> (tr -> TransM info ctx OpenTerm) ->
               TransM info ctx OpenTerm
piLRTTransM x tps body_f =
  foldr (\(i,tp) rest_f vars ->
          (\t -> ctorOpenTerm "Prelude.LRT_Fun" [tp, t]) <$>
          lambdaOpenTermTransM (x ++ show (i :: Integer)) tp
          (\var -> rest_f (vars ++ [var])))
  (body_f . typeTransF tps) (zip [0..] $ typeTransTypes tps) []

-- | Build a @LetRecType@ that describes the type of the translation of a
-- 'TypedEntry'
translateEntryLRT :: TypedEntry TransPhase ext blocks tops ret args ghosts ->
                     TypeTransM ctx OpenTerm
translateEntryLRT entry@(TypedEntry {..}) =
  trace "translateEntryLRT starting..." $ inEmptyCtxTransM $
  translateClosed (typedEntryAllArgs entry) >>= \arg_tps ->
  piLRTTransM "arg" arg_tps $ \ectx ->
  inCtxTransM ectx $
  translate typedEntryPermsIn >>= \perms_in_tps ->
  piLRTTransM "p" perms_in_tps $ \_ ->
  translateEntryRetType entry >>= \retType ->
  trace "translateEntryLRT finished" $
  return $ ctorOpenTerm "Prelude.LRT_Ret" [retType]

-- | Build a @LetRecTypes@ list that describes the types of all of the
-- entrypoints in a 'TypedBlockMap'
translateBlockMapLRTs :: TypedBlockMap TransPhase ext blocks tops ret ->
                         TypeTransM ctx OpenTerm
translateBlockMapLRTs =
  trace "translateBlockMapLRTs started..." $
  foldBlockMapLetRec
  (\entry rest_m ->
    do entryType <- translateEntryLRT entry
       rest <- rest_m
       return $ ctorOpenTerm "Prelude.LRT_Cons" [entryType, rest])
  (trace "translateBlockMapLRTs finished" $
   return $ ctorOpenTerm "Prelude.LRT_Nil" [])

-- | Lambda-abstract over all the entrypoints in a 'TypedBlockMap' that
-- correspond to letrec-bound functions, putting the lambda-bound variables into
-- a 'TypedBlockMapTrans' structure and passing it to the supplied body function
lambdaBlockMap :: TypedBlockMap TransPhase ext blocks tops ret ->
                  (TypedBlockMapTrans ext blocks tops ret ->
                   TypeTransM ctx OpenTerm) ->
                  TypeTransM ctx OpenTerm
lambdaBlockMap = helper where
  helper :: RAssign (TypedBlock TransPhase ext blocks tops ret) blks ->
            (RAssign (TypedBlockTrans ext blocks tops ret) blks ->
             TypeTransM ctx OpenTerm) ->
            TypeTransM ctx OpenTerm
  helper MNil f = f MNil
  helper (blks :>: blk) f =
    helper blks $
    foldl
    (\g (Some entry) entry_transs blks_trans ->
      if typedEntryHasMultiInDegree entry then
        do entryLRT <- translateEntryLRT entry
           lambdaOpenTermTransM "f" (applyOpenTerm
                                     (globalOpenTerm "Prelude.lrtToType")
                                     entryLRT) $ \fvar ->
             g (Some (TypedEntryTrans entry $ Just fvar) : entry_transs) blks_trans
      else
        g (Some (TypedEntryTrans entry Nothing) : entry_transs) blks_trans)
    (\entry_transs blks_trans ->
      f (blks_trans :>: TypedBlockTrans entry_transs))
    (blk ^. typedBlockEntries)
    []

-- | Translate the typed statements of an entrypoint to a function
--
-- > \top1 ... topn arg1 ... argm ghost1 ... ghostk p1 ... pj -> stmts_trans
--
-- over the top-level, local, and ghost arguments and (the translations of) the
-- input permissions of the entrypoint
translateEntryBody :: PermCheckExtC ext =>
                      TypedBlockMapTrans ext blocks tops ret ->
                      TypedEntry TransPhase ext blocks tops ret args ghosts ->
                      TypeTransM ctx OpenTerm
translateEntryBody mapTrans entry =
  inEmptyCtxTransM $
  lambdaExprCtx (typedEntryAllArgs entry) $
  lambdaPermCtx (typedEntryPermsIn entry) $ \pctx ->
  do retType <- translateEntryRetType entry
     impTransM (RL.members pctx) pctx mapTrans retType $ translate $
       typedEntryBody entry

-- | Translate all the entrypoints in a 'TypedBlockMap' that correspond to
-- letrec-bound functions to SAW core functions as in 'translateEntryBody'
translateBlockMapBodies :: PermCheckExtC ext =>
                           TypedBlockMapTrans ext blocks tops ret ->
                           TypedBlockMap TransPhase ext blocks tops ret ->
                           TypeTransM ctx OpenTerm
translateBlockMapBodies mapTrans =
  trace "translateBlockMapBodies starting..." $
  foldBlockMapLetRec
  (\entry restM ->
    pairOpenTerm <$> translateEntryBody mapTrans entry <*> restM)
  (trace "translateBlockMapBodies finished" $ return unitOpenTerm)


-- | Translate a typed CFG to a SAW term
translateCFG ::
  PermCheckExtC ext =>
  PermEnv ->
  TypedCFG ext blocks ghosts inits ret ->
  OpenTerm
translateCFG env (cfg :: TypedCFG ext blocks ghosts inits ret) =
  let h = tpcfgHandle cfg
      fun_perm = tpcfgFunPerm cfg
      blkMap = tpcfgBlockMap cfg
      ctx = typedFnHandleAllArgs h
      inits = typedFnHandleArgs h
      ghosts = typedFnHandleGhosts h
      retType = typedFnHandleRetType h in
  flip runNilTypeTransM env $ lambdaExprCtx ctx $

  -- We translate retType before extending the expr context to contain another
  -- copy of inits, as it is easier to do it here
  translateRetType retType (tpcfgOutputPerms cfg) >>= \retTypeTrans ->

  -- Extend the expr context to contain another copy of the initial arguments
  -- inits, since the initial entrypoint for the entire function takes two
  -- copies of inits, one to represent the top-level arguments and one to
  -- represent the local arguments to the entrypoint, which just happen to be
  -- the same as those top-level arguments and so get eq perms to relate them
  inExtMultiTransCopyLastM ghosts (cruCtxProxies inits) $

  -- Lambda-abstract over the permissions on the ghosts plus normal arguments;
  -- the second copy (discussed above) of the initial arguments get assigned
  -- their eq perms later
  lambdaPermCtx (extMbMulti (cruCtxProxies inits) $
                 funPermIns fun_perm) $ \pctx ->

  do -- retTypeTrans <-
     --   translateRetType retType (mbCombine $ tpcfgOutputPerms cfg)
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
           let all_membs = RL.members (cruCtxProxies $ appendCruCtx ctx inits)
               inits_membs =
                 snd $ RL.split ghosts (cruCtxProxies inits) $
                 fst $ RL.split ctx (cruCtxProxies inits) all_membs
               inits_eq_perms = eqPermTransCtx all_membs inits_membs
               all_pctx = RL.append pctx inits_eq_perms
               init_entry =
                 lookupEntryTransCast (tpcfgEntryID cfg) CruCtxNil mapTrans in
           impTransM all_membs all_pctx mapTrans retTypeTrans
           (assertPermStackEqM "translateCFG" (mbValuePermsToDistPerms $
                                               funPermToBlockInputs fun_perm)
            >>
            let px = RL.map (\_ -> Proxy) all_pctx in
            translateCallEntry "CFG" init_entry
            (nuMulti px id) (nuMulti px (\_ -> MNil))))
       ]


----------------------------------------------------------------------
-- * Translating Sets of CFGs
----------------------------------------------------------------------

-- | An existentially quantified tuple of a 'CFG', its function permission, and
-- a 'String' name we want to translate it to
data SomeCFGAndPerm ext where
  SomeCFGAndPerm :: GlobalSymbol -> String -> CFG ext blocks inits ret ->
                    FunPerm ghosts (CtxToRList inits) ret ->
                    SomeCFGAndPerm ext

-- | Extract the 'GlobalSymbol' from a 'SomeCFGAndPerm'
someCFGAndPermSym :: SomeCFGAndPerm ext -> GlobalSymbol
someCFGAndPermSym (SomeCFGAndPerm sym _ _ _) = sym

-- | Extract the 'String' name from a 'SomeCFGAndPerm'
someCFGAndPermToName :: SomeCFGAndPerm ext -> String
someCFGAndPermToName (SomeCFGAndPerm _ nm _ _) = nm

-- | Convert the 'FunPerm' of a 'SomeCFGAndPerm' to an inductive @LetRecType@
-- description of the SAW core type it translates to
someCFGAndPermLRT :: PermEnv -> SomeCFGAndPerm ext -> OpenTerm
someCFGAndPermLRT env (SomeCFGAndPerm _ _ _
                       (FunPerm ghosts args ret perms_in perms_out)) =
  flip runNilTypeTransM env $
  translateClosed (appendCruCtx ghosts args) >>= \ctx_trans ->
  piLRTTransM "arg" ctx_trans $ \ectx ->
  inCtxTransM ectx $
  translate perms_in >>= \perms_trans ->
  piLRTTransM "perm" perms_trans $ \_ ->
  translateRetType ret perms_out >>= \ret_tp ->
  return $ ctorOpenTerm "Prelude.LRT_Ret" [ret_tp]

-- | Extract the 'FunPerm' of a 'SomeCFGAndPerm' as a permission on LLVM
-- function pointer values
someCFGAndPermPtrPerm ::
  HasPtrWidth w =>
  SomeCFGAndPerm LLVM ->
  ValuePerm (LLVMPointerType w)
someCFGAndPermPtrPerm (SomeCFGAndPerm _ _ _ fun_perm) =
  withKnownNat ?ptrWidth $ ValPerm_Conj1 $ mkPermLLVMFunPtr ?ptrWidth fun_perm


-- | Type-check a set of 'CFG's against their function permissions and translate
-- the result to a pair of a @LetRecTypes@ SAW core term @lrts@ describing the
-- function permissions and a mutually-recursive function-binding argument
--
-- > \(f1:tp1) -> ... -> \(fn:tpn) -> (tp1, ..., tpn)
--
-- that defines the functions mutually recursively in terms of themselves, where
-- each @tpi@ is the @i@th type in @lrts@
tcTranslateCFGTupleFun ::
  HasPtrWidth w =>
  PermEnv -> EndianForm -> [SomeCFGAndPerm LLVM] ->
  (OpenTerm, OpenTerm)
tcTranslateCFGTupleFun env endianness cfgs_and_perms =
  let lrts = map (someCFGAndPermLRT env) cfgs_and_perms in
  let lrts_tm =
        foldr (\lrt lrts' -> ctorOpenTerm "Prelude.LRT_Cons" [lrt,lrts'])
        (ctorOpenTerm "Prelude.LRT_Nil" [])
        lrts in
  (lrts_tm ,) $
  lambdaOpenTermMulti (zip
                       (map (pack . someCFGAndPermToName) cfgs_and_perms)
                       (map (applyOpenTerm
                             (globalOpenTerm
                              "Prelude.lrtToType")) lrts)) $ \funs ->
  let env' =
        withKnownNat ?ptrWidth $
        permEnvAddGlobalSyms env $
        zipWith (\cfg_and_perm f ->
                  PermEnvGlobalEntry
                  (someCFGAndPermSym cfg_and_perm)
                  (someCFGAndPermPtrPerm cfg_and_perm)
                  [f])
        cfgs_and_perms funs in
  tupleOpenTerm $ flip map (zip cfgs_and_perms funs) $ \(cfg_and_perm, _) ->
  case cfg_and_perm of
    SomeCFGAndPerm sym _ cfg fun_perm ->
      trace ("Type-checking " ++ show sym) $
      translateCFG env' $ tcCFG ?ptrWidth env' endianness fun_perm cfg


-- | Make a "coq-safe" identifier from a string that might contain
-- non-identifier characters, where we use the SAW core notion of identifier
-- characters as letters, digits, underscore and primes. Any disallowed
-- character is mapped to the string @__xNN@, where @NN@ is the hexadecimal code
-- for that character. Additionally, a SAW core identifier is not allowed to
-- start with a prime, so a leading underscore is added in such a case.
mkSafeIdent :: ModuleName -> String -> Ident
mkSafeIdent _ [] = "_"
mkSafeIdent mnm nm =
  let is_safe_char c = isAlphaNum c || c == '_' || c == '\'' in
  mkIdent mnm $ Data.Text.pack $
  (if nm!!0 == '\'' then ('_' :) else id) $
  concatMap
  (\c -> if is_safe_char c then [c] else
           "__x" ++ showHex (ord c) "")
  nm


-- | Type-check a set of CFGs against their function permissions, translate the
-- results to SAW core functions, and add them as definitions to the SAW core
-- module with the given module name. The name of each definition will be the
-- same as the 'GlobalSymbol' associated with its CFG An additional definition
-- with the name @"n__tuple_fun"@ will also be added, where @n@ is the name
-- associated with the first CFG in the list.
tcTranslateAddCFGs ::
  HasPtrWidth w =>
  SharedContext -> ModuleName ->
  PermEnv -> EndianForm -> [SomeCFGAndPerm LLVM] ->
  IO PermEnv
tcTranslateAddCFGs sc mod_name env endianness cfgs_and_perms =
  do let (lrts, tup_fun) =
           tcTranslateCFGTupleFun env endianness cfgs_and_perms
     let tup_fun_ident =
           mkSafeIdent mod_name (someCFGAndPermToName (head cfgs_and_perms)
                                 ++ "__tuple_fun")
     tup_fun_tp <- completeOpenTerm sc $
       applyOpenTerm (globalOpenTerm "Prelude.lrtTupleType") lrts
     tup_fun_tm <- completeOpenTerm sc $
       applyOpenTermMulti (globalOpenTerm "Prelude.multiFixM") [lrts, tup_fun]
     scInsertDef sc mod_name tup_fun_ident tup_fun_tp tup_fun_tm 
     new_entries <-
       zipWithM
       (\cfg_and_perm i ->
         do tp <- completeOpenTerm sc $
              applyOpenTerm (globalOpenTerm "Prelude.lrtToType") $
              someCFGAndPermLRT env cfg_and_perm
            tm <- completeOpenTerm sc $
              projTupleOpenTerm i (globalOpenTerm tup_fun_ident)
            let ident = mkSafeIdent mod_name (someCFGAndPermToName cfg_and_perm)
            scInsertDef sc mod_name ident tp tm
            return $ withKnownNat ?ptrWidth $ PermEnvGlobalEntry
              (someCFGAndPermSym cfg_and_perm)
              (someCFGAndPermPtrPerm cfg_and_perm)
              [globalOpenTerm ident])
       cfgs_and_perms [0 ..]
     return $ permEnvAddGlobalSyms env new_entries


----------------------------------------------------------------------
-- * Top-level Entrypoints for Translating Other Things
----------------------------------------------------------------------

-- | Translate a 'FunPerm' to the SAW core type it represents
translateCompleteFunPerm :: SharedContext -> PermEnv ->
                            FunPerm ghosts args ret -> IO Term
translateCompleteFunPerm sc env fun_perm =
  completeOpenTerm sc $
  runNilTypeTransM (translate $ emptyMb fun_perm) env

-- | Translate a 'TypeRepr' to the SAW core type it represents
translateCompleteType :: SharedContext -> PermEnv ->
                         TypeRepr tp -> IO Term
translateCompleteType sc env typ_perm =
  completeOpenTerm sc $
  typeTransType1 $
  runNilTypeTransM (translate $ emptyMb typ_perm) env

-- | Translate a 'TypeRepr' within the given context of type arguments to the
-- SAW core type it represents
translateCompleteTypeInCtx :: SharedContext -> PermEnv ->
                              CruCtx args -> Mb args (TypeRepr a) -> IO Term
translateCompleteTypeInCtx sc env args ret =
  completeOpenTerm sc $
  runNilTypeTransM (piExprCtx args (typeTransType1 <$> translate ret')) env
  where ret' = mbCombine (cruCtxProxies args) . emptyMb $ ret

-- | Translate an input list of 'ValuePerms' and an output 'ValuePerm' to a SAW
-- core function type in a manner similar to 'translateCompleteFunPerm', except
-- that the returned function type is not in the @CompM@ monad.
translateCompletePureFun :: SharedContext -> PermEnv
                         -> CruCtx ctx -- ^ Type arguments
                         -> Mb ctx (ValuePerms args) -- ^ Input perms
                         -> Mb ctx (ValuePerm ret) -- ^ Return type perm
                         -> IO Term
translateCompletePureFun sc env ctx args ret =
  completeOpenTerm sc $
  runNilTypeTransM (piExprCtx ctx $ piPermCtx args' $ const $
                    typeTransTupleType <$> translate ret') env
  where args' = mbCombine pxys . emptyMb $ args
        ret'  = mbCombine pxys . emptyMb $ ret
        pxys  = cruCtxProxies ctx
