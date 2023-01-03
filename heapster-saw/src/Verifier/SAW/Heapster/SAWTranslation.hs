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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Move brackets to avoid $" #-}

module Verifier.SAW.Heapster.SAWTranslation where

import Prelude hiding (pi)

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
import Control.Monad.State hiding (ap)
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Fail as Fail

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
import Verifier.SAW.SharedTerm

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.Implication
import Verifier.SAW.Heapster.TypedCrucible

import GHC.Stack


-- | FIXME: document and move to Hobbits
suffixMembers :: prx1 ctx1 -> RAssign prx2 ctx2 ->
                 RAssign (Member (ctx1 :++: ctx2)) ctx2
suffixMembers _ MNil = MNil
suffixMembers ctx1 (ctx2 :>: _) =
  RL.map Member_Step (suffixMembers ctx1 ctx2) :>: Member_Base

-- | Build a SAW core term of type @ListSort@ from a list of types
listSortOpenTerm :: [OpenTerm] -> OpenTerm
listSortOpenTerm =
  foldr (\x y -> ctorOpenTerm "Prelude.LS_Cons" [x,y])
  (ctorOpenTerm "Prelude.LS_Nil" [])


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
                       typeTransFun :: [OpenTerm] -> tr }

-- | Apply the 'typeTransFun' of a 'TypeTrans' with the call stack
typeTransF :: HasCallStack => TypeTrans tr -> [OpenTerm] -> tr
typeTransF (TypeTrans tps f) ts | length tps == length ts = f ts
typeTransF (TypeTrans tps _) ts =
  error ("Type translation expected " ++ show (length tps) ++
         " arguments, but got " ++ show (length ts))

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

-- | Build a 'TypeTrans' for an 'OpenTerm' of a given type
openTermTypeTrans :: OpenTerm -> TypeTrans OpenTerm
openTermTypeTrans tp = mkTypeTrans1 tp id

-- | Extract out the single SAW type associated with a 'TypeTrans', or the unit
-- type if it has 0 SAW types. It is an error if it has 2 or more SAW types.
typeTransType1 :: HasCallStack => TypeTrans tr -> OpenTerm
typeTransType1 (TypeTrans [] _) = unitTypeOpenTerm
typeTransType1 (TypeTrans [tp] _) = tp
typeTransType1 _ = error ("typeTransType1" ++ nlPrettyCallStack callStack)

-- | Build the tuple type @T1 * (T2 * ... * (Tn-1 * Tn))@ of @n@ types, with the
-- special case that 0 types maps to the unit type @#()@ (and 1 type just maps
-- to itself). Note that this is different from 'tupleTypeOpenTerm', which
-- always ends with unit, i.e., which returns @T1*(T2*...*(Tn-1*(Tn*#())))@.
tupleOfTypes :: [OpenTerm] -> OpenTerm
tupleOfTypes [] = unitTypeOpenTerm
tupleOfTypes [tp] = tp
tupleOfTypes (tp:tps) = pairTypeOpenTerm tp $ tupleOfTypes tps

-- | Build the tuple @(t1,(t2,(...,(tn-1,tn))))@ of @n@ terms, with the
-- special case that 0 types maps to the unit value @()@ (and 1 value just maps
-- to itself). Note that this is different from 'tupleOpenTerm', which
-- always ends with unit, i.e., which returns @t1*(t2*...*(tn-1*(tn*())))@.
tupleOfTerms :: [OpenTerm] -> OpenTerm
tupleOfTerms [] = unitOpenTerm
tupleOfTerms [t] = t
tupleOfTerms (t:ts) = pairOpenTerm t $ tupleOfTerms ts

-- | Project the @i@th element from a term of type @'tupleOfTypes' tps@. Note
-- that this requires knowing the length of @tps@.
projTupleOfTypes :: [OpenTerm] -> Integer -> OpenTerm -> OpenTerm
projTupleOfTypes [] _ _ = error "projTupleOfTypes: projection of empty tuple!"
projTupleOfTypes [_] 0 tup = tup
projTupleOfTypes (_:_) 0 tup = pairLeftOpenTerm tup
projTupleOfTypes (_:tps) i tup =
  projTupleOfTypes tps (i-1) $ pairRightOpenTerm tup

-- | Map the 'typeTransTypes' field of a 'TypeTrans' to a single type, where a
-- single type is mapped to itself, an empty list of types is mapped to @unit@,
-- and a list of 2 or more types is mapped to a tuple of the types
typeTransTupleType :: TypeTrans tr -> OpenTerm
typeTransTupleType = tupleOfTypes . typeTransTypes

-- | Convert a 'TypeTrans' over 0 or more types to one over the one type
-- returned by 'tupleOfTypes'
tupleTypeTrans :: TypeTrans tr -> TypeTrans tr
tupleTypeTrans ttrans =
  let tps = typeTransTypes ttrans in
  TypeTrans [tupleOfTypes tps]
  (\[t] -> typeTransF ttrans $ map (\i -> projTupleOfTypes tps i t) $
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

  -- | The translation of Vectors of the Crucible any type have no content
  ETrans_AnyVector :: ExprTrans (VectorType AnyType)

  -- | The translation for every other expression type is just a SAW term. Note
  -- that this construct should not be used for the types handled above.
  ETrans_Term :: OpenTerm -> ExprTrans a

-- | A context mapping bound names to their type-level SAW translations
type ExprTransCtx = RAssign ExprTrans


-- | Describes a Haskell type that represents the translation of a term-like
-- construct that corresponds to 0 or more SAW terms
class IsTermTrans tr where
  transTerms :: HasCallStack => tr -> [OpenTerm]

-- | Build a tuple of the terms contained in a translation, with 0 terms mapping
-- to the unit term and one term mapping to itself. If @ttrans@ is a 'TypeTrans'
-- describing the SAW types associated with a @tr@ translation, then this
-- function returns an element of the type @'tupleTypeTrans' ttrans@.
transTupleTerm :: IsTermTrans tr => tr -> OpenTerm
transTupleTerm (transTerms -> [t]) = t
transTupleTerm tr = tupleOfTerms $ transTerms tr

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
  transTerms ETrans_AnyVector = []
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

instance Fail.MonadFail (TransM info ctx) where
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

-- | Run a translation computation in an extended context, where we sawLet-bind any
-- term in the supplied expression translation
inExtTransSAWLetBindM :: TransInfo info => TypeTrans (ExprTrans tp) -> OpenTerm ->
                         ExprTrans tp -> TransM info (ctx :> tp) OpenTerm ->
                         TransM info ctx OpenTerm
inExtTransSAWLetBindM tp_trans tp_ret etrans m =
  sawLetTransMultiM "z" (typeTransTypes tp_trans) tp_ret (transTerms etrans) $
  \var_tms -> inExtTransM (typeTransF tp_trans var_tms) m

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

-- | Build a pi-abstraction inside the 'TransM' monad
piOpenTermTransM :: String -> OpenTerm ->
                    (OpenTerm -> TransM info ctx OpenTerm) ->
                    TransM info ctx OpenTerm
piOpenTermTransM x tp body_f =
  ask >>= \info ->
  return (piOpenTerm (pack x) tp $ \t -> runTransM (body_f t) info)

-- | Build a let-binding in a translation monad
letTransM :: String -> OpenTerm -> TransM info ctx OpenTerm ->
             (OpenTerm -> TransM info ctx OpenTerm) ->
             TransM info ctx OpenTerm
letTransM x tp rhs_m body_m =
  do r <- ask
     return $
       letOpenTerm (pack x) tp (runTransM rhs_m r) (\x' -> runTransM (body_m x') r)

-- | Build a sawLet-binding in a translation monad
sawLetTransM :: String -> OpenTerm -> OpenTerm -> TransM info ctx OpenTerm ->
                (OpenTerm -> TransM info ctx OpenTerm) ->
                TransM info ctx OpenTerm
sawLetTransM x tp tp_ret rhs_m body_m =
  do r <- ask
     return $
       sawLetOpenTerm (pack x) tp tp_ret (runTransM rhs_m r)
                      (\x' -> runTransM (body_m x') r)

-- | Build 0 or more sawLet-bindings in a translation monad, using the same
-- variable name
sawLetTransMultiM :: String -> [OpenTerm] -> OpenTerm -> [OpenTerm] ->
                  ([OpenTerm] -> TransM info ctx OpenTerm) ->
                  TransM info ctx OpenTerm
sawLetTransMultiM _ [] _ [] f = f []
sawLetTransMultiM x (tp:tps) ret_tp (rhs:rhss) f =
  sawLetTransM x tp ret_tp (return rhs) $ \var_tm ->
  sawLetTransMultiM x tps ret_tp rhss (\var_tms -> f (var_tm:var_tms))
sawLetTransMultiM _ _ _ _ _ =
  error "sawLetTransMultiM: numbers of types and right-hand sides disagree"

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

-- | Eliminate a multi-way SAW @Eithers@ type, taking in: a list of the
-- translations of the types in the @Eithers@ type; the translation of the
-- output type; a list of functions for the branches of the @Eithers@
-- elimination; and the term of @Eithers@ type being eliminated
eithersElimTransM :: [TypeTrans tr_in] -> TypeTrans tr_out ->
                     [tr_in -> TransM info ctx OpenTerm] -> OpenTerm ->
                     TransM info ctx OpenTerm
eithersElimTransM tps tp_ret fs eith =
  foldr (\(tp,f) restM ->
          do f_trans <- lambdaTupleTransM "x_eith_elim" tp f
             rest <- restM
             return (ctorOpenTerm "Prelude.FunsTo_Cons"
                     [typeTransTupleType tp_ret,
                      typeTransTupleType tp, f_trans, rest]))
  (return $ ctorOpenTerm "Prelude.FunsTo_Nil" [typeTransTupleType tp_ret])
  (zip tps fs)
  >>= \elims_trans ->
  return (applyOpenTermMulti (globalOpenTerm "Prelude.eithers")
          [typeTransTupleType tp_ret, elims_trans, eith])

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

-- | Like `sigmaTypeTransM`, but translates `exists x.eq(y)` into just `x`
sigmaTypePermTransM :: TransInfo info => String -> TypeTrans (ExprTrans trL) ->
                       Mb (ctx :> trL) (ValuePerm trR) ->
                       TransM info ctx OpenTerm
sigmaTypePermTransM x ttrans p_cbn = case mbMatch p_cbn of
  [nuMP| ValPerm_Eq _ |] -> return $ typeTransTupleType ttrans
  _ -> sigmaTypeTransM x ttrans (flip inExtTransM $ translate p_cbn)

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

-- | Like `sigmaTransM`, but translates `exists x.eq(y)` into just `x`
sigmaPermTransM :: (TransInfo info, IsTermTrans trR2) =>
                   String -> TypeTrans (ExprTrans trL) ->
                   Mb (ctx :> trL) (ValuePerm trR1) ->
                   ExprTrans trL -> TransM info ctx trR2 ->
                   TransM info ctx OpenTerm
sigmaPermTransM x ttrans p_cbn etrans rhs_m = case mbMatch p_cbn of
  [nuMP| ValPerm_Eq _ |] -> return $ transTupleTerm etrans
  _ -> sigmaTransM x ttrans (flip inExtTransM $ translate p_cbn)
                   etrans rhs_m

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

-- | Like `sigmaElimTransM`, but translates `exists x.eq(y)` into just `x`
sigmaElimPermTransM :: (TransInfo info) =>
                       String -> TypeTrans (ExprTrans trL) ->
                       Mb (ctx :> trL) (ValuePerm trR) ->
                       TransM info ctx (TypeTrans trRet) ->
                       (ExprTrans trL -> PermTrans (ctx :> trL) trR ->
                                         TransM info ctx OpenTerm) ->
                       OpenTerm ->
                       TransM info ctx OpenTerm
sigmaElimPermTransM x tp_l p_cbn tp_ret_m f sigma = case mbMatch p_cbn of
  [nuMP| ValPerm_Eq e |] -> f (typeTransF (tupleTypeTrans tp_l) [sigma])
                              (PTrans_Eq e)
  _ -> sigmaElimTransM x tp_l (flip inExtTransM $ translate p_cbn)
                       tp_ret_m f sigma

-- | Apply an 'OpenTerm' to the current event type @E@ and to a
-- list of other arguments
applyEventOpM :: TransInfo info => OpenTerm -> [OpenTerm] ->
                 TransM info ctx OpenTerm
applyEventOpM f args =
  do evType <- identOpenTerm <$> permEnvSpecMEventType <$> infoEnv <$> ask
     return $ applyOpenTermMulti f (evType : args)

-- | Apply a named operator to the current event type @E@ and to a list of other
-- arguments
applyNamedEventOpM :: TransInfo info => Ident -> [OpenTerm] ->
                      TransM info ctx OpenTerm
applyNamedEventOpM f args =
  applyEventOpM (globalOpenTerm f) args

-- | Generate the type @SpecM E evRetType stack A@ using the current event type
-- and the supplied @stack@ and type @A@
specMTypeTransM :: TransInfo info => OpenTerm -> OpenTerm ->
                   TransM info ctx OpenTerm
specMTypeTransM stack tp = applyNamedEventOpM "Prelude.SpecM" [stack,tp]

-- | Generate the type @SpecM E evRetType emptyFunStack A@ using the current
-- event type and the supplied type @A@
emptyStackSpecMTypeTransM :: TransInfo info => OpenTerm ->
                             TransM info ctx OpenTerm
emptyStackSpecMTypeTransM tp =
  specMTypeTransM (globalOpenTerm "Prelude.emptyFunStack") tp

-- | Lambda-abstract a function stack variable of type @FunStack@
lambdaFunStackM :: (OpenTerm -> TransM info ctx OpenTerm) ->
                   TransM info ctx OpenTerm
lambdaFunStackM f =
  lambdaOpenTermTransM "stk" (globalOpenTerm "Prelude.FunStack") f

-- | Pi-abstract a function stack variable of type @FunStack@
piFunStackM :: (OpenTerm -> TransM info ctx OpenTerm) ->
               TransM info ctx OpenTerm
piFunStackM f =
  piOpenTermTransM "stk" (globalOpenTerm "Prelude.FunStack") f

-- | Apply @pushFunStack@ to push a frame onto a @FunStack@
pushFunStackOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
pushFunStackOpenTerm frame stack =
  applyGlobalOpenTerm "Prelude.pushFunStack" [frame, stack]

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

instance (Translate info ctx a tr, NuMatching a) =>
         Translate info ctx [a] [tr] where
  translate = mapM translate . mbList


----------------------------------------------------------------------
-- * Translating Types
----------------------------------------------------------------------

-- | A flag for whether or not to perform checks in the translation. We use this
-- type, rather than just 'Bool', for documentation purposes.
newtype ChecksFlag = ChecksFlag { checksFlagSet :: Bool }

-- | The 'ChecksFlag' specifying not to perform any translation checks
noChecks :: ChecksFlag
noChecks = ChecksFlag False

-- | The 'ChecksFlag' specifying to perform all translation checks
doChecks :: ChecksFlag
doChecks = ChecksFlag True

-- | Translation info for translating types and pure expressions
data TypeTransInfo ctx =
  TypeTransInfo
  {
    ttiExprCtx :: ExprTransCtx ctx,
    ttiPermEnv :: PermEnv,
    ttiChecksFlag :: ChecksFlag
  }

-- (ExprTransCtx ctx) PermEnv ChecksFlag

-- | Build an empty 'TypeTransInfo' from a 'PermEnv'
emptyTypeTransInfo :: PermEnv -> ChecksFlag -> TypeTransInfo RNil
emptyTypeTransInfo = TypeTransInfo MNil

instance TransInfo TypeTransInfo where
  infoCtx (TypeTransInfo ctx _ _) = ctx
  infoEnv (TypeTransInfo _ env _) = env
  extTransInfo etrans (TypeTransInfo ctx env checks) =
    TypeTransInfo (ctx :>: etrans) env checks

-- | The translation monad specific to translating types and pure expressions
type TypeTransM = TransM TypeTransInfo

-- | Run a 'TypeTransM' computation in the empty translation context
runNilTypeTransM :: PermEnv -> ChecksFlag -> TypeTransM RNil a -> a
runNilTypeTransM env checks m = runTransM m (emptyTypeTransInfo env checks)

-- | Run a translation computation in an empty expression translation context
inEmptyCtxTransM :: TypeTransM RNil a -> TypeTransM ctx a
inEmptyCtxTransM =
  withInfoM (\(TypeTransInfo _ env checks) -> TypeTransInfo MNil env checks)

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
    [nuMP| SequenceRepr{} |] ->
      return $ error "translate: SequenceRepr"
    [nuMP| BVRepr w |] ->
      returnType1 =<< bitvectorTransM (translate w)
    [nuMP| VectorRepr AnyRepr |] ->
      return $ mkTypeTrans0 ETrans_AnyVector

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
piExprCtx :: TransInfo info => CruCtx ctx ->
             TransM info ctx OpenTerm ->
             TransM info RNil OpenTerm
piExprCtx ctx m =
  translateClosed ctx >>= \tptrans ->
  piTransM "e" tptrans (\ectx -> inCtxTransM ectx m)

-- | Like 'piExprCtx' but append the newly bound variables to the current
-- context, rather than running in the empty context
piExprCtxApp :: TransInfo info => CruCtx ctx2 ->
                TransM info (ctx :++: ctx2) OpenTerm ->
                TransM info ctx OpenTerm
piExprCtxApp ctx m =
  translateClosed ctx >>= \tptrans ->
  piTransM "e" tptrans (\ectx -> inExtMultiTransM ectx m)


----------------------------------------------------------------------
-- * Translating Pure Expressions
----------------------------------------------------------------------

-- FIXME HERE: move these OpenTerm operations to OpenTerm.hs

-- | Build a bitvector literal from a 'BV' value
bvBVOpenTerm :: NatRepr w -> BV w -> OpenTerm
bvBVOpenTerm w bv = bvLitOpenTerm (BV.asBitsBE w bv)

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

bvSplitOpenTerm :: EndianForm -> OpenTerm -> OpenTerm -> OpenTerm ->
                   (OpenTerm, OpenTerm)
bvSplitOpenTerm BigEndian sz1 sz2 e =
  (applyOpenTermMulti (globalOpenTerm "Prelude.take") [boolTypeOpenTerm,
                                                       sz1, sz2, e],
   applyOpenTermMulti (globalOpenTerm "Prelude.drop") [boolTypeOpenTerm,
                                                       sz1, sz2, e])
bvSplitOpenTerm LittleEndian sz1 sz2 e =
  (applyOpenTermMulti (globalOpenTerm "Prelude.drop") [boolTypeOpenTerm,
                                                       sz2, sz1, e],
   applyOpenTermMulti (globalOpenTerm "Prelude.take") [boolTypeOpenTerm,
                                                       sz2, sz1, e])

bvConcatOpenTerm :: EndianForm -> OpenTerm -> OpenTerm ->
                    OpenTerm -> OpenTerm -> OpenTerm
bvConcatOpenTerm BigEndian sz1 sz2 e1 e2 =
  applyOpenTermMulti (globalOpenTerm "Prelude.append")
  [sz1, sz2, boolTypeOpenTerm, e1, e2]
bvConcatOpenTerm LittleEndian sz1 sz2 e1 e2 =
  applyOpenTermMulti (globalOpenTerm "Prelude.append")
  [sz2, sz1, boolTypeOpenTerm, e2, e1]

-- | Translate a variable to a 'Member' proof, raising an error if the variable
-- is unbound
translateVar :: Mb ctx (ExprVar a) -> Member ctx a
translateVar mb_x | Left memb <- mbNameBoundP mb_x = memb
translateVar _ = error "translateVar: unbound variable!"

-- | Get the 'TypeRepr' of an expression
mbExprType :: KnownRepr TypeRepr a => Mb ctx (PermExpr a) -> TypeRepr a
mbExprType _ = knownRepr

-- | Get the 'TypeRepr' of an expression
mbVarType :: KnownRepr TypeRepr a => Mb ctx (ExprVar a) -> TypeRepr a
mbVarType _ = knownRepr

-- | Get the 'TypeRepr' bound by a binding
mbBindingType :: KnownRepr TypeRepr tp => Mb ctx (Binding tp a) -> TypeRepr tp
mbBindingType _ = knownRepr


instance TransInfo info =>
         Translate info ctx (ExprVar a) (ExprTrans a) where
  translate mb_x = RL.get (translateVar mb_x) <$> infoCtx <$> ask

instance TransInfo info =>
         Translate info ctx (RAssign ExprVar as) (ExprTransCtx as) where
  translate mb_exprs = case mbMatch mb_exprs of
    [nuMP| MNil |] -> return MNil
    [nuMP| ns :>: n |] ->
      (:>:) <$> translate ns <*> translate n

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
      return $ ETrans_Term $ bvBVOpenTerm w $ mbLift off
    [nuMP| PExpr_BV bvfactors (BV.BV 0) |] ->
      let w = natVal3 bvfactors in
      ETrans_Term <$> foldr1 (bvAddOpenTerm w) <$> translate bvfactors
    [nuMP| PExpr_BV bvfactors off |] ->
      do let w = natRepr3 bvfactors
         bv_transs <- translate bvfactors
         return $ ETrans_Term $
           foldr (bvAddOpenTerm $ natValue w) (bvBVOpenTerm w $ mbLift off) bv_transs
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
        [nuMP| RecShapeBody _ trans_id _ |] ->
          ETrans_Term <$> applyOpenTermMulti (globalOpenTerm $ mbLift trans_id) <$>
          transTerms <$> translate args
    [nuMP| PExpr_EqShape _ _ |] -> return $ ETrans_Term unitTypeOpenTerm
    [nuMP| PExpr_PtrShape _ _ sh |] -> translate sh
    [nuMP| PExpr_FieldShape fsh |] ->
      ETrans_Term <$> tupleOfTypes <$> translate fsh
    [nuMP| PExpr_ArrayShape mb_len _ mb_sh |] ->
      do let w = natVal4 mb_len
         let w_term = natOpenTerm w
         len_term <- translate1 mb_len
         elem_tp <- translate1 mb_sh
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
    [nuMP| PExpr_FalseShape |] ->
      return $ ETrans_Term $ globalOpenTerm "Prelude.FalseProp"

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
      bvMulOpenTerm (natValue w) (bvBVOpenTerm w $ mbLift i) <$>
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

  -- | @lowned@ permissions translate to a monadic function from (the
  -- translation of) the input permissions to the output permissions
  APTrans_LOwned :: Mb ctx [PermExpr LifetimeType] ->
                    CruCtx ps_in -> CruCtx ps_out ->
                    Mb ctx (ExprPerms ps_in) ->
                    Mb ctx (ExprPerms ps_out) ->
                    OpenTerm -> AtomicPermTrans ctx LifetimeType

  -- | Simple @lowned@ permissions have no translation, because they represent
  -- @lowned@ permissions whose translations are just the identity function
  APTrans_LOwnedSimple :: CruCtx ps -> Mb ctx (ExprPerms ps) ->
                          AtomicPermTrans ctx LifetimeType

  -- | LCurrent permissions have no computational content
  APTrans_LCurrent :: Mb ctx (PermExpr LifetimeType) ->
                      AtomicPermTrans ctx LifetimeType

  -- | LFinished permissions have no computational content
  APTrans_LFinished :: AtomicPermTrans ctx LifetimeType

  -- | The translation of a struct permission is sequence of the translations of
  -- the permissions in the struct permission
  APTrans_Struct :: PermTransCtx ctx (CtxToRList args) ->
                    AtomicPermTrans ctx (StructType args)

  -- | The translation of functional permission is either a SAW term of
  -- functional type or a recursive call to the @n@th function in the most
  -- recently bound frame of recursive functions
  APTrans_Fun :: Mb ctx (FunPerm ghosts (CtxToRList cargs) gouts ret) ->
                 Either Natural OpenTerm ->
                 AtomicPermTrans ctx (FunctionHandleType cargs ret)

  -- | Propositional permissions are represented by a SAW term
  APTrans_BVProp :: (1 <= w, KnownNat w) => BVPropTrans ctx w ->
                    AtomicPermTrans ctx (LLVMPointerType w)

  -- | Any permissions have no SAW terms
  APTrans_Any :: AtomicPermTrans ctx a


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
-- along with a SAW term for its length as a bitvector and the type translation
-- for a @memblock@ permission to its head cell, which can be offset to get a
-- @memblock@ permission for any of its cells.
data LLVMArrayPermTrans ctx w = LLVMArrayPermTrans {
  llvmArrayTransPerm :: Mb ctx (LLVMArrayPerm w),
  llvmArrayTransLen :: OpenTerm,
  llvmArrayTransHeadCell :: TypeTrans (AtomicPermTrans ctx (LLVMPointerType w)),
  -- llvmArrayTransBorrows :: [LLVMArrayBorrowTrans ctx w],
  llvmArrayTransTerm :: OpenTerm
  }

-- | Get the SAW type of the cells of the translation of an array permission
llvmArrayTransCellType :: LLVMArrayPermTrans ctx w -> OpenTerm
llvmArrayTransCellType = typeTransType1 . llvmArrayTransHeadCell


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
  transTerms (APTrans_LOwned _ _ _ _ _ t) = [t]
  transTerms (APTrans_LOwnedSimple _ _) = []
  transTerms (APTrans_LCurrent _) = []
  transTerms APTrans_LFinished = []
  transTerms (APTrans_Struct pctx) = transTerms pctx
  transTerms (APTrans_Fun _ (Right t)) = [t]
  transTerms (APTrans_Fun _ (Left _)) =
    -- FIXME: handling this would probably require polymorphism over FunStack
    -- arguments in the translation of functions, because passing a pointer to a
    -- recursively defined function would not be in the empty FunStack
    [failOpenTerm
     ("Heapster cannot (yet) translate recursive calls into terms; " ++
      "This probably resulted from a function that takes a pointer to " ++
      "a function that is recursively defined with it")]
  transTerms (APTrans_BVProp prop) = transTerms prop
  transTerms APTrans_Any = []

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
atomicPermTransPerm _ (APTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out _) =
  mbMap3 (\ls -> Perm_LOwned ls tps_in tps_out) mb_ls mb_ps_in mb_ps_out
atomicPermTransPerm _ (APTrans_LOwnedSimple tps mb_lops) =
  fmap (Perm_LOwnedSimple tps) mb_lops
atomicPermTransPerm _ (APTrans_LCurrent l) = fmap Perm_LCurrent l
atomicPermTransPerm prxs APTrans_LFinished = nus prxs $ const Perm_LFinished
atomicPermTransPerm prxs (APTrans_Struct ps) =
  fmap Perm_Struct $ permTransCtxPerms prxs ps
atomicPermTransPerm _ (APTrans_Fun fp _) = fmap Perm_Fun fp
atomicPermTransPerm _ (APTrans_BVProp (BVPropTrans prop _)) =
  fmap Perm_BVProp prop
atomicPermTransPerm prxs APTrans_Any = nuMulti prxs $ const $ Perm_Any

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
  extPermTrans (PTrans_Conj aps) =
    PTrans_Conj (map extPermTrans aps)
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
  extPermTrans (APTrans_LOwned ls tps_in tps_out ps_in ps_out t) =
    APTrans_LOwned (extMb ls) tps_in tps_out (extMb ps_in) (extMb ps_out) t
  extPermTrans (APTrans_LOwnedSimple tps lops) =
    APTrans_LOwnedSimple tps (extMb lops)
  extPermTrans (APTrans_LCurrent p) = APTrans_LCurrent $ extMb p
  extPermTrans APTrans_LFinished = APTrans_LFinished
  extPermTrans (APTrans_Struct ps) = APTrans_Struct $ RL.map extPermTrans ps
  extPermTrans (APTrans_Fun fp trans) = APTrans_Fun (extMb fp) trans
  extPermTrans (APTrans_BVProp prop_trans) =
    APTrans_BVProp $ extPermTrans prop_trans
  extPermTrans APTrans_Any = APTrans_Any

instance ExtPermTrans LLVMArrayPermTrans where
  extPermTrans (LLVMArrayPermTrans ap len sh {- bs -} t) =
    LLVMArrayPermTrans (extMb ap) len (fmap extPermTrans sh)
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
                                  (LLVMArrayPermTrans ap len sh {- bs -} t)) =
  Just $ APTrans_LLVMArray $
  LLVMArrayPermTrans (mbMap2 offsetLLVMArrayPerm mb_off ap) len sh {- bs -} t
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
                         (fmap mkLLVMPermOffset mb_off)) $
  offsetLLVMPermTrans mb_off ptrans
offsetLLVMPermTrans mb_off (PTrans_Term mb_p t) =
  PTrans_Term (mbMap2 offsetLLVMPerm mb_off mb_p) t

-- | Apply 'offsetPerm' to the permissions associated with a permission
-- translation
offsetPermTrans :: Mb ctx (PermOffset a) -> PermTrans ctx a -> PermTrans ctx a
offsetPermTrans mb_off = case mbMatch mb_off of
  [nuMP| NoPermOffset |] -> id
  [nuMP| LLVMPermOffset off |] -> offsetLLVMPermTrans off

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

-- | Read an array cell of the translation of an LLVM array permission at a
-- given index, given proofs of the propositions that the index is in the array
-- as returned by 'llvmArrayIndexInArray'. Note that the first proposition
-- should always be that the cell number is <= the array length.
getLLVMArrayTransCell :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                         Mb ctx (PermExpr (BVType w)) -> OpenTerm ->
                         [BVPropTrans ctx w] ->
                         AtomicPermTrans ctx (LLVMPointerType w)
getLLVMArrayTransCell arr_trans mb_cell cell_tm (BVPropTrans _ in_rng_pf:_) =
  let w = fromInteger $ natVal arr_trans in
  fromJust $
  -- FIXME: remove offsetLLVMAtomicPermTrans, as it requires changing all
  -- name-bindings in the PermTrans it is applied to back to FreshFuns, i.e., it
  -- substitutes for all the names
  offsetLLVMAtomicPermTrans (mbMap2 llvmArrayCellToOffset
                             (llvmArrayTransPerm arr_trans) mb_cell) $
  typeTransF (llvmArrayTransHeadCell arr_trans)
  [applyOpenTermMulti (globalOpenTerm "Prelude.atBVVec")
   [natOpenTerm w, llvmArrayTransLen arr_trans,
    llvmArrayTransCellType arr_trans, llvmArrayTransTerm arr_trans,
    cell_tm, in_rng_pf]]
getLLVMArrayTransCell _ _ _ _ =
  error "getLLVMArrayTransCell: malformed arguments"


-- | Write an array cell of the translation of an LLVM array permission at a
-- given index
setLLVMArrayTransCell :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                         OpenTerm -> AtomicPermTrans ctx (LLVMPointerType w) ->
                         LLVMArrayPermTrans ctx w
setLLVMArrayTransCell arr_trans cell_tm cell_value =
  let w = fromInteger $ natVal arr_trans in
  arr_trans {
    llvmArrayTransTerm =
        applyOpenTermMulti (globalOpenTerm "Prelude.updBVVec")
        [natOpenTerm w, llvmArrayTransLen arr_trans,
         llvmArrayTransCellType arr_trans, llvmArrayTransTerm arr_trans,
         cell_tm, transTerm1 cell_value] }


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

-- | Weaken a monadic function of type @(T1*...*Tn) -> SpecM(U1*...*Um)@ to one
-- of type @(V*T1*...*Tn) -> SpecM(V*U1*...*Um)@, @n@-ary tuple types are built
-- using 'tupleOfTypes'
weakenMonadicFun1 :: OpenTerm -> [OpenTerm] -> [OpenTerm] -> OpenTerm ->
                     ImpTransM ext blocks tops rets ps ctx OpenTerm
weakenMonadicFun1 v ts us f =
  -- First form a term f1 of type V*(T1*...*Tn) -> SpecM(V*(U1*...*Um))
  do let t_tup = tupleOfTypes ts
         u_tup = tupleOfTypes us
     f1 <- applyNamedSpecOpEmptyM "Prelude.tupleSpecMFunBoth" [t_tup, u_tup, v, f]

     let f2 = case ts of
           -- If ts is empty, form the term \ (x:V) -> f1 (x, ()) to coerce f1
           -- from type V*#() -> SpecM(V*Us) to type V -> SpecM(V*Us)
           [] ->
             lambdaOpenTerm "x" v $ \x ->
             applyOpenTerm f1 (pairOpenTerm x unitOpenTerm)
           -- Otherwise, leave f1 unchanged
           _ -> f1

     case us of
       -- If us is empty, compose f2 with \ (x:V*#()) -> returnM V x.(1) to
       -- coerce from V*Us -> SpecM (V*#()) to V*Us -> SpecM V
       [] ->
         do fun_tm <-
              lambdaOpenTermTransM "x" (pairTypeOpenTerm v unitTypeOpenTerm)
              (\x -> applyNamedSpecOpEmptyM "Prelude.retS" [v, pairLeftOpenTerm x])
            applyNamedSpecOpEmptyM "Prelude.composeS"
              [tupleOfTypes (v:ts), pairTypeOpenTerm v unitTypeOpenTerm,
               v, f2, fun_tm]
       -- Otherwise, leave f2 unchanged
       _ -> return f2


-- | Weaken a monadic function of type
--
-- > (T1*...*Tn) -> SpecM e eTp emptyFunStack (U1*...*Um)
--
-- to one of type
--
-- > (V1*...*Vk*T1*...*Tn) -> SpecM e eTp emptyFunStack (V1*...*Vk*U1*...*Um)
--
-- where tuples of 2 or more types are right-nested and and in a unit type,
-- i.e., have the form @(T1 * (T2 * (... * (Tn * #()))))@
weakenMonadicFun :: [OpenTerm] -> [OpenTerm] -> [OpenTerm] -> OpenTerm ->
                    ImpTransM ext blocks tops rets ps ctx OpenTerm
weakenMonadicFun vs ts_top us_top f_top =
  foldr (\v rest_m ->
          do (ts,us,f) <- rest_m
             f' <- weakenMonadicFun1 v ts us f
             return (v:ts, v:us, f'))
  (return (ts_top, us_top, f_top))
  vs
  >>= \(_,_,ret) -> return ret

-- | Weaken a monadic function which is the translation of an ownership
-- permission @lowned(ps_in -o ps_out)@ to @lowned(P * ps_in -o P * ps_out)@
weakenLifetimeFun :: TypeTrans (PermTrans ctx a) ->
                     TypeTrans (PermTransCtx ctx ps_in) ->
                     TypeTrans (PermTransCtx ctx ps_out) ->
                     OpenTerm ->
                     ImpTransM ext blocks tops rets ps ctx OpenTerm
weakenLifetimeFun tp_trans ps_in_trans ps_out_trans f =
  weakenMonadicFun (transTerms
                    tp_trans) (transTerms
                               ps_in_trans) (transTerms ps_out_trans) f


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
           sigmaTypePermTransM "x_ex" tp_trans (mbCombine RL.typeCtxProxies p1)
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
      fmap PTrans_Conj <$> listTypeTrans <$> translate ps
    [nuMP| ValPerm_Var x _ |] ->
      mkPermTypeTrans1 p <$> translate1 x
    [nuMP| ValPerm_False |] ->
      return $ mkPermTypeTrans1 p $ globalOpenTerm "Prelude.FalseProp"

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
    [nuMP| Perm_LOwned ls tps_in tps_out ps_in ps_out |] ->
      do tp_in <- typeTransTupleType <$> translate ps_in
         tp_out <- typeTransTupleType <$> translate ps_out
         specm_tp <- emptyStackSpecMTypeTransM tp_out
         let tp = arrowOpenTerm "ps" tp_in specm_tp
         return $ mkTypeTrans1 tp (APTrans_LOwned ls
                                   (mbLift tps_in) (mbLift tps_out) ps_in ps_out)
    [nuMP| Perm_LOwnedSimple tps lops |] ->
      return $ mkTypeTrans0 $ APTrans_LOwnedSimple (mbLift tps) lops
    [nuMP| Perm_LCurrent l |] ->
      return $ mkTypeTrans0 $ APTrans_LCurrent l
    [nuMP| Perm_LFinished |] ->
      return $ mkTypeTrans0 APTrans_LFinished
    [nuMP| Perm_Struct ps |] ->
      fmap APTrans_Struct <$> translate ps
    [nuMP| Perm_Fun fun_perm |] ->
      translate fun_perm >>= \tp_term ->
      return $ mkTypeTrans1 tp_term (APTrans_Fun fun_perm . Right)
    [nuMP| Perm_BVProp prop |] ->
      fmap APTrans_BVProp <$> translate prop
    [nuMP| Perm_Any |] -> return $ mkTypeTrans0 APTrans_Any

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
     sh_trans <- translate $ mbMapCl $(mkClosed [| Perm_LLVMBlock .
                                                 llvmArrayPermHead |]) mb_ap
     let elem_tp = typeTransType1 sh_trans
     len_term <- translate1 $ mbLLVMArrayLen mb_ap
     {-
     bs_trans <-
       listTypeTrans <$> mapM (translateLLVMArrayBorrow ap) (mbList bs) -}
     let arr_tp =
           applyOpenTermMulti (globalOpenTerm "Prelude.BVVec")
           [w_term, len_term, elem_tp]
     return (w_term, len_term, elem_tp,
             mkTypeTrans1 arr_tp ({- flip $ -}
                                  LLVMArrayPermTrans mb_ap len_term sh_trans)
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

instance TransInfo info =>
         Translate info ctx (ExprPerms ps) (TypeTrans
                                            (PermTransCtx ctx ps)) where
  translate mb_eps
    | Just mb_ps <- mbExprPermsToValuePerms mb_eps = translate mb_ps
  translate mb_ps =
    error ("Translating expression permissions that could not be converted " ++
           "to variable permissions:" ++ permPrettyString emptyPPInfo mb_ps)

emptyStackOpenTerm :: OpenTerm
emptyStackOpenTerm = globalOpenTerm "Prelude.emptyFunStack"

-- Translate a FunPerm to a pi-abstraction (FIXME HERE NOW: document translation)
instance TransInfo info =>
         Translate info ctx (FunPerm ghosts args gouts ret) OpenTerm where
  translate (mbMatch ->
             [nuMP| FunPerm ghosts args gouts ret perms_in perms_out |]) =
    let tops = appendCruCtx (mbLift ghosts) (mbLift args)
        tops_prxs = cruCtxProxies tops
        rets = CruCtxCons (mbLift gouts) (mbLift ret)
        rets_prxs = cruCtxProxies rets in
    (infoCtx <$> ask) >>= \ctx ->
    case RL.appendAssoc ctx tops_prxs rets_prxs of
      Refl ->
        piExprCtxApp tops $
        piPermCtx (mbCombine tops_prxs perms_in) $ \_ ->
        specMTypeTransM emptyStackOpenTerm =<<
        translateRetType rets (mbCombine
                               (RL.append tops_prxs rets_prxs) perms_out)

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
translateRetType :: TransInfo info => CruCtx rets ->
                    Mb (ctx :++: rets) (ValuePerms ps) ->
                    TransM info ctx OpenTerm
translateRetType rets ret_perms =
  do tptrans <- translateClosed rets
     sigmaTypeTransM "ret" tptrans (flip inExtMultiTransM
                                    (translate ret_perms))

-- | Build the return type for the function resulting from an entrypoint
translateEntryRetType :: TransInfo info =>
                         TypedEntry phase ext blocks tops rets args ghosts ->
                         TransM info ((tops :++: args) :++: ghosts) OpenTerm
translateEntryRetType (TypedEntry {..}
                       :: TypedEntry phase ext blocks tops rets args ghosts) =
  let mb_perms_out =
        mbCombine (cruCtxProxies typedEntryRets) $
        extMbMulti (cruCtxProxies typedEntryGhosts) $
        extMbMulti (cruCtxProxies typedEntryArgs) $
        mbSeparate @_ @tops (cruCtxProxies typedEntryRets) typedEntryPermsOut in
  translateRetType typedEntryRets mb_perms_out


----------------------------------------------------------------------
-- * The Implication Translation Monad
----------------------------------------------------------------------

-- | A mapping from a block entrypoint to a corresponding SAW variable that is
-- bound to its translation if it has one: only those entrypoints marked as the
-- heads of strongly-connect components have translations as letrec-bound
-- variables
data TypedEntryTrans ext blocks tops rets args ghosts =
  TypedEntryTrans { typedEntryTransEntry ::
                      TypedEntry TransPhase ext blocks tops rets args ghosts,
                    typedEntryTransRecIx :: Maybe Natural }

-- | A mapping from a block to the SAW functions for each entrypoint
data TypedBlockTrans ext blocks tops rets args =
  TypedBlockTrans { typedBlockTransEntries ::
                      [Some (TypedEntryTrans ext blocks tops rets args)] }

-- | A mapping from all block entrypoints to their SAW translations
type TypedBlockMapTrans ext blocks tops rets =
  RAssign (TypedBlockTrans ext blocks tops rets) blocks

-- | Look up the translation of an entry by entry ID
lookupEntryTrans :: TypedEntryID blocks args ->
                    TypedBlockMapTrans ext blocks tops rets ->
                    Some (TypedEntryTrans ext blocks tops rets args)
lookupEntryTrans entryID blkMap =
  maybe (error "lookupEntryTrans") id $
  find (\(Some entryTrans) ->
         entryID == typedEntryID (typedEntryTransEntry entryTrans)) $
  typedBlockTransEntries (RL.get (entryBlockMember entryID) blkMap)

-- | Look up the translation of an entry by entry ID and make sure that it has
-- the supplied ghost arguments
lookupEntryTransCast :: TypedEntryID blocks args -> CruCtx ghosts ->
                        TypedBlockMapTrans ext blocks tops rets ->
                        TypedEntryTrans ext blocks tops rets args ghosts
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
                  TypedBlockMapTrans ext blocks tops rets ->
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

-- | A Haskell representation of a function stack, which is either the empty
-- stack or a push of some top frame onto a previous stack
data FunStack = EmptyFunStack | PushFunStack OpenTerm OpenTerm

-- | Build a 'FunStack' with a single frame
singleFunStack :: OpenTerm -> FunStack
singleFunStack frame = PushFunStack frame emptyStackOpenTerm

-- | Convert a 'FunStack' to the term it represents
funStackTerm :: FunStack -> OpenTerm
funStackTerm EmptyFunStack = emptyStackOpenTerm
funStackTerm (PushFunStack frame prev_stack) =
  pushFunStackOpenTerm frame prev_stack

-- | Get the top frame of a 'FunStack' if it is non-empty
funStackTop :: FunStack -> Maybe OpenTerm
funStackTop EmptyFunStack = Nothing
funStackTop (PushFunStack frame _) = Just frame

-- | Get the previous stack from a 'FunStack' if it is non-empty
funStackPrev :: FunStack -> Maybe OpenTerm
funStackPrev EmptyFunStack = Nothing
funStackPrev (PushFunStack _ prev_stack) = Just prev_stack

-- | Get the top frame and previous stack of a 'FunStack' if it is non-empty
funStackTopAndPrev :: FunStack -> Maybe (OpenTerm, OpenTerm)
funStackTopAndPrev EmptyFunStack = Nothing
funStackTopAndPrev (PushFunStack frame prev_stack) = Just (frame, prev_stack)


-- | Contextual info for an implication translation
data ImpTransInfo ext blocks tops rets ps ctx =
  ImpTransInfo
  {
    itiExprCtx :: ExprTransCtx ctx,
    itiPermCtx :: PermTransCtx ctx ctx,
    itiPermStack :: PermTransCtx ctx ps,
    itiPermStackVars :: RAssign (Member ctx) ps,
    itiPermEnv :: PermEnv,
    itiBlockMapTrans :: TypedBlockMapTrans ext blocks tops rets,
    itiReturnType :: OpenTerm,
    itiChecksFlag :: ChecksFlag,
    itiFunStack :: FunStack
  }

instance TransInfo (ImpTransInfo ext blocks tops rets ps) where
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
type ImpTransM ext blocks tops rets ps =
  TransM (ImpTransInfo ext blocks tops rets ps)

-- | Run an 'ImpTransM' computation in a 'TypeTransM' context (FIXME: better
-- documentation; e.g., the pctx starts on top of the stack)
impTransM :: forall ctx ps ext blocks tops rets a.
             RAssign (Member ctx) ps -> PermTransCtx ctx ps ->
             TypedBlockMapTrans ext blocks tops rets ->
             FunStack -> OpenTerm ->
             ImpTransM ext blocks tops rets ps ctx a ->
             TypeTransM ctx a
impTransM pvars pctx mapTrans stack retType =
  withInfoM $ \(TypeTransInfo ectx penv pflag) ->
  ImpTransInfo { itiExprCtx = ectx,
                 itiPermCtx = RL.map (const $ PTrans_True) ectx,
                 itiPermStack = pctx,
                 itiPermStackVars = pvars,
                 itiPermEnv = penv,
                 itiBlockMapTrans = mapTrans,
                 itiReturnType = retType,
                 itiChecksFlag = pflag,
                 itiFunStack = stack
               }

-- | Embed a type translation into an impure translation
-- FIXME: should no longer need this...
tpTransM :: TypeTransM ctx a -> ImpTransM ext blocks tops rets ps ctx a
tpTransM =
  withInfoM (\(ImpTransInfo {..}) ->
              TypeTransInfo itiExprCtx itiPermEnv itiChecksFlag)

-- | Run an implication translation computation in an "empty" environment, where
-- there are no variables in scope and no permissions held anywhere
inEmptyEnvImpTransM :: ImpTransM ext blocks tops rets RNil RNil a ->
                       ImpTransM ext blocks tops rets ps ctx a
inEmptyEnvImpTransM =
  withInfoM (\(ImpTransInfo {..}) ->
              ImpTransInfo { itiExprCtx = MNil, itiPermCtx = MNil,
                             itiPermStack = MNil, itiPermStackVars = MNil, .. })

-- | Get most recently bound variable
getTopVarM :: ImpTransM ext blocks tops rets ps (ctx :> tp) (ExprTrans tp)
getTopVarM = (\(_ :>: p) -> p) <$> itiExprCtx <$> ask

-- | Get the top permission on the stack
getTopPermM :: ImpTransM ext blocks tops rets (ps :> tp) ctx (PermTrans ctx tp)
getTopPermM = (\(_ :>: p) -> p) <$> itiPermStack <$> ask

-- | Helper to disambiguate the @ext@ type variable
getExtReprM :: PermCheckExtC ext exprExt =>
               ImpTransM ext blocks tops rets ps ctx (ExtRepr ext)
getExtReprM = return knownRepr

-- | Apply a transformation to the (translation of the) current perm stack
withPermStackM :: (RAssign (Member ctx) ps_in -> RAssign (Member ctx) ps_out) ->
                  (PermTransCtx ctx ps_in -> PermTransCtx ctx ps_out) ->
                  ImpTransM ext blocks tops rets ps_out ctx a ->
                  ImpTransM ext blocks tops rets ps_in ctx a
withPermStackM f_vars f_p =
  withInfoM $ \info ->
  info { itiPermStack = f_p (itiPermStack info),
         itiPermStackVars = f_vars (itiPermStackVars info) }

-- | Get the current permission stack as a 'DistPerms' in context
getPermStackDistPerms :: ImpTransM ext blocks tops rets ps ctx
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

-- | Run a computation if the current 'ChecksFlag' is set
ifChecksFlagM :: ImpTransM ext blocks tops rets ps ctx () ->
                 ImpTransM ext blocks tops rets ps ctx ()
ifChecksFlagM m =
  (itiChecksFlag <$> ask) >>= \checks ->
  if checksFlagSet checks then m else return ()

-- | Assert a property of the current permission stack, raising an 'error' if it
-- fails to hold. The 'String' names the construct being translated.
assertPermStackM :: HasCallStack => String ->
                    (RAssign (Member ctx) ps -> PermTransCtx ctx ps -> Bool) ->
                    ImpTransM ext blocks tops rets ps ctx ()
assertPermStackM nm f =
  ifChecksFlagM
  (ask >>= \info ->
   if f (itiPermStackVars info) (itiPermStack info) then return () else
     error ("translate: " ++ nm ++ nlPrettyCallStack callStack))

-- | Assert that the top portion of the current permission stack equals the
-- given 'DistPerms'
assertPermStackTopEqM :: HasCallStack => ps ~ (ps1 :++: ps2) =>
                         String -> f ps1 -> Mb ctx (DistPerms ps2) ->
                         ImpTransM ext blocks tops rets ps ctx ()
assertPermStackTopEqM nm prx expected =
  ifChecksFlagM
  (getPermStackDistPerms >>= \perms ->
   let actuals =
         fmap (snd . splitDistPerms prx (mbDistPermsToProxies expected)) perms in
   if expected == actuals then return () else
     error ("assertPermStackEqM (" ++ nm ++ "): expected permission stack:\n" ++
            permPrettyString emptyPPInfo expected ++
            "\nFound permission stack:\n" ++
            permPrettyString emptyPPInfo actuals ++
            nlPrettyCallStack callStack))

-- | Assert that the current permission stack equals the given 'DistPerms'
assertPermStackEqM :: HasCallStack => String -> Mb ctx (DistPerms ps) ->
                      ImpTransM ext blocks tops rets ps ctx ()
assertPermStackEqM nm perms =
  -- FIXME: unify this function with assertPermStackTopEqM
  ifChecksFlagM
  (getPermStackDistPerms >>= \stack_perms ->
   if perms == stack_perms then return () else
     error ("assertPermStackEqM (" ++ nm ++ "): expected permission stack:\n" ++
            permPrettyString emptyPPInfo perms ++
            "\nFound permission stack:\n" ++
            permPrettyString emptyPPInfo stack_perms ++
            nlPrettyCallStack callStack))

-- | Assert that the top permission is as given by the arguments
assertTopPermM :: HasCallStack => String -> Mb ctx (ExprVar a) ->
                  Mb ctx (ValuePerm a) ->
                  ImpTransM ext blocks tops rets (ps :> a) ctx ()
assertTopPermM nm x p =
  ifChecksFlagM
  (getPermStackDistPerms >>= \stack_perms ->
   case mbMatch stack_perms of
     [nuMP| DistPermsCons _ x' p' |] | x == x' && p == p' -> return ()
     [nuMP| DistPermsCons _ x' p' |] ->
       error ("assertTopPermM (" ++ nm ++ "): expected top permissions:\n" ++
              permPrettyString emptyPPInfo (mbMap2 distPerms1 x p) ++
              "\nFound top permissions:\n" ++
              permPrettyString emptyPPInfo (mbMap2 distPerms1 x' p') ++
              nlPrettyCallStack callStack ++
              "\nCurrent perm stack:\n" ++
              permPrettyString emptyPPInfo stack_perms))

-- | Get the (translation of the) perms for a variable
getVarPermM :: Mb ctx (ExprVar tp) ->
               ImpTransM ext blocks tops rets ps ctx (PermTrans ctx tp)
getVarPermM x = RL.get (translateVar x) <$> itiPermCtx <$> ask

-- | Assert that a variable has a given permission
assertVarPermM :: HasCallStack => String -> Mb ctx (ExprVar tp) ->
                  Mb ctx (ValuePerm tp) ->
                  ImpTransM ext blocks tops rets ps ctx ()
assertVarPermM nm x p =
  do x_p <- permTransPerm (mbToProxy p) <$> getVarPermM x
     if x_p == p then return () else
       error ("assertVarPermM (" ++ nm ++ "):\n" ++
              "expected: " ++ permPrettyString emptyPPInfo p ++ "\n" ++
              "found:" ++ permPrettyString emptyPPInfo x_p ++
              nlPrettyCallStack callStack)

-- | Set the (translation of the) perms for a variable in a computation
setVarPermM :: Mb ctx (ExprVar tp) -> PermTrans ctx tp ->
               ImpTransM ext blocks tops rets ps ctx a ->
               ImpTransM ext blocks tops rets ps ctx a
setVarPermM x p =
  local $ \info -> info { itiPermCtx =
                            RL.set (translateVar x) p $ itiPermCtx info }

-- | Clear all permissions in the permission variable map in a sub-computation,
-- leaving only those permissions on the top of the stack
clearVarPermsM :: ImpTransM ext blocks tops rets ps ctx a ->
                  ImpTransM ext blocks tops rets ps ctx a
clearVarPermsM =
  local $ \info -> info { itiPermCtx =
                            RL.map (const PTrans_True) $ itiPermCtx info }

-- | Return the current @FunStack@ as a term
funStackTermM :: ImpTransM ext blocks tops rets ps ctx OpenTerm
funStackTermM = funStackTerm <$> itiFunStack <$> ask

-- | Apply an 'OpenTerm' to the current event type @E@, @evRetType@, @stack@,
-- and a list of other arguments
applySpecOpM :: OpenTerm -> [OpenTerm] ->
                ImpTransM ext blocks tops rets ps ctx OpenTerm
applySpecOpM f args =
  do stack <- funStackTermM
     applyEventOpM f (stack : args)

-- | Like 'applySpecOpM' but where the function is given by name
applyNamedSpecOpM :: Ident -> [OpenTerm] ->
                     ImpTransM ext blocks tops rets ps ctx OpenTerm
applyNamedSpecOpM f args = applySpecOpM (globalOpenTerm f) args

-- | Apply a named @SpecM@ operation to the current event type @E@ and
-- @evRetType@, to the empty function stack, and to additional arguments
applyNamedSpecOpEmptyM :: Ident -> [OpenTerm] ->
                          ImpTransM ext blocks tops rets ps ctx OpenTerm
applyNamedSpecOpEmptyM f args =
  applyNamedEventOpM f (emptyStackOpenTerm : args)

-- | Generate the type @SpecM E evRetType stack A@ using the current event type
-- and @stack@ and the supplied type @A@. This is different from
-- 'specMTypeTransM' because it uses the current @stack@ in an 'ImpTransM'
-- computation, and so does not need it passed as an argument.
specMImpTransM :: OpenTerm -> ImpTransM ext blocks tops rets ps ctx OpenTerm
specMImpTransM tp = applyNamedSpecOpM "Prelude.SpecM" [tp]

-- | Build a term @bindS m k@ with the given @m@ of type @m_tp@ and where @k@
-- is build as a lambda with the given variable name and body
bindSpecMTransM :: OpenTerm -> TypeTrans tr -> String ->
                   (tr -> ImpTransM ext blocks tops rets ps ctx OpenTerm) ->
                   ImpTransM ext blocks tops rets ps ctx OpenTerm
bindSpecMTransM m m_tp str f =
  do ret_tp <- returnTypeM
     k_tm <- lambdaTransM str m_tp f
     applyNamedSpecOpM "Prelude.bindS" [typeTransType1 m_tp, ret_tp, m, k_tm]

-- | The current non-monadic return type
returnTypeM :: ImpTransM ext blocks tops rets ps_out ctx OpenTerm
returnTypeM = itiReturnType <$> ask

-- | Build the monadic return type @SpecM E evRetType stack ret@, where @ret@ is
-- the current return type in 'itiReturnType'
compReturnTypeM :: ImpTransM ext blocks tops rets ps_out ctx OpenTerm
compReturnTypeM = returnTypeM >>= specMImpTransM

-- | Like 'compReturnTypeM' but build a 'TypeTrans'
compReturnTypeTransM ::
  ImpTransM ext blocks tops rets ps_out ctx (TypeTrans OpenTerm)
compReturnTypeTransM = flip mkTypeTrans1 id <$> compReturnTypeM

-- | Build an @errorS@ computation with the given error message
mkErrorComp :: String -> ImpTransM ext blocks tops rets ps_out ctx OpenTerm
mkErrorComp msg =
  do ret_tp <- returnTypeM
     applyNamedSpecOpM "Prelude.errorS" [ret_tp, stringLitOpenTerm (pack msg)]

-- | The typeclass for the implication translation of a functor at any
-- permission set inside any binding to an 'OpenTerm'
class NuMatchingAny1 f => ImplTranslateF f ext blocks tops rets where
  translateF :: Mb ctx (f ps) -> ImpTransM ext blocks tops rets ps ctx OpenTerm


----------------------------------------------------------------------
-- * Translating Permission Implication Constructs
----------------------------------------------------------------------

-- | Translate the output permissions of a 'SimplImpl'
translateSimplImplOut :: Mb ctx (SimplImpl ps_in ps_out) ->
                         ImpTransM ext blocks tops rets ps ctx
                         (TypeTrans (PermTransCtx ctx ps_out))
translateSimplImplOut = translate . mbSimplImplOut

-- | Translate the head output permission of a 'SimplImpl'
translateSimplImplOutHead :: Mb ctx (SimplImpl ps_in (ps_out :> a)) ->
                             ImpTransM ext blocks tops rets ps ctx
                             (TypeTrans (PermTrans ctx a))
translateSimplImplOutHead =
  translate . mbMapCl $(mkClosed [| varAndPermPerm . RL.head |]) . mbSimplImplOut

-- | Translate the head of the tail of the output permission of a 'SimplImpl'
translateSimplImplOutTailHead :: Mb ctx (SimplImpl ps_in (ps_out :> a :> b)) ->
                                 ImpTransM ext blocks tops rets ps ctx
                                 (TypeTrans (PermTrans ctx a))
translateSimplImplOutTailHead =
  translate . mbMapCl $(mkClosed [| varAndPermPerm . RL.head . RL.tail |])
  . mbSimplImplOut

-- | Translate a 'SimplImpl' to a function on translation computations
translateSimplImpl ::
  Proxy ps -> Mb ctx (SimplImpl ps_in ps_out) ->
  ImpTransM ext blocks tops rets (ps :++: ps_out) ctx OpenTerm ->
  ImpTransM ext blocks tops rets (ps :++: ps_in) ctx OpenTerm
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
       tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(ps :>: p_top) ->
           ps :>: typeTransF tptrans [leftTrans tp1 tp2 p_top])
         m

  [nuMP| SImpl_IntroOrR _ p1 p2 |] ->
    do tp1 <- translate p1
       tp2 <- translate p2
       tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(ps :>: p_top) ->
           ps :>: typeTransF tptrans [rightTrans tp1 tp2 p_top])
         m

  [nuMP| SImpl_IntroExists _ e p |] ->
    do let tp = mbExprType e
       tp_trans <- translateClosed tp
       out_trans <- translateSimplImplOutHead mb_simpl
       etrans <- translate e
       trm <- sigmaPermTransM "x_ex" tp_trans (mbCombine RL.typeCtxProxies p)
                              etrans getTopPermM
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF out_trans [trm])
         m

  [nuMP| SImpl_Cast _ _ _ |] ->
    withPermStackM RL.tail
    (\(pctx :>: _ :>: ptrans) -> pctx :>: ptrans)
    m

  [nuMP| SImpl_CastPerm (_::ExprVar a) eqp |] ->
    do ttrans <- translateSimplImplOut mb_simpl
       let prxs_a = MNil :>: (Proxy :: Proxy a)
       let prxs1 = mbLift $ mbMapCl $(mkClosed [| distPermsToProxies
                                                . eqProofPerms |]) eqp
       let prxs = RL.append prxs_a prxs1
       withPermStackM id
         (\pctx ->
           let (pctx1, pctx2) = RL.split ps0 prxs pctx in
           RL.append pctx1 (typeTransF ttrans (transTerms pctx2)))
         m

  [nuMP| SImpl_IntroEqRefl x |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF ttrans []) m

  [nuMP| SImpl_InvertEq _ y |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM ((:>: translateVar y) . RL.tail)
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans []) m

  [nuMP| SImpl_InvTransEq _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) -> pctx :>: typeTransF ttrans []) m

  [nuMP| SImpl_UnitEq x _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF ttrans []) m


  [nuMP| SImpl_CopyEq _ _ |] ->
    withPermStackM
    (\(vars :>: var) -> (vars :>: var :>: var))
    (\(pctx :>: ptrans) -> (pctx :>: ptrans :>: ptrans))
    m

  [nuMP| SImpl_LLVMWordEq _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail (\(pctx :>: _ :>: _) ->
                                pctx :>: typeTransF ttrans []) m

  [nuMP| SImpl_LLVMOffsetZeroEq x |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF ttrans []) m

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

  [nuMP| SImpl_IntroStructTrue x _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_StructEqToPerm _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_StructPermToEq _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_IntroStructField _ _ memb _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: PTrans_Conj [APTrans_Struct pctx_str] :>: ptrans) ->
           pctx :>: typeTransF tptrans (transTerms $
                                        RL.set (mbLift memb) ptrans pctx_str))
         m

  [nuMP| SImpl_ConstFunPerm _ _ _ ident |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           pctx :>: typeTransF tptrans [globalOpenTerm $ mbLift ident])
         m

  [nuMP| SImpl_CastLLVMWord _ _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_InvertLLVMOffsetEq _ _ mb_y |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM
         (\(vars :>: _) -> (vars :>: translateVar mb_y))
         (\(pctx :>: _) -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_OffsetLLVMWord _ _ _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM
         (\(vars :>: _ :>: x_var) -> vars :>: x_var)
         (\(pctx :>: _ :>: _) -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_CastLLVMPtr _ _ _ _ |] ->
    -- FIXME: offsetLLVMPerm can throw away conjuncts, like free and llvmfunptr
    -- permissions, that change the type of the translation
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: ptrans) ->
           pctx :>: typeTransF tptrans (transTerms ptrans))
         m

  [nuMP| SImpl_CastLLVMFree _ _ e2 |] ->
    withPermStackM RL.tail
    ((:>: PTrans_Conj [APTrans_LLVMFree e2]) . RL.tail . RL.tail)
    m

  [nuMP| SImpl_CastLLVMFieldOffset _ _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans :>: _) ->
           pctx :>: typeTransF tptrans (transTerms ptrans))
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
      pctx :>: PTrans_Conj [
        APTrans_LLVMField
        (mbMapCl $(mkClosed [| \fld -> fld { llvmFieldRW = PExpr_Read } |]) mb_fld)
        ptrans'])
    m

  [nuMP| SImpl_SplitLLVMTrueField x _ _ _ |] ->
    do ttrans <- translateSimplImplOut mb_simpl
       withPermStackM (:>: translateVar x)
         (\(pctx :>: _) -> RL.append pctx $ typeTransF ttrans [])
         m

  [nuMP| SImpl_TruncateLLVMTrueField _ _ _ |] ->
    do ttrans <- translateSimplImplOut mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> RL.append pctx $ typeTransF ttrans [])
         m

  [nuMP| SImpl_ConcatLLVMTrueFields _ _ _ |] ->
    do ttrans <- translateSimplImplOut mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) -> RL.append pctx $ typeTransF ttrans [])
         m

  [nuMP| SImpl_DemoteLLVMArrayRW _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_LLVMArrayCopy _ mb_ap _ _ |] ->
    do let mb_sub_ap =
             case mbSimplImplOut mb_simpl of
               [nuP| _ :>: VarAndPerm _ (ValPerm_LLVMArray sub_ap) :>: _ |] ->
                 sub_ap
               _ -> error "translateSimplImpl: SImpl_LLVMArrayCopy: unexpected perms"
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

  [nuMP| SImpl_LLVMArrayBorrow _ mb_ap _ _ |] ->
    do let mb_sub_ap =
             case mbSimplImplOut mb_simpl of
               [nuP| _ :>: VarAndPerm _ (ValPerm_LLVMArray sub_ap) :>: _ |] ->
                 sub_ap
               _ -> error "translateSimplImpl: SImpl_LLVMArrayCopy: unexpected perms"
       sub_ap_tp_trans <- translate mb_sub_ap
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
    do (w_term, len1_tm, elem_tp, _) <- translateLLVMArrayPerm mb_ap1
       (_, len2_tm, _, _) <- translateLLVMArrayPerm mb_ap2
       tp_trans <- translateSimplImplOutHead mb_simpl
       len3_tm <- translate1 $ fmap (\(ValPerm_LLVMArray ap) ->
                                      llvmArrayLen ap) $
         fmap distPermsHeadPerm $ mbSimplImplOut mb_simpl
       (_ :>: ptrans1 :>: ptrans2) <- itiPermStack <$> ask
       arr_out_comp_tm  <-
         applyNamedSpecOpM "Prelude.appendCastBVVecS"
           [w_term, len1_tm, len2_tm, len3_tm, elem_tp,
            transTerm1 ptrans1, transTerm1 ptrans2]
       bindSpecMTransM arr_out_comp_tm tp_trans "appended_array" $ \ptrans_arr' ->
         withPermStackM RL.tail (\(pctx :>: _ :>: _) ->
                                  pctx :>: ptrans_arr') m


  [nuMP| SImpl_LLVMArrayRearrange _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_LLVMArrayToField _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans [])
         m

  [nuMP| SImpl_LLVMArrayEmpty x mb_ap |] ->
    do (w_tm, _, elem_tp, ap_tp_trans) <- translateLLVMArrayPerm mb_ap
       -- First we build a term of type Vec 0 elem_tp using EmptyVec
       let vec_tm = applyGlobalOpenTerm "Prelude.EmptyVec" [elem_tp]
       -- Next, we build a computation that casts it to BVVec w 0x0 elem_tp
       let w = fromIntegral $ natVal2 mb_ap
       let bvZero_nat_tm =
             applyGlobalOpenTerm "Prelude.bvToNat"
             [w_tm, bvLitOpenTerm (replicate w False)]
       vec_cast_m <-
         applyNamedSpecOpM "Prelude.castVecS" [elem_tp, natOpenTerm 0,
                                               bvZero_nat_tm, vec_tm]
       bindSpecMTransM vec_cast_m ap_tp_trans "empty_vec" $ \ptrans_arr ->
         withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: PTrans_Conj [APTrans_LLVMArray ptrans_arr])
         m

-- translate1/translateClosed ( zeroOfType <- get the default element )
  [nuMP| SImpl_LLVMArrayBorrowed x _ mb_ap |] ->
    do (w_tm, len_tm, elem_tp, ap_tp_trans) <- translateLLVMArrayPerm mb_ap
       withPermStackM (:>: translateVar x)
         (\(pctx :>: ptrans_block) ->
           let arr_term =
                 applyOpenTermMulti (globalOpenTerm "Prelude.repeatBVVec")
                 [w_tm, len_tm, elem_tp, transTerm1 ptrans_block] in
           pctx :>:
           PTrans_Conj [APTrans_LLVMArray $ typeTransF ap_tp_trans [arr_term]] :>:
           ptrans_block)
         m

  [nuMP| SImpl_LLVMArrayFromBlock _ _ |] ->
    do mb_ap <-
         case mbSimplImplOut mb_simpl of
           [nuP| DistPermsCons _ _ (ValPerm_LLVMArray mb_ap) |] -> return mb_ap
           _ -> error ("translateSimplImpl: SImpl_LLVMArrayFromBlock: "
                       ++ "unexpected form of output permission")
       (w_tm, len_tm, elem_tp, ap_tp_trans) <- translateLLVMArrayPerm mb_ap
       withPermStackM id
         (\(pctx :>: ptrans_cell) ->
           let arr_term =
                 -- FIXME: this generates a BVVec of length (bvNat n 1), whereas
                 -- what we need is a BVVec of length [0,0,...,1]; the two are
                 -- provably equal but not convertible in SAW core
                 {-
                 applyOpenTermMulti (globalOpenTerm "Prelude.singletonBVVec")
                 [w_tm, elem_tp, transTerm1 ptrans_cell]
                 -}
                 applyOpenTermMulti (globalOpenTerm "Prelude.repeatBVVec")
                 [w_tm, len_tm, elem_tp, transTerm1 ptrans_cell] in
           pctx :>:
           PTrans_Conj [APTrans_LLVMArray $ typeTransF ap_tp_trans [arr_term]])
         m


  [nuMP| SImpl_LLVMArrayCellCopy _ _ mb_cell |] ->
    do (_ :>: ptrans_array :>: ptrans_props) <- itiPermStack <$> ask
       let arr_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayCellCopy" ptrans_array
       let prop_transs =
             unPTransBVProps
             "translateSimplImpl: SImpl_LLVMArrayCellCopy" ptrans_props
       cell_tm <- translate1 mb_cell
       let cell_ptrans =
             getLLVMArrayTransCell arr_trans mb_cell cell_tm prop_transs
       withPermStackM id
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [cell_ptrans] :>: ptrans_array)
         m

  [nuMP| SImpl_LLVMArrayCellBorrow _ mb_ap mb_cell |] ->
    do (_ :>: ptrans_array :>: ptrans_props) <- itiPermStack <$> ask
       let arr_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayCellBorrow" ptrans_array
       let prop_transs =
             unPTransBVProps
             "translateSimplImpl: SImpl_LLVMArrayCellBorrow" ptrans_props
       cell_tm <- translate1 mb_cell
       let cell_ptrans =
             getLLVMArrayTransCell arr_trans mb_cell cell_tm prop_transs
       {- let b = LLVMArrayBorrowTrans (fmap FieldBorrow ix) prop_transs -}
       let arr_trans' =
             arr_trans { llvmArrayTransPerm =
                           mbMap2 (\ap cell ->
                                    llvmArrayAddBorrow (FieldBorrow cell) ap)
                           mb_ap mb_cell }
       withPermStackM id
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [cell_ptrans] :>:
           PTrans_Conj [APTrans_LLVMArray arr_trans'])
         m

  [nuMP| SImpl_LLVMArrayCellReturn _ mb_ap mb_cell |] ->
    do (_ :>: ptrans_cell :>: ptrans_array) <- itiPermStack <$> ask
       let aptrans_cell = case ptrans_cell of
             PTrans_Conj [aptrans] -> aptrans
             _ -> error ("translateSimplImpl: SImpl_LLVMArrayCellReturn: "
                         ++ "found non-field perm where field perm was expected")
       let arr_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayCellCopy" ptrans_array
       {- let b_trans = llvmArrayTransFindBorrow (fmap FieldBorrow cell) arr_trans -}
       cell_tm <- translate1 mb_cell
       let arr_trans' =
             (setLLVMArrayTransCell arr_trans cell_tm
              {- (llvmArrayBorrowTransProps b_trans) -} aptrans_cell)
             { llvmArrayTransPerm =
                 mbMap2 (\ap cell ->
                          llvmArrayRemBorrow (FieldBorrow cell) ap) mb_ap mb_cell }
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [APTrans_LLVMArray arr_trans'])
         m

  [nuMP| SImpl_LLVMArrayContents _ mb_ap mb_sh impl |] ->
    do p_out_trans <- translateSimplImplOutHead mb_simpl
       (w_term, len_term, elem_tp, _) <- translateLLVMArrayPerm mb_ap
       cell_in_trans <-
         translate $ mbMapCl $(mkClosed [| ValPerm_LLVMBlock .
                                         llvmArrayPermHead |]) mb_ap
       cell_out_trans <-
         translate $ mbMap2 (\ap sh -> ValPerm_LLVMBlock $ llvmArrayPermHead $
                                       ap { llvmArrayCellShape = sh })
         mb_ap mb_sh
       impl_tm <-
         -- FIXME: this code just fabricates a pretend LLVM value for the
         -- arbitrary cell of the array that is used to substitute for the
         -- variable bound by the LocalPermImpl, which seems like a hack...
         inExtTransM ETrans_LLVM $
         translateCurryLocalPermImpl "Error mapping array cell permissions:"
         (mbCombine RL.typeCtxProxies impl) MNil MNil
         (fmap ((MNil :>:) . extPermTrans) cell_in_trans) (MNil :>: Member_Base)
         (fmap ((MNil :>:) . extPermTrans) cell_out_trans)
       -- Build the computation that maps impl_tm over the input array using the
       -- mapBVVecM monadic combinator
       ptrans_arr <- getTopPermM
       arr_out_comp_tm <-
         applyNamedSpecOpM "Prelude.mapBVVecS"
           [elem_tp, typeTransType1 cell_out_trans, impl_tm,
            w_term, len_term, transTerm1 ptrans_arr]
       -- Now use bindS to bind the result of arr_out_comp_tm in the remaining
       -- computation
       bindSpecMTransM arr_out_comp_tm p_out_trans "mapped_array" $ \ptrans_arr' ->
         withPermStackM id (\(pctx :>: _) -> pctx :>: ptrans_arr') m

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

  [nuMP| SImpl_SplitLifetime _ f args l _ _ _ _ ps_in ps_out |] ->
    do pctx_out_trans <- translateSimplImplOut mb_simpl
       ps_in_trans <- translate ps_in
       ps_out_trans <- translate ps_out
       -- FIXME: write a fun to translate-and-apply a lifetimefunctor
       x_tp_trans <- translate (mbMap3 ltFuncApply f args l)
       ptrans_l <- getTopPermM
       f_tm <-
         weakenLifetimeFun x_tp_trans ps_in_trans ps_out_trans $
         transTerm1 ptrans_l
       withPermStackM
         (\(ns :>: x :>: _ :>: l2) -> ns :>: x :>: l2)
         (\(pctx :>: ptrans_x :>: _ :>: _) ->
           -- The permission for x does not change type, just its lifetime; the
           -- permission for l has the (tupled) type of x added as a new input and
           -- output with tupleSpecMFunBoth
           RL.append pctx $
           typeTransF pctx_out_trans (transTerms ptrans_x ++ [f_tm]))
         m

  [nuMP| SImpl_SubsumeLifetime _ _ _ _ _ _ _ |] ->
    do pctx_out_trans <- translateSimplImplOut mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans_l) ->
           RL.append pctx $ typeTransF pctx_out_trans (transTerms ptrans_l))
         m

  [nuMP| SImpl_ContainedLifetimeCurrent _ _ _ _ _ _ _ |] ->
    do pctx_out_trans <- translateSimplImplOut mb_simpl
       withPermStackM
         (\(ns :>: l1) -> ns :>: l1 :>: l1)
         (\(pctx :>: ptrans_l) ->
           -- Note: lcurrent perms do not contain any terms and the term for the
           -- lowned permission does not change, so the only terms in both the
           -- input and the output are in ptrans_l
           RL.append pctx $ typeTransF pctx_out_trans (transTerms ptrans_l))
         m

  [nuMP| SImpl_RemoveContainedLifetime _ _ _ _ _ _ _ |] ->
    do pctx_out_trans <- translateSimplImplOut mb_simpl
       withPermStackM
         (\(ns :>: l1 :>: _) -> ns :>: l1)
         (\(pctx :>: ptrans_l :>: _) ->
           -- Note: lcurrent perms do not contain any terms and the term for the
           -- lowned permission does not change, so the only terms in both the
           -- input and the output are in ptrans_l
           RL.append pctx $ typeTransF pctx_out_trans (transTerms ptrans_l))
         m

  [nuMP| SImpl_WeakenLifetime _ _ _ _ _ |] ->
    do pctx_out_trans <- translateSimplImplOut mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans_x :>: _) ->
           -- NOTE: lcurrent permissions have no term translations, so we can
           -- construct the output PermTransCtx by just passing the terms in
           -- ptrans_x to pctx_out_trans
           RL.append pctx (typeTransF pctx_out_trans $ transTerms ptrans_x))
         m

  [nuMP| SImpl_MapLifetime l _ _ _ ps_in ps_out _ _
                           ps_in' ps_out' ps1 ps2 impl_in impl_out |] ->
    -- First, translate the output permissions and all of the perm lists
    do pctx_out_trans <- translateSimplImplOut mb_simpl
       ps_in_trans <- tupleTypeTrans <$> translate ps_in
       ps_out_trans <- tupleTypeTrans <$> translate ps_out
       ps_in'_trans <- tupleTypeTrans <$> translate ps_in'
       ps_out'_trans <- tupleTypeTrans <$> translate ps_out'
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
             fmap (fromJustOrError . exprPermsVars) ps_in'
           ps_out_vars =
             RL.map (translateVar . getCompose) $ mbRAssign $
             fmap (fromJustOrError . exprPermsVars) ps_out
       impl_in_tm <-
         translateCurryLocalPermImpl "Error mapping lifetime input perms:" impl_in
         pctx1 vars1 ps_in'_trans ps_in'_vars ps_in_trans
       impl_out_tm <-
         translateCurryLocalPermImpl "Error mapping lifetime output perms:" impl_out
         pctx2 vars2 ps_out_trans ps_out_vars ps_out'_trans
       l_res_tm_h <-
         applyNamedSpecOpEmptyM "Prelude.composeS"
         [typeTransType1 ps_in_trans, typeTransType1 ps_out_trans,
          typeTransType1 ps_out'_trans, transTerm1 ptrans_l, impl_out_tm]
       l_res_tm <-
         applyNamedSpecOpEmptyM "Prelude.composeS"
         [typeTransType1 ps_in'_trans, typeTransType1 ps_in_trans,
          typeTransType1 ps_out'_trans, impl_in_tm, l_res_tm_h]

       -- Finally, update the permissions
       withPermStackM
         (\_ -> vars_out)
         (\_ -> RL.append pctx_ps $ typeTransF pctx_out_trans [l_res_tm])
         m

  [nuMP| SImpl_EndLifetime _ _ _ ps_in ps_out |] ->
    -- First, translate the output permissions and the input and output types of
    -- the monadic function for the lifeime ownership permission
    do ps_out_trans <- tupleTypeTrans <$> translate ps_out
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
             mbRAssign $ fmap (fromJustHelper . exprPermsVars) ps_out

       -- Now we apply the lifetime ownerhip function to ps_in and bind its output
       -- in the rest of the computation
       lifted_m <-
         applyNamedSpecOpM "Prelude.liftStackS"
         [typeTransType1 ps_out_trans,
          applyOpenTerm (transTerm1 ptrans_l) (transTupleTerm pctx_in)]
       bindSpecMTransM
         lifted_m
         ps_out_trans
         "endl_ps"
         (\pctx_out ->
           withPermStackM
           (\(_ :>: l) -> vars_out :>: l)
           (\_ -> RL.append pctx_ps pctx_out :>:
                  PTrans_Conj [APTrans_LFinished])
           m)

  [nuMP| SImpl_IntroLOwnedSimple _ _ _ |] ->
    do let prx_ps_l = mbRAssignProxies $ mbSimplImplIn mb_simpl
       ttrans <- translateSimplImplOut mb_simpl
       withPermStackM id
         (\pctx ->
           let (pctx0, pctx_ps :>: _) = RL.split ps0 prx_ps_l pctx in
           RL.append pctx0 $ typeTransF ttrans (transTerms pctx_ps))
         m

  [nuMP| SImpl_ElimLOwnedSimple _ _ mb_lops |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       lops_tp <- typeTransTupleType <$> translate mb_lops
       f_tm <-
         lambdaOpenTermTransM "ps" lops_tp $ \x ->
         applyNamedSpecOpEmptyM "Prelude.retS" [lops_tp, x]
       withPermStackM id
         (\(pctx0 :>: _) -> pctx0 :>: typeTransF ttrans [f_tm])
         m

  [nuMP| SImpl_LCurrentRefl l |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar l) (:>: typeTransF ttrans []) m

  [nuMP| SImpl_LCurrentTrans _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail (\(pctx :>: _ :>: _) ->
                                (pctx :>: typeTransF ttrans [])) m

  [nuMP| SImpl_DemoteLLVMBlockRW _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_IntroLLVMBlockEmpty x _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF ttrans [unitOpenTerm])
         m

  [nuMP| SImpl_CoerceLLVMBlockEmpty _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans [unitOpenTerm])
         m

  [nuMP| SImpl_ElimLLVMBlockToBytes _ mb_bp |] ->
    do let w = natVal2 mb_bp
       let w_term = natOpenTerm w
       len_term <- translate1 $ fmap llvmBlockLen mb_bp
       ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           let arr_term =
                 applyOpenTermMulti (globalOpenTerm "Prelude.repeatBVVec")
                 [w_term, len_term, unitTypeOpenTerm, unitOpenTerm] in
           pctx :>: typeTransF ttrans [arr_term])
         m

  [nuMP| SImpl_IntroLLVMBlockSeqEmpty _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [pairOpenTerm (transTerm1 ptrans)
                                       unitOpenTerm])
         m

  [nuMP| SImpl_ElimLLVMBlockSeqEmpty _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [pairLeftOpenTerm (transTerm1 ptrans)])
         m

  [nuMP| SImpl_SplitLLVMBlockEmpty _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           pctx :>: typeTransF ttrans [unitOpenTerm, unitOpenTerm])
         m

  -- Intro for a recursive named shape applies the fold function to the
  -- translations of the arguments plus the translations of the proofs of the
  -- permissions
  [nuMP| SImpl_IntroLLVMBlockNamed _ bp nmsh |]
    | [nuMP| RecShapeBody _ _ fold_ids |] <- mbMatch $ fmap namedShapeBody nmsh
    , [nuMP| PExpr_NamedShape _ _ _ args |] <- mbMatch $ fmap llvmBlockShape bp ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         args_trans <- translate args
         fold_id <-
           case fold_ids of
             [nuP| Just (fold_id,_) |] -> return fold_id
             _ -> error "Folding recursive shape before it is defined!"
         withPermStackM id
           (\(pctx :>: ptrans_x) ->
             pctx :>: typeTransF ttrans [applyOpenTermMulti
                                         (globalOpenTerm $ mbLift fold_id)
                                         (transTerms args_trans ++
                                          transTerms ptrans_x)])
           m

  -- Intro for a defined named shape (the other case) is a no-op
    | [nuMP| DefinedShapeBody _ |] <- mbMatch $ fmap namedShapeBody nmsh ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         withPermStackM id
           (\(pctx :>: ptrans) ->
             pctx :>: typeTransF ttrans [transTerm1 ptrans])
           m

    | otherwise -> fail "translateSimplImpl: SImpl_IntroLLVMBlockNamed, unknown named shape"

  -- Elim for a recursive named shape applies the unfold function to the
  -- translations of the arguments plus the translations of the proofs of the
  -- permissions
  [nuMP| SImpl_ElimLLVMBlockNamed _ bp nmsh |]
    | [nuMP| RecShapeBody _ _ fold_ids |] <- mbMatch $ fmap namedShapeBody nmsh
    , [nuMP| PExpr_NamedShape _ _ _ args |] <- mbMatch $ fmap llvmBlockShape bp ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         args_trans <- translate args
         unfold_id <-
           case fold_ids of
             [nuP| Just (_,unfold_id) |] -> return unfold_id
             _ -> error "Unfolding recursive shape before it is defined!"
         withPermStackM id
           (\(pctx :>: ptrans_x) ->
             pctx :>: typeTransF ttrans [applyOpenTermMulti
                                         (globalOpenTerm $ mbLift unfold_id)
                                         (transTerms args_trans ++
                                          transTerms ptrans_x)])
           m

  -- Intro for a defined named shape (the other case) is a no-op
    | [nuMP| DefinedShapeBody _ |] <- mbMatch $ fmap namedShapeBody nmsh ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         withPermStackM id
           (\(pctx :>: ptrans) ->
             pctx :>: typeTransF ttrans [transTerm1 ptrans])
           m

    | otherwise -> fail "translateSimplImpl: ElimLLVMBlockNamed, unknown named shape"

  [nuMP| SImpl_IntroLLVMBlockNamedMods _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_ElimLLVMBlockNamedMods _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_IntroLLVMBlockFromEq _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_IntroLLVMBlockPtr _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_ElimLLVMBlockPtr _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_IntroLLVMBlockField _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTupleTerm ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockField _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF (tupleTypeTrans ttrans) [transTerm1 ptrans])
         m

  [nuMP| SImpl_IntroLLVMBlockArray _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockArray _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_IntroLLVMBlockSeq _ _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans1 :>: ptrans2) ->
           let pair_term =
                 pairOpenTerm (transTerm1 ptrans1) (transTerm1 ptrans2) in
           pctx :>: typeTransF ttrans [pair_term])
         m

  [nuMP| SImpl_ElimLLVMBlockSeq _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [pairLeftOpenTerm (transTerm1 ptrans),
                                       pairRightOpenTerm (transTerm1 ptrans)])
         m

  [nuMP| SImpl_IntroLLVMBlockOr _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockOr _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_IntroLLVMBlockEx _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockEx _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockFalse _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_FoldNamed _ (NamedPerm_Rec rp) args _ |] ->
    do args_trans <- translate args
       ttrans <- translateSimplImplOutHead mb_simpl
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
       ttrans <- translateSimplImplOutHead mb_simpl
       let unfold_ident = mbLift $ fmap recPermUnfoldFun rp
       withPermStackM id
         (\(pctx :>: ptrans_x) ->
           pctx :>:
           typeTransF (tupleTypeTrans ttrans) [applyOpenTermMulti
                                               (globalOpenTerm unfold_ident)
                                               (transTerms args_trans
                                                ++ [transTerm1 ptrans_x])])
         m

  [nuMP| SImpl_FoldNamed _ (NamedPerm_Defined _) _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_UnfoldNamed _ (NamedPerm_Defined _) _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  {-
  [nuMP| SImpl_Mu _ _ _ _ |] ->
    error "FIXME HERE: SImpl_Mu: translation not yet implemented"
  -}

  [nuMP| SImpl_NamedToConj _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedFromConj _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedArgAlways _ _ _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedArgCurrent _ _ _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans :>: _) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedArgWrite _ _ _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedArgRead _ _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_ReachabilityTrans _ rp args _ y e |] ->
    do args_trans <- translate args
       e_trans <- translate e
       y_trans <- translate y
       ttrans <- translateSimplImplOutHead mb_simpl
       let trans_ident = mbLift $ fmap recPermTransMethod rp
       withPermStackM RL.tail
         (\(pctx :>: ptrans_x :>: ptrans_y) ->
           pctx :>:
           typeTransF (tupleTypeTrans ttrans) [applyOpenTermMulti
                                               (globalOpenTerm trans_ident)
                                               (transTerms args_trans
                                                ++ transTerms e_trans
                                                ++ transTerms y_trans
                                                ++ transTerms e_trans
                                                ++ [transTerm1 ptrans_x,
                                                    transTerm1 ptrans_y])])
         m

  [nuMP| SImpl_IntroAnyEqEq _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: typeTransF tp_trans []) m

  [nuMP| SImpl_IntroAnyWordPtr _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: typeTransF tp_trans []) m

  [nuMP| SImpl_ElimAnyToEq _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           pctx :>: typeTransF tp_trans []) m

  [nuMP| SImpl_ElimAnyToPtr _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           pctx :>: typeTransF tp_trans []) m


-- | A flag to indicate whether the translation of a permission implication
-- contains any failures
data HasFailures = HasFailures | NoFailures deriving Eq

instance Semigroup HasFailures where
  HasFailures <> _ = HasFailures
  _ <> HasFailures = HasFailures
  NoFailures <> NoFailures = NoFailures

instance Monoid HasFailures where
  mempty = NoFailures

-- | The monad for translating 'PermImpl's, which accumulates all failure
-- messages in all branches of a 'PermImpl' and either returns a result or
-- results in only failures
type PermImplTransM = MaybeT (Writer ([String], HasFailures))

-- | Run a 'PermImplTransM' computation
runPermImplTransM :: PermImplTransM a -> (Maybe a, ([String], HasFailures))
runPermImplTransM = runWriter . runMaybeT

-- | Signal a failure in a 'PermImplTransM' computation with the given string
pitmFail :: String -> PermImplTransM a
pitmFail str = tell ([str],HasFailures) >> mzero

-- | Catch any failures in a 'PermImplTransM' computation, returning 'Nothing'
-- if the computation completely fails, or an @a@ paired with a 'HasFailures'
-- flag to indicate if that @a@ contains some partial failures. Reset the
-- 'HasFailures' flag so that @'pitmCatching' m@ is marked as having no failures
-- even if @m@ has failures.
pitmCatching :: PermImplTransM a -> PermImplTransM (Maybe a, HasFailures)
pitmCatching m =
  do let (maybe_a, (strs,hasf)) = runPermImplTransM m
     tell (strs,NoFailures)
     return (maybe_a,hasf)

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
                         ImpTransM ext blocks tops rets ps ctx OpenTerm) ->
                  ImplFailCont ->
                  ImpTransM ext blocks tops rets ps ctx OpenTerm
forceImplTrans (Just trans) k = trans k
forceImplTrans Nothing (ImplFailContTerm errM) = return errM
forceImplTrans Nothing (ImplFailContMsg str) =
  returnTypeM >>= \tp ->
  applyNamedSpecOpM "Prelude.errorS" [tp, stringLitOpenTerm (pack str)]

-- | Perform a failure by jumping to a failure continuation or signaling an
-- error, using an alternate error message in the latter case
implTransAltErr :: String -> ImplFailCont ->
                   ImpTransM ext blocks tops rets ps ctx OpenTerm
implTransAltErr _ (ImplFailContTerm errM) = return errM
implTransAltErr str (ImplFailContMsg _) =
  returnTypeM >>= \tp ->
  applyNamedSpecOpM "Prelude.errorS" [tp, stringLitOpenTerm (pack str)]

-- | Translate a normal unary 'PermImpl1' rule that succeeds and applies the
-- translation function if the argument succeeds and fails if the translation of
-- the argument fails
translatePermImplUnary ::
  RL.TypeCtx bs =>
  ImplTranslateF r ext blocks tops rets =>
  Mb ctx (MbPermImpls r (RNil :> '(bs,ps_out))) ->
  (ImpTransM ext blocks tops rets ps_out (ctx :++: bs) OpenTerm ->
   ImpTransM ext blocks tops rets ps ctx OpenTerm) ->
  PermImplTransM (ImplFailCont ->
                  ImpTransM ext blocks tops rets ps ctx OpenTerm)
translatePermImplUnary (mbMatch -> [nuMP| MbPermImpls_Cons _ _ mb_impl |]) f =
  translatePermImpl Proxy (mbCombine RL.typeCtxProxies mb_impl) >>= \trans ->
  return $ \k -> f $ trans k


-- | Translate a 'PermImpl1' to a function on translation computations
translatePermImpl1 :: ImplTranslateF r ext blocks tops rets =>
                      Proxy '(ext, blocks, tops, ret) ->
                      Mb ctx (PermImpl1 ps ps_outs) ->
                      Mb ctx (MbPermImpls r ps_outs) ->
                      PermImplTransM
                      (ImplFailCont ->
                       ImpTransM ext blocks tops rets ps ctx OpenTerm)
translatePermImpl1 prx mb_impl mb_impls = case (mbMatch mb_impl, mbMatch mb_impls) of
  -- A failure translates to a call to the catch handler, which is the most recent
  -- Impl1_Catch, if one exists, or the SAW errorM function otherwise
  ([nuMP| Impl1_Fail str |], _) -> pitmFail $ mbLift str

  ([nuMP| Impl1_Catch |],
   [nuMP| (MbPermImpls_Cons _ (MbPermImpls_Cons _ _ mb_impl1) mb_impl2) |]) ->
    pitmCatching (translatePermImpl prx $
                  mbCombine RL.typeCtxProxies mb_impl1) >>= \case
    -- Short-circuit: if mb_impl1 succeeds, don't translate mb_impl2
    (Just trans, NoFailures) -> return trans
    (mtrans1, hasf1) ->
      pitmCatching (translatePermImpl prx $
                    mbCombine RL.typeCtxProxies mb_impl2) >>= \(mtrans2,
                                                                hasf2) ->

      -- Only report the possibility of failures if both branches have them
      (if hasf1 == HasFailures && hasf2 == HasFailures
       then tell ([],HasFailures)
       else return ()) >>

      -- Combine the two continuations
      case (mtrans1, hasf1, mtrans2, hasf2) of
        -- If mb_impl2 has no failures, drop mb_impl1
        (_, _, Just trans, NoFailures) -> return trans
        -- If both sides are defined but have failures, insert a catchpoint
        (Just trans1, _, Just trans2, _) ->
          return $ \k ->
          compReturnTypeM >>= \ret_tp ->
          letTransM "catchpoint" ret_tp (trans2 k)
          (\catchpoint -> trans1 $ ImplFailContTerm catchpoint)
        -- Otherwise, use whichever side is defined
        (Just trans, _, Nothing, _) -> return trans
        (Nothing, _, Just trans, _) -> return trans
        (Nothing, _, Nothing, _) -> mzero

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

  -- If all branches of an or elimination fail, the whole thing fails; otherwise,
  -- an or elimination performs a multi way Eithers elimination
  ([nuMP| Impl1_ElimOrs x mb_or_list |], _) ->
    -- First, translate all the PermImpls in mb_impls, using pitmCatching to
    -- isolate failures to each particular branch, but still reporting failures
    -- in any branch
    mapM (pitmCatching . translatePermImpl prx)
         (mbOrListPermImpls mb_or_list mb_impls) >>= \transs ->
    let (mtranss, hasfs) = unzip transs in
    tell ([], mconcat hasfs) >>
    -- As a special case, if all branches fail (representing as translating to
    -- Nothing), then the entire or elimination fails
    if all isNothing mtranss then mzero else
      return $ \k ->
      do let mb_or_p = mbOrListPerm mb_or_list
         () <- assertTopPermM "Impl1_ElimOrs" x mb_or_p
         tps <- mapM translate $ mbOrListDisjs mb_or_list
         tp_ret <- compReturnTypeTransM
         top_ptrans <- getTopPermM
         eithersElimTransM tps tp_ret
           (flip map mtranss $ \mtrans ptrans ->
             withPermStackM id ((:>: ptrans) . RL.tail) $
             forceImplTrans mtrans k)
           (transTupleTerm top_ptrans)

  -- An existential elimination performs a pattern-match on a Sigma
  ([nuMP| Impl1_ElimExists x p |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do () <- assertTopPermM "Impl1_ElimExists" x (fmap ValPerm_Exists p)
       let tp = mbBindingType p
       top_ptrans <- getTopPermM
       tp_trans <- translateClosed tp
       sigmaElimPermTransM "x_elimEx" tp_trans
         (mbCombine RL.typeCtxProxies p)
         compReturnTypeTransM
         (\etrans ptrans ->
           inExtTransM etrans $
           withPermStackM id ((:>: ptrans) . RL.tail) m)
         (transTerm1 top_ptrans)

  -- A false elimination becomes a call to efq
  ([nuMP| Impl1_ElimFalse mb_x |], _) ->
    return $ const $
    do mb_false <- nuMultiTransM $ const ValPerm_False
       () <- assertTopPermM "Impl1_ElimFalse" mb_x mb_false
       top_ptrans <- getTopPermM
       applyMultiTransM (return $ globalOpenTerm "Prelude.efq")
         [compReturnTypeM, return $ transTerm1 top_ptrans]

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
       let mb_y = mbCombine RL.typeCtxProxies $ fmap (const $ nu $ \y ->
                                                       PExpr_Var y) x
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
      pctx :>: PTrans_Conj [
        APTrans_LLVMField
        (mbCombine RL.typeCtxProxies $
         mbMapCl $(mkClosed [| \fld -> nu $ \y ->
                              llvmFieldSetEqVar fld y |]) mb_fld) $
        PTrans_Eq (mbCombine RL.typeCtxProxies $
                   fmap (const $ nu PExpr_Var) mb_fld)]
      :>: ptrans')
    m

  ([nuMP| Impl1_ElimLLVMBlockToEq _ mb_bp |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    inExtTransM ETrans_LLVMBlock $
    do let mb_p_out1 =
             mbCombine RL.typeCtxProxies $
             mbMapCl $(mkClosed
                       [| \bp -> nu $ \y ->
                         let len = llvmBlockLen bp in
                         ValPerm_Conj1 $ Perm_LLVMBlock $
                         bp { llvmBlockShape =
                                PExpr_EqShape len $ PExpr_Var y } |])
             mb_bp
       tp_trans1 <- translate mb_p_out1
       let mb_p_out2 =
             mbMapCl $(mkClosed
                       [| ValPerm_Conj1
                        . Perm_LLVMBlockShape . modalizeBlockShape |]) $
             extMb mb_bp
       tp_trans2 <- translate mb_p_out2
       withPermStackM (:>: Member_Base)
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans1 [unitOpenTerm] :>:
           typeTransF tp_trans2 [transTerm1 ptrans])
         m

  ([nuMP| Impl1_SplitLLVMWordField _ mb_fp mb_sz1 mb_endianness |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do let mb_e = case mbLLVMFieldContents mb_fp of
             [nuP| ValPerm_Eq (PExpr_LLVMWord e) |] -> e
             _ -> error "translatePermImpl1: Impl1_SplitLLVMWordField"
       e_tm <- translate1 mb_e
       sz1_tm <- translate mb_sz1
       sz2_tm <- translateClosed $ mbLLVMFieldSize mb_fp
       let sz2m1_tm =
             applyOpenTermMulti (globalOpenTerm "Prelude.subNat") [sz2_tm,
                                                                   sz1_tm]
       let (e1_tm,e2_tm) =
             bvSplitOpenTerm (mbLift mb_endianness) sz1_tm sz2m1_tm e_tm
       inExtTransM (ETrans_Term e1_tm) $ inExtTransM (ETrans_Term e2_tm) $
         translate
         (mbCombine RL.typeCtxProxies $ flip mbMapCl mb_fp
          ($(mkClosed
             [| \sz1 endianness fp ->
               impl1SplitLLVMWordFieldOutPerms fp sz1 endianness |])
           `clApply` toClosed (mbLift mb_sz1)
           `clApply` toClosed (mbLift mb_endianness))) >>= \pctx_out ->
         withPermStackM
         (\(vars :>: x) -> vars :>: x :>: x :>:
                           Member_Step Member_Base :>: Member_Base)
         (\(pctx :>: _) ->
           -- NOTE: all output perms are eq or ptr to eq perms, so contain no
           -- SAW core terms
           pctx `RL.append` typeTransF pctx_out [])
         m

  ([nuMP| Impl1_TruncateLLVMWordField _ mb_fp mb_sz1 mb_endianness |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do let mb_e = case mbLLVMFieldContents mb_fp of
             [nuP| ValPerm_Eq (PExpr_LLVMWord e) |] -> e
             _ -> error "translatePermImpl1: Impl1_TruncateLLVMWordField"
       e_tm <- translate1 mb_e
       sz1_tm <- translate mb_sz1
       sz2_tm <- translateClosed $ mbLLVMFieldSize mb_fp
       let sz2m1_tm =
             applyOpenTermMulti (globalOpenTerm "Prelude.subNat") [sz2_tm,
                                                                   sz1_tm]
       let (e1_tm,_) =
             bvSplitOpenTerm (mbLift mb_endianness) sz1_tm sz2m1_tm e_tm
       inExtTransM (ETrans_Term e1_tm) $
         translate
         (mbCombine RL.typeCtxProxies $ flip mbMapCl mb_fp
          ($(mkClosed
             [| \sz1 endianness fp ->
               impl1TruncateLLVMWordFieldOutPerms fp sz1 endianness |])
           `clApply` toClosed (mbLift mb_sz1)
           `clApply` toClosed (mbLift mb_endianness))) >>= \pctx_out ->
         withPermStackM (:>: Member_Base)
         (\(pctx :>: _) ->
           -- NOTE: all output perms are eq or ptr to eq perms, so contain no
           -- SAW core terms
           pctx `RL.append` typeTransF pctx_out [])
         m

  ([nuMP| Impl1_ConcatLLVMWordFields _ mb_fp1 mb_e2 mb_endianness |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do let mb_e1 = case mbLLVMFieldContents mb_fp1 of
             [nuP| ValPerm_Eq (PExpr_LLVMWord e1) |] -> e1
             _ -> error "translatePermImpl1: Impl1_ConcatLLVMWordFields"
       e1_tm <- translate1 mb_e1
       e2_tm <- translate1 mb_e2
       sz1_tm <- translateClosed $ mbLLVMFieldSize mb_fp1
       sz2_tm <- translateClosed $ mbExprBVTypeWidth mb_e2
       let endianness = mbLift mb_endianness
       let e_tm = bvConcatOpenTerm endianness sz1_tm sz2_tm e1_tm e2_tm
       inExtTransM (ETrans_Term e_tm) $
         translate (mbCombine RL.typeCtxProxies $
                    mbMap2 (\fp1 e2 ->
                             impl1ConcatLLVMWordFieldsOutPerms fp1 e2 endianness)
                    mb_fp1 mb_e2) >>= \pctx_out ->
         withPermStackM
         (\(vars :>: x :>: _) -> (vars :>: x :>: Member_Base))
         (\(pctx :>: _ :>: _) ->
           -- NOTE: all output perms are eq or ptr to eq perms, so contain no
           -- SAW core terms
           pctx `RL.append` typeTransF pctx_out [])
         m

  ([nuMP| Impl1_BeginLifetime |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    inExtTransM ETrans_Lifetime $
    do tp_trans <- translateClosed (ValPerm_LOwned
                                    [] CruCtxNil CruCtxNil MNil MNil)
       id_fun <-
         lambdaOpenTermTransM "ps_empty" unitTypeOpenTerm $ \x ->
         applyNamedSpecOpM "Prelude.retS" [unitTypeOpenTerm, x]
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
      pitmFail (mbLift prop_str)

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

  -- If e1 and e2 are already unequal, short-circuit and do nothing
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_Neq e1 e2) _ |], _)
    | not $ mbLift (mbMap2 bvCouldEqual e1 e2) ->
      translatePermImplUnary mb_impls $
        withPermStackM (:>: translateVar x)
          (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop unitOpenTerm)])

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

  -- If we know e1 < e2 statically, translate to unsafeAssert
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULt e1 e2) _ |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      translatePermImpl prx (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
      return $ \k ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         let pf_tm =
               applyOpenTermMulti (globalOpenTerm "Prelude.unsafeAssertBVULt")
               [natOpenTerm w, t1, t2]
         withPermStackM (:>: translateVar x)
           (:>: bvPropPerm (BVPropTrans prop pf_tm))
           (trans k)

  -- If we don't know e1 < e2 statically, translate to bvultWithProof
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

  -- If we know e1 <= e2 statically, translate to unsafeAssert
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq e1 e2) _ |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      translatePermImpl prx (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
      return $ \k ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         let pf_tm =
               applyOpenTermMulti (globalOpenTerm "Prelude.unsafeAssertBVULe")
               [natOpenTerm w, t1, t2]
         withPermStackM (:>: translateVar x)
           (:>: bvPropPerm (BVPropTrans prop pf_tm))
           (trans k)

  -- If we don't know e1 <= e2 statically, translate to bvuleWithProof
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

  -- If we know e1 <= e2-e3 statically, translate to unsafeAssert
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq_Diff e1 e2 e3) _ |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      translatePermImpl prx (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
      return $ \k ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         t3 <- translate1 e3
         let pf_tm =
               applyOpenTermMulti (globalOpenTerm "Prelude.unsafeAssertBVULe")
               [natOpenTerm w, t1,
                applyOpenTermMulti (globalOpenTerm
                                    "Prelude.bvSub") [natOpenTerm w, t2, t3]]
         withPermStackM (:>: translateVar x)
           (:>: bvPropPerm (BVPropTrans prop pf_tm))
           (trans k)

  -- If we don't know e1 <= e2-e3 statically, translate to bvuleWithProof
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
    pitmFail ("translatePermImpl1: Unhandled BVProp case")


-- | Translate a 'PermImpl' in the 'PermImplTransM' monad to a function that
-- takes a failure continuation and returns a monadic computation to generate
-- the translation as a term
translatePermImpl :: ImplTranslateF r ext blocks tops rets =>
                     Proxy '(ext, blocks, tops, ret) ->
                     Mb ctx (PermImpl r ps) ->
                     PermImplTransM
                     (ImplFailCont ->
                      ImpTransM ext blocks tops rets ps ctx OpenTerm)
translatePermImpl prx mb_impl = case mbMatch mb_impl of
  [nuMP| PermImpl_Done r |] ->
    return $ const $ translateF r
  [nuMP| PermImpl_Step impl1 mb_impls |] ->
    translatePermImpl1 prx impl1 mb_impls


instance ImplTranslateF r ext blocks tops rets =>
         Translate (ImpTransInfo ext blocks tops rets ps)
                   ctx (AnnotPermImpl r ps) OpenTerm where
  translate (mbMatch -> [nuMP| AnnotPermImpl err impl |]) =
    let (transF, (errs,_)) = runPermImplTransM $ translatePermImpl Proxy impl in
    forceImplTrans transF $
    ImplFailContMsg (mbLift err ++ "\n\n"
                     ++ concat (intersperse
                                "\n\n--------------------\n\n" errs))

-- We translate a LocalImplRet to a term that returns all current permissions
instance ImplTranslateF (LocalImplRet ps) ext blocks ps_in rets where
  translateF _ =
    do pctx <- itiPermStack <$> ask
       ret_tp <- returnTypeM
       applyNamedSpecOpM "Prelude.retS" [ret_tp, transTupleTerm pctx]

-- | Translate a local implication to its output, adding an error message
translateLocalPermImpl :: String -> Mb ctx (LocalPermImpl ps_in ps_out) ->
                          ImpTransM ext blocks tops rets ps_in ctx OpenTerm
translateLocalPermImpl err (mbMatch -> [nuMP| LocalPermImpl impl |]) =
  clearVarPermsM $ translate $ fmap (AnnotPermImpl err) impl

-- | Translate a local implication over two sequences of permissions (already
-- translated to types) to a monadic function with the first sequence of
-- permissions as free variables and that takes in the second permissions as
-- arguments. This monadic function is relative to the empty function stack.
-- Note that the translations of the second input permissions and the output
-- permissions must have exactly one type, i.e., already be tupled.
translateCurryLocalPermImpl ::
  String -> Mb ctx (LocalPermImpl (ps1 :++: ps2) ps_out) ->
  PermTransCtx ctx ps1 -> RAssign (Member ctx) ps1 ->
  TypeTrans (PermTransCtx ctx ps2) -> RAssign (Member ctx) ps2 ->
  TypeTrans (PermTransCtx ctx ps_out) ->
  ImpTransM ext blocks tops rets ps ctx OpenTerm
translateCurryLocalPermImpl err impl pctx1 vars1 tp_trans2 vars2 tp_trans_out =
  lambdaTransM "x_local" tp_trans2 $ \pctx2 ->
  local (\info -> info { itiReturnType = typeTransType1 tp_trans_out }) $
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
instance (PermCheckExtC ext exprExt, TransInfo info) =>
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
    [nuMP| BVUndef w |] ->
      -- FIXME: we should really handle poison values; this translation just
      -- treats them as if there were the bitvector 0 value
      return $ ETrans_Term $ bvBVOpenTerm (mbLift w) $ BV.zero (mbLift w)
    [nuMP| BVLit w mb_bv |] ->
      return $ ETrans_Term $ bvBVOpenTerm (mbLift w) $ mbLift mb_bv
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
       return (bvBVOpenTerm w (BV.one w)),
       return (bvBVOpenTerm w (BV.zero w))]
    [nuMP| BVNonzero mb_w e |] ->
      let w = mbLift mb_w in
      ETrans_Term <$>
      applyTransM (return $ globalOpenTerm "Prelude.not")
      (applyMultiTransM (return $ globalOpenTerm "Prelude.bvEq")
       [translate mb_w, translateRWV e,
        return (bvBVOpenTerm w (BV.zero w))])

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
instance (PermCheckExtC ext exprExt, TransInfo info) =>
         Translate info ctx (TypedExpr ext tp) (ExprTrans tp) where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedExpr _ (Just e) |] -> translate e
    [nuMP| TypedExpr app Nothing |] -> translate app

-- | Get the output permission on the return value of a 'TypedExpr'
exprOutPerm :: PermCheckExtC ext exprExt => Mb ctx (TypedExpr ext tp) ->
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
                  ImpTransM ext blocks tops rets ps ctx OpenTerm
translateApply nm f perms =
  do assertPermStackEqM nm perms
     expr_ctx <- itiExprCtx <$> ask
     arg_membs <- itiPermStackVars <$> ask
     let e_args = RL.map (flip RL.get expr_ctx) arg_membs
     i_args <- itiPermStack <$> ask
     return $
       {-
       trace ("translateApply for " ++ nm ++ " with perm arguments:\n" ++
              -- renderDoc (list $ debugPrettyPermCtx (mbToProxy perms) i_args)
              -- permPrettyString emptyPPInfo (permTransCtxPerms (mbToProxy perms) i_args)
              permPrettyString emptyPPInfo perms
             ) $ -}
       applyOpenTermMulti f (exprCtxToTerms e_args ++ permCtxToTerms i_args)

-- | Translate a call to (the translation of) an entrypoint, by either calling
-- the letrec-bound variable for the entrypoint, if it has one, or by just
-- translating the body of the entrypoint if it does not.
translateCallEntry :: forall ext exprExt tops args ghosts blocks ctx rets.
                      PermCheckExtC ext exprExt => String ->
                      TypedEntryTrans ext blocks tops rets args ghosts ->
                      Mb ctx (RAssign ExprVar (tops :++: args)) ->
                      Mb ctx (RAssign ExprVar ghosts) ->
                      ImpTransM ext blocks tops rets
                      ((tops :++: args) :++: ghosts) ctx OpenTerm
translateCallEntry nm entry_trans mb_tops_args mb_ghosts =
  -- First test that the stack == the required perms for entryID
  do let entry = typedEntryTransEntry entry_trans
     ectx <- translate $ mbMap2 RL.append mb_tops_args mb_ghosts
     stack <- itiPermStack <$> ask
     let mb_s =
           mbMap2 (\tops_args ghosts ->
                    permVarSubstOfNames $ RL.append tops_args ghosts)
           mb_tops_args mb_ghosts
     let mb_perms = fmap (\s -> varSubst s $ mbValuePermsToDistPerms $
                                typedEntryPermsIn entry) mb_s
     () <- assertPermStackEqM nm mb_perms

     -- Now check if entryID has an associated multiFixS-bound function
     case typedEntryTransRecIx entry_trans of
       Just ix ->
         -- If so, build the associated CallS term
         -- FIXME: refactor the code that gets the exprs for the stack
         do expr_ctx <- itiExprCtx <$> ask
            arg_membs <- itiPermStackVars <$> ask
            let e_args = RL.map (flip RL.get expr_ctx) arg_membs
            i_args <- itiPermStack <$> ask
            applyCallS ix (exprCtxToTerms e_args ++ permCtxToTerms i_args)
       Nothing ->
         inEmptyEnvImpTransM $ inCtxTransM ectx $
         do perms_trans <- translate $ typedEntryPermsIn entry
            withPermStackM
              (const $ RL.members ectx)
              (const $ typeTransF perms_trans $ transTerms stack)
              (translate $ typedEntryBody entry)


instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (CallSiteImplRet blocks tops args ghosts ps) OpenTerm where
  translate (mbMatch ->
             [nuMP| CallSiteImplRet entryID ghosts Refl mb_tavars mb_gvars |]) =
    do entry_trans <-
         lookupEntryTransCast (mbLift entryID) (mbLift ghosts) <$>
         itiBlockMapTrans <$> ask
       translateCallEntry "CallSiteImplRet" entry_trans mb_tavars mb_gvars

instance PermCheckExtC ext exprExt =>
         ImplTranslateF (CallSiteImplRet blocks tops args ghosts)
         ext blocks tops rets where
  translateF mb_tgt = translate mb_tgt


instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedJumpTarget blocks tops ps) OpenTerm where
  translate (mbMatch -> [nuMP| TypedJumpTarget siteID _ _ mb_perms_in |]) =
    do SomeTypedCallSite site <-
         lookupCallSite (mbLift siteID) <$> itiBlockMapTrans <$> ask
       let CallSiteImpl mb_impl = typedCallSiteImpl site
       translate $ flip fmap mb_perms_in $ \perms_in ->
         varSubst (permVarSubstOfNames $ distPermsVars perms_in) mb_impl

instance PermCheckExtC ext exprExt =>
         ImplTranslateF (TypedJumpTarget blocks tops) ext blocks tops rets where
  translateF mb_tgt = translate mb_tgt


----------------------------------------------------------------------
-- * Translating Typed Crucible Statements
----------------------------------------------------------------------

-- | Translate a 'TypedStmt' to a function on translation computations
translateStmt ::
  PermCheckExtC ext exprExt => ProgramLoc ->
  Mb ctx (TypedStmt ext stmt_rets ps_in ps_out) ->
  ImpTransM ext blocks tops rets ps_out (ctx :++: stmt_rets) OpenTerm ->
  ImpTransM ext blocks tops rets ps_in ctx OpenTerm
translateStmt loc mb_stmt m = case mbMatch mb_stmt of
  [nuMP| TypedSetReg tp e |] ->
    do tp_trans <- translate tp
       tp_ret <- compReturnTypeM
       etrans <- tpTransM $ translate e
       let ptrans = exprOutPerm e
       inExtTransSAWLetBindM tp_trans tp_ret etrans $
         withPermStackM (:>: Member_Base) (:>: extPermTrans ptrans) m

  [nuMP| TypedSetRegPermExpr _ e |] ->
    do etrans <- tpTransM $ translate e
       inExtTransM etrans $
         withPermStackM (:>: Member_Base) (:>: PTrans_Eq (extMb e)) m

  -- FIXME HERE: document this!
  [nuMP| TypedCall _freg fun_perm _ gexprs args |] ->
    do f_trans <- getTopPermM
       ectx_outer <- itiExprCtx <$> ask
       let rets = mbLift $ mbMapCl $(mkClosed [| funPermRets |]) fun_perm
       let rets_prxs = cruCtxProxies rets
       rets_trans <- translateClosed rets
       let perms_out =
             mbCombine rets_prxs $ flip mbMapCl mb_stmt
             ($(mkClosed [| \prxs stmt -> nuMulti prxs (typedStmtOut stmt) |])
              `clApply` toClosed rets_prxs)
       ectx_gexprs <- translate gexprs
       ectx_args <- translate args
       pctx_in <- RL.tail <$> itiPermStack <$> ask
       let (pctx_ghosts_args, _) =
             RL.split (RL.append ectx_gexprs ectx_args) ectx_gexprs pctx_in
       fret_tp <- sigmaTypeTransM "ret" rets_trans (flip inExtMultiTransM
                                                    (translate perms_out))
       let all_args =
             exprCtxToTerms ectx_gexprs ++ exprCtxToTerms ectx_args ++
             permCtxToTerms pctx_ghosts_args
       fret_trm <- case f_trans of
         PTrans_Conj [APTrans_Fun _ (Right f)] ->
           applyNamedSpecOpM "Prelude.liftStackS"
           [fret_tp, applyOpenTermMulti f all_args]
         PTrans_Conj [APTrans_Fun _ (Left ix)] ->
           applyCallS ix all_args
         _ -> error "translateStmt: TypedCall: unexpected function permission"
       bindSpecMTransM
         fret_trm (openTermTypeTrans fret_tp) "call_ret_val" $ \ret_val ->
         sigmaElimTransM "elim_call_ret_val" rets_trans
           (flip inExtMultiTransM (translate perms_out)) compReturnTypeTransM
           (\rets_ectx pctx ->
             inExtMultiTransM rets_ectx $
             withPermStackM
             (\(vars :>: _) ->
               RL.append
               (fst (RL.split
                     (RL.append ectx_gexprs ectx_args) ectx_gexprs vars)) $
               suffixMembers ectx_outer rets_prxs)
             (const pctx)
             m)
           ret_val

  -- FIXME HERE: figure out why these asserts always translate to ite True
  [nuMP| TypedAssert e _ |] ->
    applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
    [compReturnTypeM, translate1 e, m,
     mkErrorComp ("Failed Assert at " ++
                  renderDoc (ppShortFileName (plSourceLoc loc)))]

  [nuMP| TypedLLVMStmt stmt |] -> translateLLVMStmt stmt m


-- | Translate a 'TypedStmt' to a function on translation computations
translateLLVMStmt ::
  Mb ctx (TypedLLVMStmt r ps_in ps_out) ->
  ImpTransM ext blocks tops rets ps_out (ctx :> r) OpenTerm ->
  ImpTransM ext blocks tops rets ps_in ctx OpenTerm
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

  [nuMP| OffsetLLVMValue _ _ |] ->
    let mb_x_off =
          mbMapCl $(mkClosed [| \(OffsetLLVMValue x off) ->
                               PExpr_LLVMOffset (typedRegVar x) off |])
          mb_stmt in
    inExtTransM ETrans_LLVM $
    withPermStackM (:>: Member_Base) (:>: (PTrans_Eq $ extMb $ mb_x_off))
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
                              mbMapCl $(mkClosed
                                        [| \fp -> nu $ \ret ->
                                          llvmFieldSetEqVar fp ret |]) mb_fp)
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
    translateClosed (llvmEmptyBlockPermOfSize w sz) >>= \ptrans_tp ->
    withPermStackM (:>: Member_Base)
    (\(pctx :>: _) ->
      pctx
      :>: PTrans_Conj [APTrans_LLVMFrame $
                       flip nuMultiWithElim1 (extMb mb_fperm) $
                       \(_ :>: ret) fperm -> (PExpr_Var ret, sz):fperm]
      -- the unitOpenTerm argument is because ptrans_tp is a memblock permission
      -- with an empty shape; the empty shape expects a unit argument
      :>: typeTransF ptrans_tp [unitOpenTerm])
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
       let w :: NatRepr w = knownRepr
       case lookupGlobalSymbol env (mbLift gsym) w of
         Nothing -> error ("translateLLVMStmt: TypedLLVMResolveGlobal: "
                           ++ " no translation of symbol "
                           ++ globalSymbolName (mbLift gsym))
         Just (_, Left i)
           | [nuP| ValPerm_LLVMFunPtr fun_tp (ValPerm_Fun fun_perm) |] <- p ->
             let ptrans = PTrans_Conj [APTrans_LLVMFunPtr (mbLift fun_tp) $
                                       PTrans_Conj [APTrans_Fun
                                                    fun_perm (Left i)]] in
             withPermStackM (:>: Member_Base) (:>: extPermTrans ptrans) m
         Just (_, Left _) ->
           error ("translateLLVMStmt: TypedLLVMResolveGlobal: "
                  ++ " unexpected recursive call translation for symbol "
                  ++ globalSymbolName (mbLift gsym))
         Just (_, Right ts) ->
           translate (extMb p) >>= \ptrans ->
           withPermStackM (:>: Member_Base) (:>: typeTransF ptrans ts) m

  [nuMP| TypedLLVMIte _ mb_r1 _ _ |] ->
    inExtTransM ETrans_LLVM $
    do b <- translate1 $ extMb mb_r1
       tptrans <-
         translate $ mbCombine RL.typeCtxProxies $
         mbMapCl $(mkClosed
                   [| \stmt -> nu $ \ret ->
                     distPermsHeadPerm $ typedLLVMStmtOut stmt ret |])
         mb_stmt
       let t = applyOpenTerm (globalOpenTerm "Prelude.boolToEither") b
       withPermStackM (:>: Member_Base) (:>: typeTransF tptrans [t]) m


----------------------------------------------------------------------
-- * Translating Sequences of Typed Crucible Statements
----------------------------------------------------------------------

instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedRet tops rets ps) OpenTerm where
  translate (mbMatch -> [nuMP| TypedRet Refl mb_rets mb_rets_ns mb_perms |]) =
    do let perms =
             mbMap2
             (\rets_ns ps -> varSubst (permVarSubstOfNames rets_ns) ps)
             mb_rets_ns mb_perms
       () <- assertPermStackEqM "TypedRet" perms
       rets_trans <- translate mb_rets
       let rets_prxs = cruCtxProxies $ mbLift mb_rets
       rets_ns_trans <- translate mb_rets_ns
       ret_tp <- returnTypeM
       sigma_trm <-
         sigmaTransM "r" rets_trans
         (flip inExtMultiTransM $
          translate $ mbCombine rets_prxs mb_perms)
         rets_ns_trans (itiPermStack <$> ask)
       applyNamedSpecOpM "Prelude.retS" [ret_tp, sigma_trm]

instance PermCheckExtC ext exprExt =>
         ImplTranslateF (TypedRet tops rets) ext blocks tops rets where
  translateF mb_ret = translate mb_ret

instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedTermStmt blocks tops rets ps) OpenTerm where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedJump impl_tgt |] -> translate impl_tgt
    [nuMP| TypedBr reg impl_tgt1 impl_tgt2 |] ->
      applyMultiTransM (return $ globalOpenTerm "Prelude.ite")
      [compReturnTypeM, translate1 reg,
       translate impl_tgt1, translate impl_tgt2]
    [nuMP| TypedReturn impl_ret |] -> translate impl_ret
    [nuMP| TypedErrorStmt (Just str) _ |] ->
      mkErrorComp ("Error: " ++ mbLift str)
    [nuMP| TypedErrorStmt Nothing _ |] ->
      mkErrorComp "Error (unknown message)"


instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedStmtSeq ext blocks tops rets ps) OpenTerm where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedImplStmt impl_seq |] -> translate impl_seq
    [nuMP| TypedConsStmt loc stmt pxys mb_seq |] ->
      translateStmt (mbLift loc) stmt (translate $ mbCombine (mbLift pxys) mb_seq)
    [nuMP| TypedTermStmt _ term_stmt |] -> translate term_stmt

instance PermCheckExtC ext exprExt =>
         ImplTranslateF (TypedStmtSeq
                         ext blocks tops rets) ext blocks tops rets where
  translateF mb_seq = translate mb_seq


----------------------------------------------------------------------
-- * Translating CFGs
----------------------------------------------------------------------

-- | An entrypoint over some regular and ghost arguments
data SomeTypedEntry ext blocks tops rets =
  forall ghosts args.
  SomeTypedEntry (TypedEntry TransPhase ext blocks tops rets args ghosts)

-- | Get all entrypoints in a block map that will be translated to letrec-bound
-- variables, which is all entrypoints with in-degree > 1
--
-- FIXME: consider whether we want let and not letRec for entrypoints that have
-- in-degree > 1 but are not the heads of loops
typedBlockLetRecEntries :: TypedBlockMap TransPhase ext blocks tops rets ->
                           [SomeTypedEntry ext blocks tops rets]
typedBlockLetRecEntries =
  concat . RL.mapToList (map (\(Some entry) ->
                               SomeTypedEntry entry)
                         . filter (anyF typedEntryHasMultiInDegree)
                         . (^. typedBlockEntries))

-- | Fold a function over each 'TypedEntry' in a 'TypedBlockMap' that
-- corresponds to a letrec-bound variable
foldBlockMapLetRec ::
  (forall args ghosts.
   TypedEntry TransPhase ext blocks tops rets args ghosts -> b -> b) ->
  b -> TypedBlockMap TransPhase ext blocks tops rets -> b
foldBlockMapLetRec f r =
  foldr (\(SomeTypedEntry entry) -> f entry) r . typedBlockLetRecEntries

-- | Map a function over each 'TypedEntry' in a 'TypedBlockMap' that
-- corresponds to a letrec-bound variable
mapBlockMapLetRec ::
  (forall args ghosts.
   TypedEntry TransPhase ext blocks tops rets args ghosts -> b) ->
  TypedBlockMap TransPhase ext blocks tops rets -> [b]
mapBlockMapLetRec f =
  map (\(SomeTypedEntry entry) -> f entry) . typedBlockLetRecEntries

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
translateEntryLRT :: PermEnv ->
                     TypedEntry TransPhase ext blocks tops rets args ghosts ->
                     OpenTerm
translateEntryLRT env entry@(TypedEntry {..}) =
  runNilTypeTransM env noChecks $
  translateClosed (typedEntryAllArgs entry) >>= \arg_tps ->
  piLRTTransM "arg" arg_tps $ \ectx ->
  inCtxTransM ectx $
  translate typedEntryPermsIn >>= \perms_in_tps ->
  piLRTTransM "p" perms_in_tps $ \_ ->
  translateEntryRetType entry >>= \retType ->
  return $ ctorOpenTerm "Prelude.LRT_Ret" [retType]

-- | Build a list of @LetRecType@ values that describe the types of all of the
-- entrypoints in a 'TypedBlockMap' that will be bound as recursive functions
translateBlockMapLRTs :: PermEnv ->
                         TypedBlockMap TransPhase ext blocks tops rets ->
                         [OpenTerm]
translateBlockMapLRTs env blkMap =
  mapBlockMapLetRec (translateEntryLRT env) blkMap

-- | Return a @LetRecType@ value for the translation of the function permission
-- of a CFG
translateCFGInitEntryLRT :: PermEnv ->
                            TypedCFG ext blocks ghosts inits gouts ret ->
                            OpenTerm
translateCFGInitEntryLRT env (tpcfgFunPerm ->
                              (FunPerm ghosts args gouts ret perms_in perms_out)) =
  runNilTypeTransM env noChecks $
  translateClosed (appendCruCtx ghosts args) >>= \ctx_trans ->
  piLRTTransM "arg" ctx_trans $ \ectx ->
  inCtxTransM ectx $
  translate perms_in >>= \perms_trans ->
  piLRTTransM "perm" perms_trans $ \_ ->
  translateRetType (CruCtxCons gouts ret) perms_out >>= \ret_tp ->
  return $ ctorOpenTerm "Prelude.LRT_Ret" [ret_tp]

-- | FIXME HERE NOW: docs
translateCFGLRTs :: PermEnv -> TypedCFG ext blocks ghosts inits gouts ret ->
                    [OpenTerm]
translateCFGLRTs env cfg =
  translateCFGInitEntryLRT env cfg :
  translateBlockMapLRTs env (tpcfgBlockMap cfg)

-- | Apply @mkFrameCall@ to a frame, an index @n@ in that frame, and list of
-- arguments to build a recursive call to the @n@th function in the frame
mkFrameCall :: OpenTerm -> Natural -> [OpenTerm] -> OpenTerm
mkFrameCall frame ix args =
  applyGlobalOpenTerm "Prelude.mkFrameCall" (frame : natOpenTerm ix : args)

-- | Apply the @callS@ operation to some arguments to build a recursive call
applyCallS :: Natural -> [OpenTerm] ->
              ImpTransM ext blocks tops rets ps ctx OpenTerm
applyCallS ix args =
  do stack <- itiFunStack <$> ask
     case funStackTopAndPrev stack of
       Just (frame, prev_stack) ->
         let call = mkFrameCall frame ix args in
         applyNamedEventOpM "Prelude.callS" [prev_stack, frame, call]
       Nothing ->
         error "applyCallS: Attempt to call a recursive function that is not in scope"

-- | FIXME HERE NOW: docs
translateTypedEntry ::
  Some (TypedEntry TransPhase ext blocks tops rets args) ->
  StateT Natural (TypeTransM ctx) (Some (TypedEntryTrans ext blocks tops rets args))
translateTypedEntry (Some entry) =
  if typedEntryHasMultiInDegree entry then
    do i <- get
       put (i+1)
       return (Some (TypedEntryTrans entry $ Just i))
  else return $ Some (TypedEntryTrans entry Nothing)

-- | Computes a list of @TypedEntryTrans@ values from a list of
-- @TypedEntry@ values that pair each entry with their translation
translateTypedBlock ::
  TypedBlock TransPhase ext blocks tops rets args ->
  StateT Natural (TypeTransM ctx) (TypedBlockTrans ext blocks tops rets args)
translateTypedBlock blk =
  TypedBlockTrans <$>
  mapM translateTypedEntry (blk ^. typedBlockEntries)

-- | Translate a @TypedBlockMap@ to a @TypedBlockMapTrans@ by generating
-- @CallS@ calls for each of the entrypoints that represents a recursive call
translateTypedBlockMap ::
  TypedBlockMap TransPhase ext blocks tops rets ->
  StateT Natural (TypeTransM ctx) (TypedBlockMapTrans ext blocks tops rets)
translateTypedBlockMap blkMap =
  traverseRAssign translateTypedBlock blkMap

-- | Translate the typed statements of an entrypoint to a function
--
-- > \top1 ... topn arg1 ... argm ghost1 ... ghostk p1 ... pj -> stmts_trans
--
-- over the top-level, local, and ghost arguments and (the translations of) the
-- input permissions of the entrypoint
translateEntryBody :: PermCheckExtC ext exprExt =>
                      FunStack -> TypedBlockMapTrans ext blocks tops rets ->
                      TypedEntry TransPhase ext blocks tops rets args ghosts ->
                      TypeTransM RNil OpenTerm
translateEntryBody stack mapTrans entry =
  lambdaExprCtx (typedEntryAllArgs entry) $
  lambdaPermCtx (typedEntryPermsIn entry) $ \pctx ->
  do retType <- translateEntryRetType entry
     impTransM (RL.members pctx) pctx mapTrans stack retType $
       translate $ typedEntryBody entry

-- | Translate all the entrypoints in a 'TypedBlockMap' that correspond to
-- letrec-bound functions to SAW core functions as in 'translateEntryBody'
translateBlockMapBodies :: PermCheckExtC ext exprExt => FunStack ->
                           TypedBlockMapTrans ext blocks tops rets ->
                           TypedBlockMap TransPhase ext blocks tops rets ->
                           TypeTransM RNil [OpenTerm]
translateBlockMapBodies stack mapTrans blkMap =
  sequence $
  mapBlockMapLetRec (translateEntryBody stack mapTrans) blkMap

-- | FIXME HERE NOW: docs
translateCFGInitEntryBody ::
  PermCheckExtC ext exprExt => FunStack ->
  TypedBlockMapTrans ext blocks (ghosts :++: inits) (gouts :> ret) ->
  TypedCFG ext blocks ghosts inits gouts ret ->
  TypeTransM RNil OpenTerm
translateCFGInitEntryBody stack mapTrans (cfg :: TypedCFG ext blocks ghosts inits gouts ret) =
  let fun_perm = tpcfgFunPerm cfg
      h = tpcfgHandle cfg
      ctx = typedFnHandleAllArgs h
      inits = typedFnHandleArgs h
      ghosts = typedFnHandleGhosts h
      retTypes = typedFnHandleRetTypes h in
  lambdaExprCtx ctx $
  translateRetType retTypes (tpcfgOutputPerms cfg) >>= \retTypeTrans ->

  -- Extend the expr context to contain another copy of the initial arguments
  -- inits, since the initial entrypoint for the entire function takes two
  -- copies of inits, one to represent the top-level arguments and one to
  -- represent the local arguments to the entrypoint, which just happen to be
  -- the same as those top-level arguments and so get eq perms to relate them
  inExtMultiTransCopyLastM ghosts (cruCtxProxies inits) $

  lambdaPermCtx (funPermToBlockInputs fun_perm) $ \pctx ->
  let all_membs = RL.members pctx
      all_px = RL.map (\_ -> Proxy) pctx
      init_entry = lookupEntryTransCast (tpcfgEntryID cfg) CruCtxNil mapTrans in
  impTransM all_membs pctx mapTrans stack retTypeTrans $
  translateCallEntry "CFG" init_entry (nuMulti all_px id) (nuMulti all_px $
                                                           const MNil)

-- | FIXME HERE NOW: docs
translateCFGBodies :: PermCheckExtC ext exprExt => FunStack -> Natural ->
                      TypedCFG ext blocks ghosts inits gouts ret ->
                      TypeTransM RNil [OpenTerm]
translateCFGBodies stack start_ix cfg =
  do let blkMap = tpcfgBlockMap cfg
     mapTrans <-
       evalStateT (translateTypedBlockMap blkMap) (start_ix+1)
     bodies <- translateBlockMapBodies stack mapTrans blkMap
     init_body <- translateCFGInitEntryBody stack mapTrans cfg
     return (init_body : bodies)

-- | Lambda-abstract over all the expression and permission arguments of the
-- translation of a CFG, passing them to a Haskell function
lambdaCFGArgs :: PermEnv -> TypedCFG ext blocks ghosts inits gouts ret ->
                 ([OpenTerm] -> TypeTransM (ghosts :++: inits) OpenTerm) ->
                 OpenTerm
lambdaCFGArgs env cfg bodyF =
  runNilTypeTransM env noChecks $
  lambdaExprCtx (typedFnHandleAllArgs (tpcfgHandle cfg)) $
  lambdaPermCtx (funPermIns $ tpcfgFunPerm cfg) $ \pctx ->
  do ectx <- infoCtx <$> ask
     bodyF (transTerms ectx ++ transTerms pctx)

-- | Pi-abstract over all the expression and permission arguments of the
-- translation of a CFG, passing them to a Haskell function
piCFGArgs :: PermEnv -> TypedCFG ext blocks ghosts inits gouts ret ->
             ([OpenTerm] -> TypeTransM (ghosts :++: inits) OpenTerm) ->
             OpenTerm
piCFGArgs env cfg bodyF =
  runNilTypeTransM env noChecks $
  piExprCtx (typedFnHandleAllArgs (tpcfgHandle cfg)) $
  piPermCtx (funPermIns $ tpcfgFunPerm cfg) $ \pctx ->
  do ectx <- infoCtx <$> ask
     bodyF (transTerms ectx ++ transTerms pctx)

-- | Translate a typed CFG to a SAW term (FIXME HERE NOW: explain the term that
-- is generated and the fun args)
translateCFG :: PermEnv -> OpenTerm -> OpenTerm -> OpenTerm -> Natural ->
                TypedCFG ext blocks ghosts inits gouts ret ->
                OpenTerm
translateCFG env prev_stack frame bodies ix cfg =
  lambdaCFGArgs env cfg $ \args ->
  applyNamedEventOpM "Prelude.multiFixS" [prev_stack, frame, bodies,
                                          mkFrameCall frame ix args]


----------------------------------------------------------------------
-- * Translating Sets of CFGs
----------------------------------------------------------------------

-- | An existentially quantified tuple of a 'CFG', its function permission, and
-- a 'String' name we want to translate it to
data SomeCFGAndPerm ext where
  SomeCFGAndPerm :: GlobalSymbol -> String -> CFG ext blocks inits ret ->
                    FunPerm ghosts (CtxToRList inits) gouts ret ->
                    SomeCFGAndPerm ext

-- | An existentially quantified tuple of a 'TypedCFG', its 'GlobalSymbol', and
-- a 'String' name we want to translate it to
data SomeTypedCFG ext where
  SomeTypedCFG :: GlobalSymbol -> String ->
                  TypedCFG ext blocks ghosts inits gouts ret ->
                  SomeTypedCFG ext

-- | Extract the 'GlobalSymbol' from a 'SomeCFGAndPerm'
someCFGAndPermSym :: SomeCFGAndPerm ext -> GlobalSymbol
someCFGAndPermSym (SomeCFGAndPerm sym _ _ _) = sym

-- | Extract the 'String' name from a 'SomeCFGAndPerm'
someCFGAndPermToName :: SomeCFGAndPerm ext -> String
someCFGAndPermToName (SomeCFGAndPerm _ nm _ _) = nm

-- | Helper function to build an LLVM function permission from a 'FunPerm'
mkPtrFunPerm :: HasPtrWidth w => FunPerm ghosts args gouts ret ->
                ValuePerm (LLVMPointerType w)
mkPtrFunPerm fun_perm =
  withKnownNat ?ptrWidth $ ValPerm_Conj1 $ mkPermLLVMFunPtr ?ptrWidth fun_perm

-- | Map a 'SomeCFGAndPerm' to a 'PermEnvGlobalEntry' with no translation, i.e.,
-- with an 'error' term for the translation
someCFGAndPermGlobalEntry :: HasPtrWidth w => SomeCFGAndPerm ext ->
                             PermEnvGlobalEntry
someCFGAndPermGlobalEntry (SomeCFGAndPerm sym _ _ fun_perm) =
  withKnownNat ?ptrWidth $
  PermEnvGlobalEntry sym (mkPtrFunPerm fun_perm) $
  error "someCFGAndPermGlobalEntry: unexpected translation during type-checking"

-- | Convert the 'FunPerm' of a 'SomeCFGAndPerm' to an inductive @LetRecType@
-- description of the SAW core type it translates to
someCFGAndPermLRT :: PermEnv -> SomeCFGAndPerm ext -> OpenTerm
someCFGAndPermLRT env (SomeCFGAndPerm _ _ _
                       (FunPerm ghosts args gouts ret perms_in perms_out)) =
  runNilTypeTransM env noChecks $
  translateClosed (appendCruCtx ghosts args) >>= \ctx_trans ->
  piLRTTransM "arg" ctx_trans $ \ectx ->
  inCtxTransM ectx $
  translate perms_in >>= \perms_trans ->
  piLRTTransM "perm" perms_trans $ \_ ->
  translateRetType (CruCtxCons gouts ret) perms_out >>= \ret_tp ->
  return $ ctorOpenTerm "Prelude.LRT_Ret" [ret_tp]

-- | Extract the 'FunPerm' of a 'SomeTypedCFG' as a permission on LLVM function
-- pointer values
someTypedCFGPtrPerm :: HasPtrWidth w => SomeTypedCFG LLVM ->
                       ValuePerm (LLVMPointerType w)
someTypedCFGPtrPerm (SomeTypedCFG _ _ cfg) = mkPtrFunPerm $ tpcfgFunPerm cfg

-- | Make a term of type @LetRecTypes@ from a list of @LetRecType@ terms
lrtsOpenTerm :: [OpenTerm] -> OpenTerm
lrtsOpenTerm lrts =
  let tp = dataTypeOpenTerm "Prelude.LetRecType" [] in
  foldr (\hd tl -> ctorOpenTerm "Prelude.Cons1" [tp, hd, tl])
  (ctorOpenTerm "Prelude.Nil1" [tp])
  lrts

-- | FIXME HERE NOW: docs
tcTranslateAddCFGs ::
  HasPtrWidth w => SharedContext -> ModuleName -> PermEnv -> ChecksFlag ->
  EndianForm -> DebugLevel -> [SomeCFGAndPerm LLVM] ->
  IO PermEnv
tcTranslateAddCFGs sc mod_name env checks endianness dlevel cfgs_and_perms =
  withKnownNat ?ptrWidth $
  do
    -- First, we type-check all the CFGs, mapping them to SomeTypedCFGs; this
    -- uses a temporary PermEnv where all the function symbols being
    -- type-checked are assigned their permissions, but no translation yet
    let tmp_env1 =
          permEnvAddGlobalSyms env $
          map someCFGAndPermGlobalEntry cfgs_and_perms
    let tcfgs =
          flip map cfgs_and_perms $ \(SomeCFGAndPerm gsym nm cfg fun_perm) ->
          SomeTypedCFG gsym nm $
          debugTraceTraceLvl dlevel ("Type-checking " ++ show gsym) $
          debugTrace verboseDebugLevel dlevel
          ("With type:\n" ++ permPrettyString emptyPPInfo fun_perm) $
          tcCFG ?ptrWidth tmp_env1 endianness dlevel fun_perm cfg

    -- Next, generate a list of all the LetRecTypes in all of the functions,
    -- along with a list of indices into that list of where the LRTs of each
    -- function are in that list
    let gen_lrts_ixs (i::Natural) (SomeTypedCFG _ _ tcfg : tcfgs') =
          let lrts = translateCFGLRTs env tcfg in
          (i, lrts) : gen_lrts_ixs (i + fromIntegral (length lrts)) tcfgs'
        gen_lrts_ixs _ [] = []
    let (fun_ixs, lrtss) = unzip $ gen_lrts_ixs 0 tcfgs
    let lrts = concat lrtss
    let frame = lrtsOpenTerm lrts
    let stack = singleFunStack frame

    -- Now, generate a SAW core tuple of all the bodies of mutually recursive
    -- functions for all the CFGs
    bodies_tm <-
      completeNormOpenTerm sc $
      runNilTypeTransM env checks $
      -- Create a temporary PermEnv that maps each Crucible symbol with a CFG in
      -- our list to a recursive call to the corresponding function in our new
      -- frame of recursive functions
      do tmp_env <-
           permEnvAddGlobalSyms env <$>
           zipWithM (\some_tpcfg@(SomeTypedCFG sym _ _) i ->
                      do let fun_p = someTypedCFGPtrPerm some_tpcfg
                         return $ PermEnvGlobalEntry sym fun_p (Left i))
           tcfgs fun_ixs
         bodiess <-
           local (\info -> info { ttiPermEnv = tmp_env }) $
           zipWithM (\i (SomeTypedCFG _ _ cfg) ->
                      translateCFGBodies stack i cfg) fun_ixs tcfgs
         return $ tupleOpenTerm $ concat bodiess

    -- Add a named definition for bodies_tm
    let bodies_ident =
          mkSafeIdent mod_name (someCFGAndPermToName (head cfgs_and_perms)
                                ++ "__bodies")
    bodies_tp <-
      completeNormOpenTerm sc $
      runNilTypeTransM env checks $
      applyNamedEventOpM "Prelude.FrameTuple" [funStackTerm stack, frame]
    scInsertDef sc mod_name bodies_ident bodies_tp bodies_tm
    let bodies = globalOpenTerm bodies_ident

    -- Finally, generate definitions for each of our functions as applications
    -- of multiFixS to our the bodies function defined above
    new_entries <-
      zipWithM
      (\(SomeTypedCFG sym nm cfg) i ->
        do tp <-
             completeNormOpenTerm sc $ piCFGArgs env cfg $ \_ ->
             let fun_perm = tpcfgFunPerm cfg in
             translateRetType (funPermRets fun_perm) (funPermOuts fun_perm) >>=
             specMTypeTransM emptyStackOpenTerm
           tm <- completeNormOpenTerm sc $
             translateCFG env emptyStackOpenTerm frame bodies i cfg
           let ident = mkSafeIdent mod_name nm
           scInsertDef sc mod_name ident tp tm
           let perm = mkPtrFunPerm $ tpcfgFunPerm cfg
           return $ PermEnvGlobalEntry sym perm (Right [globalOpenTerm ident]))
      tcfgs fun_ixs
    return $ permEnvAddGlobalSyms env new_entries


----------------------------------------------------------------------
-- * Top-level Entrypoints for Translating Other Things
----------------------------------------------------------------------

-- | Translate a 'FunPerm' to the SAW core type it represents
translateCompleteFunPerm :: SharedContext -> PermEnv ->
                            FunPerm ghosts args gouts ret -> IO Term
translateCompleteFunPerm sc env fun_perm =
  completeNormOpenTerm sc $
  runNilTypeTransM env noChecks (translate $ emptyMb fun_perm)

-- | Translate a 'TypeRepr' to the SAW core type it represents
translateCompleteType :: SharedContext -> PermEnv -> TypeRepr tp -> IO Term
translateCompleteType sc env typ_perm =
  completeNormOpenTerm sc $ typeTransType1 $
  runNilTypeTransM env noChecks $ translate $ emptyMb typ_perm

-- | Translate a 'TypeRepr' within the given context of type arguments to the
-- SAW core type it represents
translateCompleteTypeInCtx :: SharedContext -> PermEnv ->
                              CruCtx args -> Mb args (TypeRepr a) -> IO Term
translateCompleteTypeInCtx sc env args ret =
  completeNormOpenTerm sc $
  runNilTypeTransM env noChecks (piExprCtx args (typeTransType1 <$>
                                                 translate ret))

-- | Translate an input list of 'ValuePerms' and an output 'ValuePerm' to a SAW
-- core function type in a manner similar to 'translateCompleteFunPerm', except
-- that the returned function type is not in the @SpecM@ monad.
translateCompletePureFun :: SharedContext -> PermEnv
                         -> CruCtx ctx -- ^ Type arguments
                         -> Mb ctx (ValuePerms args) -- ^ Input perms
                         -> Mb ctx (ValuePerm ret) -- ^ Return type perm
                         -> IO Term
translateCompletePureFun sc env ctx args ret =
  completeNormOpenTerm sc $ runNilTypeTransM env noChecks $
  piExprCtx ctx $ piPermCtx args $ const $
  typeTransTupleType <$> translate ret
