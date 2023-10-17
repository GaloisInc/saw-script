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
{-# Language DeriveFunctor #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Move brackets to avoid $" #-}

module Verifier.SAW.Heapster.SAWTranslation where

import Prelude hiding (pi)

import Data.Maybe
import Numeric.Natural
import Data.List hiding (inits)
import Data.Text (pack)
import Data.Kind
import GHC.TypeLits
import Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import Data.Functor.Compose
import Data.Functor.Constant
import Control.Applicative
import Control.Lens hiding ((:>), Index, ix, op, getting)
import qualified Control.Monad as Monad
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

import Verifier.SAW.Utils (panic)
import Verifier.SAW.Name
import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor hiding (Constant)
import Verifier.SAW.SharedTerm hiding (Constant)

-- import Verifier.SAW.Heapster.GenMonad
import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.PatternMatchUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.Implication
import Verifier.SAW.Heapster.TypedCrucible
import Verifier.SAW.Heapster.NamedMb

import GHC.Stack


-- | FIXME: document and move to Hobbits
suffixMembers :: prx1 ctx1 -> RAssign prx2 ctx2 ->
                 RAssign (Member (ctx1 :++: ctx2)) ctx2
suffixMembers _ MNil = MNil
suffixMembers ctx1 (ctx2 :>: _) =
  RL.map Member_Step (suffixMembers ctx1 ctx2) :>: Member_Base

-- | Weaken a 'Member' proof by appending another context to the context it
-- proves membership in
weakenMemberR :: RAssign any ctx2 -> Member ctx1 a -> Member (ctx1 :++: ctx2) a
weakenMemberR MNil memb = memb
weakenMemberR (ctx1 :>: _) memb = Member_Step (weakenMemberR ctx1 memb)

-- | Test if a 'Member' of the append of two contexts is a 'Member' of the first
-- or the second context
appendMemberCase :: prx1 ctx1 -> RAssign prx2 ctx2 ->
                    Member (ctx1 :++: ctx2) a ->
                    Either (Member ctx1 a) (Member ctx2 a)
appendMemberCase _ MNil memb = Left memb
appendMemberCase _ (_ :>: _) Member_Base = Right Member_Base
appendMemberCase ctx1 (ctx2 :>: _) (Member_Step memb) =
  case appendMemberCase ctx1 ctx2 memb of
    Left memb1 -> Left memb1
    Right memb2 -> Right (Member_Step memb2)

-- | Get the length of a 'Member' proof, thereby converting a 'Member' of a
-- context into a deBruijn index
memberLength :: Member ctx a -> Natural
memberLength Member_Base = 0
memberLength (Member_Step memb) = 1 + memberLength memb


-- FIXME HERE NOWNOW: move these to OpenTerm.hs

-- | Build a bitvector type with the given length
bitvectorTypeOpenTerm :: OpenTerm -> OpenTerm
bitvectorTypeOpenTerm w =
  applyGlobalOpenTerm "Prelude.Vec" [w, globalOpenTerm "Prelude.Bool"]

-- | Build the SAW core type @BVVec n len d@
bvVecTypeOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm
bvVecTypeOpenTerm w_term len_term elem_tp =
  applyGlobalOpenTerm "Prelude.BVVec" [w_term, len_term, elem_tp]

-- | Build the type @FunIx T@ from a type description @T@
funIxTypeOpenTerm :: OpenTerm -> OpenTerm
funIxTypeOpenTerm t = applyGlobalOpenTerm "Prelude.FunIx" [t]

-- | Build the type @Either a b@ from types @a@ and @b@
eitherTypeOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
eitherTypeOpenTerm a b = dataTypeOpenTerm "Prelude.Either" [a,b]

-- | Build the type @Sigma a (\ (x:a) -> b)@ from variable name @x@, type @a@,
-- and type-level function @b@
sigmaTypeOpenTerm :: LocalName -> OpenTerm -> (OpenTerm -> OpenTerm) -> OpenTerm
sigmaTypeOpenTerm x tp f =
  dataTypeOpenTerm "Prelude.Sigma" [tp, lambdaOpenTerm x tp f]

-- | Build the type @Sigma a1 (\ (x1:a1) -> Sigma a2 (\ (x2:a2) -> ...))@
sigmaTypeOpenTermMulti :: LocalName -> [OpenTerm] -> ([OpenTerm] -> OpenTerm) ->
                          OpenTerm
sigmaTypeOpenTermMulti _ [] f = f []
sigmaTypeOpenTermMulti x (tp:tps) f =
  sigmaTypeOpenTerm x tp $ \ t ->
  sigmaTypeOpenTermMulti x tps $ \ts -> f (t:ts)

-- | Build the dependent pair @exists a (\ (x:a) -> b) x y@ whose type is given
-- by 'sigmaTypeOpenTerm'
sigmaOpenTerm :: LocalName -> OpenTerm -> (OpenTerm -> OpenTerm) ->
                 OpenTerm -> OpenTerm -> OpenTerm
sigmaOpenTerm x tp tp_f trm_l trm_r =
  ctorOpenTerm "Prelude.exists" [tp, lambdaOpenTerm x tp tp_f, trm_l, trm_r]

-- | Build the right-nested dependent pair @(x1, (x2, ...(xn, y)))@ whose type
-- is given by 'sigmaTypeOpenTermMulti'
sigmaOpenTermMulti :: LocalName -> [OpenTerm] -> ([OpenTerm] -> OpenTerm) ->
                      [OpenTerm] -> OpenTerm -> OpenTerm
sigmaOpenTermMulti _ [] _ [] trm = trm
sigmaOpenTermMulti x (tp:tps) tp_f (trm_l:trms_l) trm_r =
  sigmaOpenTerm x tp (\t -> sigmaTypeOpenTermMulti x tps (tp_f . (t:))) trm_l $
  sigmaOpenTermMulti x tps (tp_f . (trm_l:)) trms_l trm_r
sigmaOpenTermMulti _ _ _ _ _ =
  panic "sigmaOpenTermMulti" ["The number of types and arguments disagree"]

-- | Take a nested dependent pair (of the type returned by
-- 'sigmaTypeOpenTermMulti') and apply a function @f@ to all of its projections
sigmaElimOpenTermMulti :: LocalName -> [OpenTerm] -> ([OpenTerm] -> OpenTerm) ->
                          OpenTerm -> ([OpenTerm] -> OpenTerm) -> OpenTerm
sigmaElimOpenTermMulti _ [] _ t f_elim = f_elim [t]
sigmaElimOpenTermMulti x (tp:tps) tp_f sig f_elim =
  let b_fun = lambdaOpenTerm x tp (\t -> sigmaTypeOpenTermMulti x tps (tp_f . (t:)))
      proj1 = applyGlobalOpenTerm "Prelude.Sigma_proj1" [tp, b_fun, sig]
      proj2 = applyGlobalOpenTerm "Prelude.Sigma_proj2" [tp, b_fun, sig] in
  sigmaElimOpenTermMulti x tps (tp_f . (proj1:)) proj2 (f_elim . (proj1:))

-- | The kind description for the unit type
unitKindDesc :: OpenTerm
unitKindDesc = ctorOpenTerm "Prelude.Kind_Expr" [ctorOpenTerm
                                                 "Prelude.Kind_unit" []]

-- | The @ExprKind@ for the bitvector type with width @w@
bvExprKind :: Natural -> OpenTerm
bvExprKind w = ctorOpenTerm "Prelude.Kind_bv" [natOpenTerm w]

-- | The type @TpDesc@ of type descriptions
tpDescTypeOpenTerm :: OpenTerm
tpDescTypeOpenTerm = dataTypeOpenTerm "Prelude.TpDesc" []

-- | The type description for the unit type
unitTpDesc :: OpenTerm
unitTpDesc = ctorOpenTerm "Prelude.Tp_Kind" [unitKindDesc]

-- | The kind description for the Boolean type
boolKindDesc :: OpenTerm
boolKindDesc = ctorOpenTerm "Prelude.Kind_Expr" [ctorOpenTerm
                                                 "Prelude.Kind_bool" []]

-- | The kind description for the Nat type
natKindDesc :: OpenTerm
natKindDesc = ctorOpenTerm "Prelude.Kind_Expr" [ctorOpenTerm
                                                "Prelude.Kind_nat" []]

-- | The kind description for the type @bitvector w@
bvKindDesc :: Natural -> OpenTerm
bvKindDesc w = ctorOpenTerm "Prelude.Kind_Expr" [bvExprKind w]

-- | The kind description for the type of type descriptions
tpKindDesc :: OpenTerm
tpKindDesc = ctorOpenTerm "Prelude.Kind_Tp" []

-- | Build a pair type description from two type descriptions
pairTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
pairTpDesc d1 d2 = ctorOpenTerm "Prelude.Tp_Pair" [d1,d2]

-- | Build a tuple type description from a list of type descriptions
tupleTpDesc :: [OpenTerm] -> OpenTerm
tupleTpDesc [] = unitTpDesc
tupleTpDesc [d] = d
tupleTpDesc (d : ds) = pairTpDesc d (tupleTpDesc ds)

-- | Build a sum type description from two type descriptions
sumTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
sumTpDesc d1 d2 = ctorOpenTerm "Prelude.Tp_Sum" [d1,d2]

-- | Build a type description for the type @BVVec n len d@
bvVecTpDesc :: OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm
bvVecTpDesc w_term len_term elem_d =
  applyGlobalOpenTerm "Prelude.Tp_BVVec" [elem_d, w_term, len_term]

-- | Build a type expression of type @TpExpr EK@ of kind description @EK@ from a
-- type-level value of type @exprKindElem EK@
constTpExpr :: OpenTerm -> OpenTerm -> OpenTerm
constTpExpr k_d v = ctorOpenTerm "Prelude.TpExpr_Const" [k_d, v]

-- | Build a type description expression from a bitvector value of a given width
bvConstTpExpr :: Natural -> OpenTerm -> OpenTerm
bvConstTpExpr w bv = constTpExpr (bvExprKind w) bv

-- | Build a type expression for the bitvector sum of a list of type
-- expressions, all of the given width
bvSumTpExprs :: Natural -> [OpenTerm] -> OpenTerm
bvSumTpExprs w [] = bvConstTpExpr w (natOpenTerm 0)
bvSumTpExprs _ [bv] = bv
bvSumTpExprs w (bv:bvs) =
  ctorOpenTerm "Prelude.TpExpr_BinOp"
  [bvExprKind w, bvExprKind w, bvExprKind w,
   ctorOpenTerm "Prelude.BinOp_AddBV" [natOpenTerm w], bv, bvSumTpExprs w bvs]

-- | Build a type expression for the bitvector product of two type expressions
bvMulTpExpr :: Natural -> OpenTerm -> OpenTerm -> OpenTerm
bvMulTpExpr w bv1 bv2 =
  ctorOpenTerm "Prelude.TpExpr_BinOp"
  [bvExprKind w, bvExprKind w, bvExprKind w,
   ctorOpenTerm "Prelude.BinOp_MulBV" [natOpenTerm w], bv1, bv2]

-- | Build a type description for a sigma type from a kind description for the
-- first element and a type description with an additional free variable for the
-- second
sigmaTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
sigmaTpDesc k d = ctorOpenTerm "Prelude.Tp_Sigma" [k,d]

-- | Build a type description for 0 or more nested sigma types over a list of
-- kind descriptions
sigmaTpDescMulti :: [OpenTerm] -> OpenTerm -> OpenTerm
sigmaTpDescMulti [] d = d
sigmaTpDescMulti (k:ks) d = sigmaTpDesc k $ sigmaTpDescMulti ks d

-- | Build the type description for a function index of arrow type
arrowTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
arrowTpDesc d_in d_out = ctorOpenTerm "Prelude.Tp_Arr" [d_in, d_out]

-- | Build the type description for a function index of multi-arity arrow type
arrowTpDescMulti :: [OpenTerm] -> OpenTerm -> OpenTerm
arrowTpDescMulti tps_in tp_out = foldr arrowTpDesc tp_out tps_in

-- | Build the type description for a pi-abstraction over a kind description
piTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
piTpDesc kd tpd = ctorOpenTerm "Prelude.Tp_Pi" [kd, tpd]

-- | Build the type description for a multi-arity pi-abstraction over a sequence
-- of kind descriptions, i.e., SAW core terms of type @KindDesc@
piTpDescMulti :: [OpenTerm] -> OpenTerm -> OpenTerm
piTpDescMulti ks tp = foldr piTpDesc tp ks

-- | Build a type description for a free deBruijn index
varTpDesc :: OpenTerm -> Natural -> OpenTerm
varTpDesc d ix = ctorOpenTerm "Prelude.Tp_Var" [d, natOpenTerm ix]

-- | Build a type-level expression with a given @ExprKind@ for a free variable
varTpExpr :: OpenTerm -> Natural -> OpenTerm
varTpExpr ek ix = ctorOpenTerm "Prelude.TpExpr_Var" [ek, natOpenTerm ix]

-- | Build the type description @Tp_Subst T K e@ that represents an explicit
-- substitution of expression @e@ of kind @K@ into type description @T@
substTpDesc :: OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm
substTpDesc d k_d e = applyGlobalOpenTerm "Prelude.Tp_Subst" [d,k_d,e]

-- | Build the type description that performs 0 or more explicit substitutions
substTpDescMulti :: OpenTerm -> [OpenTerm] -> [OpenTerm] -> OpenTerm
substTpDescMulti d [] [] = d
substTpDescMulti d (k_d:k_ds) (e:es) =
  substTpDescMulti (substTpDesc d k_d e) k_ds es
substTpDescMulti _ _ _ =
  panic "substTpDescMulti" ["Mismatched number of kinds versus expressions"]

-- | Build the type description that performs 0 or more explicit substitutions
-- from a type description given by an identifier
substIdTpDescMulti :: Ident -> [OpenTerm] -> [OpenTerm] -> OpenTerm
substIdTpDescMulti i = substTpDescMulti (globalOpenTerm i)

-- | Map from type description @T@ to the type @T@ describes
tpElemTypeOpenTerm :: OpenTerm -> OpenTerm
tpElemTypeOpenTerm d =
  applyGlobalOpenTerm "Prelude.tpElem" [d]

-- | Build a @SpecM@ computation that returns a value
retSOpenTerm :: EventType -> OpenTerm -> OpenTerm -> OpenTerm
retSOpenTerm ev tp x =
  applyGlobalOpenTerm "Prelude.retS" [evTypeTerm ev, tp, x]

-- | Build a @SpecM@ computation using a bind
bindSOpenTerm :: EventType -> OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm ->
                 OpenTerm
bindSOpenTerm ev a b m f =
  applyGlobalOpenTerm "Prelude.bindS" [evTypeTerm ev, a, b, m, f]

-- | Build a @SpecM@ error computation with the given error message
errorSOpenTerm :: EventType -> OpenTerm -> String -> OpenTerm
errorSOpenTerm ev ret_tp msg =
  applyGlobalOpenTerm "Prelude.errorS"
  [evTypeTerm ev, ret_tp, stringLitOpenTerm (pack msg)]

-- | Build a @SpecM@ computation that calls a function index
callSOpenTerm :: EventType -> OpenTerm -> OpenTerm -> [OpenTerm] -> OpenTerm
callSOpenTerm ev d ix args =
  applyGlobalOpenTerm "Prelude.CallS" ([evTypeTerm ev, d, ix] ++ args)


----------------------------------------------------------------------
-- * Type Translations
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

-- | Apply the 'typeTransFun' of a 'TypeTrans' to a list of SAW core terms
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
mkTypeTrans0 tr = TypeTrans [] $ \case
  [] -> tr
  _ -> error "mkTypeTrans0: incorrect number of terms"

-- | Build a 'TypeTrans' represented by 1 SAW type
mkTypeTrans1 :: OpenTerm -> (OpenTerm -> tr) -> TypeTrans tr
mkTypeTrans1 tp f = TypeTrans [tp] $ \case
  [t] -> f t
  _ -> error "mkTypeTrans1: incorrect number of terms"

-- | Build a 'TypeTrans' for an 'OpenTerm' of a given type
openTermTypeTrans :: OpenTerm -> TypeTrans OpenTerm
openTermTypeTrans tp = mkTypeTrans1 tp id

-- | Build a 'TypeTrans' for a list of 'OpenTerm's of 0 or more types
openTermsTypeTrans :: [OpenTerm] -> TypeTrans [OpenTerm]
openTermsTypeTrans tps = TypeTrans tps id

-- | Extract out the single SAW type associated with a 'TypeTrans', or the unit
-- type if it has 0 SAW types. It is an error if it has 2 or more SAW types.
typeTransType1 :: HasCallStack => TypeTrans tr -> OpenTerm
typeTransType1 (TypeTrans [] _) = unitTypeOpenTerm
typeTransType1 (TypeTrans [tp] _) = tp
typeTransType1 _ =
  panic "typeTransType1" ["found multiple types where at most 1 was expected"]

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
projTupleOfTypes [] _ _ =
  panic "projTupleOfTypes" ["projection of empty tuple!"]
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
  (\case
      [t] ->
        typeTransF ttrans $ map (\i -> projTupleOfTypes tps i t) $
        take (length $ typeTransTypes ttrans) [0..]
      _ -> panic "tupleTypeTrans" ["incorrect number of terms"])

{-
-- | Convert a 'TypeTrans' over 0 or more types to one over 1 type of the form
-- @#(tp1, #(tp2, ... #(tpn, #()) ...))@. This is "strict" in the sense that
-- even a single type is tupled.
strictTupleTypeTrans :: TypeTrans tr -> TypeTrans tr
strictTupleTypeTrans ttrans =
  TypeTrans [tupleTypeOpenTerm $ typeTransTypes ttrans]
  (\case
      [t] ->
        typeTransF ttrans $ map (\i -> projTupleOpenTerm i t) $
        take (length $ typeTransTypes ttrans) [0..]
      _ -> error "strictTupleTypeTrans: incorrect number of terms")
-}

-- | Build a type translation for a list of translations
listTypeTrans :: [TypeTrans tr] -> TypeTrans [tr]
listTypeTrans [] = pure []
listTypeTrans (trans:transs) = liftA2 (:) trans $ listTypeTrans transs


----------------------------------------------------------------------
-- * Expression Translations
----------------------------------------------------------------------

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

  -- | The translation of a shape is a list of 0 or more type descriptions along
  -- with the translations to the types they represent, in that order
  ETrans_Shape :: [OpenTerm] -> [OpenTerm] -> ExprTrans (LLVMShapeType w)

  -- | The translation of a permission is a list of 0 or more type descriptions
  -- along with the translations to the types they represent, in that order
  ETrans_Perm :: [OpenTerm] -> [OpenTerm] -> ExprTrans (ValuePermType a)

  -- | The translation for every other expression type is just a SAW term. Note
  -- that this construct should not be used for the types handled above.
  ETrans_Term :: TypeRepr a -> OpenTerm -> ExprTrans a

-- | A context mapping bound names to their type-level SAW translations
type ExprTransCtx = RAssign ExprTrans


-- | Destruct an 'ExprTrans' of shape type to a list of type descriptions and
-- the types they represent, in that order
unETransShape :: ExprTrans (LLVMShapeType w) -> ([OpenTerm], [OpenTerm])
unETransShape (ETrans_Shape ds tps) = (ds, tps)
unETransShape (ETrans_Term _ _) =
  panic "unETransShape" ["Incorrect translation of a shape expression"]

-- | Destruct an 'ExprTrans' of permission type to a list of type descriptions
-- and the types they represent, in that order
unETransPerm :: ExprTrans (ValuePermType a) -> ([OpenTerm], [OpenTerm])
unETransPerm (ETrans_Perm ds tps) = (ds, tps)
unETransPerm (ETrans_Term _ _) =
  panic "unETransPerm" ["Incorrect translation of a shape expression"]


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

{-
-- | Build a tuple of the terms contained in a translation. This is "strict" in
-- that it always makes a tuple, even for a single type, unlike
-- 'transTupleTerm'.  If @ttrans@ is a 'TypeTrans' describing the SAW types
-- associated with a @tr@ translation, then this function returns an element of
-- the type @'strictTupleTypeTrans' ttrans@.
strictTransTupleTerm :: IsTermTrans tr => tr -> OpenTerm
strictTransTupleTerm tr = tupleOpenTerm $ transTerms tr
-}

-- | Like 'transTupleTerm' but raise an error if there are more than 1 terms
transTerm1 :: HasCallStack => IsTermTrans tr => tr -> OpenTerm
transTerm1 (transTerms -> []) = unitOpenTerm
transTerm1 (transTerms -> [t]) = t
transTerm1 tr = panic "transTerm1" ["Expected at most one term, but found "
                                    ++ show (length $ transTerms tr)]

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
  transTerms (ETrans_Shape ds _) = [tupleTpDesc ds]
  transTerms (ETrans_Perm ds _) = [tupleTpDesc ds]
  transTerms (ETrans_Term _ t) = [t]

instance IsTermTrans (ExprTransCtx ctx) where
  transTerms MNil = []
  transTerms (ctx :>: etrans) = transTerms ctx ++ transTerms etrans


-- | Map a context of expression translations to a list of 'OpenTerm's
exprCtxToTerms :: ExprTransCtx tps -> [OpenTerm]
exprCtxToTerms = concat . RL.mapToList transTerms

-- | Map an 'ExprTrans' to its type translation
exprTransType :: ExprTrans tp -> TypeTrans (ExprTrans tp)
exprTransType ETrans_LLVM = mkTypeTrans0 ETrans_LLVM
exprTransType ETrans_LLVMBlock = mkTypeTrans0 ETrans_LLVMBlock
exprTransType ETrans_LLVMFrame = mkTypeTrans0 ETrans_LLVMFrame
exprTransType ETrans_Lifetime = mkTypeTrans0  ETrans_Lifetime
exprTransType ETrans_RWModality = mkTypeTrans0 ETrans_RWModality
exprTransType (ETrans_Struct etranss) = ETrans_Struct <$> exprCtxType etranss
exprTransType ETrans_Fun = mkTypeTrans0 ETrans_Fun
exprTransType ETrans_Unit = mkTypeTrans0 ETrans_Unit
exprTransType ETrans_AnyVector = mkTypeTrans0 ETrans_AnyVector
exprTransType (ETrans_Shape _ _) =
  mkTypeTrans1 tpDescTypeOpenTerm (\d ->
                                    ETrans_Shape [d] [tpElemTypeOpenTerm d])
exprTransType (ETrans_Perm _ _) =
  mkTypeTrans1 tpDescTypeOpenTerm (\d -> ETrans_Perm [d] [tpElemTypeOpenTerm d])
exprTransType (ETrans_Term tp t) =
  mkTypeTrans1 (openTermType t) (ETrans_Term tp)

-- | Map a context of expression translation to a list of the SAW core types of
-- all the terms it contains
exprCtxType :: ExprTransCtx ctx -> TypeTrans (ExprTransCtx ctx)
exprCtxType MNil = mkTypeTrans0 MNil
exprCtxType (ectx :>: e) = (:>:) <$> exprCtxType ectx <*> exprTransType e


-- | Convert an 'ExprTrans' to a list of SAW core terms of type @kindExpr K@,
-- one for each kind description @K@ returned by 'translateType' for the type of
-- the 'ExprTrans'
exprTransDescs :: ExprTrans a -> [OpenTerm]
exprTransDescs ETrans_LLVM = []
exprTransDescs ETrans_LLVMBlock = []
exprTransDescs ETrans_LLVMFrame = []
exprTransDescs ETrans_Lifetime = []
exprTransDescs ETrans_RWModality = []
exprTransDescs (ETrans_Struct etranss) =
  concat $ RL.mapToList exprTransDescs etranss
exprTransDescs ETrans_Fun = []
exprTransDescs ETrans_Unit = []
exprTransDescs ETrans_AnyVector = []
exprTransDescs (ETrans_Shape ds _) = ds
exprTransDescs (ETrans_Perm ds _) = ds
exprTransDescs (ETrans_Term tp t) =
  case translateKindDescs tp of
    [d] -> [ctorOpenTerm "Prelude.TpExpr_Const" [d, t]]
    _ -> panic "exprTransDescs" ["ETrans_Term type has incorrect number of kinds"]

-- | A "proof" that @ctx2@ is an extension of @ctx1@, i.e., that @ctx2@ equals
-- @ctx1 :++: ctx3@ for some @ctx3@
data CtxExt ctx1 ctx2 where
  CtxExt :: RAssign Proxy ctx3 -> CtxExt ctx1 (ctx1 :++: ctx3)

-- | Build a context extension proof to an appended context
mkCtxExt :: RAssign prx ctx3 -> CtxExt ctx1 (ctx1 :++: ctx3)
mkCtxExt prxs = CtxExt $ RL.map (const Proxy) prxs

-- | Reflexivity of 'CtxExt'
reflCtxExt :: CtxExt ctx ctx
reflCtxExt = CtxExt MNil

-- | Transitively combine two context extensions
transCtxExt :: CtxExt ctx1 ctx2 -> CtxExt ctx2 ctx3 ->
               CtxExt ctx1 ctx3
transCtxExt ((CtxExt ectx2') :: CtxExt ctx1 ctx2) (CtxExt ectx3')
  | Refl <- RL.appendAssoc (Proxy :: Proxy ctx1) ectx2' ectx3'
  = CtxExt (RL.append ectx2' ectx3')

extCtxExt :: Proxy ctx1 -> RAssign Proxy ctx2 -> CtxExt (ctx1 :++: ctx2) ctx3 ->
             CtxExt ctx1 ctx3
extCtxExt ctx1 ctx2 (CtxExt ctx4)
  | Refl <- RL.appendAssoc ctx1 ctx2 ctx4
  = CtxExt (RL.append ctx2 ctx4)

ctxExtToExprExt :: CtxExt ctx1 ctx2 -> ExprTransCtx ctx2 ->
                   ExprCtxExt ctx1 ctx2
ctxExtToExprExt ((CtxExt ctx3) :: CtxExt ctx1 ctx2) ectx =
  ExprCtxExt $ snd $ RL.split (Proxy :: Proxy ctx1) ctx3 ectx


-- | An extension of expression context @ctx1@ to @ctx2@, which is just an
-- 'ExprTransCtx' for the suffix @ctx3@ such that @ctx1:++:ctx3 = ctx2@
data ExprCtxExt ctx1 ctx2 where
  ExprCtxExt :: ExprTransCtx ctx3 -> ExprCtxExt ctx1 (ctx1 :++: ctx3)

-- | The reflexive context extension, proving that any context extends itself
reflExprCtxExt :: ExprCtxExt ctx ctx
reflExprCtxExt = ExprCtxExt MNil

-- | Transitively combine two context extensions
transExprCtxExt :: ExprCtxExt ctx1 ctx2 -> ExprCtxExt ctx2 ctx3 ->
                   ExprCtxExt ctx1 ctx3
transExprCtxExt ((ExprCtxExt ectx2')
                 :: ExprCtxExt ctx1 ctx2) (ExprCtxExt ectx3')
  | Refl <- RL.appendAssoc (Proxy :: Proxy ctx1) ectx2' ectx3'
  = ExprCtxExt (RL.append ectx2' ectx3')

-- | Use any 'RAssign' object to extend a multi-binding
extMbAny :: RAssign any ctx2 -> Mb ctx1 a -> Mb (ctx1 :++: ctx2) a
extMbAny ctx2 = extMbMulti (RL.map (const Proxy) ctx2)

-- | Use a 'CtxExt' to extend a multi-binding
extMbExt :: ExprCtxExt ctx1 ctx2 -> Mb ctx1 a -> Mb ctx2 a
extMbExt (ExprCtxExt ctx2) = extMbAny ctx2

{- FIXME: keeping this in case we need it later
-- | Un-extend the left-hand context of an expression context extension
extExprCtxExt :: ExprTrans tp -> ExprCtxExt (ctx1 :> tp) ctx2 ->
                 ExprCtxExt ctx1 ctx2
extExprCtxExt etrans ((ExprCtxExt ctx3) :: ExprCtxExt (ctx1 :> tp) ctx2) =
  case RL.appendRNilConsEq (Proxy :: Proxy ctx1) etrans ctx3 of
    Refl -> ExprCtxExt (RL.append (MNil :>: etrans) ctx3)
-}

-- | Use an 'ExprCtxExt' to extend an 'ExprTransCtx'
extExprTransCtx :: ExprCtxExt ctx1 ctx2 -> ExprTransCtx ctx1 ->
                   ExprTransCtx ctx2
extExprTransCtx (ExprCtxExt ectx2) ectx1 = RL.append ectx1 ectx2

-- | Use an 'ExprCtxExt' to "un-extend" an 'ExprTransCtx'
unextExprTransCtx :: ExprCtxExt ctx1 ctx2 -> ExprTransCtx ctx2 ->
                     ExprTransCtx ctx1
unextExprTransCtx ((ExprCtxExt ectx3) :: ExprCtxExt ctx1 ctx2) ectx2 =
  fst $ RL.split (Proxy :: Proxy ctx1) ectx3 ectx2


----------------------------------------------------------------------
-- * Translation Monads
----------------------------------------------------------------------

-- | Class for valid translation info types, which must contain at least a
-- context of expression translations
class TransInfo info where
  infoCtx :: info ctx -> ExprTransCtx ctx
  infoEnv :: info ctx -> PermEnv
  infoChecksFlag :: info ctx -> ChecksFlag
  extTransInfo :: ExprTrans tp -> info ctx -> info (ctx :> tp)

-- | Get the event type stored in a 'TransInfo'
infoEvType :: TransInfo info => info ctx -> EventType
infoEvType = permEnvEventType . infoEnv

-- | A "translation monad" is a 'Reader' monad with some info type that is
-- parameterized by a translation context
newtype TransM info (ctx :: RList CrucibleType) a =
  TransM { unTransM :: Reader (info ctx) a }
  deriving (Functor, Applicative, Monad, OpenTermLike)

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

-- | Build a @sawLet@-binding in a translation monad that binds a pure variable
sawLetTransM :: String -> OpenTerm -> OpenTerm -> OpenTerm ->
                (OpenTerm -> TransM info ctx OpenTerm) ->
                TransM info ctx OpenTerm
sawLetTransM x tp tp_ret rhs body_m =
  do r <- ask
     return $
       sawLetOpenTerm (pack x) tp tp_ret rhs $ \x' ->
       runTransM (body_m x') r

-- | Build 0 or more sawLet-bindings in a translation monad, using the same
-- variable name
sawLetTransMultiM :: String -> [OpenTerm] -> OpenTerm -> [OpenTerm] ->
                     ([OpenTerm] -> TransM info ctx OpenTerm) ->
                     TransM info ctx OpenTerm
sawLetTransMultiM _ [] _ [] f = f []
sawLetTransMultiM x (tp:tps) ret_tp (rhs:rhss) f =
  sawLetTransM x tp ret_tp rhs $ \var_tm ->
  sawLetTransMultiM x tps ret_tp rhss (\var_tms -> f (var_tm:var_tms))
sawLetTransMultiM _ _ _ _ _ =
  panic "sawLetTransMultiM" ["numbers of types and right-hand sides disagree"]

-- | Run a translation computation in an extended context, where we sawLet-bind any
-- term in the supplied expression translation
inExtTransSAWLetBindM :: TransInfo info => TypeTrans (ExprTrans tp) ->
                         OpenTerm -> ExprTrans tp ->
                         TransM info (ctx :> tp) OpenTerm ->
                         TransM info ctx OpenTerm
inExtTransSAWLetBindM tp_trans tp_ret etrans m =
  sawLetTransMultiM "z" (map openTermLike $
                         typeTransTypes tp_trans) tp_ret (transTerms etrans) $
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
applyMultiTransM :: TransM info ctx OpenTerm ->
                    [TransM info ctx OpenTerm] ->
                    TransM info ctx OpenTerm
applyMultiTransM m ms = foldl applyTransM m ms

-- | Apply an identifier to the results of multiple translations
applyGlobalTransM :: Ident -> [TransM info ctx OpenTerm] ->
                     TransM info ctx OpenTerm
applyGlobalTransM ident ms = applyGlobalOpenTerm ident <$> sequence ms

-- | Build a nested lambda-abstraction
--
-- > \x1:tp1 -> ... -> \xn:tpn -> body
--
-- over the types in a 'TypeTrans', using the 'String' as a variable name prefix
-- for the @xi@ variables
lambdaTrans :: String -> TypeTrans tr -> (tr -> OpenTerm) -> OpenTerm
lambdaTrans x (TypeTrans tps tr_f) body_f =
  lambdaOpenTermMulti
  (zipWith (\i tp -> (pack (x ++ show (i :: Integer)), tp)) [0..] tps)
  (body_f . tr_f)

-- | Build a nested lambda-abstraction
--
-- > \x1:tp1 -> ... -> \xn:tpn -> body
--
-- over the types in a 'TypeTrans' inside a translation monad, using the
-- 'String' as a variable name prefix for the @xi@ variables
lambdaTransM :: String -> TypeTrans tr -> (tr -> TransM info ctx OpenTerm) ->
                TransM info ctx OpenTerm
lambdaTransM x tp body_f =
  ask >>= \info -> return (lambdaTrans x tp (flip runTransM info . body_f))

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
          (zipWith (\i tp -> (pack (x ++ show (i :: Integer)), tp))
           [0..] (typeTransTypes tps))
          (\ts -> runTransM (body_f $ typeTransF tps ts) info))

{-
-- | Build a pi-abstraction inside the 'TransM' monad
piOpenTermTransM :: String -> OpenTerm ->
                    (OpenTerm -> TransM info ctx OpenTerm) ->
                    TransM info ctx OpenTerm
piOpenTermTransM x tp body_f =
  ask >>= \info ->
  return (piOpenTerm (pack x) tp $ \t -> runTransM (body_f t) info)
-}

-- | Build a let-binding in a translation monad
letTransM :: String -> OpenTerm -> TransM info ctx OpenTerm ->
             (OpenTerm -> TransM info ctx OpenTerm) ->
             TransM info ctx OpenTerm
letTransM x tp rhs_m body_m =
  do r <- ask
     return $
       letOpenTerm (pack x) tp (runTransM rhs_m r) $ \x' ->
       runTransM (body_m x') r

-- | Build a bitvector type in a translation monad
bitvectorTransM :: TransM info ctx OpenTerm -> TransM info ctx OpenTerm
bitvectorTransM m = bitvectorTypeOpenTerm <$> m

-- | Build an @Either@ type in SAW from the 'typeTransTupleType's of the left
-- and right types
eitherTypeTrans :: TypeTrans trL -> TypeTrans trR -> OpenTerm
eitherTypeTrans tp_l tp_r =
  eitherTypeOpenTerm (typeTransTupleType tp_l) (typeTransTupleType tp_r)

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
     return $ applyGlobalOpenTerm "Prelude.either"
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
  return (applyGlobalOpenTerm "Prelude.eithers"
          [typeTransTupleType tp_ret, elims_trans, eith])


-- | Build the right-nested dependent pair type whose sequence of left-hand
-- projections have the types of the supplied 'TypeTrans' and whose right-hand
-- projection is the 'typeTransTupleType' of the supplied monadic function
sigmaTypeTransM :: LocalName -> TypeTrans trL ->
                   (trL -> TransM info ctx (TypeTrans trR)) ->
                   TransM info ctx OpenTerm
sigmaTypeTransM x tptrans tp_f =
  ask >>= \info ->
  return (sigmaTypeOpenTermMulti x (typeTransTypes tptrans)
          (typeTransTupleType . flip runTransM info . tp_f . typeTransF tptrans))

-- | Like 'sigmaTypeTransM', but translates 'exists x.eq(y)' into the tuple of
-- types of 'x', omitting the right-hand projection type
sigmaTypePermTransM :: TransInfo info => LocalName ->
                       TypeTrans (ExprTrans trL) ->
                       Mb (ctx :> trL) (ValuePerm trR) ->
                       TransM info ctx OpenTerm
sigmaTypePermTransM x ttrans mb_p = case mbMatch mb_p of
  [nuMP| ValPerm_Eq _ |] -> return $ typeTransTupleType ttrans
  _ ->
    sigmaTypeTransM x ttrans $ \etrans ->
    inExtTransM etrans (translate mb_p)

-- | Build a nested dependent pair of the type returned by 'sigmaTypeTransM'.
-- Note that the 'TypeTrans' returned by the type-level function will in general
-- be in a larger context than that of the right-hand projection argument, so we
-- allow the representation types to be different to accommodate for this.
sigmaTransM :: (IsTermTrans trL, IsTermTrans trR2) =>
               LocalName -> TypeTrans trL ->
               (trL -> TransM info ctx (TypeTrans trR1)) ->
               trL -> TransM info ctx trR2 ->
               TransM info ctx OpenTerm
sigmaTransM _ (typeTransTypes -> []) _ _ rhs_m = transTupleTerm <$> rhs_m
sigmaTransM x tp_l tp_r lhs rhs_m =
  ask >>= \info ->
  return (sigmaOpenTermMulti x (typeTransTypes tp_l)
          (typeTransTupleType . flip runTransM info . tp_r . typeTransF tp_l)
          (transTerms lhs)
          (transTupleTerm $ runTransM rhs_m info))

-- | Like `sigmaTransM`, but translates `exists x.eq(y)` into just `x`
sigmaPermTransM :: (TransInfo info, IsTermTrans trR2) =>
                   LocalName -> TypeTrans (ExprTrans trL) ->
                   Mb (ctx :> trL) (ValuePerm trR1) ->
                   ExprTrans trL -> TransM info ctx trR2 ->
                   TransM info ctx OpenTerm
sigmaPermTransM x ttrans mb_p etrans rhs_m = case mbMatch mb_p of
  [nuMP| ValPerm_Eq _ |] -> return $ transTupleTerm etrans
  _ -> sigmaTransM x ttrans (flip inExtTransM $ translate mb_p) etrans rhs_m


-- | Eliminate a dependent pair of the type returned by 'sigmaTypeTransM'
sigmaElimTransM :: (IsTermTrans trL, IsTermTrans trR) =>
                   LocalName -> TypeTrans trL ->
                   (trL -> TransM info ctx (TypeTrans trR)) ->
                   TransM info ctx (TypeTrans trRet) ->
                   (trL -> trR -> TransM info ctx OpenTerm) ->
                   OpenTerm ->
                   TransM info ctx OpenTerm
sigmaElimTransM _ tp_l@(typeTransTypes -> []) tp_r _ f sigma =
  do let proj_l = typeTransF tp_l []
     proj_r <- flip (typeTransF . tupleTypeTrans) [sigma] <$> tp_r proj_l
     f proj_l proj_r
sigmaElimTransM x tp_l tp_r_mF _tp_ret_m f sigma =
  do info <- ask
     let tp_r_f = flip runTransM info . tp_r_mF . typeTransF tp_l
     return $
       sigmaElimOpenTermMulti x (typeTransTypes tp_l)
       (typeTransTupleType . tp_r_f)
       sigma
       (\ts -> let (ts_l, ts_r) = splitAt (length (typeTransTypes tp_l)) ts
                   trL = typeTransF tp_l ts_l
                   tp_r = tp_r_f ts_l in
               flip runTransM info $ f trL (typeTransF tp_r ts_r))


-- | Like `sigmaElimTransM`, but translates `exists x.eq(y)` into just `x`
sigmaElimPermTransM :: (TransInfo info) =>
                       LocalName -> TypeTrans (ExprTrans trL) ->
                       Mb (ctx :> trL) (ValuePerm trR) ->
                       TransM info ctx (TypeTrans trRet) ->
                       (ExprTrans trL -> PermTrans (ctx :> trL) trR ->
                                         TransM info ctx OpenTerm) ->
                       OpenTerm ->
                       TransM info ctx OpenTerm
sigmaElimPermTransM x tp_l mb_p tp_ret_m f sigma = case mbMatch mb_p of
  [nuMP| ValPerm_Eq e |] ->
    f (typeTransF (tupleTypeTrans tp_l) [sigma]) (PTrans_Eq e)
  _ ->
    sigmaElimTransM x tp_l (flip inExtTransM $ translate mb_p) tp_ret_m f sigma

-- | Apply an 'OpenTerm' to the current event type @E@ and to a
-- list of other arguments
applyEventOpM :: TransInfo info => OpenTerm -> [OpenTerm] ->
                 TransM info ctx OpenTerm
applyEventOpM f args =
  do evType <- evTypeTerm <$> infoEvType <$> ask
     return $ applyOpenTermMulti f (evType : args)

-- | Apply a named operator to the current event type @E@ and to a list of other
-- arguments
applyNamedEventOpM :: TransInfo info => Ident -> [OpenTerm] ->
                      TransM info ctx OpenTerm
applyNamedEventOpM f args = applyEventOpM (globalOpenTerm f) args

-- | Generate the type @SpecM E evRetType stack A@ using the current event type
-- and the supplied @stack@ and type @A@
specMTypeTransM :: TransInfo info => OpenTerm -> OpenTerm ->
                   TransM info ctx OpenTerm
specMTypeTransM stack tp = applyNamedEventOpM "Prelude.SpecM" [stack,tp]


-- | The class for translating to SAW
class Translate info ctx a tr | ctx a -> tr where
  translate :: Mb ctx a -> TransM info ctx tr

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

-- | Build an empty 'TypeTransInfo' from a 'PermEnv'
emptyTypeTransInfo :: PermEnv -> ChecksFlag -> TypeTransInfo RNil
emptyTypeTransInfo = TypeTransInfo MNil

instance TransInfo TypeTransInfo where
  infoCtx (TypeTransInfo ctx _ _) = ctx
  infoEnv (TypeTransInfo _ env _) = env
  infoChecksFlag (TypeTransInfo _ _ cflag) = cflag
  extTransInfo etrans (TypeTransInfo ctx env checks) =
    TypeTransInfo (ctx :>: etrans) env checks

-- | The translation monad specific to translating types and pure expressions
type TypeTransM = TransM TypeTransInfo

-- | Any 'TransM' can run a 'TypeTransM'
tpTransM :: TransInfo info => TypeTransM ctx a -> TransM info ctx a
tpTransM =
  withInfoM $ \info ->
  TypeTransInfo (infoCtx info) (infoEnv info) (infoChecksFlag info)

-- | Run a 'TypeTransM' computation in the empty translation context
runNilTypeTransM :: PermEnv -> ChecksFlag -> TypeTransM RNil a -> a
runNilTypeTransM env checks m = runTransM m (emptyTypeTransInfo env checks)

-- | Convert a 'TypeTransM' computation into a pure function that takes in an
-- 'ExprTransCtx'
ctxFunTypeTransM :: TypeTransM ctx a -> TypeTransM ctx' (ExprTransCtx ctx -> a)
ctxFunTypeTransM m =
  do TypeTransInfo {..} <- ask
     return $ \ectx -> runTransM m $ TypeTransInfo { ttiExprCtx = ectx, .. }

-- | Run a translation computation in an empty expression translation context
inEmptyCtxTransM :: TypeTransM RNil a -> TypeTransM ctx a
inEmptyCtxTransM =
  withInfoM (\(TypeTransInfo _ env checks) -> TypeTransInfo MNil env checks)

instance TransInfo info => Translate info ctx (NatRepr n) OpenTerm where
  translate mb_n = return $ natOpenTerm $ mbLift $ fmap natValue mb_n

-- | Make a type translation that uses a single term of the given type
mkTermType1 :: KnownRepr TypeRepr a => OpenTerm -> TypeTrans (ExprTrans a)
mkTermType1 tp = mkTypeTrans1 tp (ETrans_Term knownRepr)

-- | Make a type translation that uses a single term of the given type using an
-- explicit 'TypeRepr' for the Crucible type
mkTermType1Repr :: TypeRepr a -> OpenTerm -> TypeTrans (ExprTrans a)
mkTermType1Repr repr tp = mkTypeTrans1 tp (ETrans_Term repr)


-- | Translate a permission expression type to a 'TypeTrans' and to a list of
-- kind descriptions that describe the types in the 'TypeTrans'
translateType :: TypeRepr a -> (TypeTrans (ExprTrans a), [OpenTerm])
translateType UnitRepr = (mkTypeTrans0 ETrans_Unit, [])
translateType BoolRepr =
  (mkTermType1 (globalOpenTerm "Prelude.Bool"), [boolKindDesc])
translateType NatRepr =
  (mkTermType1 (dataTypeOpenTerm "Prelude.Nat" []), [natKindDesc])
translateType (BVRepr w) =
  withKnownNat w
  (mkTermType1 (bitvectorTypeOpenTerm (natOpenTerm $ natValue w)),
   [bvKindDesc (natValue w)])
translateType (VectorRepr AnyRepr) = (mkTypeTrans0 ETrans_AnyVector, [])

-- Our special-purpose intrinsic types, whose translations do not have
-- computational content
translateType (LLVMPointerRepr _) = (mkTypeTrans0 ETrans_LLVM, [])
translateType (LLVMBlockRepr _) = (mkTypeTrans0 ETrans_LLVMBlock, [])
translateType (LLVMFrameRepr _) = (mkTypeTrans0 ETrans_LLVMFrame, [])
translateType LifetimeRepr = (mkTypeTrans0 ETrans_Lifetime, [])
translateType PermListRepr =
  panic "translateType" ["PermList type no longer supported!"]
translateType RWModalityRepr = (mkTypeTrans0 ETrans_RWModality, [])

-- Permissions and LLVM shapes translate to type descriptions
translateType (ValuePermRepr _) =
  (mkTypeTrans1 tpDescTypeOpenTerm (\d ->
                                     ETrans_Perm [d] [tpElemTypeOpenTerm d]),
   [tpKindDesc])
translateType (LLVMShapeRepr _) =
  (mkTypeTrans1 tpDescTypeOpenTerm (\d ->
                                     ETrans_Shape [d] [tpElemTypeOpenTerm d]),
   [tpKindDesc])

translateType tp@(FloatRepr _) =
  (mkTermType1Repr tp $ dataTypeOpenTerm "Prelude.Float" [],
   panic "translateType" ["Type descriptions of floats not yet supported"])

translateType (StringRepr UnicodeRepr) =
  (mkTermType1 stringTypeOpenTerm,
   panic "translateType" ["Type descriptions of strings not yet supported"])
translateType (StringRepr _) =
  panic "translateType" ["Non-unicode strings not supported"]
translateType (FunctionHandleRepr _ _) =
  -- NOTE: function permissions translate to the SAW function, but the function
  -- handle itself has no SAW translation
  (mkTypeTrans0 ETrans_Fun, [])

translateType (StructRepr tps) =
    let (tp_transs, ds) = translateCruCtx (mkCruCtx tps) in
    (fmap ETrans_Struct tp_transs, ds)

-- Default case is to panic for unsupported types
translateType tp =
  panic "translateType" ["Type not supported: " ++ show tp]


-- | Translate a 'CruCtx' to a 'TypeTrans' and to a list of kind descriptions
-- that describe the types in the 'TypeTrans'
translateCruCtx :: CruCtx ctx -> (TypeTrans (ExprTransCtx ctx), [OpenTerm])
translateCruCtx CruCtxNil = (mkTypeTrans0 MNil, [])
translateCruCtx (CruCtxCons ctx tp) =
  let (ctx_trans, ds1) = translateCruCtx ctx
      (tp_trans, ds2) = translateType tp in
  ((:>:) <$> ctx_trans <*> tp_trans, ds1 ++ ds2)

-- | Translate a permission expression type to a list of kind descriptions
translateKindDescs :: TypeRepr a -> [OpenTerm]
translateKindDescs = snd . translateType

-- Translate an expression type to a 'TypeTrans', which both gives a list of 0
-- or more SAW core types and also gives a function to create an expression
-- translation from SAW core terms of those types
instance TransInfo info =>
         Translate info ctx (TypeRepr a) (TypeTrans (ExprTrans a)) where
  translate = return . fst . translateType . mbLift

instance TransInfo info =>
         Translate info ctx (CruCtx as) (TypeTrans (ExprTransCtx as)) where
  translate = return . fst . translateCruCtx . mbLift

-- | Translate all types in a Crucible context and lambda-abstract over them
lambdaExprCtx :: TransInfo info => CruCtx ctx -> TransM info ctx OpenTerm ->
                 TransM info RNil OpenTerm
lambdaExprCtx ctx m =
  translateClosed ctx >>= \tptrans ->
  lambdaTransM "e" tptrans (\ectx -> inCtxTransM ectx m)

-- | Translate all types in a Crucible context and pi-abstract over them
piExprCtx :: TransInfo info => CruCtx ctx -> TransM info ctx OpenTerm ->
             TransM info RNil OpenTerm
piExprCtx ctx m =
  translateClosed ctx >>= \tptrans ->
  piTransM "e" tptrans (\ectx -> inCtxTransM ectx m)

-- | Like 'piExprCtx' but append the newly bound variables to the current
-- context, rather than running in the empty context
piExprCtxApp :: TransInfo info => CruCtx ctx2 ->
                TransM info (ctx1 :++: ctx2) OpenTerm ->
                TransM info ctx1 OpenTerm
piExprCtxApp ctx m =
  translateClosed ctx >>= \tptrans ->
  piTransM "e" tptrans (\ectx -> inExtMultiTransM ectx m)


----------------------------------------------------------------------
-- * Translating to Type Descriptions
----------------------------------------------------------------------

-- | Translation info for translating to type descriptions, which contains an
-- 'ExprTransCtx' for some prefix of @ctx@. The remainder of @ctx@ are variables
-- that each translate to zero or more deBruijn indices in type-level
-- expressions of the given kind descriptions. Note that this type does not
-- satisfy 'TransInfo', because that class requires an 'ExprTransCtx' for all of
-- @ctx@.
data DescTransInfo ctx where
  DescTransInfo ::
    ExprTransCtx ctx1 -> RAssign (Constant [OpenTerm]) ctx2 -> PermEnv ->
    ChecksFlag -> DescTransInfo (ctx1 :++: ctx2)

-- | Build a sequence of 'Proxy's for the context of a 'DescTransInfo'
dtiProxies :: DescTransInfo ctx -> RAssign Proxy ctx
dtiProxies (DescTransInfo ectx1 ctx2 _ _) =
  RL.append (RL.map (const Proxy) ectx1) (RL.map (const Proxy) ctx2)

-- | Translate a 'Member' proof representing a variable in a 'DescTransInfo'
-- context into either an 'ExprTrans', if the variable is bound in the
-- 'ExprTransCtx' portion of the context, or a 'Natural' that gives the deBruijn
-- index associated with the variable plus a list of its kind descriptions
dtiTranslateMemb :: DescTransInfo ctx -> Member ctx a ->
                    Either (ExprTrans a) (Natural, [OpenTerm])
dtiTranslateMemb (DescTransInfo ectx MNil _ _) memb =
  Left $ RL.get memb ectx
dtiTranslateMemb (DescTransInfo _ (_ :>: Constant ds) _ _) Member_Base =
  Right (0, ds)
dtiTranslateMemb (DescTransInfo ectx1 (ctx2 :>: Constant kds)
                  checks env) (Member_Step memb) =
  case dtiTranslateMemb (DescTransInfo ectx1 ctx2 checks env) memb of
    Left etrans -> Left etrans
    Right (i, ds) -> Right (i + fromIntegral (length kds), ds)

-- | Extend the context of a 'DescTransInfo' with free deBruijn variables for a
-- list of kind descriptions
extDescTransInfo :: [OpenTerm] -> DescTransInfo ctx -> DescTransInfo (ctx :> tp)
extDescTransInfo ds (DescTransInfo ctx1 ctx2 env checks) =
  DescTransInfo ctx1 (ctx2 :>: Constant ds) env checks

-- | The translation monad specific to translating type descriptions
type DescTransM = TransM DescTransInfo

-- | Run a 'DescTransM' computation with an additional deBruijn variable
inExtDescTransM :: [OpenTerm] -> DescTransM (ctx :> tp) a -> DescTransM ctx a
inExtDescTransM ds = withInfoM (extDescTransInfo ds)

-- | Run a 'DescTransM' computation with a set of additional deBruijn variables
inExtDescTransMultiM :: RAssign (Constant [OpenTerm]) ctx2 ->
                        DescTransM (ctx1 :++: ctx2) a -> DescTransM ctx1 a
inExtDescTransMultiM MNil m = m
inExtDescTransMultiM (ctx :>: Constant tp) m =
  inExtDescTransMultiM ctx $ inExtDescTransM tp m

-- | Run a 'DescTransM' computation in an extended expression context that binds
-- all the newly-bound variables to deBruijn indices. Pass the concatenated list
-- of all the kind descriptions of those variables to the sub-computation.
inExtCtxDescTransM :: CruCtx ctx2 ->
                      ([OpenTerm] -> DescTransM (ctx1 :++: ctx2) a) ->
                      DescTransM ctx1 a
inExtCtxDescTransM ctx m =
  let kdesc_ctx = RL.map (Constant . translateKindDescs) $ cruCtxToTypes ctx
      kdescs = concat $ RL.toList kdesc_ctx in
  inExtDescTransMultiM kdesc_ctx $ m kdescs

-- | Run a 'DescTransM' computation in any 'TransM' monad satifying 'TransInfo'
descTransM :: TransInfo info => DescTransM ctx a -> TransM info ctx a
descTransM =
  withInfoM $ \info ->
  DescTransInfo (infoCtx info) MNil (infoEnv info) (infoChecksFlag info)

-- | The class for translating to type descriptions or type-level expressions.
-- This should hold for any type that has a 'Translate' instance to a
-- 'TypeTrans'. The type descriptions returned in this case should describe
-- exactly the types in the 'TypeTrans' returned by the 'Translate' instance,
-- though 'translateDesc' is allowed to 'panic' in some cases where 'translate'
-- succeeds, meaning that some of the types cannot be described in type
-- descriptions. This also holds for the 'PermExpr' type, where the return
-- values are type-level expressions for each of the kind descriptions returned
-- by 'translateType'.
class TranslateDescs a where
  translateDescs :: Mb ctx a -> DescTransM ctx [OpenTerm]

-- | Translate to a single type description by tupling all the descriptions
-- return by 'translateDescs'
translateDesc :: TranslateDescs a => Mb ctx a -> DescTransM ctx OpenTerm
translateDesc mb_a = tupleTpDesc <$> translateDescs mb_a

-- | Translate to a single type description or type expression, raising an error
-- if the given construct translates to 0 or more than 1 SAW core term
translateDesc1 :: TranslateDescs a => Mb ctx a -> DescTransM ctx OpenTerm
translateDesc1 mb_a = translateDescs mb_a >>= \case
  [d] -> return d
  ds -> panic "translateDesc1" ["Expected one type-level expression, found "
                                ++ show (length ds)]

-- | Translate a variable to either a SAW core value, if it is bound to a value,
-- or a natural number deBruijn index for the the first of the 0 or more
-- deBruijn indices that the variable translates to along with their kind
-- descriptions if not
translateVarDesc :: Mb ctx (ExprVar a) ->
                    DescTransM ctx (Either (ExprTrans a) (Natural, [OpenTerm]))
translateVarDesc mb_x = flip dtiTranslateMemb (translateVar mb_x) <$> ask

-- | A type translation with type descriptions for its types
data DescTypeTrans tr = DescTypeTrans { descTypeTrans :: TypeTrans tr,
                                        descTypeTransDescs :: [OpenTerm] }

instance Functor DescTypeTrans where
  fmap f (DescTypeTrans ttr ds) = DescTypeTrans (fmap f ttr) ds

instance Applicative DescTypeTrans where
  pure x = DescTypeTrans (mkTypeTrans0 x) []
  liftA2 f (DescTypeTrans tr1 ds1) (DescTypeTrans tr2 ds2) =
    DescTypeTrans (liftA2 f tr1 tr2) (ds1 ++ ds2)

-- | Apply the 'typeTransFun' of a 'TypeTrans' in a 'DescTypeTrans'
descTypeTransF :: HasCallStack => DescTypeTrans tr -> [OpenTerm] -> tr
descTypeTransF dtp_trans = typeTransF (descTypeTrans dtp_trans)

-- | Build the type description of the multi-arity arrow type from the types in
-- order in the first type translation to the tuple of the types in the second
arrowDescTrans :: DescTypeTrans tr1 -> DescTypeTrans tr2 -> OpenTerm
arrowDescTrans tp1 tp2 =
  arrowTpDescMulti (descTypeTransDescs tp1) (tupleTpDesc $
                                             descTypeTransDescs tp2)

-- | Translate a type-like object to a type translation and type descriptions
translateDescType :: TransInfo info => Translate info ctx a (TypeTrans tr) =>
                     TranslateDescs a =>
                     Mb ctx a -> TransM info ctx (DescTypeTrans tr)
translateDescType mb_a =
  DescTypeTrans <$> translate mb_a <*> descTransM (translateDescs mb_a)


----------------------------------------------------------------------
-- * Translating Permission Expressions
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
  (applyGlobalOpenTerm "Prelude.take" [boolTypeOpenTerm, sz1, sz2, e],
   applyGlobalOpenTerm "Prelude.drop" [boolTypeOpenTerm, sz1, sz2, e])
bvSplitOpenTerm LittleEndian sz1 sz2 e =
  (applyGlobalOpenTerm "Prelude.drop" [boolTypeOpenTerm, sz2, sz1, e],
   applyGlobalOpenTerm "Prelude.take" [boolTypeOpenTerm, sz2, sz1, e])

bvConcatOpenTerm :: EndianForm -> OpenTerm -> OpenTerm ->
                    OpenTerm -> OpenTerm -> OpenTerm
bvConcatOpenTerm BigEndian sz1 sz2 e1 e2 =
  applyGlobalOpenTerm "Prelude.append" [sz1, sz2, boolTypeOpenTerm, e1, e2]
bvConcatOpenTerm LittleEndian sz1 sz2 e1 e2 =
  applyGlobalOpenTerm "Prelude.append" [sz2, sz1, boolTypeOpenTerm, e2, e1]

-- | Translate a variable to a 'Member' proof, raising an error if the variable
-- is unbound
translateVar :: Mb ctx (ExprVar a) -> Member ctx a
translateVar mb_x | Left memb <- mbNameBoundP mb_x = memb
translateVar _ = panic "translateVar" ["unbound variable!"]

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
  translate mb_e = case mbMatch mb_e of
    [nuMP| PExpr_Var x |] -> translate x
    [nuMP| PExpr_Unit |] -> return ETrans_Unit
    [nuMP| PExpr_Bool True |] ->
      return $ ETrans_Term knownRepr $ globalOpenTerm "Prelude.True"
    [nuMP| PExpr_Bool False |] ->
      return $ ETrans_Term knownRepr $ globalOpenTerm "Prelude.False"
    [nuMP| PExpr_Nat i |] ->
      return $ ETrans_Term knownRepr $ natOpenTerm $ mbLift i
    [nuMP| PExpr_String str |] ->
      return $ ETrans_Term knownRepr $ stringLitOpenTerm $ pack $ mbLift str
    [nuMP| PExpr_BV bvfactors@[] off |] ->
      let w = natRepr3 bvfactors in
      return $ ETrans_Term knownRepr $ bvBVOpenTerm w $ mbLift off
    [nuMP| PExpr_BV bvfactors (BV.BV 0) |] ->
      let w = natVal3 bvfactors in
      ETrans_Term knownRepr <$> foldr1 (bvAddOpenTerm w) <$> translate bvfactors
    [nuMP| PExpr_BV bvfactors off |] ->
      do let w = natRepr3 bvfactors
         bv_transs <- translate bvfactors
         return $ ETrans_Term knownRepr $
           foldr (bvAddOpenTerm $ natValue w) (bvBVOpenTerm w $ mbLift off) bv_transs
    [nuMP| PExpr_Struct args |] ->
      ETrans_Struct <$> translate args
    [nuMP| PExpr_Always |] ->
      return ETrans_Lifetime
    [nuMP| PExpr_LLVMWord _ |] -> return ETrans_LLVM
    [nuMP| PExpr_LLVMOffset _ _ |] -> return ETrans_LLVM
    [nuMP| PExpr_Fun _ |] -> return ETrans_Fun
    [nuMP| PExpr_PermListNil |] -> return $ ETrans_Term knownRepr unitTypeOpenTerm
    [nuMP| PExpr_PermListCons _ _ p l |] ->
      ETrans_Term knownRepr <$> (pairTypeOpenTerm <$>
                                 (typeTransTupleType <$> translate p) <*>
                                 (translate1 l))
    [nuMP| PExpr_RWModality _ |] -> return ETrans_RWModality

    -- LLVM shapes are translated to type descriptions by translateDescs
    [nuMP| PExpr_EmptyShape |] ->
      return $ ETrans_Shape [] []
    [nuMP| PExpr_NamedShape _ _ nmsh args |] ->
      case mbMatch $ fmap namedShapeBody nmsh of
        [nuMP| DefinedShapeBody _ |] ->
          translate (mbMap2 unfoldNamedShape nmsh args)
        [nuMP| OpaqueShapeBody _ tp_id desc_id |] ->
          do let (_, k_ds) = translateCruCtx (mbLift $ fmap namedShapeArgs nmsh)
             args_terms <- transTerms <$> translate args
             args_ds <- descTransM $ translateDescs args
             return $
               ETrans_Shape [substIdTpDescMulti (mbLift desc_id) k_ds args_ds]
               [applyGlobalOpenTerm (mbLift tp_id) args_terms]
        [nuMP| RecShapeBody _ tp_id desc_id |] ->
          do let (_, k_ds) = translateCruCtx (mbLift $ fmap namedShapeArgs nmsh)
             args_terms <- transTerms <$> translate args
             args_ds <- descTransM $ translateDescs args
             return $
               ETrans_Shape [substIdTpDescMulti (mbLift desc_id) k_ds args_ds]
               [applyGlobalOpenTerm (mbLift tp_id) args_terms]
    [nuMP| PExpr_EqShape _ _ |] -> return $ ETrans_Shape [] []
    [nuMP| PExpr_PtrShape _ _ sh |] -> translate sh
    [nuMP| PExpr_FieldShape fsh |] ->
      ETrans_Shape <$> descTransM (translateDescs fsh) <*> translate fsh
    [nuMP| PExpr_ArrayShape mb_len _ mb_sh |] ->
      do let w = natVal4 mb_len
         let w_term = natOpenTerm w
         len_d <- descTransM $ translateBVDesc mb_len
         len_term <- translate1 mb_len
         (elem_ds, elem_tps) <- unETransShape <$> translate mb_sh
         return $
           ETrans_Shape [bvVecTpDesc w_term len_d (tupleTpDesc elem_ds)]
           [bvVecTypeOpenTerm w_term len_term (tupleOfTypes elem_tps)]
    [nuMP| PExpr_SeqShape sh1 sh2 |] ->
      do (ds1, tps1) <- unETransShape <$> translate sh1
         (ds2, tps2) <- unETransShape <$> translate sh2
         return $ ETrans_Shape (ds1 ++ ds2) (tps1 ++ tps2)
    [nuMP| PExpr_OrShape sh1 sh2 |] ->
      do (ds1, tps1) <- unETransShape <$> translate sh1
         (ds2, tps2) <- unETransShape <$> translate sh2
         return $
           ETrans_Shape [sumTpDesc (tupleTpDesc ds1) (tupleTpDesc ds2)]
           [eitherTypeOpenTerm (tupleOfTypes tps1) (tupleOfTypes tps2)]
    [nuMP| PExpr_ExShape mb_mb_sh |] ->
      do let tp_repr = mbLift $ fmap bindingType mb_mb_sh
         let mb_sh = mbCombine RL.typeCtxProxies mb_mb_sh
         let (tptrans, _) = translateType tp_repr
         d <- descTransM $
           inExtCtxDescTransM (singletonCruCtx tp_repr) $ \kdescs ->
           sigmaTpDescMulti kdescs <$> translateDesc mb_sh
         -- NOTE: we are explicitly using laziness of the ETrans_Shape
         -- constructor so that the following recursive call does not generate
         -- the type description a second time and then throw it away. The
         -- reason we don't use that result is that that recursive call is in
         -- the context of SAW core variables for tp (bound by sigmaTypeTransM),
         -- whereas the description of the sigma type requires binding deBruijn
         -- index for that sigma type variable
         tp <- sigmaTypeTransM "x_exsh" tptrans $ \e ->
           inExtTransM e (openTermsTypeTrans <$> snd <$>
                          unETransShape <$> translate mb_sh)
         return $ ETrans_Shape [d] [tp]
    [nuMP| PExpr_FalseShape |] ->
      return $
      ETrans_Shape [ctorOpenTerm "Prelude.Tp_Void" []] [dataTypeOpenTerm
                                                        "Prelude.Void" []]

    [nuMP| PExpr_ValPerm p |] ->
      ETrans_Perm <$> descTransM (translateDescs p) <*> (typeTransTypes <$>
                                                         translate p)


-- LLVM field shapes translate to the list of type descriptions that the
-- permission they contain translates to
instance TransInfo info =>
         Translate info ctx (LLVMFieldShape w) [OpenTerm] where
  translate (mbMatch -> [nuMP| LLVMFieldShape p |]) =
    typeTransTypes <$> translate p

-- The TranslateDescs instance for LLVM field shapes returns the type
-- descriptions associated with the contained permission
instance TranslateDescs (LLVMFieldShape w) where
  translateDescs (mbMatch -> [nuMP| LLVMFieldShape p |]) =
    translateDescs p

-- A sequence of expressions translates to an ExprTransctx
instance TransInfo info =>
         Translate info ctx (PermExprs as) (ExprTransCtx as) where
  translate mb_exprs = case mbMatch mb_exprs of
    [nuMP| PExprs_Nil |] -> return MNil
    [nuMP| PExprs_Cons es e |] ->
      (:>:) <$> translate es <*> translate e

-- A BVFactor translates to a SAW core term of bitvector type
instance TransInfo info => Translate info ctx (BVFactor w) OpenTerm where
  translate mb_f = case mbMatch mb_f of
    [nuMP| BVFactor (BV.BV 1) x |] -> translate1 (fmap PExpr_Var x)
    [nuMP| BVFactor i x |] ->
      let w = natRepr4 x in
      bvMulOpenTerm (natValue w) (bvBVOpenTerm w $ mbLift i) <$>
      translate1 (fmap PExpr_Var x)

-- | Translate a bitvector constant value to a type-level expression
translateBVConstDesc :: NatRepr w -> BV w -> OpenTerm
translateBVConstDesc w bv =
  bvConstTpExpr (natValue w) (bvBVOpenTerm w bv)

-- | Translate a bitvector variable to a type-level expression
translateBVVarDesc :: NatRepr w -> Mb ctx (ExprVar (BVType w)) ->
                      DescTransM ctx OpenTerm
translateBVVarDesc w mb_x = translateVarDesc mb_x >>= \case
  Left bv -> return $ bvConstTpExpr (natValue w) (transTerm1 bv)
  Right (ix, [_]) -> return $ varTpExpr (bvExprKind $ natValue w) ix
  Right (_, ds) ->
    panic "translateBVVarDesc" ["Expected one kind for variable, found "
                                ++ show (length ds)]

-- | Translate a 'BVFactor' to a type-level expression
translateBVFactorDesc :: Mb ctx (BVFactor w) -> DescTransM ctx OpenTerm
translateBVFactorDesc mb_f =
  case mbMatch mb_f of
    [nuMP| BVFactor (BV.BV 1) mb_x |] ->
      translateBVVarDesc (natRepr4 mb_x) mb_x
    [nuMP| BVFactor mb_i mb_x |] ->
      let w = natRepr4 mb_x in
      bvMulTpExpr (natValue w) (translateBVConstDesc w $ mbLift mb_i) <$>
      translateBVVarDesc w mb_x

-- | Translate an expression of bitvector type to a type-level expression
translateBVDesc :: KnownNat w => Mb ctx (PermExpr (BVType w)) ->
                   DescTransM ctx OpenTerm
translateBVDesc mb_e =
  let w = mbExprBVTypeWidth mb_e in
  case mbMatch mb_e of
    [nuMP| PExpr_Var mb_x |] -> translateBVVarDesc w mb_x
    [nuMP| PExpr_BV mb_fs mb_i |] ->
      do fs_exprs <- mapM translateBVFactorDesc $ mbList mb_fs
         let i_expr = translateBVConstDesc w $ mbLift mb_i
         return $ bvSumTpExprs (natValue w) (fs_exprs ++ [i_expr])

-- translateDescs on permission expressions yield a list of SAW core terms of
-- type @kindExpr K@, one for each kind @K@ in the list of kind descriptions
-- returned by translateType
instance TranslateDescs (PermExpr a) where
  translateDescs mb_e = case mbMatch mb_e of
    [nuMP| PExpr_Var mb_x |] ->
      translateVarDesc mb_x >>= \case
      Left etrans -> return $ exprTransDescs etrans
      Right (ix, ds) -> return $ zipWith varTpDesc ds [ix..]
    [nuMP| PExpr_Unit |] -> return []
    [nuMP| PExpr_Bool b |] ->
      return [constTpExpr boolKindDesc $ boolOpenTerm $ mbLift b]
    [nuMP| PExpr_Nat n |] ->
      return [constTpExpr natKindDesc $ natOpenTerm $ mbLift n]
    [nuMP| PExpr_String _ |] ->
      panic "translateDescs"
      ["Cannot (yet?) translate strings to type-level expressions"]
    [nuMP| PExpr_BV _ _ |] -> (:[]) <$> translateBVDesc mb_e
    [nuMP| PExpr_Struct es |] -> translateDescs es
    [nuMP| PExpr_Always |] -> return []
    [nuMP| PExpr_LLVMWord _ |] -> return []
    [nuMP| PExpr_LLVMOffset _ _ |] -> return []
    [nuMP| PExpr_Fun _ |] -> return []
    [nuMP| PExpr_PermListNil |] ->
      panic "translateDescs" ["PermList type no longer supported!"]
    [nuMP| PExpr_PermListCons _ _ _ _ |] ->
      panic "translateDescs" ["PermList type no longer supported!"]
    [nuMP| PExpr_RWModality _ |] -> return []

    -- NOTE: the cases for the shape expressions here overlap significantly with
    -- those in the Translate instance for PermExpr. The difference is that
    -- these cases can handle some of the expression context being deBruijn
    -- indices instead of ExprTranss, by virtue of the fact that here we only
    -- return the type descriptions and not the types
    [nuMP| PExpr_EmptyShape |] -> return []
    [nuMP| PExpr_NamedShape _ _ nmsh args |] ->
      case mbMatch $ fmap namedShapeBody nmsh of
        [nuMP| DefinedShapeBody _ |] ->
          translateDescs (mbMap2 unfoldNamedShape nmsh args)
        [nuMP| OpaqueShapeBody _ _ desc_id |] ->
          do let (_, k_ds) = translateCruCtx (mbLift $ fmap namedShapeArgs nmsh)
             args_ds <- translateDescs args
             return [substIdTpDescMulti (mbLift desc_id) k_ds args_ds]
        [nuMP| RecShapeBody _ _ desc_id |] ->
          do let (_, k_ds) = translateCruCtx (mbLift $ fmap namedShapeArgs nmsh)
             args_ds <- translateDescs args
             return [substIdTpDescMulti (mbLift desc_id) k_ds args_ds]
    [nuMP| PExpr_EqShape _ _ |] -> return []
    [nuMP| PExpr_PtrShape _ _ sh |] -> translateDescs sh
    [nuMP| PExpr_FieldShape fsh |] -> translateDescs fsh
    [nuMP| PExpr_ArrayShape mb_len _ mb_sh |] ->
      do let w = natVal4 mb_len
         let w_term = natOpenTerm w
         len_term <- translateBVDesc mb_len
         elem_d <- translateDesc mb_sh
         return [bvVecTpDesc w_term len_term elem_d]
    [nuMP| PExpr_SeqShape sh1 sh2 |] ->
      do ds1 <- translateDescs sh1
         ds2 <- translateDescs sh2
         return (ds1 ++ ds2)
    [nuMP| PExpr_OrShape sh1 sh2 |] ->
      (\d -> [d]) <$> (sumTpDesc <$> translateDesc sh1 <*> translateDesc sh2)
    [nuMP| PExpr_ExShape mb_sh |] ->
      let tp = mbLift $ fmap bindingType mb_sh in
      inExtCtxDescTransM (singletonCruCtx tp) $ \kdescs ->
      (\d -> [d]) <$> sigmaTpDescMulti kdescs <$>
      translateDesc (mbCombine RL.typeCtxProxies mb_sh)
    [nuMP| PExpr_FalseShape |] ->
      return [ctorOpenTerm "Prelude.Tp_Void" []]

    [nuMP| PExpr_ValPerm mb_p |] -> translateDescs mb_p


instance TranslateDescs (PermExprs tps) where
  translateDescs mb_es = case mbMatch mb_es of
    [nuMP| MNil |] -> return []
    [nuMP| es :>: e |] -> (++) <$> translateDescs es <*> translateDescs e


----------------------------------------------------------------------
-- * Permission Translations
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

  -- | The translation of an LLVM block permission is a sequence of elements of
  -- the translations of its shapes to types
  APTrans_LLVMBlock :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMBlockPerm w) -> [OpenTerm] ->
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

  -- | The translation of an LLVMBlockShape permission is a sequence of elements
  -- of the translations of its shape to types
  APTrans_LLVMBlockShape :: (1 <= w, KnownNat w) =>
                            Mb ctx (PermExpr (LLVMShapeType w)) -> [OpenTerm] ->
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
  APTrans_LOwned ::
    Mb ctx [PermExpr LifetimeType] -> CruCtx ps_in -> CruCtx ps_out ->
    Mb ctx (ExprPerms ps_in) -> Mb ctx (ExprPerms ps_out) ->
    LOwnedTrans ctx ps_extra ps_in ps_out ->
    AtomicPermTrans ctx LifetimeType

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

  -- | The translation of functional permission is a SAW term of @FunIx@ type
  APTrans_Fun :: Mb ctx (FunPerm ghosts (CtxToRList cargs) gouts ret) ->
                 FunTransTerm ->
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

-- | The translation of the vacuously true permission
pattern PTrans_True :: PermTrans ctx a
pattern PTrans_True = PTrans_Conj []

-- | A single @lowned@ permission translation
pattern PTrans_LOwned ::
  () => (a ~ LifetimeType) =>
  Mb ctx [PermExpr LifetimeType] -> CruCtx ps_in -> CruCtx ps_out ->
  Mb ctx (ExprPerms ps_in) -> Mb ctx (ExprPerms ps_out) ->
  LOwnedTrans ctx ps_extra ps_in ps_out ->
  PermTrans ctx a
pattern PTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t =
  PTrans_Conj [APTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t]

-- | A single function permission
pattern PTrans_Fun :: () => (a ~ FunctionHandleType cargs ret) =>
                      Mb ctx (FunPerm ghosts (CtxToRList cargs) gouts ret) ->
                      FunTransTerm -> PermTrans ctx a
pattern PTrans_Fun mb_fun_perm tr = PTrans_Conj [APTrans_Fun mb_fun_perm tr]

-- | The translation of a function permission to a term
data FunTransTerm
     -- | A function represented as a corecursive function index, i.e., a term
     -- of type @FunIx T@, where @T@ is a type description of the type of the
     -- function. The first term is the event type, the second is @T@, and the
     -- third is the function index.
  = FunTransIx EventType OpenTerm OpenTerm
    -- | A monadic function represented as a monadic function, i.e., a term of
    -- type @specFun E nil T@, where @E@ is the current event type and @T@ is a
    -- type description of the type of the function
  | FunTransFun EventType OpenTerm OpenTerm

-- | Convert a 'FunTransTerm' to an index, i.e., term of type @FunIx T@
funTransTermToIx :: FunTransTerm -> OpenTerm
funTransTermToIx (FunTransIx _ _ funix) = funix
funTransTermToIx (FunTransFun ev d f) =
  applyGlobalOpenTerm "Prelude.LambdaS" [evTypeTerm ev, d, f]

-- | Apply a 'FunTransTerm' to a list of arguments
applyFunTransTerm :: FunTransTerm -> [OpenTerm] -> OpenTerm
applyFunTransTerm (FunTransIx ev d funix) = callSOpenTerm ev d funix
applyFunTransTerm (FunTransFun _ _ f) = applyOpenTermMulti f


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

data SomeLOwnedTrans ctx ps_in ps_out =
  forall ps_extra. SomeLOwnedTrans (LOwnedTrans ctx ps_extra ps_in ps_out)

-- | Extract the 'LOwnedTrans' of a conjunction of a single @lowned@ permission
-- with the specified input and output types
unPTransLOwned :: String -> Mb ctx (CruCtx ps_in) -> Mb ctx (CruCtx ps_out) ->
                  PermTrans ctx LifetimeType ->
                  SomeLOwnedTrans ctx ps_in ps_out
unPTransLOwned _ tps_in tps_out
  (PTrans_LOwned _ (testEquality (mbLift tps_in) -> Just Refl)
   (testEquality (mbLift tps_out) -> Just Refl) _ _ lotr)
  = SomeLOwnedTrans lotr
unPTransLOwned fname _ _ _ =
  panic fname ["Expected lowned permission"]

-- | A context mapping bound names to their perm translations
type PermTransCtx ctx ps = RAssign (PermTrans ctx) ps

-- | A 'DescTypeTrans' yielding a single 'PermTrans'
type Desc1PermTpTrans ctx a = DescTypeTrans (PermTrans ctx a)

-- | A 'DescTypeTrans' yielding a 'PermTransCtx'
type DescPermsTpTrans ctx ps = DescTypeTrans (PermTransCtx ctx ps)

-- | Prepand an empty list of permissions to a 'DescPermsTpTrans'
preNilDescPermsTpTrans :: DescPermsTpTrans ctx ps ->
                          DescPermsTpTrans ctx (RNil :++: ps)
preNilDescPermsTpTrans = liftA2 RL.append (pure MNil)

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
  transTerms (APTrans_LLVMBlock _ ts) = ts
  transTerms (APTrans_LLVMFree _) = []
  transTerms (APTrans_LLVMFunPtr _ trans) = transTerms trans
  transTerms APTrans_IsLLVMPtr = []
  transTerms (APTrans_LLVMBlockShape _ ts) = ts
  transTerms (APTrans_NamedConj _ _ _ t) = [t]
  transTerms (APTrans_DefinedNamedConj _ _ _ ptrans) = transTerms ptrans
  transTerms (APTrans_LLVMFrame _) = []
  transTerms (APTrans_LOwned _ _ _ eps_in _ lotr) =
    [lownedTransTerm eps_in lotr]
  transTerms (APTrans_LOwnedSimple _ _) = []
  transTerms (APTrans_LCurrent _) = []
  transTerms APTrans_LFinished = []
  transTerms (APTrans_Struct pctx) = transTerms pctx
  transTerms (APTrans_Fun _ t) = [funTransTermToIx t]
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
atomicPermTransPerm _ (APTrans_LOwned
                       mb_ls tps_in tps_out mb_ps_in mb_ps_out _) =
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

-- | Extend the context of a 'PermTrans' with a single type
extPermTrans :: ExtPermTrans f => ExprTrans tp -> f ctx a -> f (ctx :> tp) a
extPermTrans e = extPermTransMulti (MNil :>: e)

-- | Extend the context of a permission translation using a 'CtxExt'
extPermTransExt :: ExprCtxExt ctx1 ctx2 ->
                   PermTrans ctx1 a -> PermTrans ctx2 a
extPermTransExt (ExprCtxExt ctx) ptrans =
  extPermTransMulti ctx ptrans

-- | Extend the context of a 'PermTransCtx' using a 'CtxExt'
extPermTransCtxExt :: ExprCtxExt ctx1 ctx2 ->
                      PermTransCtx ctx1 ps -> PermTransCtx ctx2 ps
extPermTransCtxExt cext = RL.map (extPermTransExt cext)


-- | Generic function to extend the context of the translation of a permission
class ExtPermTrans f where
  extPermTransMulti :: ExprTransCtx ctx2 -> f ctx1 a -> f (ctx1 :++: ctx2) a

instance ExtPermTrans PermTrans where
  extPermTransMulti ectx (PTrans_Eq e) =
    PTrans_Eq $ extMbAny ectx e
  extPermTransMulti ectx (PTrans_Conj aps) =
    PTrans_Conj (map (extPermTransMulti ectx) aps)
  extPermTransMulti ectx (PTrans_Defined n args a ptrans) =
    PTrans_Defined n (extMbAny ectx args) (extMbAny ectx a)
    (extPermTransMulti ectx ptrans)
  extPermTransMulti ectx (PTrans_Term p t) = PTrans_Term (extMbAny ectx p) t

instance ExtPermTrans AtomicPermTrans where
  extPermTransMulti ectx (APTrans_LLVMField fld ptrans) =
    APTrans_LLVMField (extMbAny ectx fld) (extPermTransMulti ectx ptrans)
  extPermTransMulti ectx (APTrans_LLVMArray arr_trans) =
    APTrans_LLVMArray $ extPermTransMulti ectx arr_trans
  extPermTransMulti ectx (APTrans_LLVMBlock mb_bp ts) =
    APTrans_LLVMBlock (extMbAny ectx mb_bp) ts
  extPermTransMulti ectx  (APTrans_LLVMFree e) =
    APTrans_LLVMFree $ extMbAny ectx e
  extPermTransMulti ectx (APTrans_LLVMFunPtr tp ptrans) =
    APTrans_LLVMFunPtr tp (extPermTransMulti ectx ptrans)
  extPermTransMulti _ APTrans_IsLLVMPtr = APTrans_IsLLVMPtr
  extPermTransMulti ectx (APTrans_LLVMBlockShape mb_sh ts) =
    APTrans_LLVMBlockShape (extMbAny ectx mb_sh) ts
  extPermTransMulti ectx (APTrans_NamedConj npn args off t) =
    APTrans_NamedConj npn (extMbAny ectx args) (extMbAny ectx off) t
  extPermTransMulti ectx (APTrans_DefinedNamedConj npn args off ptrans) =
    APTrans_DefinedNamedConj npn (extMbAny ectx args) (extMbAny ectx off)
    (extPermTransMulti ectx ptrans)
  extPermTransMulti ectx (APTrans_LLVMFrame fp) =
    APTrans_LLVMFrame $ extMbAny ectx fp
  extPermTransMulti ectx (APTrans_LOwned ls tps_in tps_out ps_in ps_out lotr) =
    APTrans_LOwned (extMbAny ectx ls) tps_in tps_out
    (extMbAny ectx ps_in) (extMbAny ectx ps_out)
    (extLOwnedTransMulti ectx lotr)
  extPermTransMulti ectx (APTrans_LOwnedSimple tps lops) =
    APTrans_LOwnedSimple tps (extMbAny ectx lops)
  extPermTransMulti ectx (APTrans_LCurrent p) =
    APTrans_LCurrent $ extMbAny ectx p
  extPermTransMulti _ APTrans_LFinished = APTrans_LFinished
  extPermTransMulti ectx (APTrans_Struct ps) =
    APTrans_Struct $ RL.map (extPermTransMulti ectx) ps
  extPermTransMulti ectx (APTrans_Fun fp trans) =
    APTrans_Fun (extMbAny ectx fp) trans
  extPermTransMulti ectx (APTrans_BVProp prop_trans) =
    APTrans_BVProp $ extPermTransMulti ectx prop_trans
  extPermTransMulti _ APTrans_Any = APTrans_Any

instance ExtPermTrans LLVMArrayPermTrans where
  extPermTransMulti ectx (LLVMArrayPermTrans ap len sh {- bs -} t) =
    LLVMArrayPermTrans (extMbAny ectx ap) len
    (fmap (extPermTransMulti ectx) sh) {- (map extPermTrans bs) -} t

{-
instance ExtPermTrans LLVMArrayBorrowTrans where
  extPermTrans (LLVMArrayBorrowTrans mb_b prop_transs) =
    LLVMArrayBorrowTrans (extMb mb_b) (map extPermTrans prop_transs)
-}

instance ExtPermTrans BVPropTrans where
  extPermTransMulti ectx (BVPropTrans prop t) =
    BVPropTrans (extMbAny ectx prop) t

instance ExtPermTrans BVRangeTrans where
  extPermTransMulti ectx (BVRangeTrans rng t1 t2) =
    BVRangeTrans (extMbAny ectx rng) t1 t2

-- | Extend the context of a permission translation context
extPermTransCtx :: ExprTrans tp -> PermTransCtx ctx ps ->
                   PermTransCtx (ctx :> tp) ps
extPermTransCtx e = RL.map (extPermTrans e)

-- | Extend the context of a permission translation context
extPermTransCtxMulti :: ExprTransCtx ctx2 -> PermTransCtx ctx1 ps ->
                        PermTransCtx (ctx1 :++: ctx2) ps
extPermTransCtxMulti ectx2 = RL.map (extPermTransMulti ectx2)

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
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMBlock mb_bp ts) =
  Just $ APTrans_LLVMBlock
  (mbMap2 (\off bp ->
            bp { llvmBlockOffset =
                   bvAdd (llvmBlockOffset bp) off } ) mb_off mb_bp)
  ts
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


----------------------------------------------------------------------
-- * Translations of Array Permissions
----------------------------------------------------------------------

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
  [applyGlobalOpenTerm "Prelude.atBVVec"
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
        applyGlobalOpenTerm "Prelude.updBVVec"
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
      elem_tp = llvmArrayTransCellType arr_trans
      len_tm = llvmArrayTransLen arr_trans
      v_tm = llvmArrayTransTerm arr_trans
      off_tm = transTerm1 $ bvRangeTransOff rng_trans
      len'_tm = transTerm1 $ bvRangeTransLen rng_trans
      (p1_trans, p2_trans, _) = expectLengthAtLeastTwo prop_transs
      BVPropTrans _ p1_tm = p1_trans
      BVPropTrans _ p2_tm = p2_trans in
  typeTransF sub_arr_tp
  [applyGlobalOpenTerm "Prelude.sliceBVVec"
   [natOpenTerm w, len_tm, elem_tp, off_tm, len'_tm, p1_tm, p2_tm, v_tm]]

-- | Write a slice (= a sub-array) of the translation of an LLVM array
-- permission given the translation of the slice and of the offset of that slice
-- in the larger array
setLLVMArrayTransSlice :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          LLVMArrayPermTrans ctx w -> OpenTerm ->
                          LLVMArrayPermTrans ctx w
setLLVMArrayTransSlice arr_trans sub_arr_trans off_tm =
  let w = fromInteger $ natVal arr_trans
      elem_tp = llvmArrayTransCellType arr_trans
      len_tm = llvmArrayTransLen arr_trans
      arr_tm = llvmArrayTransTerm arr_trans
      len'_tm = llvmArrayTransLen sub_arr_trans
      sub_arr_tm = llvmArrayTransTerm sub_arr_trans in
  arr_trans
  { llvmArrayTransTerm =
      applyGlobalOpenTerm "Prelude.updSliceBVVec"
      [natOpenTerm w, len_tm, elem_tp, arr_tm, off_tm, len'_tm, sub_arr_tm] }


----------------------------------------------------------------------
-- * Translations of Lifetime Ownership Permissions
----------------------------------------------------------------------

-- | An 'LOwnedInfo' is essentially a set of translations of "proof objects" of
-- permission list @ps@, in a variable context @ctx@, along with additional
-- information (the @SpecM@ event type and the eventual return type of the
-- overall computation) required to apply @bindS@
data LOwnedInfo ps ctx =
  LOwnedInfo { lownedInfoECtx :: ExprTransCtx ctx,
               lownedInfoPCtx :: PermTransCtx ctx ps,
               lownedInfoPVars :: RAssign (Member ctx) ps,
               lownedInfoEvType :: EventType,
               lownedInfoRetType :: OpenTerm }

-- | Convert an 'ImpTransInfo' to an 'LOwnedInfo'
impInfoToLOwned :: ImpTransInfo ext blocks tops rets ps ctx -> LOwnedInfo ps ctx
impInfoToLOwned (ImpTransInfo {..}) =
  LOwnedInfo { lownedInfoECtx = itiExprCtx,
               lownedInfoPCtx = itiPermStack,
               lownedInfoPVars = itiPermStackVars,
               lownedInfoEvType = permEnvEventType itiPermEnv,
               lownedInfoRetType = itiReturnType }

-- | Convert an 'LOwnedInfo' to an 'ImpTransInfo' using an existing
-- 'ImpTransInfo', throwing away all permissions in the 'ImpTransInfo'
lownedInfoToImp :: LOwnedInfo ps ctx ->
                   ImpTransInfo ext blocks tops rets ps' ctx' ->
                   ImpTransInfo ext blocks tops rets ps ctx
lownedInfoToImp (LOwnedInfo {..}) (ImpTransInfo {..}) =
  ImpTransInfo { itiExprCtx = lownedInfoECtx, itiPermStack = lownedInfoPCtx,
                 itiPermStackVars = lownedInfoPVars,
                 itiPermCtx = RL.map (const PTrans_True) lownedInfoECtx,
                 itiReturnType = lownedInfoRetType, .. }

loInfoSetPerms :: PermTransCtx ctx ps' -> RAssign (Member ctx) ps' ->
                  LOwnedInfo ps ctx -> LOwnedInfo ps' ctx
loInfoSetPerms ps' vars' (LOwnedInfo {..}) =
  LOwnedInfo { lownedInfoPCtx = ps', lownedInfoPVars = vars', ..}

loInfoSplit :: prx ps1 -> RAssign any ps2 ->
               LOwnedInfo (ps1 :++: ps2) ctx ->
               (LOwnedInfo ps1 ctx, LOwnedInfo ps2 ctx)
loInfoSplit (_ :: prx ps1) prx2 (LOwnedInfo {..}) =
  let prx1 :: Proxy ps1 = Proxy
      (ps1, ps2) = RL.split prx1 prx2 lownedInfoPCtx
      (vars1, vars2) = RL.split prx1 prx2 lownedInfoPVars in
  (LOwnedInfo { lownedInfoPCtx = ps1, lownedInfoPVars = vars1, .. },
   LOwnedInfo { lownedInfoPCtx = ps2, lownedInfoPVars = vars2, .. })

loInfoAppend :: LOwnedInfo ps1 ctx -> LOwnedInfo ps2 ctx ->
                LOwnedInfo (ps1 :++: ps2) ctx
loInfoAppend info1 info2 =
  LOwnedInfo { lownedInfoECtx = lownedInfoECtx info1
             , lownedInfoPCtx =
                 RL.append (lownedInfoPCtx info1) (lownedInfoPCtx info2)
             , lownedInfoPVars =
                 RL.append (lownedInfoPVars info1) (lownedInfoPVars info2)
             , lownedInfoEvType = lownedInfoEvType info1
             , lownedInfoRetType = lownedInfoRetType info1 }

extLOwnedInfoExt :: ExprCtxExt ctx1 ctx2 -> LOwnedInfo ps ctx1 ->
                    LOwnedInfo ps ctx2
extLOwnedInfoExt cext@(ExprCtxExt ectx3) (LOwnedInfo {..}) =
  LOwnedInfo { lownedInfoECtx = RL.append lownedInfoECtx ectx3,
               lownedInfoPCtx = extPermTransCtxExt cext lownedInfoPCtx,
               lownedInfoPVars = RL.map (weakenMemberR ectx3) lownedInfoPVars,
               .. }


-- | An 'LOwnedTransM' is a form of parameterized continuation-state monad
-- similar to the construct in GenMonad.hs. A computation of this type returns
-- an @a@ while also mapping from permission stack @ps_in@, represented as an
-- 'LOwnedInfo', to permission stack @ps_out@. The additional complexity here is
-- that the expression context @ctx@ can change during computation, and that
-- type argument parameterizes the 'LOwnedInfo' structure. Specifically, the
-- 'LOwnedInfo' structure for @ps_in@ can be relative to any context @ctx_in@
-- that extends type argument @ctx@, where the extension is chosen by the caller
-- / context outside the computation. The computation itself can then choose the
-- extended context @ctx_out@ extending @ctx_in@ to be used for the 'LOwnedInfo'
-- structure for @ps_out@.
newtype LOwnedTransM ps_in ps_out ctx a =
  LOwnedTransM {
  runLOwnedTransM ::
      forall ctx_in. ExprCtxExt ctx ctx_in -> LOwnedInfo ps_in ctx_in ->
      (forall ctx_out. ExprCtxExt ctx_in ctx_out -> LOwnedInfo ps_out ctx_out ->
       a -> OpenTerm) ->
      OpenTerm }

-- | The bind operation for 'LOwnedTransM'
(>>>=) :: LOwnedTransM ps_in ps' ctx a -> (a -> LOwnedTransM ps' ps_out ctx b) ->
          LOwnedTransM ps_in ps_out ctx b
m >>>= f = LOwnedTransM $ \cext s1 k ->
  runLOwnedTransM m cext s1 $ \cext' s2 x ->
  runLOwnedTransM (f x) (transExprCtxExt cext cext') s2 $ \cext'' ->
  k (transExprCtxExt cext' cext'')

-- | The bind operation for 'LOwnedTransM' that throws away the first value
(>>>) :: LOwnedTransM ps_in ps' ctx a -> LOwnedTransM ps' ps_out ctx b ->
         LOwnedTransM ps_in ps_out ctx b
m1 >>> m2 = m1 >>>= \_ -> m2

instance Functor (LOwnedTransM ps_in ps_out ctx) where
  fmap f m = m >>>= \x -> return (f x)

instance Applicative (LOwnedTransM ps ps ctx) where
  pure x = LOwnedTransM $ \_ s k -> k reflExprCtxExt s x
  (<*>) = Monad.ap

instance Monad (LOwnedTransM ps ps ctx) where
  (>>=) = (>>>=)

-- | Set the output permission stack to @ps_out@
gput :: LOwnedInfo ps_out ctx -> LOwnedTransM ps_in ps_out ctx ()
gput loInfo =
  LOwnedTransM $ \cext _ k ->
  k reflExprCtxExt (extLOwnedInfoExt cext loInfo) ()

{-
data ExtLOwnedInfo ps ctx where
  ExtLOwnedInfo :: ExprCtxExt ctx ctx' -> LOwnedInfo ps ctx' ->
                   ExtLOwnedInfo ps ctx

instance ps_in ~ ps_out =>
         MonadState (ExtLOwnedInfo ps_in ctx) (LOwnedTransM ps_in ps_out ctx) where
  get = LOwnedTransM $ \cext s k -> k reflExprCtxExt s (ExtLOwnedInfo cext s)
  put = gput
-}

-- | Get the current permission stack, with the additional complexity that it
-- could be in an extended expression context @ctx'@
ggetting :: (forall ctx'. ExprCtxExt ctx ctx' ->
             LOwnedInfo ps_in ctx' -> LOwnedTransM ps_in ps_out ctx' a) ->
            LOwnedTransM ps_in ps_out ctx a
ggetting f =
  LOwnedTransM $ \cext s k ->
  runLOwnedTransM (f cext s) reflExprCtxExt s $ \cext' ->
  k cext'

-- | Modify the current permission stack relative to its extended expression
-- context @ctx'@
gmodify :: (forall ctx'. ExprCtxExt ctx ctx' ->
            LOwnedInfo ps_in ctx' -> LOwnedInfo ps_out ctx') ->
           LOwnedTransM ps_in ps_out ctx ()
gmodify f = ggetting $ \cext loInfo -> gput (f cext loInfo)

-- | Extend the expression context of an 'LOwnedTransM' computation
extLOwnedTransM :: ExprCtxExt ctx ctx' -> LOwnedTransM ps_in ps_out ctx a ->
                   LOwnedTransM ps_in ps_out ctx' a
extLOwnedTransM cext m =
  LOwnedTransM $ \cext' -> runLOwnedTransM m (transExprCtxExt cext cext')

-- | A representation of the translation of an @lowned@ permission as a
-- transformer from a permission stack @ps_in@ to a permission stack @ps_out@
type LOwnedTransTerm ctx ps_in ps_out = LOwnedTransM ps_in ps_out ctx ()

-- | Build an 'LOwnedTransTerm' transformer from @ps_in@ to @ps_out@ relative to
-- context @ctx@ that applies a single SAW core term of type @FunIx T@ as the
-- transformation, where type description @T@ is defined by 'arrowDescTrans'.
mkLOwnedTransTermFromTerm :: DescPermsTpTrans ctx ps_in ->
                             DescPermsTpTrans ctx ps_out ->
                             RAssign (Member ctx) ps_out -> OpenTerm ->
                             LOwnedTransTerm ctx ps_in ps_out
mkLOwnedTransTermFromTerm trans_in trans_out vars_out t =
  LOwnedTransM $ \(ExprCtxExt ctx') loInfo k ->
  let ev = lownedInfoEvType loInfo
      d = arrowDescTrans trans_in trans_out
      t_app = callSOpenTerm ev d t (transTerms $ lownedInfoPCtx loInfo)
      t_ret_trans = tupleTypeTrans $ descTypeTrans trans_out
      t_ret_tp = typeTransTupleType $ descTypeTrans trans_out in
  bindSOpenTerm ev t_ret_tp (lownedInfoRetType loInfo) t_app $
  lambdaOpenTerm "lowned_ret" t_ret_tp $ \lowned_ret ->
  let pctx_out' =
        extPermTransCtxMulti ctx' $ typeTransF t_ret_trans [lowned_ret]
      vars_out' = RL.map (weakenMemberR ctx') vars_out in
  k reflExprCtxExt (loInfoSetPerms pctx_out' vars_out' loInfo) ()


-- | Build the SAW core term for the function of type @specFun T@ for the
-- transformation from @ps_in@ to @ps_out@ represented by an 'LOwnedTransTerm'
lownedTransTermFun :: EventType -> ExprTransCtx ctx ->
                      RAssign (Member ctx) ps_in ->
                      DescPermsTpTrans ctx ps_in ->
                      DescPermsTpTrans ctx ps_out ->
                      LOwnedTransTerm ctx ps_in ps_out -> OpenTerm
lownedTransTermFun ev ectx vars_in tps_in tps_out t =
  lambdaTrans "p" (descTypeTrans tps_in) $ \ps_in ->
  let ret_tp = typeTransTupleType $ descTypeTrans tps_out in
  let loInfo =
        LOwnedInfo { lownedInfoECtx = ectx,
                     lownedInfoPCtx = ps_in, lownedInfoPVars = vars_in,
                     lownedInfoEvType = ev, lownedInfoRetType = ret_tp } in
  runLOwnedTransM t reflExprCtxExt loInfo $ \_ loInfo_out () ->
  transTupleTerm (lownedInfoPCtx loInfo_out)

-- | Extend the expression context of an 'LOwnedTransTerm'
extLOwnedTransTerm :: ExprTransCtx ctx2 ->
                      LOwnedTransTerm ctx1 ps_in ps_out ->
                      LOwnedTransTerm (ctx1 :++: ctx2) ps_in ps_out
extLOwnedTransTerm ectx2 = extLOwnedTransM (ExprCtxExt ectx2)

-- | Build an 'LOwnedTransTerm' that acts as the identity function on the SAW
-- core terms in the permissions, using the supplied permission translation for
-- the output permissions, which must have the same SAW core terms as the input
-- permissions (or the identity translation would be ill-typed)
idLOwnedTransTerm :: DescPermsTpTrans ctx ps_out ->
                     RAssign (Member ctx) ps_out ->
                     LOwnedTransTerm ctx ps_in ps_out
idLOwnedTransTerm dtr_out vars_out =
  gmodify $ \(ExprCtxExt ctx') loInfo ->
  loInfo { lownedInfoPVars = RL.map (weakenMemberR ctx') vars_out,
           lownedInfoPCtx =
             descTypeTransF (fmap (extPermTransCtxMulti ctx') dtr_out)
             (transTerms (lownedInfoPCtx loInfo)) }

weakenLOwnedTransTerm :: Desc1PermTpTrans ctx tp ->
                         LOwnedTransTerm ctx ps_in ps_out ->
                         LOwnedTransTerm ctx (ps_in :> tp) (ps_out :> tp)
weakenLOwnedTransTerm tptr t =
  ggetting $ \cext info_top ->
  let (info_ps_in, info_tp) = loInfoSplit Proxy (MNil :>: Proxy) info_top in
  gput info_ps_in >>>
  extLOwnedTransM cext t >>>
  gmodify (\cext' info' ->
            loInfoAppend info' $ extLOwnedInfoExt cext' $
            info_tp { lownedInfoPCtx =
                        (MNil :>:) $ extPermTransExt cext $ descTypeTransF tptr $
                        transTerms $ lownedInfoPCtx info_tp })

-- | Combine 'LOwnedTransTerm's for the 'SImpl_MapLifetime' rule
mapLtLOwnedTransTerm ::
  prx ps_extra1 -> RAssign any1 ps_extra2 -> RAssign any2 ps_in ->
  LOwnedTransTerm ctx (ps_extra1 :++: ps_in) ps_mid ->
  LOwnedTransTerm ctx (ps_extra2 :++: ps_mid) ps_out ->
  LOwnedTransTerm ctx ((ps_extra1 :++: ps_extra2) :++: ps_in) ps_out
mapLtLOwnedTransTerm prx_extra1 prx_extra2 prx_in t1 t2 =
  ggetting $ \cext info_extra_in ->
  let (info_extra, info_in) = loInfoSplit Proxy prx_in info_extra_in
      (info_extra1, info_extra2) =
        loInfoSplit prx_extra1 prx_extra2 info_extra in
  gput (loInfoAppend info_extra1 info_in) >>>
  extLOwnedTransM cext t1 >>>
  gmodify (\cext' info_out ->
            loInfoAppend (extLOwnedInfoExt cext' info_extra2) info_out) >>>
  extLOwnedTransM cext t2

-- | The translation of an @lowned@ permission
data LOwnedTrans ctx ps_extra ps_in ps_out =
  LOwnedTrans {
  lotrEvType :: EventType,
  lotrECtx :: ExprTransCtx ctx,
  lotrPsExtra :: PermTransCtx ctx ps_extra,
  lotrVarsExtra :: RAssign (Member ctx) ps_extra,
  lotrTpTransIn :: DescPermsTpTrans ctx ps_in,
  lotrTpTransOut :: DescPermsTpTrans ctx ps_out,
  lotrTpTransExtra :: DescPermsTpTrans ctx ps_extra,
  lotrTerm :: LOwnedTransTerm ctx (ps_extra :++: ps_in) ps_out }

-- | Build an initial 'LOwnedTrans' with an empty @ps_extra@
mkLOwnedTrans :: EventType -> ExprTransCtx ctx -> DescPermsTpTrans ctx ps_in ->
                 DescPermsTpTrans ctx ps_out -> RAssign (Member ctx) ps_out ->
                 OpenTerm -> LOwnedTrans ctx RNil ps_in ps_out
mkLOwnedTrans ev ectx tps_in tps_out vars_out t =
  LOwnedTrans ev ectx MNil MNil tps_in tps_out (pure MNil)
  (mkLOwnedTransTermFromTerm (preNilDescPermsTpTrans tps_in) tps_out vars_out t)

-- | Build an initial 'LOwnedTrans' with an empty @ps_extra@ and an identity
-- function on SAW core terms
mkLOwnedTransId :: EventType -> ExprTransCtx ctx -> DescPermsTpTrans ctx ps ->
                   DescPermsTpTrans ctx ps -> RAssign (Member ctx) ps ->
                   LOwnedTrans ctx RNil ps ps
mkLOwnedTransId ev ectx tps_in tps_out vars_out =
  LOwnedTrans ev ectx MNil MNil tps_in tps_out (pure MNil)
  (idLOwnedTransTerm tps_out vars_out)

-- | Extend the context of an 'LOwnedTrans'
extLOwnedTransMulti :: ExprTransCtx ctx2 ->
                       LOwnedTrans ctx1 ps_extra ps_in ps_out ->
                       LOwnedTrans (ctx1 :++: ctx2) ps_extra ps_in ps_out
extLOwnedTransMulti ctx2 (LOwnedTrans ev ectx ps_extra vars_extra ptrans_in
                          ptrans_out ptrans_extra t) =
  LOwnedTrans
  ev (RL.append ectx ctx2) (extPermTransCtxMulti ctx2 ps_extra)
  (RL.map (weakenMemberR ctx2) vars_extra)
  (fmap (extPermTransCtxMulti ctx2) ptrans_in)
  (fmap (extPermTransCtxMulti ctx2) ptrans_out)
  (fmap (extPermTransCtxMulti ctx2) ptrans_extra)
  (extLOwnedTransTerm ctx2 t)

-- | Weaken an 'LOwnedTrans' by adding one more permission to the input and
-- output permission lists. The SAW core terms taken in for the new input
-- permission are used as the SAW core terms for the new output permission, so
-- the weakening acts as a form of identity function between these new
-- permissions. The new input and output permissions can be different, but they
-- should translate to the same list of SAW core types, or otherwise the new
-- transformation would be ill-typed.
weakenLOwnedTrans ::
  Desc1PermTpTrans ctx tp ->
  Desc1PermTpTrans ctx tp ->
  LOwnedTrans ctx ps_extra ps_in ps_out ->
  LOwnedTrans ctx ps_extra (ps_in :> tp) (ps_out :> tp)
weakenLOwnedTrans tp_in tp_out (LOwnedTrans {..}) =
  LOwnedTrans { lotrTpTransIn = liftA2 (:>:) lotrTpTransIn tp_in,
                lotrTpTransOut = liftA2 (:>:) lotrTpTransOut tp_out,
                lotrTerm = weakenLOwnedTransTerm tp_out lotrTerm, .. }

-- | Convert an 'LOwnedTrans' to a closure that gets added to the list of
-- closures for the current spec definition, and partially apply that closure to
-- the current expression context and its @ps_extra@ terms
lownedTransTerm :: Mb ctx (ExprPerms ps_in) ->
                   LOwnedTrans ctx ps_extra ps_in ps_out -> OpenTerm
lownedTransTerm (mbExprPermsMembers -> Just vars_in) lotr =
  let tps_extra_in =
        liftA2 RL.append (lotrTpTransExtra lotr) (lotrTpTransIn lotr)
      vars_extra_in = RL.append (lotrVarsExtra lotr) vars_in
      d = arrowDescTrans tps_extra_in (lotrTpTransOut lotr) in
  applyGlobalOpenTerm "Prelude.LambdaS"
  [evTypeTerm (lotrEvType lotr), d,
   lownedTransTermFun (lotrEvType lotr) (lotrECtx lotr)
   vars_extra_in tps_extra_in (lotrTpTransOut lotr) (lotrTerm lotr)]
lownedTransTerm _ _ =
  failOpenTerm "FIXME HERE NOW: write this error message"

-- | Apply the 'SImpl_MapLifetime' rule to an 'LOwnedTrans'
mapLtLOwnedTrans ::
  PermTransCtx ctx ps1 -> RAssign (Member ctx) ps1 ->
  DescPermsTpTrans ctx ps1 ->
  PermTransCtx ctx ps2 -> RAssign (Member ctx) ps2 ->
  DescPermsTpTrans ctx ps2 ->
  RAssign any ps_in' -> DescPermsTpTrans ctx ps_in' ->
  DescPermsTpTrans ctx ps_out' ->
  LOwnedTransTerm ctx (ps1 :++: ps_in') ps_in ->
  LOwnedTransTerm ctx (ps2 :++: ps_out) ps_out' ->
  LOwnedTrans ctx ps_extra ps_in ps_out ->
  LOwnedTrans ctx ((ps1 :++: ps_extra) :++: ps2) ps_in' ps_out'
mapLtLOwnedTrans pctx1 vars1 dtr1 pctx2 vars2 dtr2
  prx_in' dtr_in' dtr_out' t1 t2
  (LOwnedTrans {..}) =
  LOwnedTrans
  { lotrEvType = lotrEvType
  , lotrPsExtra = RL.append (RL.append pctx1 lotrPsExtra) pctx2
  , lotrVarsExtra = RL.append (RL.append vars1 lotrVarsExtra) vars2
  , lotrTpTransIn = dtr_in' , lotrTpTransOut = dtr_out'
  , lotrTpTransExtra =
      liftA2 RL.append (liftA2 RL.append dtr1 lotrTpTransExtra) dtr2
  , lotrTerm =
      mapLtLOwnedTransTerm (RL.append pctx1 lotrPsExtra) pctx2 prx_in'
      (mapLtLOwnedTransTerm pctx1 lotrPsExtra prx_in' t1 lotrTerm)
      t2
  }


----------------------------------------------------------------------
-- * Translating Permissions to Types
----------------------------------------------------------------------

-- | Make a type translation of a 'BVProp' from it and its pure type
mkBVPropTrans :: Mb ctx (BVProp w) -> OpenTerm ->
                 TypeTrans (BVPropTrans ctx w)
mkBVPropTrans prop tp = mkTypeTrans1 tp $ BVPropTrans prop

instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (BVProp w) (TypeTrans (BVPropTrans ctx w)) where
  translate prop = case mbMatch prop of
    [nuMP| BVProp_Eq e1 e2 |] ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         return $ mkBVPropTrans prop $
           dataTypeOpenTerm "Prelude.Eq"
           [applyOpenTermMulti (globalOpenTerm "Prelude.Vec")
            [natOpenTerm w, globalOpenTerm "Prelude.Bool"],
            t1, t2]

    [nuMP| BVProp_Neq _ _ |] ->
      -- NOTE: we don't need a proof object for not equal proofs, because we don't
      -- actually use them for anything, but it is easier to just have all BVProps
      -- be represented as something, so we use the unit type
      return $ mkBVPropTrans prop unitTypeOpenTerm

    [nuMP| BVProp_ULt e1 e2 |] ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         return $ mkBVPropTrans prop $
           dataTypeOpenTerm "Prelude.Eq"
           [globalOpenTerm "Prelude.Bool",
            applyOpenTermMulti (globalOpenTerm "Prelude.bvult")
            [natOpenTerm w, t1, t2], trueOpenTerm]

    [nuMP| BVProp_ULeq e1 e2 |] ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         return $ mkBVPropTrans prop $
           dataTypeOpenTerm "Prelude.Eq"
           [globalOpenTerm "Prelude.Bool",
            applyOpenTermMulti (globalOpenTerm "Prelude.bvule")
            [natOpenTerm w, t1, t2], trueOpenTerm]

    [nuMP| BVProp_ULeq_Diff e1 e2 e3 |] ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         t3 <- translate1 e3
         return $ mkBVPropTrans prop $
           dataTypeOpenTerm "Prelude.Eq"
           [globalOpenTerm "Prelude.Bool",
            applyOpenTermMulti (globalOpenTerm "Prelude.bvule")
            [natOpenTerm w, t1,
             applyOpenTermMulti (globalOpenTerm "Prelude.bvSub")
              [natOpenTerm w, t2, t3]],
            trueOpenTerm]

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
         case lookupNamedPerm env (mbLift npn) of
           Just (NamedPerm_Opaque op) ->
             error "FIXME HERE NOWNOW: translate opaque named permissions"
             {-
             exprCtxPureTypeTerms <$> translate args >>= \case
             Just args_exprs ->
               return $ mkPermTypeTrans1 p $ TypeDescPure $
               applyGlobalOpenTerm (opaquePermTrans op) args_exprs
             Nothing ->
               panic "translate"
               ["Heapster cannot yet handle opaque permissions over impure types"] -}
           Just (NamedPerm_Rec rp) ->
             error "FIXME HERE NOWNOW: translate recursive named permissions"
             {-
             exprCtxPureTypeTerms <$> translate args >>= \case
             Just args_exprs ->
               return $ mkPermTypeTrans1 p $ TypeDescPure $
               applyOpenTermMulti (globalOpenTerm $ recPermTransType rp) args_exprs
             Nothing ->
               panic "translate"
               ["Heapster cannot yet handle recursive permissions over impure types"] -}
           Just (NamedPerm_Defined dp) ->
             fmap (PTrans_Defined (mbLift npn) args off) <$>
             translate (mbMap2 (unfoldDefinedPerm dp) args off)
           Nothing -> panic "translate" ["Unknown permission name!"]
    [nuMP| ValPerm_Conj ps |] ->
      fmap PTrans_Conj <$> listTypeTrans <$> translate ps
    [nuMP| ValPerm_Var x _ |] ->
      do (_, tps) <- unETransPerm <$> translate x
         return $ mkTypeTrans1 (tupleOfTypes tps) (PTrans_Term p)
    [nuMP| ValPerm_False |] ->
      return $ mkPermTypeTrans1 p $ globalOpenTerm "Prelude.FalseProp"


instance TranslateDescs (ValuePerm a) where
  translateDescs mb_p = error "FIXME HERE NOWNOW"


instance TransInfo info =>
         Translate info ctx (AtomicPerm a) (TypeTrans
                                            (AtomicPermTrans ctx a)) where
  translate mb_p = case mbMatch mb_p of
    [nuMP| Perm_LLVMField fld |] ->
      fmap (APTrans_LLVMField fld) <$> translate (fmap llvmFieldContents fld)

    [nuMP| Perm_LLVMArray ap |] ->
      fmap APTrans_LLVMArray <$> translate ap

    [nuMP| Perm_LLVMBlock bp |] ->
      do (_, tps) <- unETransShape <$> translate (fmap llvmBlockShape bp)
         return $ TypeTrans tps (APTrans_LLVMBlock bp)

    [nuMP| Perm_LLVMFree e |] ->
      return $ mkTypeTrans0 $ APTrans_LLVMFree e
    [nuMP| Perm_LLVMFunPtr tp p |] ->
      translate p >>= \tp_ptrans ->
      return $ fmap (APTrans_LLVMFunPtr $ mbLift tp) tp_ptrans
    [nuMP| Perm_IsLLVMPtr |] ->
      return $ mkTypeTrans0 APTrans_IsLLVMPtr
    [nuMP| Perm_LLVMBlockShape sh |] ->
      do (_, tps) <- unETransShape <$> translate sh
         return $ TypeTrans tps (APTrans_LLVMBlockShape sh)
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
         return $ fmap (\case
                           (PTrans_Term _ t) ->
                             APTrans_NamedConj (mbLift npn) args off t
                           _ -> error "translateSimplImpl: Perm_NamedConj") ptrans
    [nuMP| Perm_LLVMFrame fp |] ->
      return $ mkTypeTrans0 $ APTrans_LLVMFrame fp
    [nuMP| Perm_LOwned ls tps_in tps_out ps_in ps_out |] ->
      case mbExprPermsMembers ps_out of
        Just vars_out ->
          do ev <- infoEvType <$> ask
             ectx <- infoCtx <$> ask
             dtr_in <- tpTransM $ translateDescType ps_in
             dtr_out <- tpTransM $ translateDescType ps_out
             let d = arrowDescTrans dtr_in dtr_out
             return $ mkTypeTrans1 (funIxTypeOpenTerm d) $ \t ->
               (APTrans_LOwned ls (mbLift tps_in) (mbLift tps_out) ps_in ps_out $
                mkLOwnedTrans ev ectx dtr_in dtr_out vars_out t)
        Nothing ->
          error "FIXME HERE NOWNOW: handle this error!"
    [nuMP| Perm_LOwnedSimple tps lops |] ->
      return $ mkTypeTrans0 $ APTrans_LOwnedSimple (mbLift tps) lops
    [nuMP| Perm_LCurrent l |] ->
      return $ mkTypeTrans0 $ APTrans_LCurrent l
    [nuMP| Perm_LFinished |] ->
      return $ mkTypeTrans0 APTrans_LFinished
    [nuMP| Perm_Struct ps |] ->
      fmap APTrans_Struct <$> translate ps
    [nuMP| Perm_Fun fun_perm |] ->
      do tp_desc <- descTransM (translateDesc fun_perm)
         ev <- infoEvType <$> ask
         return $
           mkTypeTrans1 (funIxTypeOpenTerm tp_desc)
           (APTrans_Fun fun_perm . FunTransIx ev tp_desc)
    [nuMP| Perm_BVProp prop |] ->
      fmap APTrans_BVProp <$> translate prop
    [nuMP| Perm_Any |] -> return $ mkTypeTrans0 APTrans_Any


instance TranslateDescs (AtomicPerm a) where
  translateDescs mb_p = error "FIXME HERE NOWNOW"


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
     -- To translate mb_ap to an element type, we form the block permission for
     -- the first cell of the array and translate that to a TypeTrans
     elem_tp_trans <- translate $ mbMapCl $(mkClosed [| Perm_LLVMBlock .
                                                      llvmArrayPermHead |]) mb_ap
     let elem_tp = typeTransTupleType elem_tp_trans
     len_term <- translate1 $ mbLLVMArrayLen mb_ap
     {-
     bs_trans <-
       listTypeTrans <$> mapM (translateLLVMArrayBorrow ap) (mbList bs) -}
     let arr_tp = bvVecTypeOpenTerm w_term len_term elem_tp
     return (w_term, len_term, elem_tp,
             mkTypeTrans1 arr_tp
             ({- flip $ -} LLVMArrayPermTrans mb_ap len_term elem_tp_trans
                           {- <*> bs_trans -}))

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

instance TranslateDescs (ValuePerms ps) where
  translateDescs mb_ps = case mbMatch mb_ps of
    [nuMP| ValPerms_Nil |] -> return []
    [nuMP| ValPerms_Cons ps p |] ->
      (++) <$> translateDescs ps <*> translateDescs p


-- Translate a DistPerms by translating its corresponding ValuePerms
instance TransInfo info =>
         Translate info ctx (DistPerms ps) (TypeTrans
                                            (PermTransCtx ctx ps)) where
  translate = translate . mbDistPermsToValuePerms

instance TranslateDescs (DistPerms ps) where
  translateDescs = translateDescs . mbDistPermsToValuePerms


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

instance TranslateDescs (ExprPerms ps) where
  translateDescs mb_eps
    | Just mb_ps <- mbExprPermsToValuePerms mb_eps = translateDescs mb_ps
  translateDescs mb_ps =
    error ("Translating expression permissions that could not be converted " ++
           "to variable permissions:" ++ permPrettyString emptyPPInfo mb_ps)


-- Translate a FunPerm to a pi-abstraction (FIXME HERE NOW: document translation)
instance TransInfo info =>
         Translate info ctx (FunPerm ghosts args gouts ret) OpenTerm where
  translate (mbMatch ->
             [nuMP| FunPerm ghosts args gouts ret perms_in perms_out |]) =
    let tops = appendCruCtx (mbLift ghosts) (mbLift args)
        tops_prxs = cruCtxProxies tops
        rets = CruCtxCons (mbLift gouts) (mbLift ret)
        rets_prxs = cruCtxProxies rets in
    (RL.map (const Proxy) <$> infoCtx <$> ask) >>= \ctx ->
    case RL.appendAssoc ctx tops_prxs rets_prxs of
      Refl ->
        piExprCtxApp tops $
        do tptrans_in <- translate (mbCombine tops_prxs perms_in)
           piTransM "p" tptrans_in $ \_ ->
             translateRetType rets (mbCombine
                                    (RL.append tops_prxs rets_prxs) perms_out)

instance TranslateDescs (FunPerm ghosts args gouts ret) where
  translateDescs (mbMatch ->
                  [nuMP| FunPerm ghosts args gouts ret perms_in perms_out |]) =
    let tops = appendCruCtx (mbLift ghosts) (mbLift args)
        tops_prxs = cruCtxProxies tops
        rets = CruCtxCons (mbLift gouts) (mbLift ret)
        rets_prxs = cruCtxProxies rets in
    (dtiProxies <$> ask) >>= \ctx ->
    case RL.appendAssoc ctx tops_prxs rets_prxs of
      Refl ->
        inExtCtxDescTransM tops $ \kdescs ->
        (\d -> [d]) <$> piTpDescMulti kdescs <$>
        do ds_in <- translateDescs (mbCombine tops_prxs perms_in)
           arrowTpDescMulti ds_in <$>
             translateRetTpDesc rets (mbCombine
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

-- | Build the return type for a function, as a right-nested sigma type over the
-- translations of the types in @rets@, with the tuple of the translations of
-- the returned permissions to types
translateRetType :: TransInfo info => CruCtx rets ->
                    Mb (ctx :++: rets) (ValuePerms ps) ->
                    TransM info ctx OpenTerm
translateRetType rets ret_perms =
  do tptrans <- translateClosed rets
     sigmaTypeTransM "ret" tptrans $ \ectx ->
       inExtMultiTransM ectx (translate ret_perms)

-- | Build the type description of the type returned by 'translateRetType'
translateRetTpDesc :: CruCtx rets ->
                      Mb (ctx :++: rets) (ValuePerms ps) ->
                      DescTransM ctx OpenTerm
translateRetTpDesc rets ret_perms =
  inExtCtxDescTransM rets $ \kdescs ->
  sigmaTpDescMulti kdescs <$> translateDesc ret_perms

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

-- | A mapping from a block entrypoint to a corresponding SAW function index
-- (including the type description @T@ and the SAW core term of type @FunIx T@)
-- that is bound to its translation if it has one: only those entrypoints marked
-- as the heads of strongly-connect components have translations as recursive
-- functions
data TypedEntryTrans ext blocks tops rets args ghosts =
  TypedEntryTrans { typedEntryTransEntry ::
                      TypedEntry TransPhase ext blocks tops rets args ghosts,
                    typedEntryTransClos :: Maybe (OpenTerm, OpenTerm) }

-- | A mapping from a block to the SAW functions for each entrypoint
data TypedBlockTrans ext blocks tops rets args =
  TypedBlockTrans { typedBlockTransEntries ::
                      [Some (TypedEntryTrans ext blocks tops rets args)] }

-- | A mapping from all block entrypoints to their SAW translations
type TypedBlockMapTrans ext blocks tops rets =
  RAssign (TypedBlockTrans ext blocks tops rets) blocks

-- | A dummy 'TypedBlockMapTrans' with no blocks
emptyTypedBlockMapTrans :: TypedBlockMapTrans () RNil RNil RNil
emptyTypedBlockMapTrans = MNil

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
    itiChecksFlag :: ChecksFlag
  }

instance TransInfo (ImpTransInfo ext blocks tops rets ps) where
  infoCtx = itiExprCtx
  infoEnv = itiPermEnv
  infoChecksFlag = itiChecksFlag
  extTransInfo etrans (ImpTransInfo {..}) =
    ImpTransInfo
    { itiExprCtx = itiExprCtx :>: etrans
    , itiPermCtx = consPermTransCtx (extPermTransCtx etrans itiPermCtx) PTrans_True
    , itiPermStack = extPermTransCtx etrans itiPermStack
    , itiPermStackVars = RL.map Member_Step itiPermStackVars
    , .. }

-- | The monad for impure translations
type ImpTransM ext blocks tops rets ps =
  TransM (ImpTransInfo ext blocks tops rets ps)

-- | Run an 'ImpTransM' computation in a 'TypeTransM' context (FIXME: better
-- documentation; e.g., the pctx starts on top of the stack)
impTransM :: forall ctx ps ext blocks tops rets a.
             RAssign (Member ctx) ps -> PermTransCtx ctx ps ->
             TypedBlockMapTrans ext blocks tops rets -> OpenTerm ->
             ImpTransM ext blocks tops rets ps ctx a ->
             TypeTransM ctx a
impTransM pvars pctx mapTrans retType =
  withInfoM $ \(TypeTransInfo ectx penv pflag) ->
  ImpTransInfo { itiExprCtx = ectx,
                 itiPermCtx = RL.map (const $ PTrans_True) ectx,
                 itiPermStack = pctx,
                 itiPermStackVars = pvars,
                 itiPermEnv = penv,
                 itiBlockMapTrans = mapTrans,
                 itiReturnType = retType,
                 itiChecksFlag = pflag
               }

-- | Run an inner 'ImpTransM' computation that does not use the block map
emptyBlocksImpTransM :: ImpTransM () RNil RNil RNil ps ctx a ->
                        ImpTransM ext blocks tops rets ps ctx a
emptyBlocksImpTransM =
  withInfoM (\(ImpTransInfo {..}) ->
              ImpTransInfo { itiBlockMapTrans = emptyTypedBlockMapTrans, .. })

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

-- | Build a term @bindS m k@ with the given @m@ of type @m_tp@ and where @k@
-- is build as a lambda with the given variable name and body
bindSpecMTransM :: OpenTerm -> TypeTrans tr -> String ->
                   (tr -> ImpTransM ext blocks tops rets ps ctx OpenTerm) ->
                   ImpTransM ext blocks tops rets ps ctx OpenTerm
bindSpecMTransM m m_tptrans str f =
  do ev <- infoEvType <$> ask
     ret_tp <- returnTypeM
     k_tm <- lambdaTransM str m_tptrans f
     let m_tp = typeTransTupleType m_tptrans
     return $ bindSOpenTerm ev m_tp ret_tp m k_tm

-- | The current non-monadic return type
returnTypeM :: ImpTransM ext blocks tops rets ps_out ctx OpenTerm
returnTypeM = itiReturnType <$> ask

-- | Build the monadic return type @SpecM E ret@, where @ret@ is the current
-- return type in 'itiReturnType'
compReturnTypeM :: ImpTransM ext blocks tops rets ps_out ctx OpenTerm
compReturnTypeM =
  do ev <- infoEvType <$> ask
     ret_tp <- returnTypeM
     return $ applyGlobalOpenTerm "Prelude.SpecM" [evTypeTerm ev, ret_tp]

-- | Like 'compReturnTypeM' but build a 'TypeTrans'
compReturnTypeTransM ::
  ImpTransM ext blocks tops rets ps_out ctx (TypeTrans OpenTerm)
compReturnTypeTransM = openTermTypeTrans <$> compReturnTypeM

-- | Build an @errorS@ computation with the given error message
mkErrorComp :: String -> ImpTransM ext blocks tops rets ps_out ctx OpenTerm
mkErrorComp msg =
  do ev <- infoEvType <$> ask
     ret_tp <- returnTypeM
     return $ errorSOpenTerm ev ret_tp msg

-- | The typeclass for the implication translation of a functor at any
-- permission set inside any binding to an 'OpenTerm'
class NuMatchingAny1 f => ImplTranslateF f ext blocks tops rets where
  translateF :: Mb ctx (f ps) -> ImpTransM ext blocks tops rets ps ctx OpenTerm


----------------------------------------------------------------------
-- * Translating Permission Implication Constructs
----------------------------------------------------------------------

-- | A failure continuation represents any catch that is around the current
-- 'PermImpl', and can either be a term to jump to / call (meaning that there is
-- a catch) or an error message (meaning there is not)
data ImplFailCont
     -- | A continuation that calls a term on failure
  = ImplFailContTerm OpenTerm
    -- | An error message to print on failure, along with the event type needed
    -- to build an @errorS@ spec term
  | ImplFailContMsg EventType String

-- | Convert an 'ImplFailCont' to an error, which should have the given type
implFailContTerm :: OpenTerm -> ImplFailCont -> OpenTerm
implFailContTerm _ (ImplFailContTerm t) = t
implFailContTerm tp (ImplFailContMsg ev msg) = errorSOpenTerm ev tp msg

-- | Convert an 'ImplFailCont' to an error as in 'implFailContTerm', but use an
-- alternate error message in the case of 'ImplFailContMsg'
implFailAltContTerm :: OpenTerm -> String -> ImplFailCont -> OpenTerm
implFailAltContTerm _ _ (ImplFailContTerm t) = t
implFailAltContTerm tp msg (ImplFailContMsg ev _) = errorSOpenTerm ev tp msg

-- | The type of terms use to translation permission implications, which can
-- contain calls to the current failure continuation
newtype PImplTerm ext blocks tops rets ps ctx =
  PImplTerm { popPImplTerm ::
                ImplFailCont -> ImpTransM ext blocks tops rets ps ctx OpenTerm }
  deriving OpenTermLike

-- | Build a 'PImplTerm' from the first 'PImplTerm' that uses the second as the
-- failure continuation
catchPImplTerm :: PImplTerm ext blocks tops rets ps ctx ->
                  PImplTerm ext blocks tops rets ps ctx ->
                  PImplTerm ext blocks tops rets ps ctx
catchPImplTerm t t_catch =
  PImplTerm $ \k ->
  compReturnTypeM >>= \tp ->
  letTransM "catchpoint" tp (popPImplTerm t_catch k) $ \k_tm ->
  popPImplTerm t $ ImplFailContTerm k_tm

-- | The failure 'PImplTerm', which immediately calls its failure continuation
failPImplTerm :: PImplTerm ext blocks tops rets ps ctx
failPImplTerm =
  PImplTerm $ \k -> compReturnTypeM >>= \tp -> return (implFailContTerm tp k)

-- | Return the failure 'PImplTerm' like 'failPImplTerm' but use an alternate
-- error message in the case that the failure continuation is an error message
failPImplTermAlt :: String -> PImplTerm ext blocks tops rets ps ctx
failPImplTermAlt msg = PImplTerm $ \k ->
  compReturnTypeM >>= \tp ->
  return (implFailContTerm tp (case k of
                                  ImplFailContMsg ev _ -> ImplFailContMsg ev msg
                                  _ -> k))

-- | "Force" an optional 'PImplTerm' to a 'PImplTerm' by converting a 'Nothing'
-- to the 'failPImplTerm'
forcePImplTerm :: Maybe (PImplTerm ext blocks tops rets ps ctx) ->
                  PImplTerm ext blocks tops rets ps ctx
forcePImplTerm (Just t) = t
forcePImplTerm Nothing = failPImplTerm


-- | A flag to indicate whether a 'PImplTerm' calls its failure continuation
data HasFailures = HasFailures | NoFailures deriving Eq

instance Semigroup HasFailures where
  HasFailures <> _ = HasFailures
  _ <> HasFailures = HasFailures
  NoFailures <> NoFailures = NoFailures

instance Monoid HasFailures where
  mempty = NoFailures

-- | A function for translating an @r@
newtype ImpRTransFun r ext blocks tops rets ctx =
  ImpRTransFun { appImpTransFun ::
                   forall ps ctx'. CtxExt ctx ctx' -> Mb ctx' (r ps) ->
                   ImpTransM ext blocks tops rets ps ctx' OpenTerm }

extImpRTransFun :: RAssign Proxy ctx' ->
                   ImpRTransFun r ext blocks tops rets ctx ->
                   ImpRTransFun r ext blocks tops rets (ctx :++: ctx')
extImpRTransFun ctx' f =
  ImpRTransFun $ \cext mb_r ->
  appImpTransFun f (extCtxExt Proxy ctx' cext) mb_r


-- | A monad transformer that adds an 'ImpRTransFun' translation function
newtype ImpRTransFunT r ext blocks tops rets ctx m a =
  ImpRTransFunT { unImpRTransFunT ::
                    ReaderT (ImpRTransFun r ext blocks tops rets ctx) m a }
  deriving (Functor, Applicative, Monad, MonadTrans)

-- | Run an 'ImpRTransFunT' computation to get an underlying computation in @m@
runImpRTransFunT :: ImpRTransFunT r ext blocks tops rets ctx m a ->
                    ImpRTransFun r ext blocks tops rets ctx -> m a
runImpRTransFunT m = runReaderT (unImpRTransFunT m)

-- | Map the underlying computation type of an 'ImpRTransFunT'
mapImpRTransFunT :: (m a -> n b) ->
                    ImpRTransFunT r ext blocks tops rets ctx m a ->
                    ImpRTransFunT r ext blocks tops rets ctx n b
mapImpRTransFunT f = ImpRTransFunT . mapReaderT f . unImpRTransFunT

-- | The computation type for translation permission implications, which
-- includes the following effects: a 'MaybeT' for representing terms that
-- translate to errors using 'Nothing'; a 'WriterT' that tracks all the error
-- messages used in translating a term along with a 'HasFailures' flag that
-- indicates whether the returned 'PImplTerm' uses its failure continuation; and
-- an 'ImpRTransFunT' to pass along a function for translating the final @r@
-- result inside the current 'PermImpl'
type PImplTransM r ext blocks tops rets ctx =
  MaybeT (WriterT ([String], HasFailures)
          (ImpRTransFunT r ext blocks tops rets ctx Identity))

-- | Run a 'PermImplTransM' computation
runPermImplTransM ::
  PImplTransM r ext blocks tops rets ctx a ->
  ImpRTransFun r ext blocks tops rets ctx ->
  (Maybe a, ([String], HasFailures))
runPermImplTransM m rTransFun =
  runIdentity $ runImpRTransFunT (runWriterT $ runMaybeT m) rTransFun

extPermImplTransM :: RAssign Proxy ctx' ->
                     PImplTransM r ext blocks tops rets (ctx :++: ctx') a ->
                     PImplTransM r ext blocks tops rets ctx a
extPermImplTransM ctx' m =
  pimplRTransFunM >>= \rtransFun ->
  MaybeT $ WriterT $ return $ runPermImplTransM m $ extImpRTransFun ctx' rtransFun

{-
extPermImplTransM :: ExprTransCtx ctx' ->
                     PImplTransM r ext blocks tops rets ps (ctx :++: ctx') a ->
                     PImplTransM r ext blocks tops rets ps ctx a
extPermImplTransM ctx' m =
  pimplRTransFunM >>= \rtransFun ->
  MaybeT $ WriterT $ return $ runPermImplTransM m $ extImpRTransFun ctx' rtransFun

extPermImplTransMTerm :: CruCtx ctx' ->
                         PImplTransMTerm r ext blocks tops rets ps (ctx :++: ctx') ->
                         PImplTransMTerm r ext blocks tops rets ps ctx
extPermImplTransMTerm ctx' m =
  MaybeT $ WriterT $ ImpRTransFun $ reader $ \rtransFun -> PImplTerm $ \k ->
  TransM $ reader $ \info ->
  let ectx' = runTransM (translateClosed ctx') info in
  return $ runPermImplTransM m $ extImpRTransFun ectx' rtransFun
-}

-- | Look up the @r@ translation function
pimplRTransFunM :: PImplTransM r ext blocks tops rets ctx
                   (ImpRTransFun r ext blocks tops rets ctx)
pimplRTransFunM = lift $ lift $ ImpRTransFunT ask

-- | Build an error term by recording the error message and returning 'Nothing'
pimplFailM :: String -> PImplTransM r ext blocks tops rets ctx a
pimplFailM msg = tell ([msg],HasFailures) >> mzero

-- | Catch a potential 'Nothing' return value in a 'PImplTransM' computation
pimplCatchM :: PImplTransM r ext blocks tops rets ctx a ->
               PImplTransM r ext blocks tops rets ctx (Maybe a)
pimplCatchM m = lift $ runMaybeT m

-- | Prepend a 'String' to all error messages generated in a computation
pimplPrependMsgM :: String -> PImplTransM r ext blocks tops rets ctx a ->
                    PImplTransM r ext blocks tops rets ctx a
pimplPrependMsgM str m =
  pass ((, (\(msgs, hasfs) -> (map (str++) msgs, hasfs))) <$> m)

type PImplTransMTerm r ext blocks tops rets ps ctx =
  PImplTransM r ext blocks tops rets ctx
  (PImplTerm ext blocks tops rets ps ctx)

-- | Run the first 'PImplTransM' computation to produce a 'PImplTerm' and use
-- the second computation to generate the failure continuation of that first
-- 'PImplTerm', using optimizations to omit the first or second term when it is
-- not needed.
pimplHandleFailM :: PImplTransMTerm r ext blocks tops rets ps ctx ->
                    PImplTransMTerm r ext blocks tops rets ps ctx ->
                    PImplTransMTerm r ext blocks tops rets ps ctx
pimplHandleFailM m m_catch =
  do
    -- Run the default computation m, exposing whether it returned a term or not
    -- and whether it calls the failure continuation or not
     (maybe_t, (fails,hasf)) <- lift $ lift $ runWriterT $ runMaybeT m
     -- We want to retain all failure messages from m, but we are handling any
     -- calls to the failure continuation, so we are NoFailures for now
     tell (fails, NoFailures)
     case (maybe_t, hasf) of
       (Just t, NoFailures) ->
         -- If t does not call the failure continuation, then we have no need to
         -- use m_catch, and we just return t
         return t
       (Just t, HasFailures) ->
         -- If t does potentially call the failure continuation, then let-bind
         -- the result of m_catch as its failure continuation; note that we
         -- preserve any MaybeT and WriterT effects of m_catch, meaning that its
         -- failure messages and HasFailures flag are preserved, and if it
         -- returns Nothing then so will this entire computation
         do maybe_t_catch <- lift $ runMaybeT m_catch
            case maybe_t_catch of
              Just t_catch -> return $ catchPImplTerm t t_catch
              Nothing -> return t
       (Nothing, _) ->
         -- If t definitely fails, then just use m_catch
         m_catch


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
         (\case
             (pctx :>: PTrans_Conj [APTrans_Struct pctx_str] :>: ptrans) ->
               pctx :>: typeTransF tptrans (transTerms $
                                            RL.set (mbLift memb) ptrans pctx_str)
             _ -> error "translateSimplImpl: SImpl_IntroStructField")
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
    do ev <- infoEvType <$> ask
       (w_term, len1_tm, elem_tp, _) <- translateLLVMArrayPerm mb_ap1
       (_, len2_tm, _, _) <- translateLLVMArrayPerm mb_ap2
       tp_trans <- translateSimplImplOutHead mb_simpl
       len3_tm <-
         translate1 $
         fmap (\case
                  (ValPerm_LLVMArray ap) -> llvmArrayLen ap
                  _ -> error "translateSimplImpl: SImpl_LLVMArrayAppend") $
         fmap distPermsHeadPerm $ mbSimplImplOut mb_simpl
       (_ :>: ptrans1 :>: ptrans2) <- itiPermStack <$> ask
       let arr_out_comp_tm =
             applyGlobalOpenTerm "Prelude.appendCastBVVecS"
             [evTypeTerm ev, w_term, len1_tm, len2_tm, len3_tm, elem_tp,
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
       ev <- infoEvType <$> ask
       let vec_cast_m =
             applyGlobalOpenTerm "Prelude.castVecS"
             [evTypeTerm ev, elem_tp, natOpenTerm 0, bvZero_nat_tm, vec_tm]
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
                 applyGlobalOpenTerm "Prelude.repeatBVVec"
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
                 applyGlobalOpenTerm "Prelude.repeatBVVec"
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
         (fmap ((MNil :>:) . extPermTrans ETrans_LLVM) cell_in_trans)
         (MNil :>: Member_Base)
         (fmap ((MNil :>:) . extPermTrans ETrans_LLVM) cell_out_trans)
       -- Build the computation that maps impl_tm over the input array using the
       -- mapBVVecM monadic combinator
       ptrans_arr <- getTopPermM
       ev <- infoEvType <$> ask
       let arr_out_comp_tm =
             applyGlobalOpenTerm "Prelude.mapBVVecS"
             [evTypeTerm ev, elem_tp, typeTransType1 cell_out_trans, impl_tm,
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

  [nuMP| SImpl_SplitLifetime mb_x f args l mb_l2 _ _ _ _ _ |] ->
    -- FIXME HERE: get rid of the mbMaps!
    do let l2_e = fmap PExpr_Var mb_l2
       let f_l_args = mbMap3 ltFuncApply f args l
       let f_l2_min = mbMap2 ltFuncMinApply f l2_e
       let x_tp = mbVarType mb_x
       f_l2_args_trans <- translateSimplImplOutTailHead mb_simpl
       f_l_args_trans <- tpTransM $ translateDescType f_l_args
       f_l2_min_trans <- tpTransM $ translateDescType f_l2_min
       withPermStackM
         (\(ns :>: x :>: _ :>: l2) -> ns :>: x :>: l2)
         (\case
             (pctx :>: ptrans_x :>: _ :>:
              PTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t)
               ->
               pctx :>: typeTransF f_l2_args_trans (transTerms ptrans_x) :>:
               PTrans_LOwned mb_ls (CruCtxCons tps_in x_tp)
               (CruCtxCons tps_out x_tp)
               (mbMap3 (\ps x p -> ps :>: ExprAndPerm (PExpr_Var x) p)
                mb_ps_in mb_x f_l2_min)
               (mbMap3 (\ps x p -> ps :>: ExprAndPerm (PExpr_Var x) p)
                mb_ps_out mb_x f_l_args)
               (weakenLOwnedTrans f_l2_min_trans f_l_args_trans t)
             _ ->
               panic "translateSimplImpl"
               ["In SImpl_SplitLifetime rule: expected an lowned permission"])
         m

  [nuMP| SImpl_SubsumeLifetime _ _ _ _ _ _ mb_l2 |] ->
    flip (withPermStackM id) m $ \case
    (pctx :>: PTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t) ->
      pctx :>:
      PTrans_LOwned (mbMap2 (:) mb_l2 mb_ls) tps_in tps_out mb_ps_in mb_ps_out t
    _ ->
      panic "translateSimplImpl"
      ["In SImpl_SubsumeLifetime rule: expected an lowned permission"]

  [nuMP| SImpl_ContainedLifetimeCurrent _ _ _ _ _ _ _ |] ->
    do ttr_lcur <- translateSimplImplOutTailHead mb_simpl
       withPermStackM
         (\(ns :>: l1) -> ns :>: l1 :>: l1)
         (\(pctx :>: ptrans_l) ->
           pctx :>: typeTransF ttr_lcur [] :>: ptrans_l)
         m

  [nuMP| SImpl_RemoveContainedLifetime _ _ _ _ _ _ mb_l2 |] ->
    withPermStackM
    (\(ns :>: l :>: _) -> ns :>: l)
    (\case
        (pctx :>:
         PTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t :>: _) ->
          let mb_ls' = mbMap2 (\l2 ls ->
                                delete (PExpr_Var l2) ls) mb_l2 mb_ls in
          pctx :>: PTrans_LOwned mb_ls' tps_in tps_out mb_ps_in mb_ps_out t
        _ ->
          panic "translateSimplImpl"
          ["In SImpl_RemoveContainedLifetime rule: expected an lowned permission"])
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

  [nuMP| SImpl_MapLifetime _ mb_ls tps_in tps_out _ _ tps_in' tps_out'
                           ps_in' ps_out' ps1 ps2 impl_in impl_out |] ->
    -- First, translate the various permissions and implications
    do ttr_inF' <- tpTransM $ translateDescType ps_in'
       ttr_outF' <- tpTransM $ translateDescType ps_out'
       ttr1F <- tpTransM $ translateDescType ps1
       ttr2F <- tpTransM $ translateDescType ps2
       t1 <-
         translateLOwnedPermImpl "Error mapping lowned input perms:" impl_in
       t2 <-
         translateLOwnedPermImpl "Error mapping lowned output perms:" impl_out

       -- Next, split out the various input permissions from the rest of the pctx
       let prxs1 = mbRAssignProxies ps1
       let prxs2 = mbRAssignProxies ps2
       let prxs_in = RL.append prxs1 prxs2 :>: Proxy
       let prxs_in' = cruCtxProxies $ mbLift tps_in'
       pctx <- itiPermStack <$> ask
       let (pctx0, pctx12 :>: ptrans_l) = RL.split ps0 prxs_in pctx
       let (pctx1, pctx2) = RL.split prxs1 prxs2 pctx12
       let some_lotr =
             unPTransLOwned "translateSimplImpl" tps_in tps_out ptrans_l

       -- Also split out the input variables and replace them with the ps_out vars
       pctx_vars <- itiPermStackVars <$> ask
       let (vars_ps, vars12 :>: _) = RL.split ps0 prxs_in pctx_vars
       let (vars1, vars2) = RL.split prxs1 prxs2 vars12

       -- Finally, modify the PTrans_LOwned on top of the stack using
       -- mapLtLOwnedTrans
       withPermStackM
         (\(_ :>: l) -> vars_ps :>: l)
         (\_ ->
           case some_lotr of
             SomeLOwnedTrans lotr ->
               pctx0 :>:
               PTrans_LOwned mb_ls (mbLift tps_in') (mbLift tps_out') ps_in' ps_out'
               (mapLtLOwnedTrans pctx1 vars1 ttr1F pctx2 vars2 ttr2F
                prxs_in' ttr_inF' ttr_outF' t1 t2 lotr))
         m

  [nuMP| SImpl_EndLifetime _ tps_in tps_out ps_in ps_out |] ->
    -- First, translate the in and out permissions of the lowned permission
    do dtr_in <- tpTransM $ translateDescType ps_in
       dtr_out <- tpTransM $ translateDescType ps_out
       let prxs_in = mbRAssignProxies ps_in :>: Proxy
       let d = arrowDescTrans dtr_in dtr_out

       -- Next, split out the ps_in permissions from the rest of the pctx
       pctx <- itiPermStack <$> ask
       let (pctx_ps, pctx_in :>: ptrans_l) = RL.split ps0 prxs_in pctx
       let some_lotr =
             unPTransLOwned "translateSimplImpl" tps_in tps_out ptrans_l

       -- Also split out the ps_in variables and replace them with the ps_out vars
       pctx_vars <- itiPermStackVars <$> ask
       let (ps_vars, _ :>: _) = RL.split ps0 prxs_in pctx_vars
       let vars_out = case mbExprPermsMembers ps_out of
             Just x -> x
             Nothing -> panic "translateSimplImpl"
               ["In SImpl_EndLifetime rule: malformed ps_out"]

       -- Now we apply the lifetime ownerhip function to ps_in and bind its output
       -- in the rest of the computation
       ev <- infoEvType <$> ask
       case some_lotr of
         SomeLOwnedTrans lotr ->
           bindSpecMTransM
           (callSOpenTerm ev d (lownedTransTerm ps_in lotr) (transTerms pctx_in))
           (descTypeTrans dtr_out)
           "endl_ps"
           (\pctx_out ->
             withPermStackM
             (\(_ :>: l) -> RL.append ps_vars vars_out :>: l)
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

  [nuMP| SImpl_ElimLOwnedSimple mb_l mb_tps mb_ps |] ->
    case (mbExprPermsMembers mb_ps, mbMaybe (mbMap2 lownedPermsSimpleIn mb_l mb_ps)) of
      (Just vars, Just mb_ps') ->
        do ev <- infoEvType <$> ask
           ectx <- infoCtx <$> ask
           dtr_in <- tpTransM $ translateDescType mb_ps'
           dtr_out <- tpTransM $ translateDescType mb_ps
           withPermStackM id
             (\(pctx :>: _) ->
               pctx :>:
               PTrans_LOwned (fmap (const []) mb_l)
               (mbLift mb_tps) (mbLift mb_tps) mb_ps' mb_ps
               (mkLOwnedTransId ev ectx dtr_in dtr_out vars))
             m
      _ ->
        panic "translateSimplImpl"
        ["In SImpl_ElimLOwnedSimple rule: malformed permissions argument"]

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
         (\pctx -> pctx :>: typeTransF ttrans [])
         m

  [nuMP| SImpl_CoerceLLVMBlockEmpty _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans [])
         m

  [nuMP| SImpl_ElimLLVMBlockToBytes _ mb_bp |] ->
    do let w = natVal2 mb_bp
       let w_term = natOpenTerm w
       len_term <- translate1 $ fmap llvmBlockLen mb_bp
       ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           let arr_term =
                 applyGlobalOpenTerm "Prelude.repeatBVVec"
                 [w_term, len_term, unitTypeOpenTerm, unitOpenTerm] in
           pctx :>: typeTransF ttrans [arr_term])
         m

  [nuMP| SImpl_IntroLLVMBlockSeqEmpty _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_ElimLLVMBlockSeqEmpty _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_SplitLLVMBlockEmpty _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans [])
         m

  -- Intro for a recursive named shape applies the fold function to the
  -- translations of the arguments plus the translations of the proofs of the
  -- permissions
  [nuMP| SImpl_IntroLLVMBlockNamed _ bp nmsh |]
    | [nuMP| RecShapeBody _ _ _ |] <- mbMatch $ fmap namedShapeBody nmsh
    , [nuMP| PExpr_NamedShape _ _ _ args |] <- mbMatch $ fmap llvmBlockShape bp ->
      {-
      do ttrans <- translateSimplImplOutHead mb_simpl
         args_trans <- translate args
         let args_tms = case exprCtxPureTypeTerms args_trans of
               Just tms -> map openTermLike tms
               Nothing -> panic "translateSimplImpl"
                 ["SImpl_IntroLLVMBlockNamed: found impure terms"]
         fold_id <-
           case fold_ids of
             [nuP| Just (fold_id,_) |] -> return fold_id
             _ -> error "Folding recursive shape before it is defined!"
         withPermStackM id
           (\(pctx :>: ptrans_x) ->
             pctx :>: typeTransF ttrans [applyGlobalTermLike (mbLift fold_id)
                                         (args_tms ++ transTerms ptrans_x)])
           m -}
      error "FIXME HERE NOWNOW: how to translate recursive named permissions"

  -- Intro for a defined named shape (the other case) is a no-op
    | [nuMP| DefinedShapeBody _ |] <- mbMatch $ fmap namedShapeBody nmsh ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         withPermStackM id
           (\(pctx :>: ptrans) ->
             pctx :>: typeTransF ttrans (transTerms ptrans))
           m

    | otherwise ->
        panic "translateSimplImpl"
        ["SImpl_IntroLLVMBlockNamed, unknown named shape"]

  -- Elim for a recursive named shape applies the unfold function to the
  -- translations of the arguments plus the translations of the proofs of the
  -- permissions
  [nuMP| SImpl_ElimLLVMBlockNamed _ bp nmsh |]
    | [nuMP| RecShapeBody _ _ desc_id |] <- mbMatch $ fmap namedShapeBody nmsh
    , [nuMP| PExpr_NamedShape _ _ _ args |] <- mbMatch $ fmap llvmBlockShape bp ->
      {-
      do ttrans <- translateSimplImplOutHead mb_simpl
         args_trans <- translate args
         let args_tms = case exprCtxPureTypeTerms args_trans of
               Just tms -> map openTermLike tms
               Nothing -> panic "translateSimplImpl"
                 ["SImpl_IntroLLVMBlockNamed: found impure terms"]
         unfold_id <-
           case fold_ids of
             [nuP| Just (_,unfold_id) |] -> return unfold_id
             _ -> error "Unfolding recursive shape before it is defined!"
         withPermStackM id
           (\(pctx :>: ptrans_x) ->
             pctx :>: typeTransF ttrans [applyGlobalTermLike (mbLift unfold_id)
                                         (args_tms ++ transTerms ptrans_x)])
           m -}
      error "FIXME HERE NOWNOW: how to translate recursive named permissions"

  -- Intro for a defined named shape (the other case) is a no-op
    | [nuMP| DefinedShapeBody _ |] <- mbMatch $ fmap namedShapeBody nmsh ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         withPermStackM id
           (\(pctx :>: ptrans) ->
             pctx :>: typeTransF ttrans [transTerm1 ptrans])
           m

    | otherwise ->
        panic "translateSimplImpl" ["ElimLLVMBlockNamed, unknown named shape"]

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
           pctx :>: typeTransF ttrans (transTerms ptrans))
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
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_ElimLLVMBlockField _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
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
           pctx :>: typeTransF ttrans (transTerms ptrans1
                                       ++ transTerms ptrans2))
         m

  [nuMP| SImpl_ElimLLVMBlockSeq _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
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
    error "FIXME HERE NOWNOW: how to handle recursive perms"
    {-
    do args_trans <- translate args
       let args_tms = case exprCtxPureTypeTerms args_trans of
             Just tms -> map openTermLike tms
             Nothing -> panic "translateSimplImpl"
               ["SImpl_FoldNamed: impure arguments"]
       ttrans <- translateSimplImplOutHead mb_simpl
       let fold_ident = mbLift $ fmap recPermFoldFun rp
       withPermStackM id
         (\(pctx :>: ptrans_x) ->
           pctx :>: typeTransF ttrans [applyGlobalTermLike fold_ident
                                       (args_tms ++ transTerms ptrans_x)])
         m -}

  [nuMP| SImpl_UnfoldNamed _ (NamedPerm_Rec rp) args _ |] ->
    error "FIXME HERE NOWNOW: how to handle recursive perms"
    {-
    do args_trans <- translate args
       let args_tms = case exprCtxPureTypeTerms args_trans of
             Just tms -> map openTermLike tms
             Nothing -> panic "translateSimplImpl"
               ["SImpl_UnfoldNamed: impure arguments"]
       ttrans <- tupleTypeTrans <$> translateSimplImplOutHead mb_simpl
       let unfold_ident = mbLift $ fmap recPermUnfoldFun rp
       withPermStackM id
         (\(pctx :>: ptrans_x) ->
           pctx :>:
           typeTransF ttrans [applyGlobalTermLike unfold_ident
                              (args_tms ++ [transTerm1 ptrans_x])])
         m -}

  [nuMP| SImpl_FoldNamed _ (NamedPerm_Defined _) _ _ |] ->
    error "FIXME HERE NOWNOW: how to handle recursive perms"
    {-
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m -}

  [nuMP| SImpl_UnfoldNamed _ (NamedPerm_Defined _) _ _ |] ->
    error "FIXME HERE NOWNOW: how to handle recursive perms"
    {-
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m -}

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
           typeTransF (tupleTypeTrans ttrans) [applyGlobalOpenTerm trans_ident
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


-- | Translate a normal unary 'PermImpl1' rule that succeeds and applies the
-- translation function if the argument succeeds and fails if the translation of
-- the argument fails
translatePermImplUnary ::
  NuMatchingAny1 r => RL.TypeCtx bs =>
  Mb ctx (MbPermImpls r (RNil :> '(bs,ps_out))) ->
  (ImpTransM ext blocks tops rets ps_out (ctx :++: bs) OpenTerm ->
   ImpTransM ext blocks tops rets ps ctx OpenTerm) ->
  PImplTransMTerm r ext blocks tops rets ps ctx
translatePermImplUnary (mbMatch -> [nuMP| MbPermImpls_Cons _ _ mb_impl |]) f =
  let bs = RL.typeCtxProxies in
  PImplTerm <$> fmap f <$> popPImplTerm <$>
  extPermImplTransM bs (translatePermImpl (mbCombine bs mb_impl))

-- | Translate a 'PermImpl1' to a function on translation computations
translatePermImpl1 :: NuMatchingAny1 r =>
                      Mb ctx (PermImpl1 ps ps_outs) ->
                      Mb ctx (MbPermImpls r ps_outs) ->
                      PImplTransMTerm r ext blocks tops rets ps ctx
translatePermImpl1 mb_impl mb_impls = case (mbMatch mb_impl, mbMatch mb_impls) of
  -- A failure translates to a call to the catch handler, which is the most recent
  -- Impl1_Catch, if one exists, or the SAW errorM function otherwise
  ([nuMP| Impl1_Fail err |], _) ->
    pimplFailM (mbLift (fmap ppError err))

  ([nuMP| Impl1_Catch dbg_str |],
   [nuMP| (MbPermImpls_Cons _ (MbPermImpls_Cons _ _ mb_impl1) mb_impl2) |]) ->
    pimplHandleFailM
    (pimplPrependMsgM ("Case 1 of " ++ mbLift dbg_str) $
     translatePermImpl $ mbCombine RL.typeCtxProxies mb_impl1)
    (pimplPrependMsgM ("Case 2 of " ++ mbLift dbg_str) $
     translatePermImpl $ mbCombine RL.typeCtxProxies mb_impl2)

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
  ([nuMP| Impl1_ElimOrs dbg_str x mb_or_list |], _) ->
    -- First, translate all the PermImpls in mb_impls, using pitmCatching to
    -- isolate failures to each particular branch, but still reporting failures
    -- in any branch
    zipWithM (\mb_impl' (i::Int) ->
               pimplPrependMsgM ("Case " ++ show i ++
                                 " of " ++ mbLift dbg_str) $
               pimplCatchM $ translatePermImpl mb_impl')
    (mbOrListPermImpls mb_or_list mb_impls) [1..] >>= \maybe_transs ->
    -- As a special case, if all branches fail (representing as translating to
    -- Nothing), then the entire or elimination fails
    if all isNothing maybe_transs then mzero else
      return $ PImplTerm $ \k ->
      do let mb_or_p = mbOrListPerm mb_or_list
         () <- assertTopPermM "Impl1_ElimOrs" x mb_or_p
         tps <- mapM translate $ mbOrListDisjs mb_or_list
         tp_ret <- compReturnTypeTransM
         top_ptrans <- getTopPermM
         eithersElimTransM tps tp_ret
           (flip map maybe_transs $ \maybe_trans ptrans ->
             withPermStackM id ((:>: ptrans) . RL.tail) $
             popPImplTerm (forcePImplTerm maybe_trans) k)
           (transTupleTerm top_ptrans)

  -- An existential elimination performs a pattern-match on a Sigma
  ([nuMP| Impl1_ElimExists x p |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do let tp = mbBindingType p
       () <- assertTopPermM "Impl1_ElimExists" x (fmap ValPerm_Exists p)
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
    return $ PImplTerm $ const $
    do mb_false <- nuMultiTransM $ const ValPerm_False
       () <- assertTopPermM "Impl1_ElimFalse" mb_x mb_false
       top_ptrans <- getTopPermM
       applyGlobalTransM "Prelude.efq"
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
         (\case
             (pctx :>: PTrans_Conj [APTrans_Struct pctx_str]) ->
               pctx :>: PTrans_Conj [APTrans_Struct $
                                     RL.set (mbLift memb) (PTrans_Eq mb_y) pctx_str]
               :>: RL.get (mbLift memb) pctx_str
             _ ->
               error "translatePermImpl1: Impl1_ElimStructField")
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
           pctx :>: typeTransF tp_trans1 [] :>:
           typeTransF tp_trans2 (transTerms ptrans))
         m

  ([nuMP| Impl1_SplitLLVMWordField _ mb_fp mb_sz1 mb_endianness |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do let mb_e = case mbLLVMFieldContents mb_fp of
             [nuP| ValPerm_Eq (PExpr_LLVMWord e) |] -> e
             _ -> error "translatePermImpl1: Impl1_SplitLLVMWordField"
       e_tm <- translate1 mb_e
       sz1_tm <- translate mb_sz1
       sz2_tm <- translateClosed $ mbLLVMFieldSize mb_fp
       let sz2m1_tm = applyGlobalOpenTerm "Prelude.subNat" [sz2_tm, sz1_tm]
       let (e1_tm,e2_tm) =
             bvSplitOpenTerm (mbLift mb_endianness) sz1_tm sz2m1_tm e_tm
       inExtTransM (ETrans_Term knownRepr e1_tm) $
         inExtTransM (ETrans_Term knownRepr e2_tm) $
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
       let sz2m1_tm = applyGlobalOpenTerm "Prelude.subNat" [sz2_tm, sz1_tm]
       let (e1_tm,_) =
             bvSplitOpenTerm (mbLift mb_endianness) sz1_tm sz2m1_tm e_tm
       inExtTransM (ETrans_Term knownRepr e1_tm) $
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
       inExtTransM (ETrans_Term knownRepr e_tm) $
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
    do ev <- infoEvType <$> ask
       ectx <- infoCtx <$> ask
       let prxs = RL.map (const Proxy) ectx
       let mb_ps = (nuMulti prxs (const MNil))
       let ttr = pure MNil
       withPermStackM (:>: Member_Base)
         (:>:
          PTrans_LOwned
          (nuMulti prxs (const [])) CruCtxNil CruCtxNil mb_ps mb_ps
          (mkLOwnedTransId ev ectx ttr ttr MNil))
         m

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
      pimplFailM (mbLift prop_str)

  -- Otherwise, insert an equality test with proof construction. Note that, as
  -- with all TryProveBVProps, if the test fails and there is no failure
  -- continuation, we insert just the proposition failure string using
  -- implTransAltErr, not the entire type-checking error message, because this is
  -- considered just an assertion and not a failure
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_Eq e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    do prop_tp_trans <- translate prop
       ret_tp <- compReturnTypeM
       applyGlobalTransM "Prelude.maybe"
         [ return (typeTransType1 prop_tp_trans), return ret_tp
         , return (implFailAltContTerm ret_tp (mbLift prop_str) k)
         , lambdaTransM "eq_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             popPImplTerm trans k)
         , applyGlobalTransM "Prelude.bvEqWithProof"
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
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    let w = natVal2 prop in
    applyGlobalTransM "Prelude.ite"
    [ compReturnTypeM
    , applyGlobalTransM "Prelude.bvEq"
      [ return (natOpenTerm w), translate1 e1, translate1 e2 ]
    , (\ret_tp ->
        implFailAltContTerm ret_tp (mbLift prop_str) k) <$> compReturnTypeM
    , withPermStackM (:>: translateVar x)
      (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop unitOpenTerm)]) $
      popPImplTerm trans k]

  -- If we know e1 < e2 statically, translate to unsafeAssert
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULt e1 e2) _ |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
      return $ PImplTerm $ \k ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         let pf_tm =
               applyGlobalOpenTerm "Prelude.unsafeAssertBVULt"
               [natOpenTerm w, t1, t2]
         withPermStackM (:>: translateVar x)
           (:>: bvPropPerm (BVPropTrans prop pf_tm))
           (popPImplTerm trans k)

  -- If we don't know e1 < e2 statically, translate to bvultWithProof
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULt e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    do prop_tp_trans <- translate prop
       ret_tp <- compReturnTypeM
       applyGlobalTransM "Prelude.maybe"
         [ return (typeTransType1 prop_tp_trans), return ret_tp
         , return (implFailAltContTerm ret_tp (mbLift prop_str) k)
         , lambdaTransM "ult_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             popPImplTerm trans k)
         , applyGlobalTransM "Prelude.bvultWithProof"
           [ return (natOpenTerm $ natVal2 prop), translate1 e1, translate1 e2]
         ]

  -- If we know e1 <= e2 statically, translate to unsafeAssert
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq e1 e2) _ |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
      return $ PImplTerm $ \k ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         let pf_tm =
               applyGlobalOpenTerm "Prelude.unsafeAssertBVULe"
               [natOpenTerm w, t1, t2]
         withPermStackM (:>: translateVar x)
           (:>: bvPropPerm (BVPropTrans prop pf_tm))
           (popPImplTerm trans k)

  -- If we don't know e1 <= e2 statically, translate to bvuleWithProof
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    do prop_tp_trans <- translate prop
       ret_tp <- compReturnTypeM
       applyGlobalTransM "Prelude.maybe"
         [ return (typeTransType1 prop_tp_trans), return ret_tp
         , return (implFailAltContTerm ret_tp (mbLift prop_str) k)
         , lambdaTransM "ule_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             popPImplTerm trans k)
         , applyGlobalTransM "Prelude.bvuleWithProof"
           [ return (natOpenTerm $ natVal2 prop), translate1 e1, translate1 e2]
         ]

  -- If we know e1 <= e2-e3 statically, translate to unsafeAssert
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq_Diff e1 e2 e3) _ |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
      return $ PImplTerm $ \k ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         t3 <- translate1 e3
         let pf_tm =
               applyGlobalOpenTerm "Prelude.unsafeAssertBVULe"
               [natOpenTerm w, t1,
                applyGlobalOpenTerm "Prelude.bvSub" [natOpenTerm w, t2, t3]]
         withPermStackM (:>: translateVar x)
           (:>: bvPropPerm (BVPropTrans prop pf_tm))
           (popPImplTerm trans k)

  -- If we don't know e1 <= e2-e3 statically, translate to bvuleWithProof
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq_Diff e1 e2 e3) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    do prop_tp_trans <- translate prop
       ret_tp <- compReturnTypeM
       applyGlobalTransM "Prelude.maybe"
         [ return (typeTransType1 prop_tp_trans), return ret_tp
         , return (implFailAltContTerm ret_tp (mbLift prop_str) k)
         , lambdaTransM "ule_diff_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             popPImplTerm trans k)
         , applyGlobalTransM "Prelude.bvuleWithProof"
           [ return (natOpenTerm $ natVal2 prop), translate1 e1,
             applyGlobalTransM "Prelude.bvSub"
             [return (natOpenTerm $ natVal2 prop), translate1 e2, translate1 e3]]
         ]

  ([nuMP| Impl1_TryProveBVProp _ _ _ |], _) ->
    pimplFailM ("translatePermImpl1: Unhandled BVProp case")

-- | Translate a 'PermImpl' in the 'PermImplTransM' monad to a function that
-- takes a failure continuation and returns a monadic computation to generate
-- the translation as a term
translatePermImpl :: NuMatchingAny1 r => Mb ctx (PermImpl r ps) ->
                     PImplTransMTerm r ext blocks tops rets ps ctx
translatePermImpl mb_impl = case mbMatch mb_impl of
  [nuMP| PermImpl_Done r |] ->
    do f <- pimplRTransFunM
       return $ PImplTerm $ const $ appImpTransFun f reflCtxExt r
  [nuMP| PermImpl_Step impl1 mb_impls |] ->
    translatePermImpl1 impl1 mb_impls

translatePermImplToTerm :: NuMatchingAny1 r => String ->
                           Mb ctx (PermImpl r ps) ->
                           ImpRTransFun r ext blocks tops rets ctx ->
                           ImpTransM ext blocks tops rets ps ctx OpenTerm
translatePermImplToTerm err mb_impl k =
  let (maybe_ptm, (errs,_)) =
        runPermImplTransM (translatePermImpl mb_impl) k in
  (infoEvType <$> ask) >>= \ev ->
  popPImplTerm (forcePImplTerm maybe_ptm) $
  ImplFailContMsg ev (err ++ "\n\n"
                      ++ concat (intersperse
                                 "\n\n--------------------\n\n" errs))

instance ImplTranslateF r ext blocks tops rets =>
         Translate (ImpTransInfo ext blocks tops rets ps)
                   ctx (AnnotPermImpl r ps) OpenTerm where
  translate (mbMatch -> [nuMP| AnnotPermImpl err mb_impl |]) =
    translatePermImplToTerm (mbLift err) mb_impl (ImpRTransFun $
                                                  const translateF)

-- We translate a LocalImplRet to a term that returns all current permissions
instance ImplTranslateF (LocalImplRet ps) ext blocks ps_in rets where
  translateF _ =
    do pctx <- itiPermStack <$> ask
       ev <- infoEvType <$> ask
       ret_tp <- returnTypeM
       return $ retSOpenTerm ev ret_tp (transTupleTerm pctx)

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
  local (\info -> info { itiReturnType = typeTransTupleType tp_trans_out }) $
  withPermStackM
    (const (RL.append vars1 vars2))
    (const (RL.append pctx1 pctx2))
    (translateLocalPermImpl err impl)

-- | Translate a 'LocalPermImpl' to an 'LOwnedTransTerm'
translateLOwnedPermImpl :: String -> Mb ctx (LocalPermImpl ps_in ps_out) ->
                           ImpTransM ext blocks tops rets ps ctx
                           (LOwnedTransTerm ctx ps_in ps_out)
translateLOwnedPermImpl err (mbMatch -> [nuMP| LocalPermImpl mb_impl |]) =
  ask >>= \info_top ->
  return $ LOwnedTransM $ \e_ext loinfo_in k ->
  flip runTransM (lownedInfoToImp loinfo_in info_top) $
  translatePermImplToTerm err (extMbExt e_ext mb_impl) $
  ImpRTransFun $ \cext' r ->
  case mbMatch r of
    [nuMP| LocalImplRet Refl |] ->
      do info_out <- ask
         let e_ext' = ctxExtToExprExt cext' $ itiExprCtx info_out
         return $ k e_ext' (impInfoToLOwned info_out) ()


{-
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

-- | Translate a 'RegWithVal' to exactly one SAW term via 'transPureTerm1'
translateRWV :: TransInfo info => Mb ctx (RegWithVal a) ->
                TransM info ctx OpenTerm
translateRWV mb_rwv = transPureTerm1 <$> translate mb_rwv

-- translate for a TypedExpr yields an ExprTrans
instance (PermCheckExtC ext exprExt, TransInfo info) =>
         Translate info ctx (App ext RegWithVal tp) (ExprTrans tp) where
  translate mb_e = case mbMatch mb_e of
    [nuMP| BaseIsEq BaseBoolRepr e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.boolEq")
      [translateRWV e1, translateRWV e2]
  --  [nuMP| BaseIsEq BaseNatRepr e1 e2 |] ->
  --    ETrans_Term <$>
  --    applyMultiPureTransM (return $ globalOpenTerm "Prelude.equalNat")
  --    [translateRWV e1, translateRWV e2]
    [nuMP| BaseIsEq (BaseBVRepr w) e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvEq")
      [translate w, translateRWV e1, translateRWV e2]

    [nuMP| EmptyApp |] -> return ETrans_Unit

    -- Booleans
    [nuMP| BoolLit True |] ->
      return $ ETrans_Term knownRepr $ globalOpenTerm "Prelude.True"
    [nuMP| BoolLit False |] ->
      return $ ETrans_Term knownRepr $ globalOpenTerm "Prelude.False"
    [nuMP| Not e |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.not")
      [translateRWV e]
    [nuMP| And e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.and")
      [translateRWV e1, translateRWV e2]
    [nuMP| Or e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.or")
      [translateRWV e1, translateRWV e2]
    [nuMP| BoolXor e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.xor")
      [translateRWV e1, translateRWV e2]

    -- Natural numbers
    [nuMP| Expr.NatLit n |] ->
      return $ ETrans_Term knownRepr $ natOpenTerm $ mbLift n
    [nuMP| NatLt e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.ltNat")
      [translateRWV e1, translateRWV e2]
    -- [nuMP| NatLe _ _ |] ->
    [nuMP| NatEq e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.equalNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatAdd e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.addNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatSub e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.subNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatMul e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.mulNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatDiv e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.divNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatMod e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.modNat")
      [translateRWV e1, translateRWV e2]

    -- Function handles: the expression part of a function handle has no
    -- computational content
    [nuMP| HandleLit _ |] -> return ETrans_Fun

    -- Bitvectors
    [nuMP| BVUndef w |] ->
      -- FIXME: we should really handle poison values; this translation just
      -- treats them as if there were the bitvector 0 value
      return $ ETrans_Term knownRepr $
      bvBVOpenTerm (mbLift w) $ BV.zero (mbLift w)
    [nuMP| BVLit w mb_bv |] ->
      return $ ETrans_Term knownRepr $ bvBVOpenTerm (mbLift w) $ mbLift mb_bv
    [nuMP| BVConcat w1 w2 e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.join")
      [translate w1, translate w2, translateRWV e1, translateRWV e2]
    [nuMP| BVTrunc w1 w2 e |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvTrunc")
      [return (natOpenTerm (natValue (mbLift w2) - natValue (mbLift w1))),
       translate w1,
       translateRWV e]
    [nuMP| BVZext w1 w2 e |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvUExt")
      [return (natOpenTerm (natValue (mbLift w1) - natValue (mbLift w2))),
       translate w2, translateRWV e]
    [nuMP| BVSext w1 w2 e |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSExt")
      [return (natOpenTerm (natValue (mbLift w1) - natValue (mbLift w2))),
       -- NOTE: bvSExt adds 1 to the 2nd arg
       return (natOpenTerm (natValue (mbLift w2) - 1)),
       translateRWV e]
    [nuMP| BVNot w e |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvNot")
      [translate w, translateRWV e]
    [nuMP| BVAnd w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvAnd")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVOr w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvOr")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVXor w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvXor")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVNeg w e |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvNeg")
      [translate w, translateRWV e]
    [nuMP| BVAdd w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvAdd")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSub w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSub")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVMul w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvMul")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUdiv w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvUDiv")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSdiv w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSDiv")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUrem w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvURem")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSrem w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSRem")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUle w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvule")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUlt w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvult")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSle w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvsle")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSlt w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvslt")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVCarry w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvCarry")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSCarry w e1 e2 |] ->
      -- NOTE: bvSCarry adds 1 to the bitvector length
      let w_minus_1 = natOpenTerm (natValue (mbLift w) - 1) in
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSCarry")
      [return w_minus_1, translateRWV e1, translateRWV e2]
    [nuMP| BVSBorrow w e1 e2 |] ->
      -- NOTE: bvSBorrow adds 1 to the bitvector length
      let w_minus_1 = natOpenTerm (natValue (mbLift w) - 1) in
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSBorrow")
      [return w_minus_1, translateRWV e1, translateRWV e2]
    [nuMP| BVShl w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvShiftL")
      [translate w, return (globalOpenTerm "Prelude.Bool"), translate w,
       return (globalOpenTerm "Prelude.False"), translateRWV e1, translateRWV e2]
    [nuMP| BVLshr w e1 e2 |] ->
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvShiftR")
      [translate w, return (globalOpenTerm "Prelude.Bool"), translate w,
       return (globalOpenTerm "Prelude.False"), translateRWV e1, translateRWV e2]
    [nuMP| BVAshr w e1 e2 |] ->
      let w_minus_1 = natOpenTerm (natValue (mbLift w) - 1) in
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSShiftR")
      [return w_minus_1, return (globalOpenTerm "Prelude.Bool"), translate w,
       translateRWV e1, translateRWV e2]
    [nuMP| BoolToBV mb_w e |] ->
      let w = mbLift mb_w in
      ETrans_Term knownRepr <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.ite")
      [bitvectorTransM (translate mb_w),
       translateRWV e,
       return (bvBVOpenTerm w (BV.one w)),
       return (bvBVOpenTerm w (BV.zero w))]
    [nuMP| BVNonzero mb_w e |] ->
      let w = mbLift mb_w in
      ETrans_Term knownRepr <$>
      applyPureTransM (return $ globalOpenTerm "Prelude.not")
      (applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvEq")
       [translate mb_w, translateRWV e,
        return (bvBVOpenTerm w (BV.zero w))])

    -- Strings
    [nuMP| Expr.StringLit (UnicodeLiteral text) |] ->
      return $ ETrans_Term knownRepr $ stringLitOpenTerm $
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

{-
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
-}

-- | Translate a call to (the translation of) an entrypoint, by either calling
-- the letrec-bound variable for the entrypoint, if it has one, or by just
-- translating the body of the entrypoint if it does not.
translateCallEntry :: forall ext exprExt tops args ghosts blocks ctx rets.
                      PermCheckExtC ext exprExt => String ->
                      TypedEntryTrans ext blocks tops rets args ghosts ->
                      Mb ctx (RAssign ExprVar (tops :++: args)) ->
                      Mb ctx (RAssign ExprVar ghosts) ->
                      ImpTransM ext blocks tops rets
                      ((tops :++: args) :++: ghosts) ctx SpecTerm
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

     -- Now check if entryID has an associated recursive closure
     case typedEntryTransClos entry_trans of
       Just (lrt, clos_tm) ->
         -- If so, build the associated CallS term, which applies the closure to
         -- the expressions with permissions on the stack followed by the proofs
         -- objects for those permissions
         do expr_ctx <- itiExprCtx <$> ask
            arg_membs <- itiPermStackVars <$> ask
            let e_args = RL.map (flip RL.get expr_ctx) arg_membs
            i_args <- itiPermStack <$> ask
            return (applyCallClosSpecTerm lrt clos_tm
                    (exprCtxToTerms e_args ++ permCtxToTerms i_args))
       Nothing ->
         -- Otherwise, continue translating with the target entrypoint, with all
         -- the current expressions free but with only those permissions on top
         -- of the stack
         inEmptyEnvImpTransM $ inCtxTransM ectx $
         do perms_trans <- translate $ typedEntryPermsIn entry
            withPermStackM
              (const $ RL.members ectx)
              (const $ typeTransF perms_trans $ transTerms stack)
              (translate $ _mbBinding $ typedEntryBody entry)

instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (CallSiteImplRet blocks tops args ghosts ps) SpecTerm where
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
         (TypedJumpTarget blocks tops ps) SpecTerm where
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
  ImpTransM ext blocks tops rets ps_out (ctx :++: stmt_rets) SpecTerm ->
  ImpTransM ext blocks tops rets ps_in ctx SpecTerm
translateStmt loc mb_stmt m = case mbMatch mb_stmt of
  [nuMP| TypedSetReg tp e |] ->
    do tp_trans <- translate tp
       tp_ret <- compReturnTypeM
       etrans <- tpTransM $ translate e
       let ptrans = exprOutPerm e
       inExtTransSAWLetBindM tp_trans tp_ret etrans $
         withPermStackM (:>: Member_Base) (:>: extPermTrans etrans ptrans) m

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
       fret_tp <-
         mkTermTypeTrans <$>
         sigmaTypeTransM "ret" rets_trans (hasPureTrans perms_out)
         (\ectx -> inExtMultiTransM ectx (typeTransTupleDesc <$>
                                          translate perms_out))
       let all_args =
             exprCtxToTerms ectx_gexprs ++ exprCtxToTerms ectx_args ++
             permCtxToTerms pctx_ghosts_args
       fun_tp_desc <- descTransM (translateDesc fun_perm)
       fapp_trm <- case f_trans of
             PTrans_Fun _ f_trm ->
               applyEvOpM "Prelude.CallS" [fun_tp_desc, f_trm]
             _ ->
               panic "translateStmt"
               ["TypedCall: unexpected function permission"]
       bindSpecMTransM
         fapp_trm fret_tp "call_ret_val" $ \ret_val ->
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
    applyGlobalTransM "Prelude.ite"
    [compReturnTypeM, translate1 e, m,
     mkErrorComp ("Failed Assert at " ++
                  renderDoc (ppShortFileName (plSourceLoc loc)))]

  [nuMP| TypedLLVMStmt stmt |] -> translateLLVMStmt stmt m


-- | Translate a 'TypedStmt' to a function on translation computations
translateLLVMStmt ::
  Mb ctx (TypedLLVMStmt r ps_in ps_out) ->
  ImpTransM ext blocks tops rets ps_out (ctx :> r) SpecTerm ->
  ImpTransM ext blocks tops rets ps_in ctx SpecTerm
translateLLVMStmt mb_stmt m = case mbMatch mb_stmt of
  [nuMP| ConstructLLVMWord (TypedReg x) |] ->
    inExtTransM ETrans_LLVM $
    withPermStackM (:>: Member_Base) (:>: (PTrans_Eq $ extMb $
                                           fmap (PExpr_LLVMWord . PExpr_Var) x)) m

  [nuMP| AssertLLVMWord reg _ |] ->
    inExtTransM (ETrans_Term knownRepr $ natOpenTerm 0) $
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
      -- the unitTermLike argument is because ptrans_tp is a memblock permission
      -- with an empty shape; the empty shape expects a unit argument
      :>: typeTransF ptrans_tp [unitTermLike])
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
    (\case
        (pctx :>: PTrans_Conj [APTrans_LLVMFunPtr tp' ptrans])
          | Just Refl <- testEquality (mbLift tp) tp' ->
            pctx :>: ptrans
        _ -> error ("translateLLVMStmt: TypedLLVMLoadHandle: "
                    ++ "unexpected permission stack"))
    m

  [nuMP| TypedLLVMResolveGlobal gsym (p :: ValuePerm (LLVMPointerType w))|] ->
    withKnownNat ?ptrWidth $
    inExtTransM ETrans_LLVM $
    do env <- infoEnv <$> ask
       ev <- infoEvType <$> ask
       let w :: NatRepr w = knownRepr
       case lookupGlobalSymbol env (mbLift gsym) w of
         Nothing ->
           panic "translateLLVMStmt"
           ["TypedLLVMResolveGlobal: no translation of symbol "
            ++ globalSymbolName (mbLift gsym)]
         Just (_, GlobalTransFuns [f])
           | [nuP| ValPerm_LLVMFunPtr fun_tp (ValPerm_Fun fun_perm) |] <- p ->
             do d <- descTransM <$> translateDesc (extMb fun_perm)
                let ptrans =
                      PTrans_Conj [APTrans_LLVMFunPtr (mbLift fun_tp) $
                                   PTrans_Fun fun_perm $ FunTransFun ev d f]
                withPermStackM (:>: Member_Base)
                  (:>: extPermTrans ETrans_LLVM ptrans) m
         Just (_, GlobalTransFun _) ->
           panic "translateLLVMStmt"
           ["TypedLLVMResolveGlobal: unexpected function translation for symbol "
            ++ globalSymbolName (mbLift gsym)]
         Just (_, GlobalTransTerms ts) ->
           do ptrans <- translate (extMb p)
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
       let t = applyGlobalTermLike "Prelude.boolToEither" [b]
       withPermStackM (:>: Member_Base) (:>: typeTransF tptrans [t]) m


----------------------------------------------------------------------
-- * Translating Sequences of Typed Crucible Statements
----------------------------------------------------------------------

instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedRet tops rets ps) SpecTerm where
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
       return $ returnSpecTerm ret_tp sigma_trm

instance PermCheckExtC ext exprExt =>
         ImplTranslateF (TypedRet tops rets) ext blocks tops rets where
  translateF mb_ret = translate mb_ret

instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedTermStmt blocks tops rets ps) SpecTerm where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedJump impl_tgt |] -> translate impl_tgt
    [nuMP| TypedBr reg impl_tgt1 impl_tgt2 |] ->
      applyGlobalTransM "Prelude.ite"
      [compReturnTypeM, translate1 reg,
       translate impl_tgt1, translate impl_tgt2]
    [nuMP| TypedReturn impl_ret |] -> translate impl_ret
    [nuMP| TypedErrorStmt (Just str) _ |] ->
      mkErrorComp ("Error: " ++ mbLift str)
    [nuMP| TypedErrorStmt Nothing _ |] ->
      mkErrorComp "Error (unknown message)"


instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedStmtSeq ext blocks tops rets ps) SpecTerm where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedImplStmt impl_seq |] -> translate impl_seq
    [nuMP| TypedConsStmt loc stmt pxys mb_seq |] ->
      translateStmt (mbLift loc) stmt (translate $ mbCombine (mbLift pxys) (_mbBinding <$> mb_seq))
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

-- | Get all entrypoints in a block map that will be translated to closures,
-- which is all entrypoints with in-degree > 1
typedBlockClosEntries :: TypedBlockMap TransPhase ext blocks tops rets ->
                           [SomeTypedEntry ext blocks tops rets]
typedBlockClosEntries =
  concat . RL.mapToList (map (\(Some entry) ->
                               SomeTypedEntry entry)
                         . filter (anyF typedEntryHasMultiInDegree)
                         . (^. typedBlockEntries))

-- | Fold a function over each 'TypedEntry' in a 'TypedBlockMap' that
-- corresponds to a letrec-bound variable
foldBlockMapClos ::
  (forall args ghosts.
   TypedEntry TransPhase ext blocks tops rets args ghosts -> b -> b) ->
  b -> TypedBlockMap TransPhase ext blocks tops rets -> b
foldBlockMapClos f r =
  foldr (\(SomeTypedEntry entry) -> f entry) r . typedBlockClosEntries

-- | Map a function over each 'TypedEntry' in a 'TypedBlockMap' that
-- corresponds to a letrec-bound variable
mapBlockMapClos ::
  (forall args ghosts.
   TypedEntry TransPhase ext blocks tops rets args ghosts -> b) ->
  TypedBlockMap TransPhase ext blocks tops rets -> [b]
mapBlockMapClos f =
  map (\(SomeTypedEntry entry) -> f entry) . typedBlockClosEntries

-- | Build a @LetRecType@ that describes the type of the translation of a
-- 'TypedEntry' to a closure
translateEntryLRT :: TypedEntry TransPhase ext blocks tops rets args ghosts ->
                     TypeTransM ctx OpenTerm
translateEntryLRT entry@(TypedEntry {..}) =
  inEmptyCtxTransM $
  translateClosed (typedEntryAllArgs entry) >>= \arg_tps ->
  piLRTTransM "arg" arg_tps $ \ectx ->
  inCtxTransM ectx $
  translate typedEntryPermsIn >>= \perms_in_tps ->
  arrowLRTTransM perms_in_tps $
  translateEntryRetType entry >>= \retType ->
  return $ ctorOpenTerm "Prelude.LRT_Ret" [typeDescLRT retType]

-- | Build a list of @LetRecType@ values that describe the types of all of the
-- entrypoints in a 'TypedBlockMap' that will be translated to closures
translateBlockMapLRTs :: TypedBlockMap TransPhase ext blocks tops rets ->
                         TypeTransM ctx [OpenTerm]
translateBlockMapLRTs blkMap =
  sequence $ mapBlockMapClos translateEntryLRT blkMap

-- | Translate the function permission of a CFG to a @LetRecType@
translateCFGLRT :: TypedCFG ext blocks ghosts inits gouts ret ->
                   TypeTransM ctx OpenTerm
translateCFGLRT cfg =
  typeDescLRT <$> translateClosed (tpcfgFunPerm cfg)

-- | Translate a 'TypedEntry' to a 'TypedEntryTrans' by associating a closure
-- term with it if it has one, i.e., if its in-degree is greater than 1. If it
-- does need a closure, the 'Natural' state tracks the index to be used for the
-- next closure, so use the current value and increment it.
--
-- Note that the return type is a monad inside a monad. This is so that the
-- caller can see the 'Natural' state without running the 'TypeTransM'
-- computation, which is necessary later on for tying the knot
translateTypedEntry ::
  Some (TypedEntry TransPhase ext blocks tops rets args) ->
  State Natural (TypeTransM RNil (Some
                                  (TypedEntryTrans ext blocks tops rets args)))
translateTypedEntry (Some entry) =
  if typedEntryHasMultiInDegree entry then
    do i <- get
       put (i+1)
       return $ do lrt <- translateEntryLRT entry
                   return (Some (TypedEntryTrans entry $
                                 Just (lrt, mkBaseClosSpecTerm i)))
  else return $ return $ Some (TypedEntryTrans entry Nothing)

-- | Translate a 'TypedBlock' to a 'TypedBlockTrans' by translating each
-- entrypoint in the block using 'translateTypedEntry'; see
-- 'translateTypedEntry' for an explanation of the monad-in-monad type
translateTypedBlock ::
  TypedBlock TransPhase ext blocks tops rets args ->
  State Natural (TypeTransM RNil (TypedBlockTrans ext blocks tops rets args))
translateTypedBlock blk =
  (TypedBlockTrans <$>) <$> sequence <$>
  mapM translateTypedEntry (blk ^. typedBlockEntries)

-- | Helper function to translate a 'TypedBlockMap' to a 'TypedBlockMapTrans' by
-- translating every entrypoint using 'translateTypedEntry'; see
-- 'translateTypedEntry' for an explanation of the monad-in-monad type
translateTypedBlockMapH ::
  RAssign (TypedBlock TransPhase ext blocks tops rets) blks ->
  State Natural (TypeTransM RNil
                 (RAssign (TypedBlockTrans ext blocks tops rets) blks))
translateTypedBlockMapH MNil = return $ return MNil
translateTypedBlockMapH (blkMap :>: blk) =
  do blkMapTransM <- translateTypedBlockMapH blkMap
     blkTransM <- translateTypedBlock blk
     return ((:>:) <$> blkMapTransM <*> blkTransM)

-- | Translate a 'TypedBlockMap' to a 'TypedBlockMapTrans' by translating every
-- entrypoint using 'translateTypedEntry'; see 'translateTypedEntry' for an
-- explanation of the monad-in-monad type
translateTypedBlockMap ::
  TypedBlockMap TransPhase ext blocks tops rets ->
  State Natural (TypeTransM RNil (TypedBlockMapTrans ext blocks tops rets))
translateTypedBlockMap = translateTypedBlockMapH

-- | Translate the typed statements of an entrypoint to a function
--
-- > \top1 ... topn arg1 ... argm ghost1 ... ghostk p1 ... pj -> stmts_trans
--
-- over the top-level, local, and ghost arguments and (the translations of) the
-- input permissions of the entrypoint
translateEntryBody :: PermCheckExtC ext exprExt =>
                      TypedBlockMapTrans ext blocks tops rets ->
                      TypedEntry TransPhase ext blocks tops rets args ghosts ->
                      TypeTransM RNil SpecTerm
translateEntryBody mapTrans entry =
  lambdaExprCtx (typedEntryAllArgs entry) $
  lambdaPermCtx (typedEntryPermsIn entry) $ \pctx ->
  do retType <- translateEntryRetType entry
     impTransM (RL.members pctx) pctx mapTrans retType $
       translate $ _mbBinding $ typedEntryBody entry

-- | Translate all the entrypoints in a 'TypedBlockMap' that translate to
-- closures into the @LetRecType@s and bodies of those closures
translateBlockMapBodies :: PermCheckExtC ext exprExt =>
                           TypedBlockMapTrans ext blocks tops rets ->
                           TypedBlockMap TransPhase ext blocks tops rets ->
                           TypeTransM RNil [(OpenTerm, SpecTerm)]
translateBlockMapBodies mapTrans blkMap =
  sequence $ mapBlockMapClos (\entry ->
                               (,) <$> translateEntryLRT entry <*>
                               translateEntryBody mapTrans entry) blkMap

-- | Translate a CFG to a monadic function that takes all the top-level
-- arguments to that CFG and calls into its initial entrypoint; this monadic
-- function is used as the body of one of the closures used to translate the CFG
translateCFGInitBody ::
  PermCheckExtC ext exprExt =>
  TypedBlockMapTrans ext blocks (ghosts :++: inits) (gouts :> ret) ->
  TypedCFG ext blocks ghosts inits gouts ret ->
  TypeTransM RNil SpecTerm
translateCFGInitBody mapTrans cfg =
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
  impTransM all_membs pctx mapTrans retTypeTrans $
  translateCallEntry "CFG" init_entry (nuMulti all_px id) (nuMulti all_px $
                                                           const MNil)

-- | Translate a CFG to a monadic function that passes all of its arguments to
-- the closure with the given index, which is meant to be the closure whose body
-- is defined by 'translateCFGInitBody'
translateCFGIxCall :: TypedCFG ext blocks ghosts inits gouts ret -> Natural ->
                      TypeTransM RNil SpecTerm
translateCFGIxCall cfg ix =
  do let fun_perm = tpcfgFunPerm cfg
         h = tpcfgHandle cfg
         ctx = typedFnHandleAllArgs h
     lrt <- translateCFGLRT cfg
     lambdaExprCtx ctx $ lambdaPermCtx (funPermIns fun_perm) $ \pctx ->
       (infoCtx <$> ask) >>= \ectx ->
       return $
       applyCallClosSpecTerm lrt (mkBaseClosSpecTerm ix) (transTerms ectx ++
                                                          transTerms pctx)

-- | The components of the spec definition that a CFG translates to. Note that,
-- if the CFG is for a function that is mutually recursive with other functions,
-- then it also needs the closures of those functions in its spec definition.
data CFGTrans =
  CFGTrans { cfgTransLRT :: OpenTerm,
             cfgTransCloss :: [(OpenTerm,SpecTerm)],
             cfgTransBody :: SpecTerm }

-- | Translate a CFG to a list of closure definitions, represented as a pair of
-- a @LetRecType@ and a monadic function of that @LetRecType@. These closures
-- are for the CFG itself and for all of its entrypoints that are translated to
-- closures, i.e., with in-degree > 1. Use the current 'Natural' in the 'State'
-- monad as the starting index for these closures, and increment that 'Natural'
-- state for each closure body returned. Also return the 'Natural' index used
-- for the closure for the entire CFG. See 'translateTypedEntry' for an
-- explanation of the monad-in-monad type.
translateCFG :: PermCheckExtC ext exprExt =>
                TypedCFG ext blocks ghosts inits gouts ret ->
                State Natural (Natural, TypeTransM RNil CFGTrans)
translateCFG cfg =
  do let blkMap = tpcfgBlockMap cfg
     -- Get the natural number index for the top-level closure of the CFG
     cfg_ix <- get
     put (cfg_ix + 1)
     -- Translate the block map of the CFG by generating calls to closures for
     -- all the entrypoints with in-degree > 1
     mapTransM <- translateTypedBlockMap blkMap
     -- Return the CFG index and the computation for creating the bodies
     return
       (cfg_ix,
        do mapTrans <- mapTransM
           -- Generate the actual closure bodies + LRTs for those entrypoints
           closs <- translateBlockMapBodies mapTrans blkMap
           -- Generate the closure body + LRT for the entire CFG
           cfg_clos_body <- translateCFGInitBody mapTrans cfg
           cfg_lrt <- translateCFGLRT cfg
           let cfg_clos = (cfg_lrt,cfg_clos_body)
           -- Generate the body of the CFG, that calls the cfg_body closure
           cfg_body <- translateCFGIxCall cfg cfg_ix
           -- Then, finally, return all the closure lrts and bodies
           return $ CFGTrans cfg_lrt (cfg_clos : closs) cfg_body)


----------------------------------------------------------------------
-- * Translating Sets of CFGs
----------------------------------------------------------------------

-- | An existentially quantified tuple of a 'TypedCFG', its 'GlobalSymbol', and
-- a 'String' name we want to translate it to
data SomeTypedCFG ext where
  SomeTypedCFG :: PermCheckExtC ext exprExt => GlobalSymbol -> String ->
                  TypedCFG ext blocks ghosts inits gouts ret ->
                  SomeTypedCFG ext

-- | Helper function to build an LLVM function permission from a 'FunPerm'
mkPtrFunPerm :: HasPtrWidth w => FunPerm ghosts args gouts ret ->
                ValuePerm (LLVMPointerType w)
mkPtrFunPerm fun_perm =
  withKnownNat ?ptrWidth $ ValPerm_Conj1 $ mkPermLLVMFunPtr ?ptrWidth fun_perm

-- | Extract the 'FunPerm' of a 'SomeTypedCFG' as a permission on LLVM function
-- pointer values
someTypedCFGPtrPerm :: HasPtrWidth w => SomeTypedCFG LLVM ->
                       ValuePerm (LLVMPointerType w)
someTypedCFGPtrPerm (SomeTypedCFG _ _ cfg) = mkPtrFunPerm $ tpcfgFunPerm cfg

-- | Convert a 'SomedTypedCFG' and a closure index for its initial entrypoint
-- closure into an entry in the permission environment
someTypedCFGIxEntry :: HasPtrWidth w => SomeTypedCFG LLVM -> Natural ->
                       PermEnvGlobalEntry
someTypedCFGIxEntry (SomeTypedCFG sym _ cfg) ix =
  withKnownNat ?ptrWidth $
  PermEnvGlobalEntry sym (mkPtrFunPerm $ tpcfgFunPerm cfg)
  (GlobalTransClos $ mkBaseClosSpecTerm ix)

-- | Translate a list of CFGs for mutually recursive functions to a list of
-- @LetRecType@s and spec definitions of those @LetRecType@s
translateCFGsToDefs :: HasPtrWidth w => PermEnv -> ChecksFlag ->
                       [SomeTypedCFG LLVM] -> [(OpenTerm,OpenTerm)]
translateCFGsToDefs env checks some_cfgs =
  let (cfg_ixs, cfg_transsM) =
        unzip $ evalState (mapM (\(SomeTypedCFG _ _ cfg) ->
                                  translateCFG cfg) some_cfgs) 0
      tmp_env = permEnvAddGlobalSyms env $
        zipWith someTypedCFGIxEntry some_cfgs cfg_ixs
      cfg_transs = runNilTypeTransM tmp_env checks $ sequence cfg_transsM
      closs = concat $ map cfgTransCloss cfg_transs in
  map (\cfg_trans ->
        let lrt = cfgTransLRT cfg_trans in
        (lrt,
         defineSpecOpenTerm (permEnvEventTypeTerm env) closs
         lrt (cfgTransBody cfg_trans)))
  cfg_transs


-- | An existentially quantified tuple of a 'CFG', its function permission, and
-- a 'String' name we want to translate it to
data SomeCFGAndPerm ext where
  SomeCFGAndPerm :: GlobalSymbol -> String -> CFG ext blocks inits ret ->
                    FunPerm ghosts (CtxToRList inits) gouts ret ->
                    SomeCFGAndPerm ext

-- | Extract the 'GlobalSymbol' from a 'SomeCFGAndPerm'
someCFGAndPermSym :: SomeCFGAndPerm ext -> GlobalSymbol
someCFGAndPermSym (SomeCFGAndPerm sym _ _ _) = sym

-- | Extract the 'String' name from a 'SomeCFGAndPerm'
someCFGAndPermToName :: SomeCFGAndPerm ext -> String
someCFGAndPermToName (SomeCFGAndPerm _ nm _ _) = nm

-- | Map a 'SomeCFGAndPerm' to a 'PermEnvGlobalEntry' with no translation, i.e.,
-- with an 'error' term for the translation
someCFGAndPermGlobalEntry :: HasPtrWidth w => SomeCFGAndPerm ext ->
                             PermEnvGlobalEntry
someCFGAndPermGlobalEntry (SomeCFGAndPerm sym _ _ fun_perm) =
  withKnownNat ?ptrWidth $
  PermEnvGlobalEntry sym (mkPtrFunPerm fun_perm) $
  panic "someCFGAndPermGlobalEntry"
  ["Attempt to translate CFG during its own type-checking"]

-- | Convert the 'FunPerm' of a 'SomeCFGAndPerm' to an inductive @LetRecType@
-- description of the SAW core type it translates to
someCFGAndPermLRT :: PermEnv -> SomeCFGAndPerm ext -> OpenTerm
someCFGAndPermLRT env (SomeCFGAndPerm _ _ _ fun_perm) =
  typeDescLRT $ runNilTypeTransM env noChecks $ translateClosed fun_perm

-- | Construct a spec definition type for the event type in the supplied
-- environment with the supplied @LetRecType@
permEnvSpecDefOpenTerm :: PermEnv -> OpenTerm -> OpenTerm
permEnvSpecDefOpenTerm env lrt =
  applyGlobalOpenTerm "Prelude.SpecDef"
  [permEnvEventTypeTerm env, lrt]

-- | Type-check a list of functions in the Heapster type system, translate each
-- to a spec definition bound to the SAW core 'String' name associated with it,
-- add these translations as function permissions in the current environment,
-- and return the list of type-checked CFGs
tcTranslateAddCFGs ::
  HasPtrWidth w => SharedContext -> ModuleName -> PermEnv -> ChecksFlag ->
  EndianForm -> DebugLevel -> [SomeCFGAndPerm LLVM] ->
  IO (PermEnv, [SomeTypedCFG LLVM])
tcTranslateAddCFGs sc mod_name env checks endianness dlevel cfgs_and_perms =
  withKnownNat ?ptrWidth $
  do
    -- First, we type-check all the CFGs, mapping them to SomeTypedCFGs; this
    -- uses a temporary PermEnv where all the function symbols being
    -- type-checked are assigned their permissions, but no translation yet
    let tmp_env1 =
          permEnvAddGlobalSyms env $
          map someCFGAndPermGlobalEntry cfgs_and_perms
    let tc_cfgs =
          flip map cfgs_and_perms $ \(SomeCFGAndPerm gsym nm cfg fun_perm) ->
          SomeTypedCFG gsym nm $
          debugTraceTraceLvl dlevel ("Type-checking " ++ show gsym) $
          debugTrace verboseDebugLevel dlevel
          ("With type:\n" ++ permPrettyString emptyPPInfo fun_perm) $
          tcCFG ?ptrWidth tmp_env1 endianness dlevel fun_perm cfg

    -- Next, translate all those CFGs to spec definitions
    let lrts_defs = translateCFGsToDefs env checks tc_cfgs

    -- Insert each spec definition as a SAW core definition bound to its
    -- corresponding ident in the SAW core module mod_name, and generate entries
    -- for the environment mapping each function name to its SAW core ident
    new_entries <-
      zipWithM
      (\(SomeTypedCFG sym nm cfg) (lrt, def_tm) ->
        do tp <- completeNormOpenTerm sc $ permEnvSpecDefOpenTerm env lrt
           tm <- completeNormOpenTerm sc def_tm
           let ident = mkSafeIdent mod_name nm
           scInsertDef sc mod_name ident tp tm
           let perm = mkPtrFunPerm $ tpcfgFunPerm cfg
           return $ PermEnvGlobalEntry sym perm (GlobalTransDef $
                                                 globalOpenTerm ident))
      tc_cfgs lrts_defs

    -- Add the new entries to the environment and return the new environment and
    -- the type-checked CFGs
    return (permEnvAddGlobalSyms env new_entries, tc_cfgs)


----------------------------------------------------------------------
-- * Top-level Entrypoints for Translating Other Things
----------------------------------------------------------------------

-- | Translate a function permission to the type of a spec definition for the
-- translation of a function with that permission
translateCompleteFunPerm :: SharedContext -> PermEnv ->
                            FunPerm ghosts args gouts ret -> IO Term
translateCompleteFunPerm sc env fun_perm =
  completeNormOpenTerm sc $ permEnvSpecDefOpenTerm env $ typeDescLRT $
  runNilTypeTransM env noChecks (translateClosed fun_perm)

-- | Translate a 'TypeRepr' to the SAW core type it represents
translateCompleteType :: SharedContext -> PermEnv -> TypeRepr tp -> IO Term
translateCompleteType sc env typ_perm =
  completeNormOpenTerm sc $ typeTransType1 $
  runNilTypeTransM env noChecks $ translateType True typ_perm

-- | Translate a 'TypeRepr' within the given context of type arguments to the
-- SAW core type it represents
translateCompleteTypeInCtx :: SharedContext -> PermEnv ->
                              CruCtx args -> Mb args (TypeRepr a) -> IO Term
translateCompleteTypeInCtx sc env args ret =
  completeNormOpenTerm sc $ runNilTypeTransM env noChecks $
  piExprCtxPure args (typeTransType1 <$> translateType True (mbLift ret))

-- | Translate an input list of 'ValuePerms' and an output 'ValuePerm' to a pure
-- SAW core function type, not in the @SpecM@ monad. It is an error if any of
-- the permissions are impure, such as @lowned@ permissions.
translateCompletePureFun :: SharedContext -> PermEnv
                         -> CruCtx ctx -- ^ Type arguments
                         -> Mb ctx (ValuePerms args) -- ^ Input perms
                         -> Mb ctx (ValuePerm ret) -- ^ Return type perm
                         -> IO Term
translateCompletePureFun sc env ctx ps_in p_out =
  completeNormOpenTerm sc $ runNilTypeTransM env noChecks $ piExprCtxPure ctx $
  do ps_in_trans <- translate ps_in
     p_out_trans <- translate p_out
     let justOrPanic (Just x) = x
         justOrPanic Nothing =
           panic "translateCompletePureFun"
           ["Attempt to translate an impure permission to a pure type"]
     let (tps_in, tp_out) =
           justOrPanic
           ((,) <$>
            mapM typeDescPureType (typeTransDescs ps_in_trans) <*>
            typeDescPureType (tupleOfTypeDescs $ typeTransDescs p_out_trans))
     return $ piOpenTermMulti (map ("_",) tps_in) (const tp_out)
-}
