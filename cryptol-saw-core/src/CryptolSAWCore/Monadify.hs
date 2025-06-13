{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}

{- |
Module      : CryptolSAWCore.Monadify
Copyright   : Galois, Inc. 2021
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module implements a "monadification" transformation, which converts "pure"
SAW core terms that use inconsistent operations like @fix@ and convert them to
monadic SAW core terms that use monadic versions of these operations that are
consistent. The monad that is used is the @SpecM@ monad that is axiomatized in
the SAW core prelude. This is only a partial transformation, meaning that it
will fail on some SAW core terms. Specifically, it requires that all
applications @f arg@ in a term either have a non-dependent function type for @f@
(i.e., a function with type @'Pi' x a b@ where @x@ does not occur in @b@) or a
pure argument @arg@ that does not use any of the inconsistent operations.

Monadification is easiest to understand as a transformation on types that at a
high level replaces any function type of the form @a1 -> ... -> an -> b@ with
the monadic function type @a1' -> ... -> an' -> SpecM b'@, where @b'@ and each
@ai'@ are the result of monadifying @b@ and @ai@, respectively. Non-function
type constructors like pairs or vectors are monadified to themselves, though
their type arguments are also monadified. One slight complexity here is in
handling sequence types, which are either vectors for finite sequences or
functions from a natural number index to the element at that index for infinite
sequences. Since function types become monadic function types, infinite
sequences become monadic functions from a natural numbers to elements, i.e.,
streams of computations. This is all handled by defining the type @mseq@ of
"monadified sequences" that use vectors for finite lengths and streams of
computations for the infinite length.

In more detail, this transformation is defined with two type-level
transformations, @MT(a)@ and @CompMT(a)@, which define the "argument" and
"computational" monadification of @a@. The former is used to monadify arguments
in function types, and is also used to define _the_ monadification of a type.
The latter is used to monadify the return type of a function type, and adds a
@SpecM@ to that return type. These functions are defined as follows:

> MT(Pi x (sort 0) b) = Pi x (sort 0) CompMT(b)
> MT(Pi x Num b) = Pi x Num CompMT(b)
> MT(Pi _ a b) = MT(a) -> CompMT(b)
> MT(#(a,b)) = #(MT(a),MT(b))
> MT(seq n a) = mseq n MT(a)
> MT(f arg) = f MT(arg)  -- For pure type function f
> MT(cnst) = cnst
> MT(dt args) = dt MT(args)
> MT(x) = x
> MT(_) = error

> CompMT(tp = Pi _ _ _) = MT(tp)
> CompMT(n : Num) = n
> CompMT(tp) = SpecM MT(tp)

The way monadification of types is implemented here is in two pieces. The first
is the 'monadifyType' function and its associated helpers, which converts a SAW
core type into an internal representation captured by the Haskell type
'MonType'. The second piece is the functions 'toArgType' and 'toCompType', which
map a 'MonType' generated from SAW type @a@ to the result of applying @MT(a)@
and @CompMT(a)@, respectively.


FIXME: explain the term-level transformation below

Term-level translation:

MonArg(t : tp) ==> MT(tp)
MonArg(t) =
  case Mon(t) of
    m : SpecM MT(a) => shift \k -> m >>= \x -> k x
    _ => t

Mon(t : tp) ==> MT(tp) or CompMT(tp)  (which are the same type for pis)
Mon((f : Pi x a b) arg) = Mon(f) MT(arg)
Mon((f : Pi _ a b) arg) = Mon(f) MonArg(arg)
Mon(Lambda x a t) = Lambda x MT(a) Mon(t)
Mon((t,u)) = (MonArg(t),MonArg(u))
Mon(c args) = c MonArg(args)
Mon(x) = x
Mon(fix) = fixM (of some form...)
Mon(cnst) = cnstM  if cnst is impure and monadifies to constM
Mon(cnst) = cnst   otherwise
-}

module CryptolSAWCore.Monadify where

import Numeric.Natural
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as Text
import Control.Monad (forM_, unless)
import Control.Monad.Cont (Cont, cont, runCont)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Control.Monad.State (MonadState(..), StateT(..), evalStateT, modify)
import Control.Monad.Trans (MonadTrans(..))
import qualified Control.Monad.Fail as Fail
-- import Control.Monad.IO.Class (MonadIO, liftIO)
import qualified Data.Text as T
import qualified Text.URI as URI
import Data.Type.Equality

import qualified SAWSupport.Pretty as PPS (defaultOpts)

import SAWCore.Module (Def(..), ResolvedName(..), lookupVarIndexInMap)
import SAWCore.Name
import SAWCore.Term.Functor
import SAWCore.SharedTerm
import SAWCore.OpenTerm
import SAWCore.Term.Pretty (scPrettyTermInCtx)

import CryptolSAWCore.Panic
import CryptolSAWCore.TypedTerm
import CryptolSAWCore.Cryptol (Env)
import SAWCore.Recognizer
-- import SAWCore.Position
import CryptolSAWCore.PreludeM

import GHC.Stack
-- import Debug.Trace


-- FIXME: move to OpenTerm.hs

-- | A global definition, which is either a primitive or a constant. As
-- described in the documentation for 'ExtCns', the names need not be unique,
-- but the 'VarIndex' is, and this is what is used to index 'GlobalDef's.
data GlobalDef = GlobalDef { globalDefName :: NameInfo,
                             globalDefIndex :: VarIndex,
                             globalDefType :: Term,
                             globalDefTerm :: Term }

instance Eq GlobalDef where
  gd1 == gd2 = globalDefIndex gd1 == globalDefIndex gd2

instance Ord GlobalDef where
  compare gd1 gd2 = compare (globalDefIndex gd1) (globalDefIndex gd2)

instance Show GlobalDef where
  show = show . globalDefName

-- | Get the 'String' name of a 'GlobalDef'
globalDefString :: GlobalDef -> String
globalDefString = T.unpack . toAbsoluteName . globalDefName

-- | Build an 'OpenTerm' from a 'GlobalDef'
globalDefOpenTerm :: GlobalDef -> OpenTerm
globalDefOpenTerm = closedOpenTerm . globalDefTerm

-- | Recognize a named global definition, including its type
asTypedGlobalDef :: Recognizer Term GlobalDef
asTypedGlobalDef t =
  case unwrapTermF t of
    Constant ec ->
      Just $ GlobalDef (ecName ec) (ecVarIndex ec) (ecType ec) t
    FTermF (ExtCns ec) ->
      Just $ GlobalDef (ecName ec) (ecVarIndex ec) (ecType ec) t
    _ -> Nothing


-- FIXME HERE NOW: remove these if no longer needed
{-

----------------------------------------------------------------------
-- * Typing All Subterms
----------------------------------------------------------------------

-- | A SAW core term where all of the subterms are typed
data TypedSubsTerm
  = TypedSubsTerm { tpSubsIndex :: Maybe TermIndex,
                    tpSubsFreeVars :: BitSet,
                    tpSubsTermF :: TermF TypedSubsTerm,
                    tpSubsTypeF :: TermF TypedSubsTerm,
                    tpSubsSort :: Sort }

-- | Convert a 'Term' to a 'TypedSubsTerm'
typeAllSubterms :: SharedContext -> Term -> IO TypedSubsTerm
typeAllSubterms = error "FIXME HERE"

-- | Convert a 'TypedSubsTerm' back to a 'Term'
typedSubsTermTerm :: TypedSubsTerm -> Term
typedSubsTermTerm = error "FIXME HERE"

-- | Get the type of a 'TypedSubsTerm' as a 'TypedSubsTerm'
typedSubsTermType :: TypedSubsTerm -> TypedSubsTerm
typedSubsTermType tst =
  TypedSubsTerm { tpSubsIndex = Nothing, tpSubsFreeVars = tpSubsFreeVars tst,
                  tpSubsTermF = tpSubsTypeF tst,
                  tpSubsTypeF = FTermF (Sort (tpSubsSort tst) noFlags),
                  tpSubsSort = sortOf (tpSubsSort tst) }

-- | Count the number of right-nested pi-abstractions of a 'TypedSubsTerm'
typedSubsTermArity :: TypedSubsTerm -> Int
typedSubsTermArity (TypedSubsTerm { tpSubsTermF = Pi _ _ tst }) =
  1 + typedSubsTermArity tst
typedSubsTermArity _ = 0

-- | Count the number of right-nested pi abstractions in a term, which
-- represents a type. This assumes that the type is in WHNF.
typeArity :: Term -> Int
typeArity tp = length $ fst $ asPiList tp

class ToTerm a where
  toTerm :: a -> Term

instance ToTerm Term where
  toTerm = id

instance ToTerm TypedSubsTerm where
  toTerm = typedSubsTermTerm

unsharedApply :: Term -> Term -> Term
unsharedApply f arg = Unshared $ App f arg
-}


----------------------------------------------------------------------
-- * Monadifying Types
----------------------------------------------------------------------

-- | Test if a 'Term' is a first-order function type
isFirstOrderType :: Term -> Bool
isFirstOrderType (asPi -> Just (_, asPi -> Just _, _)) = False
isFirstOrderType (asPi -> Just (_, _, tp_out)) = isFirstOrderType tp_out
isFirstOrderType _ = True

-- | The implicit argument version of 'EventType'
type HasSpecMEvType = (?specMEvType :: EventType)

-- | The kinds used in monadification, i.e., the types of 'MonType's. These
-- correspond to constructors of the SAW core type @KindDesc@, though we only
-- use the subset that occur in Cryptol types here
data MonKind = MKType | MKNum deriving Eq

type MKType = 'MKType
type MKNum = 'MKNum

-- | The @Num@ type as a SAW core term
numTypeOpenTerm :: OpenTerm
numTypeOpenTerm = dataTypeOpenTerm "Cryptol.Num" []

-- | Representing type-level kinds at the data level
data KindRepr (k :: MonKind) where
  MKTypeRepr :: KindRepr MKType
  MKNumRepr :: KindRepr MKNum

-- | Convert a 'KindRepr' to the SAW core type it represents
kindReprOpenTerm :: KindRepr k -> OpenTerm
kindReprOpenTerm MKTypeRepr = sortOpenTerm $ mkSort 0
kindReprOpenTerm MKNumRepr = numTypeOpenTerm

instance TestEquality KindRepr where
  -- NOTE: we write the patterns like this so that there are still 2*n cases for
  -- n constructors but if we add a new constructor coverage checking will fail
  testEquality MKTypeRepr MKTypeRepr = Just Refl
  testEquality MKTypeRepr _ = Nothing
  testEquality MKNumRepr MKNumRepr = Just Refl
  testEquality MKNumRepr _ = Nothing

-- | A 'KindRepr' for a kind that is determined at runtime
data SomeKindRepr where SomeKindRepr :: KindRepr k -> SomeKindRepr

-- | A binary operation on @Num@ expressions
data NumBinOp = NBinOp_Add | NBinOp_Mul

-- | A representation of type-level @Num@ expressions, i.e., SAW core terms of
-- type @TpExpr Kind_num@
data NumTpExpr
     -- | A type-level deBrujn level (not index; see docs on 'MTyVarLvl', below)
  = NExpr_VarLvl Natural
    -- | A @Num@ value as an expression
  | NExpr_Const OpenTerm
    -- | A binary operation on @Num@s
  | NExpr_BinOp NumBinOp NumTpExpr NumTpExpr

-- | The internal (to monadification) representation of a SAW core type that is
-- being monadified. Most of these constructors have corresponding constructors
-- in the SAW core inductive type @TpDesc@ of type descriptions, other than
-- 'MTyIndesc', which represents indescribable types
data MonType
  = forall k. MTyForall LocalName (KindRepr k) (TpExpr k -> MonType)
  | MTyArrow MonType MonType
  | MTySeq NumTpExpr MonType
  | MTyUnit
  | MTyBool
  | MTyBV Natural
  | MTyPair MonType MonType
  | MTySum MonType MonType
    -- | A type with no type description, meaning it cannot be used in a
    -- fixpoint
  | MTyIndesc OpenTerm
    -- | A type-level deBruijn level, where 0 refers to the outermost binding
    -- (as opposed to deBruijn indices, where 0 refers to the innermost
    -- binding); only used by 'toTpDesc' to convert a 'MonType' to a type
    -- description, and should never be seen outside of that function
  | MTyVarLvl Natural

-- | A type-level expression of the given kind; corresponds to the SAW core type
-- @kindElem K@
type family TpExpr (k::MonKind) where
  TpExpr MKType = MonType
  TpExpr MKNum = NumTpExpr

-- | A type-level expression whose kind is determined dynamically
data SomeTpExpr where SomeTpExpr :: KindRepr k -> TpExpr k -> SomeTpExpr

-- | Build a deBruijn level as a type-level expression of a given kind
kindVar :: KindRepr k -> Natural -> TpExpr k
kindVar MKTypeRepr = MTyVarLvl
kindVar MKNumRepr = NExpr_VarLvl

-- | Build a type-level expression from a value of kind @k@
kindOfVal :: KindRepr k -> OpenTerm -> TpExpr k
kindOfVal MKTypeRepr = MTyIndesc
kindOfVal MKNumRepr = NExpr_Const

-- | Test if a monadification type @tp@ is considered a base type, meaning that
-- @CompMT(tp) = CompM MT(tp)@
isBaseType :: MonType -> Bool
isBaseType (MTyForall _ _ _) = False
isBaseType (MTyArrow _ _) = False
isBaseType _ = True

-- | Convert a SAW core 'Term' to a monadification kind, if possible
monadifyKind :: Term -> Maybe SomeKindRepr
monadifyKind (asDataType -> Just (num, []))
  | primName num == "Cryptol.Num" = Just $ SomeKindRepr MKNumRepr
monadifyKind (asSort -> Just s) | s == mkSort 0 = Just $ SomeKindRepr MKTypeRepr
monadifyKind _ = Nothing

-- | Convert a numeric binary operation to a SAW core binary function on @Num@
numBinOpOp :: NumBinOp -> OpenTerm
numBinOpOp NBinOp_Add = globalOpenTerm "Cryptol.tcAdd"
numBinOpOp NBinOp_Mul = globalOpenTerm "Cryptol.tcMul"

-- | Convert a numeric type expression to a SAW core @Num@ term; it is an error
-- if it contains a deBruijn level
numExprVal :: NumTpExpr -> OpenTerm
numExprVal (NExpr_VarLvl _) =
  panic "numExprVal" ["Unexpected deBruijn variable"]
numExprVal (NExpr_Const n) = n
numExprVal (NExpr_BinOp op e1 e2) =
  applyOpenTermMulti (numBinOpOp op) [numExprVal e1, numExprVal e2]

-- | Convert a 'MonType' to the argument type @MT(tp)@ it represents; should
-- only ever be applied to a 'MonType' that represents a valid SAW core type,
-- i.e., one not containing 'MTyNum' or 'MTyVarLvl'
toArgType :: HasSpecMEvType => MonType -> OpenTerm
toArgType (MTyForall x k body) =
  piOpenTerm x (kindReprOpenTerm k) (\e -> toCompType (body $ kindOfVal k e))
toArgType (MTyArrow t1 t2) =
  arrowOpenTerm "_" (toArgType t1) (toCompType t2)
toArgType (MTySeq n t) =
  applyOpenTermMulti (globalOpenTerm "SpecM.mseq")
  [evTypeTerm ?specMEvType, numExprVal n, toArgType t]
toArgType MTyUnit = unitTypeOpenTerm
toArgType MTyBool = boolTypeOpenTerm
toArgType (MTyBV n) = bitvectorTypeOpenTerm $ natOpenTerm n
toArgType (MTyPair mtp1 mtp2) =
  pairTypeOpenTerm (toArgType mtp1) (toArgType mtp2)
toArgType (MTySum mtp1 mtp2) =
  dataTypeOpenTerm "Prelude.Either" [toArgType mtp1, toArgType mtp2]
toArgType (MTyIndesc t) = t
toArgType (MTyVarLvl _) = panic "toArgType" ["Unexpected deBruijn index"]

-- | Convert a 'MonType' to the computation type @CompMT(tp)@ it represents
toCompType :: HasSpecMEvType => MonType -> OpenTerm
toCompType mtp@(MTyForall _ _ _) = toArgType mtp
toCompType mtp@(MTyArrow _ _) = toArgType mtp
toCompType mtp = specMTypeOpenTerm ?specMEvType $ toArgType mtp

-- | Convert a 'TpExpr' to either an argument type or a @Num@ term, depending on
-- its kind
tpExprVal :: HasSpecMEvType => KindRepr k -> TpExpr k -> OpenTerm
tpExprVal MKTypeRepr = toArgType
tpExprVal MKNumRepr = numExprVal

-- | Convert a 'SomeTpExpr' to either an argument type or a @Num@ term,
-- depending on its kind
someTpExprVal :: HasSpecMEvType => SomeTpExpr -> OpenTerm
someTpExprVal (SomeTpExpr k e) = tpExprVal k e

-- | Convert a 'MonKind' to the kind description it represents
toKindDesc :: KindRepr k -> OpenTerm
toKindDesc MKTypeRepr = tpKindDesc
toKindDesc MKNumRepr = numKindDesc

-- | Convert a numeric binary operation to a SAW core term of type @TpExprBinOp@
numBinOpExpr :: NumBinOp -> OpenTerm
numBinOpExpr NBinOp_Add = ctorOpenTerm "SpecM.BinOp_AddNum" []
numBinOpExpr NBinOp_Mul = ctorOpenTerm "SpecM.BinOp_MulNum" []

-- | Convert a numeric type expression to a type-level expression, i.e., a SAW
-- core term of type @TpExpr Kind_num@, assuming the supplied number of bound
-- deBruijn levels
numExprExpr :: Natural -> NumTpExpr -> OpenTerm
numExprExpr lvl (NExpr_VarLvl l) =
  -- Convert to a deBruijn index instead of a level (we use levels because they
  -- are invariant under substitution): since there are lvl free variables, the
  -- most recently bound is lvl - 1, so this has deBruijn index 0, while the
  -- least recently bound is 0, so this has deBruijn index lvl - 1; lvl - l - 1
  -- thus gives us what we need
  varTpExpr numExprKind (lvl - l - 1)
numExprExpr _ (NExpr_Const n) = constTpExpr numExprKind n
numExprExpr lvl (NExpr_BinOp op e1 e2) =
  binOpTpExpr (numBinOpExpr op) numKindDesc numKindDesc numKindDesc
  (numExprExpr lvl e1) (numExprExpr lvl e2)

-- | Main implementation of 'toTpDesc'. Convert a 'MonType' to the type
-- description it represents, assuming the supplied number of bound deBruijn
-- indices. The 'Bool' flag indicates whether the 'MonType' should be treated
-- like a function type, meaning that the @Tp_M@ constructor should be added if
-- the type is not already a function type.
toTpDescH :: Natural -> Bool -> MonType -> OpenTerm
toTpDescH lvl _ (MTyForall _ k body) =
  piTpDesc (toKindDesc k) $ toTpDescH (lvl+1) True $ body $ kindVar k lvl
toTpDescH lvl _ (MTyArrow mtp1 mtp2) =
  arrowTpDesc (toTpDescH lvl False mtp1) (toTpDescH lvl True mtp2)
toTpDescH lvl True mtp =
  -- Convert a non-functional type to a functional one by making a nullary
  -- monadic function, i.e., applying the @SpecM@ type constructor
  mTpDesc $ toTpDescH lvl False mtp
toTpDescH lvl False (MTySeq n mtp) =
  seqTpDesc (numExprExpr lvl n) (toTpDescH lvl False mtp)
toTpDescH _ False MTyUnit = unitTpDesc
toTpDescH _ False MTyBool = boolTpDesc
toTpDescH _ False (MTyBV w) = bvTpDesc w
toTpDescH lvl False (MTyPair mtp1 mtp2) =
  pairTpDesc (toTpDescH lvl False mtp1) (toTpDescH lvl False mtp2)
toTpDescH lvl False (MTySum mtp1 mtp2) =
  sumTpDesc (toTpDescH lvl False mtp1) (toTpDescH lvl False mtp2)
toTpDescH _ _ (MTyIndesc trm) =
  bindPPOpenTerm trm $ \pp_trm ->
  failOpenTerm ("toTpDescH: indescribable type:\n" ++ pp_trm)
toTpDescH lvl False (MTyVarLvl l) =
  -- Convert a deBruijn level to a deBruijn index; see comments in numExprExpr
  varTpDesc (lvl - l - 1)

-- | Convert a 'MonType' to the type description it represents
toTpDesc :: MonType -> OpenTerm
toTpDesc = toTpDescH 0 False

-- | The mapping for monadifying Cryptol typeclasses
-- FIXME: this is no longer needed, as it is now the identity
typeclassMonMap :: [(Ident,Ident)]
typeclassMonMap =
  [("Cryptol.PEq", "Cryptol.PEq"),
   ("Cryptol.PCmp", "Cryptol.PCmp"),
   ("Cryptol.PSignedCmp", "Cryptol.PSignedCmp"),
   ("Cryptol.PZero", "Cryptol.PZero"),
   ("Cryptol.PLogic", "Cryptol.PLogic"),
   ("Cryptol.PRing", "Cryptol.PRing"),
   ("Cryptol.PIntegral", "Cryptol.PIntegral"),
   ("Cryptol.PLiteral", "Cryptol.PLiteral")]

-- | The mapping for monadifying type-level binary @Num@ operations
numBinOpMonMap :: [(Ident,NumBinOp)]
numBinOpMonMap =
  [("Cryptol.tcAdd", NBinOp_Add), ("Cryptol.tcMul", NBinOp_Mul)
   -- FIXME: handle the others:
   -- "Cryptol.tcSub", "Cryptol.tcDiv", "Cryptol.tcMod", "Cryptol.tcExp",
   -- "Cryptol.tcMin", "Cryptol.tcMax"
  ]

-- | A context of local variables used for monadifying types, which includes the
-- variable names, their original types (before monadification), and an optional
-- 'MonType' bound to the variable if its type corresponds to a 'MonKind',
-- meaning its binding site is being translated into an 'MTyForall'.
--
-- NOTE: the reason this type is different from 'MonadifyCtx', the context type
-- for monadifying terms, is that monadifying arrow types does not introduce a
-- local 'MonTerm' argument, since they are not dependent functions and so do
-- not use a HOAS encoding.
type MonadifyTypeCtx = [(LocalName, Term, Maybe SomeTpExpr)]

-- | Pretty-print a 'Term' relative to a 'MonadifyTypeCtx'
ppTermInTypeCtx :: MonadifyTypeCtx -> Term -> String
ppTermInTypeCtx ctx t =
  scPrettyTermInCtx PPS.defaultOpts (map (\(x,_,_) -> x) ctx) t

-- | Extract the variables and their original types from a 'MonadifyTypeCtx'
typeCtxPureCtx :: MonadifyTypeCtx -> [(LocalName,Term)]
typeCtxPureCtx = map (\(x,tp,_) -> (x,tp))


-- | Monadify a type and convert it to its corresponding argument type
monadifyTypeArgType :: (HasCallStack, HasSpecMEvType) => MonadifyTypeCtx ->
                       Term -> OpenTerm
monadifyTypeArgType ctx t = toArgType $ monadifyType ctx t

-- | Check if a type-level operation, given by identifier, matching a 'NumBinOp'
monadifyNumBinOp :: Ident -> Maybe NumBinOp
monadifyNumBinOp i = lookup i numBinOpMonMap


-- | Convert a SAW core 'Term' to a type-level expression of some kind, or panic
-- if this is not possible
monadifyTpExpr :: (HasCallStack, HasSpecMEvType) => MonadifyTypeCtx -> Term ->
                  SomeTpExpr
{-
monadifyTpExpr ctx t
  | trace ("\nmonadifyTpExpr:\n" ++ ppTermInTypeCtx ctx t) False = undefined
-}

-- Type cases
monadifyTpExpr ctx (asPi -> Just (x, tp_in, tp_out))
  | Just (SomeKindRepr k) <- monadifyKind tp_in =
    SomeTpExpr MKTypeRepr $
    MTyForall x k (\tp' ->
                    let ctx' = (x,tp_in,Just (SomeTpExpr k tp')):ctx in
                    monadifyType ctx' tp_out)
monadifyTpExpr ctx tp@(asPi -> Just (_, _, tp_out))
  | inBitSet 0 (looseVars tp_out) =
    -- FIXME: make this a failure instead of an error
    error ("monadifyType: " ++
           "dependent function type with non-kind argument type: " ++
           ppTermInTypeCtx ctx tp)
monadifyTpExpr ctx tp@(asPi -> Just (x, tp_in, tp_out)) =
  SomeTpExpr MKTypeRepr $
  MTyArrow (monadifyType ctx tp_in) (monadifyType ((x,tp,Nothing):ctx) tp_out)
monadifyTpExpr _ (asTupleType -> Just []) =
  SomeTpExpr MKTypeRepr $ MTyUnit
monadifyTpExpr ctx (asPairType -> Just (tp1, tp2)) =
  SomeTpExpr MKTypeRepr $
  MTyPair (monadifyType ctx tp1) (monadifyType ctx tp2)
{-
monadifyType ctx (asRecordType -> Just tps) =
  MTyRecord $ map (\(fld,tp) -> (fld, monadifyType ctx tp)) $ Map.toList tps
-}
{- FIXME: do we ever need this?
monadifyType ctx (asDataType -> Just (eq_pn, [k_trm, tp1, tp2]))
  | primName eq_pn == "Prelude.Eq" =
  , isJust (monadifyKind k_trm) =
    -- NOTE: technically this is a Prop and not a sort 0, but it doesn't matter
    MTyIndesc $ dataTypeOpenTerm "Prelude.Eq" [monadifyTypeArgType ctx tp1,
                                               monadifyTypeArgType ctx tp2]
-}
monadifyTpExpr ctx (asDataType -> Just (pn, args)) =
  -- NOTE: this case only recognizes data types whose arguments are all types
  -- and/or Nums
  SomeTpExpr MKTypeRepr $
  MTyIndesc $ dataTypeOpenTerm (primName pn) (map (someTpExprVal .
                                                   monadifyTpExpr ctx) args)
monadifyTpExpr _ (asBitvectorType -> Just w) =
  SomeTpExpr MKTypeRepr $ MTyBV w
monadifyTpExpr ctx (asVectorType -> Just (asNat -> Just n, a)) =
  let nM = NExpr_Const $ ctorOpenTerm "Cryptol.TCNum" [natOpenTerm n]
   in SomeTpExpr MKTypeRepr $ MTySeq nM (monadifyType ctx a)
monadifyTpExpr ctx (asApplyAll -> ((asGlobalDef -> Just seq_id), [n, a]))
  | seq_id == "Cryptol.seq" =
    SomeTpExpr MKTypeRepr $ MTySeq (monadifyNum ctx n) (monadifyType ctx a)
monadifyTpExpr ctx (asApp -> Just ((asGlobalDef -> Just f), arg))
  | Just f_trans <- lookup f typeclassMonMap =
    SomeTpExpr MKTypeRepr $ MTyIndesc $
    applyOpenTerm (globalOpenTerm f_trans) $ monadifyTypeArgType ctx arg
monadifyTpExpr _ (asGlobalDef -> Just bool_id)
  | bool_id == "Prelude.Bool" = 
    SomeTpExpr MKTypeRepr $ MTyBool
monadifyTpExpr _ (asGlobalDef -> Just integer_id)
  | integer_id == "Prelude.Integer" =
    SomeTpExpr MKTypeRepr $ MTyIndesc $ globalOpenTerm "Prelude.Integer"
{-
monadifyType ctx (asApplyAll -> (f, args))
  | Just glob <- asTypedGlobalDef f
  , Just ec_k <- monadifyKind $ globalDefType glob
  , margs <- map (monadifyType ctx) args
  , Just k_out <- applyKinds ec_k margs =
    MTyBase k_out (applyOpenTermMulti (globalDefOpenTerm glob) $
                   map toArgType margs)
-}

-- Num cases
monadifyTpExpr _ (asGlobalApply "Cryptol.TCInf" -> Just [])
  = SomeTpExpr MKNumRepr $ NExpr_Const $ ctorOpenTerm "Cryptol.TCInf" []
monadifyTpExpr _ (asGlobalApply "Cryptol.TCNum" -> Just [asNat -> Just n])
  = SomeTpExpr MKNumRepr $ NExpr_Const $ ctorOpenTerm "Cryptol.TCNum" [natOpenTerm n]
monadifyTpExpr ctx (asApplyAll -> ((asGlobalDef -> Just f), [arg1, arg2]))
  | Just op <- monadifyNumBinOp f
  = SomeTpExpr MKNumRepr $ NExpr_BinOp op (monadifyNum ctx arg1) (monadifyNum ctx arg2)
monadifyTpExpr ctx (asLocalVar -> Just i)
  | i < length ctx
  , (_,_,Just (SomeTpExpr k e)) <- ctx!!i = SomeTpExpr k e
monadifyTpExpr ctx tp =
  -- XXX this doesn't look like it should be a panic
  panic "monadifyTpExpr" [
      "Not a valid type or numeric expression for monadification: " <>
          T.pack (ppTermInTypeCtx ctx tp)
  ]

-- | Convert a SAW core 'Term' to a monadification type, or panic if this is not
-- possible
monadifyType :: (HasCallStack, HasSpecMEvType) => MonadifyTypeCtx -> Term ->
                MonType
monadifyType ctx t
  | SomeTpExpr MKTypeRepr tp <- monadifyTpExpr ctx t = tp
monadifyType ctx t =
  panic "monadifyType" ["Not a type: " <> T.pack (ppTermInTypeCtx ctx t)]

-- | Convert a SAW core 'Term' to a type-level numeric expression, or panic if
-- this is not possible
monadifyNum :: (HasCallStack, HasSpecMEvType) => MonadifyTypeCtx -> Term ->
               NumTpExpr
monadifyNum ctx t
  | SomeTpExpr MKNumRepr e <- monadifyTpExpr ctx t = e
monadifyNum ctx t =
  panic "monadifyNum" ["Not a numeric expression: " <> T.pack (ppTermInTypeCtx ctx t)]


----------------------------------------------------------------------
-- * Monadified Terms
----------------------------------------------------------------------

-- | A representation of a term that has been translated to argument type
-- @MT(tp)@
data ArgMonTerm
    -- | A monadification term of a base type @MT(tp)@
  = BaseMonTerm MonType OpenTerm
    -- | A monadification term of non-depedent function type
  | FunMonTerm LocalName MonType MonType (ArgMonTerm -> MonTerm)
    -- | A monadification term of polymorphic type
  | forall k. ForallMonTerm LocalName (KindRepr k) (TpExpr k -> MonTerm)

-- | A representation of a term that has been translated to computational type
-- @CompMT(tp)@
data MonTerm
  = ArgMonTerm ArgMonTerm
  | CompMonTerm MonType OpenTerm

-- | An argument to a 'MonTerm' of functional type
data MonArg
     -- | A type-level expression argument to a polymorphic function
  = forall k. TpArg (KindRepr k) (TpExpr k)
    -- | A term-level argument to a non-dependent function
  | TrmArg ArgMonTerm

-- | Convert a 'SomeTpExpr' to a type-level 'MonArg' argument
tpExprToArg :: SomeTpExpr -> MonArg
tpExprToArg (SomeTpExpr k e) = TpArg k e

-- | Convert a numeric expression to a type-level 'MonArg' argument
numToArg :: NumTpExpr -> MonArg
numToArg = TpArg MKNumRepr

-- | Get the monadification type of a monadification term
class GetMonType a where
  getMonType :: a -> MonType

instance GetMonType ArgMonTerm where
  getMonType (BaseMonTerm tp _) = tp
  getMonType (ForallMonTerm x k body) = MTyForall x k (getMonType . body)
  getMonType (FunMonTerm _ tp_in tp_out _) = MTyArrow tp_in tp_out

instance GetMonType MonTerm where
  getMonType (ArgMonTerm t) = getMonType t
  getMonType (CompMonTerm tp _) = tp


-- | Convert a monadification term to a SAW core term of type @CompMT(tp)@
class ToCompTerm a where
  toCompTerm :: HasSpecMEvType => a -> OpenTerm

instance ToCompTerm ArgMonTerm where
  toCompTerm (BaseMonTerm mtp t) =
    retSOpenTerm ?specMEvType (toArgType mtp) t
  toCompTerm (FunMonTerm x tp_in _ body) =
    lambdaOpenTerm x (toArgType tp_in) (toCompTerm . body . fromArgTerm tp_in)
  toCompTerm (ForallMonTerm x k body) =
    lambdaOpenTerm x (kindReprOpenTerm k) (toCompTerm . body . kindOfVal k)

instance ToCompTerm MonTerm where
  toCompTerm (ArgMonTerm amtrm) = toCompTerm amtrm
  toCompTerm (CompMonTerm _ trm) = trm


-- | Convert an 'ArgMonTerm' to a SAW core term of type @MT(tp)@
toArgTerm :: HasSpecMEvType => ArgMonTerm -> OpenTerm
toArgTerm (BaseMonTerm _ t) = t
toArgTerm t = toCompTerm t


-- | Build a monadification term from a term of type @MT(tp)@
class FromArgTerm a where
  fromArgTerm :: HasSpecMEvType => MonType -> OpenTerm -> a

instance FromArgTerm ArgMonTerm where
  fromArgTerm (MTyForall x k body) t =
    ForallMonTerm x k (\tp -> fromCompTerm (body tp) (applyOpenTerm t $
                                                      tpExprVal k tp))
  fromArgTerm (MTyArrow t1 t2) t =
    FunMonTerm "_" t1 t2 (\x -> fromCompTerm t2 (applyOpenTerm t $ toArgTerm x))
  fromArgTerm tp t = BaseMonTerm tp t

instance FromArgTerm MonTerm where
  fromArgTerm mtp t = ArgMonTerm $ fromArgTerm mtp t

-- | Build a monadification term from a computational term of type @CompMT(tp)@
fromCompTerm :: HasSpecMEvType => MonType -> OpenTerm -> MonTerm
fromCompTerm mtp t | isBaseType mtp = CompMonTerm mtp t
fromCompTerm mtp t = ArgMonTerm $ fromArgTerm mtp t

-- | Test if a monadification type @tp@ is pure, meaning @MT(tp)=tp@
monTypeIsPure :: MonType -> Bool
monTypeIsPure (MTyForall _ _ _) = False
monTypeIsPure (MTyArrow _ _) = False
monTypeIsPure (MTySeq _ _) = False
monTypeIsPure MTyUnit = True
monTypeIsPure MTyBool = True
monTypeIsPure (MTyBV _) = True
monTypeIsPure (MTyPair mtp1 mtp2) = monTypeIsPure mtp1 && monTypeIsPure mtp2
monTypeIsPure (MTySum mtp1 mtp2) = monTypeIsPure mtp1 && monTypeIsPure mtp2
monTypeIsPure (MTyIndesc _) = True
monTypeIsPure (MTyVarLvl _) =
  panic "monTypeIsPure" ["Unexpected type variable"]

-- | Test if a monadification type @tp@ is semi-pure, meaning @SemiP(tp) = tp@,
-- where @SemiP@ is defined in the documentation for 'fromSemiPureTermFun' below
monTypeIsSemiPure :: MonType -> Bool
monTypeIsSemiPure (MTyForall _ k tp_f) =
  monTypeIsSemiPure $ tp_f $ kindOfVal k $
  -- This dummy OpenTerm should never be inspected by the recursive call
  error "monTypeIsSemiPure"
monTypeIsSemiPure (MTyArrow tp_in tp_out) =
  monTypeIsPure tp_in && monTypeIsSemiPure tp_out
monTypeIsSemiPure (MTySeq _ _) = False
monTypeIsSemiPure MTyUnit = True
monTypeIsSemiPure MTyBool = True
monTypeIsSemiPure (MTyBV _) = True
monTypeIsSemiPure (MTyPair mtp1 mtp2) =
  -- NOTE: functions in pairs are not semi-pure; only pure types in pairs are
  -- semi-pure
  monTypeIsPure mtp1 && monTypeIsPure mtp2
monTypeIsSemiPure (MTySum mtp1 mtp2) =
  -- NOTE: same as pairs
  monTypeIsPure mtp1 && monTypeIsPure mtp2
monTypeIsSemiPure (MTyIndesc _) = True
monTypeIsSemiPure (MTyVarLvl _) =
  panic "monTypeIsSemiPure" ["Unexpected type variable"]

-- | Build a monadification term from a function on terms which, when viewed as
-- a lambda, is a "semi-pure" function of the given monadification type, meaning
-- it maps terms of argument type @MT(tp)@ to an output value of argument type;
-- i.e., it has type @SemiP(tp)@, defined as:
--
-- > SemiP(Pi x (sort 0) b) = Pi x (sort 0) SemiP(b)
-- > SemiP(Pi x Num b) = Pi x Num SemiP(b)
-- > SemiP(Pi _ a b) = MT(a) -> SemiP(b)
-- > SemiP(a) = MT(a)
fromSemiPureTermFun :: HasSpecMEvType => MonType -> ([OpenTerm] -> OpenTerm) ->
                       ArgMonTerm
fromSemiPureTermFun (MTyForall x k body) f =
  ForallMonTerm x k $ \e ->
  ArgMonTerm $ fromSemiPureTermFun (body e) (f . (tpExprVal k e:))
fromSemiPureTermFun (MTyArrow t1 t2) f =
  FunMonTerm "_" t1 t2 $ \x ->
  ArgMonTerm $ fromSemiPureTermFun t2 (f . (toArgTerm x:))
fromSemiPureTermFun tp f = BaseMonTerm tp (f [])

-- | Like 'fromSemiPureTermFun' but use a term rather than a term function
fromSemiPureTerm :: HasSpecMEvType => MonType -> OpenTerm -> ArgMonTerm
fromSemiPureTerm mtp t = fromSemiPureTermFun mtp (applyOpenTermMulti t)

-- | Build an 'ArgMonTerm' that 'fail's when converted to a term
failArgMonTerm :: HasSpecMEvType => MonType -> String -> ArgMonTerm
failArgMonTerm tp str = BaseMonTerm tp (failOpenTerm str)

-- | Build a 'MonTerm' that 'fail's when converted to a term
failMonTerm :: HasSpecMEvType => MonType -> String -> MonTerm
failMonTerm tp str = ArgMonTerm $ failArgMonTerm tp str

-- | Apply a monadified type to a type or term argument in the sense of
-- 'applyPiOpenTerm', meaning give the type of applying @f@ of a type to a
-- particular argument @arg@
applyMonType :: HasCallStack => MonType -> MonArg -> MonType
applyMonType (MTyForall _ k1 f) (TpArg k2 t)
  | Just Refl <- testEquality k1 k2 = f t
applyMonType (MTyArrow _ tp_ret) (TrmArg _) = tp_ret
applyMonType _ _ = error "applyMonType: application at incorrect type"

-- | Apply a monadified term to a type or term argument
applyMonTerm :: HasCallStack => MonTerm -> MonArg -> MonTerm
applyMonTerm (ArgMonTerm (ForallMonTerm _ k1 f)) (TpArg k2 e)
  | Just Refl <- testEquality k1 k2 = f e
applyMonTerm (ArgMonTerm (FunMonTerm _ _ _ f)) (TrmArg arg) = f arg
applyMonTerm (ArgMonTerm (ForallMonTerm _ _ _)) _ =
  panic "applyMonTerm" ["Application of term at incorrect type"]
applyMonTerm (ArgMonTerm (FunMonTerm _ _ _ _)) _ =
  panic "applyMonTerm" ["Application of term at incorrect type"]
applyMonTerm (ArgMonTerm (BaseMonTerm _ _)) _ =
  panic "applyMonTerm" ["Application of non-functional pure term"]
applyMonTerm (CompMonTerm _ _) _ =
  panic "applyMonTerm" ["Application of non-functional computational term"]

-- | Apply a monadified term to 0 or more arguments
applyMonTermMulti :: HasCallStack => MonTerm -> [MonArg] -> MonTerm
applyMonTermMulti = foldl applyMonTerm

-- | Build a 'MonTerm' from a global of a given argument type, applying it to
-- the current 'EventType' if the 'Bool' flag is 'True'
mkGlobalArgMonTerm :: HasSpecMEvType => MonType -> Ident -> Bool -> ArgMonTerm
mkGlobalArgMonTerm tp ident params_p =
  fromArgTerm tp (if params_p
                  then applyGlobalOpenTerm ident [evTypeTerm ?specMEvType]
                  else globalOpenTerm ident)

-- | Build a 'MonTerm' from a 'GlobalDef' of semi-pure type, applying it to the
-- current 'EventType' if the 'Bool' flag is 'True'
mkSemiPureGlobalDefTerm :: HasSpecMEvType => GlobalDef -> Bool -> ArgMonTerm
mkSemiPureGlobalDefTerm glob params_p =
  fromSemiPureTerm (monadifyType [] $ globalDefType glob)
  (if params_p
   then applyOpenTermMulti (globalDefOpenTerm glob) [evTypeTerm ?specMEvType]
   else globalDefOpenTerm glob)

-- | Build a 'MonTerm' from a constructor with the given 'ExtCns'
mkCtorArgMonTerm :: HasSpecMEvType => ExtCns Term -> ArgMonTerm
mkCtorArgMonTerm ec
  | not (isFirstOrderType (ecType ec)) =
    failArgMonTerm (monadifyType [] $ ecType ec)
    ("monadification failed: cannot handle constructor "
     ++ Text.unpack (toAbsoluteName (ecName ec)) ++ " with higher-order type")
mkCtorArgMonTerm ec =
  case ecName ec of
    ModuleIdentifier ident ->
      fromSemiPureTermFun (monadifyType [] $ ecType ec) (ctorOpenTerm ident)
    ImportedName{} ->
      failArgMonTerm (monadifyType [] $ ecType ec)
      ("monadification failed: cannot handle constructor "
       ++ Text.unpack (toAbsoluteName (ecName ec)) ++ " with non-ident name")


----------------------------------------------------------------------
-- * Monadification Environments and Contexts
----------------------------------------------------------------------

-- | A monadification macro is a function that inspects its first @N@ arguments
-- before deciding how to monadify itself
data MonMacro = MonMacro {
  macroNumArgs :: Int,
  macroApply :: GlobalDef -> [Term] -> MonadifyM MonTerm }

-- | Make a simple 'MonMacro' that inspects 0 arguments and just returns a term
monMacro0 :: MonTerm -> MonMacro
monMacro0 mtrm = MonMacro 0 $ \_ _ -> usingEvType $ return mtrm

-- | Make a 'MonMacro' that maps a named global to a global of semi-pure type.
-- (See 'fromSemiPureTermFun'.) Because we can't get access to the type of the
-- global until we apply the macro, we monadify its type at macro application
-- time. The 'Bool' flag indicates whether the current 'EventType' should also
-- be passed as the first argument to the "to" global.
semiPureGlobalMacro :: Ident -> Ident -> Bool -> MonMacro
semiPureGlobalMacro from to params_p =
  MonMacro 0 $ \glob args -> usingEvType $
  if globalDefName glob == ModuleIdentifier from && args == [] then
    return $ ArgMonTerm $
    fromSemiPureTerm (monadifyType [] $ globalDefType glob)
    (if params_p then applyGlobalOpenTerm to [evTypeTerm ?specMEvType]
     else globalOpenTerm to)
  else
    error ("Monadification macro for " ++ show from ++ " applied incorrectly")

-- | Make a 'MonMacro' that maps a named global to a global of argument type.
-- Because we can't get access to the type of the global until we apply the
-- macro, we monadify its type at macro application time. The 'Bool' flag
-- indicates whether the "to" global is polymorphic in the event type, in which
-- case the current 'EventType' is passed as its first argument.
argGlobalMacro :: NameInfo -> Ident -> Bool -> MonMacro
argGlobalMacro from to params_p =
  MonMacro 0 $ \glob args -> usingEvType $
  if globalDefName glob == from && args == [] then
    return $ ArgMonTerm $
    mkGlobalArgMonTerm (monadifyType [] $ globalDefType glob) to params_p
  else
    error ("Monadification macro for " ++ show from ++ " applied incorrectly")

-- | An environment for monadification
data MonadifyEnv = MonadifyEnv {
  -- | How to monadify named functions
  monEnvMonTable :: Map NameInfo MonMacro,
  -- | The @EvType@ used for monadification
  monEnvEvType :: EventType
  }

-- | Look up the monadification of a name in a 'MonadifyEnv'
monEnvLookup :: NameInfo -> MonadifyEnv -> Maybe MonMacro
monEnvLookup nmi env = Map.lookup nmi (monEnvMonTable env)

-- | Add a monadification for a name to a 'MonadifyEnv'
monEnvAdd :: NameInfo -> MonMacro -> MonadifyEnv -> MonadifyEnv
monEnvAdd nmi macro env =
  env { monEnvMonTable = Map.insert nmi macro (monEnvMonTable env) }

-- | A context for monadifying 'Term's which maintains, for each deBruijn index
-- in scope, both its original un-monadified type along with either a 'MonTerm'
-- or 'MonType' for the translation of the variable to a local variable of
-- monadified type or monadified kind
type MonadifyCtx = [(LocalName,Term,MonArg)]

-- | Convert a 'MonadifyCtx' to a 'MonadifyTypeCtx'
ctxToTypeCtx :: MonadifyCtx -> MonadifyTypeCtx
ctxToTypeCtx = map (\(x,tp,arg) ->
                     (x,tp,case arg of
                         TpArg k mtp -> Just (SomeTpExpr k mtp)
                         TrmArg _ -> Nothing))

-- | Pretty-print a 'Term' relative to a 'MonadifyCtx'
ppTermInMonCtx :: MonadifyCtx -> Term -> String
ppTermInMonCtx ctx t =
  scPrettyTermInCtx PPS.defaultOpts (map (\(x,_,_) -> x) ctx) t

-- | A memoization table for monadifying terms: a map from 'TermIndex'es to
-- 'MonTerm's and, possibly, corresponding 'ArgMonTerm's. The latter are simply
-- the result of calling 'argifyMonTerm' on the former, but are only added when
-- needed (i.e. when 'memoArgMonTerm' is called, e.g. in 'monadifyArg').
type MonadifyMemoTable = IntMap (MonTerm, Maybe ArgMonTerm)

-- | The empty memoization table
emptyMemoTable :: MonadifyMemoTable
emptyMemoTable = IntMap.empty


----------------------------------------------------------------------
-- * The Monadification Monad
----------------------------------------------------------------------

-- | The read-only state of a monadification computation
data MonadifyROState = MonadifyROState {
  -- | The monadification environment
  monStEnv :: MonadifyEnv,
  -- | The monadification context
  monStCtx :: MonadifyCtx,
  -- | The monadified return type of the top-level term being monadified; that
  -- is, we are inside a call to 'monadifyTerm' applied to some function of SAW
  -- core type @a1 -> ... -> an -> b@, and this is the type @b@
  monStTopRetType :: MonType
}

-- | Get the monadification table from a 'MonadifyROState'
monStMonTable :: MonadifyROState -> Map NameInfo MonMacro
monStMonTable = monEnvMonTable . monStEnv

-- | The monad for monadifying SAW core terms
newtype MonadifyM a =
  MonadifyM { unMonadifyM ::
                ReaderT MonadifyROState (StateT MonadifyMemoTable
                                         (Cont MonTerm)) a }
  deriving (Functor, Applicative, Monad,
            MonadReader MonadifyROState, MonadState MonadifyMemoTable)

-- | Get the current 'EventType' in a 'MonadifyM' computation
askEvType :: MonadifyM EventType
askEvType = monEnvEvType <$> monStEnv <$> ask

-- | Run a 'MonadifyM' computation with the current 'EventType'
usingEvType :: (HasSpecMEvType => MonadifyM a) -> MonadifyM a
usingEvType m =
  do ev <- askEvType
     let ?specMEvType = ev in m

instance Fail.MonadFail MonadifyM where
  fail str =
    usingEvType $
    do ret_tp <- topRetType
       shiftMonadifyM $ \_ -> failMonTerm ret_tp str

-- | Capture the current continuation and pass it to a function, which must
-- return the final computation result. Note that this is slightly differnet
-- from normal shift, and I think corresponds to the C operator, but my quick
-- googling couldn't find the right name...
shiftMonadifyM :: ((a -> MonTerm) -> MonTerm) -> MonadifyM a
shiftMonadifyM f = MonadifyM $ lift $ lift $ cont f

-- | Locally run a 'MonadifyM' computation with an empty memoization table,
-- making all binds be local to that computation, and return the result
resetMonadifyM :: MonType -> MonadifyM MonTerm -> MonadifyM MonTerm
resetMonadifyM ret_tp m =
  do ro_st <- ask
     return $ runMonadifyM (monStEnv ro_st) (monStCtx ro_st) ret_tp m

-- | Get the monadified return type of the top-level term being monadified
topRetType :: MonadifyM MonType
topRetType = monStTopRetType <$> ask

-- | Run a monadification computation
--
-- FIXME: document the arguments
runMonadifyM :: MonadifyEnv -> MonadifyCtx -> MonType ->
                MonadifyM MonTerm -> MonTerm
runMonadifyM env ctx top_ret_tp m =
  let ro_st = MonadifyROState env ctx top_ret_tp in
  runCont (evalStateT (runReaderT (unMonadifyM m) ro_st) emptyMemoTable) id

-- | Run a monadification computation using a mapping for identifiers that have
-- already been monadified and generate a SAW core term
runCompleteMonadifyM :: MonadIO m => SharedContext -> MonadifyEnv ->
                        Term -> MonadifyM MonTerm ->
                        m Term
runCompleteMonadifyM sc env top_ret_tp m =
  let ?specMEvType = monEnvEvType env in
  liftIO $ completeOpenTerm sc $ toCompTerm $
  runMonadifyM env [] (monadifyType [] top_ret_tp) m

-- | Memoize a computation of the monadified term associated with a 'TermIndex'
memoMonTerm :: TermIndex -> MonadifyM MonTerm -> MonadifyM MonTerm
memoMonTerm i m =
  (IntMap.lookup i <$> get) >>= \case
  Just (mtm, _) ->
    return mtm
  Nothing ->
    do mtm <- m
       modify (IntMap.insert i (mtm, Nothing))
       return mtm

-- | Memoize a computation of the monadified term of argument type associated
-- with a 'TermIndex', using a memoized 'ArgTerm' directly if it exists or
-- applying 'argifyMonTerm' to a memoized 'MonTerm' (and memoizing the result)
-- if it exists
memoArgMonTerm :: TermIndex -> MonadifyM MonTerm -> MonadifyM ArgMonTerm
memoArgMonTerm i m =
  (IntMap.lookup i <$> get) >>= \case
  Just (_, Just argmtm) ->
    return argmtm
  Just (mtm, Nothing) ->
    do argmtm <- argifyMonTerm mtm
       modify (IntMap.insert i (mtm, Just argmtm))
       return argmtm
  Nothing ->
    do mtm <- m
       argmtm <- argifyMonTerm mtm
       modify (IntMap.insert i (mtm, Just argmtm))
       return argmtm

-- | Turn a 'MonTerm' of type @CompMT(tp)@ to a term of argument type @MT(tp)@
-- by inserting a monadic bind if the 'MonTerm' is computational
argifyMonTerm :: MonTerm -> MonadifyM ArgMonTerm
argifyMonTerm (ArgMonTerm mtrm) = return mtrm
argifyMonTerm (CompMonTerm mtp trm) =
  usingEvType $
  do let tp = toArgType mtp
     top_ret_tp <- topRetType
     shiftMonadifyM $ \k ->
       CompMonTerm top_ret_tp $
       bindSOpenTerm ?specMEvType tp (toArgType top_ret_tp) trm $
       lambdaOpenTerm "x" tp (toCompTerm . k . fromArgTerm mtp)

-- | Build a proof of @isFinite n@ by calling @assertFiniteS@ and binding the
-- result to an 'ArgMonTerm'
assertIsFinite :: HasSpecMEvType => NumTpExpr -> MonadifyM ArgMonTerm
assertIsFinite e =
  let n = numExprVal e in
  argifyMonTerm (CompMonTerm
                 (MTyIndesc (applyOpenTerm
                             (globalOpenTerm "CryptolM.isFinite") n))
                 (applyGlobalOpenTerm "CryptolM.assertFiniteS"
                  [evTypeTerm ?specMEvType, n]))


----------------------------------------------------------------------
-- * Monadification
----------------------------------------------------------------------

-- | Apply a monadifying operation (like 'monadifyTpExpr') in a 'MonadifyM'
monadifyOpM :: HasCallStack =>
               (HasSpecMEvType => MonadifyTypeCtx -> Term -> a) ->
               Term -> MonadifyM a
monadifyOpM f tm =
  usingEvType $
  do ctx <- monStCtx <$> ask
     return $ f (ctxToTypeCtx ctx) tm

-- | Monadify a type-level expression in the context of the 'MonadifyM' monad
monadifyTpExprM :: HasCallStack => Term -> MonadifyM SomeTpExpr
monadifyTpExprM = monadifyOpM monadifyTpExpr

-- | Monadify a type in the context of the 'MonadifyM' monad
monadifyTypeM :: HasCallStack => Term -> MonadifyM MonType
monadifyTypeM = monadifyOpM monadifyType

-- | Monadify a numeric expression in the context of the 'MonadifyM' monad
monadifyNumM :: HasCallStack => Term -> MonadifyM NumTpExpr
monadifyNumM = monadifyOpM monadifyNum

-- | Monadify a term to a monadified term of argument type
monadifyArg :: HasCallStack => Maybe MonType -> Term -> MonadifyM ArgMonTerm
{-
monadifyArg _ t
  | trace ("Monadifying term of argument type: " ++ showTerm t) False
  = undefined
-}
monadifyArg mtp t@(STApp { stAppIndex = ix }) =
  memoArgMonTerm ix $ usingEvType $ monadifyTerm' mtp t
monadifyArg mtp t =
  usingEvType (monadifyTerm' mtp t) >>= argifyMonTerm

-- | Monadify a term to argument type and convert back to a term
monadifyArgTerm :: HasCallStack => Maybe MonType -> Term -> MonadifyM OpenTerm
monadifyArgTerm mtp t = usingEvType (toArgTerm <$> monadifyArg mtp t)

-- | Monadify a term
monadifyTerm :: Maybe MonType -> Term -> MonadifyM MonTerm
{-
monadifyTerm _ t
  | trace ("Monadifying term: " ++ showTerm t) False
  = undefined
-}
monadifyTerm mtp t@(STApp { stAppIndex = ix }) =
  memoMonTerm ix $ usingEvType $ monadifyTerm' mtp t
monadifyTerm mtp t =
  usingEvType $ monadifyTerm' mtp t

-- | The main implementation of 'monadifyTerm', which monadifies a term given an
-- optional monadification type. The type must be given for introduction forms
-- (i.e.,, lambdas, pairs, and records), but is optional for elimination forms
-- (i.e., applications, projections, and also in this case variables). Note that
-- this means monadification will fail on terms with beta or tuple redexes.
monadifyTerm' :: HasCallStack => HasSpecMEvType =>
                 Maybe MonType -> Term -> MonadifyM MonTerm
monadifyTerm' (Just mtp) t@(asLambda -> Just _) =
  ask >>= \(MonadifyROState { monStEnv = env, monStCtx = ctx }) ->
  return $ monadifyLambdas env ctx mtp t
{-
monadifyTerm' (Just mtp@(MTyForall _ _ _)) t =
  ask >>= \ro_st ->
  get >>= \table ->
  return $ monadifyLambdas (monStEnv ro_st) table (monStCtx ro_st) mtp t
monadifyTerm' (Just mtp@(MTyArrow _ _)) t =
  ask >>= \ro_st ->
  get >>= \table ->
  return $ monadifyLambdas (monStEnv ro_st) table (monStCtx ro_st) mtp t
-}
monadifyTerm' (Just mtp@(MTyPair mtp1 mtp2)) (asPairValue ->
                                              Just (trm1, trm2)) =
  fromArgTerm mtp <$> (pairOpenTerm <$>
                       monadifyArgTerm (Just mtp1) trm1 <*>
                       monadifyArgTerm (Just mtp2) trm2)
{-
monadifyTerm' (Just mtp@(MTyRecord fs_mtps)) (asRecordValue -> Just trm_map)
  | length fs_mtps == Map.size trm_map
  , (fs,mtps) <- unzip fs_mtps
  , Just trms <- mapM (\f -> Map.lookup f trm_map) fs =
    fromArgTerm mtp <$> recordOpenTerm <$> zip fs <$>
    zipWithM monadifyArgTerm (map Just mtps) trms
-}
monadifyTerm' _ (asPairSelector -> Just (trm, False)) =
  do mtrm <- monadifyArg Nothing trm
     mtp <- case getMonType mtrm of
       MTyPair t _ -> return t
       _ -> fail "Monadification failed: projection on term of non-pair type"
     return $ fromArgTerm mtp $
       pairLeftOpenTerm $ toArgTerm mtrm
monadifyTerm' (Just mtp@(MTySeq n mtp_elem)) (asFTermF ->
                                              Just (ArrayValue _ trms)) =
  do trms' <- traverse (monadifyArgTerm $ Just mtp_elem) trms
     return $ fromArgTerm mtp $
       applyOpenTermMulti (globalOpenTerm "CryptolM.seqToMseq")
       [evTypeTerm ?specMEvType, numExprVal n, toArgType mtp_elem,
        flatOpenTerm $ ArrayValue (toArgType mtp_elem) trms']
monadifyTerm' _ (asPairSelector -> Just (trm, True)) =
  do mtrm <- monadifyArg Nothing trm
     mtp <- case getMonType mtrm of
       MTyPair _ t -> return t
       _ -> fail "Monadification failed: projection on term of non-pair type"
     return $ fromArgTerm mtp $
       pairRightOpenTerm $ toArgTerm mtrm
{-
monadifyTerm' _ (asRecordSelector -> Just (trm, fld)) =
  do mtrm <- monadifyArg Nothing trm
     mtp <- case getMonType mtrm of
       MTyRecord mtps | Just mtp <- lookup fld mtps -> return mtp
       _ -> fail ("Monadification failed: " ++
                  "record projection on term of incorrect type")
     return $ fromArgTerm mtp $ projRecordOpenTerm (toArgTerm mtrm) fld
-}
monadifyTerm' _ (asLocalVar -> Just ix) =
  (monStCtx <$> ask) >>= \case
  ctx | ix >= length ctx -> fail "Monadification failed: vaiable out of scope!"
  ctx | (_,_,TrmArg mtrm) <- ctx !! ix -> return $ ArgMonTerm mtrm
  _ -> fail "Monadification failed: type variable used in term position!"
monadifyTerm' _ (asTupleValue -> Just []) =
  return $ ArgMonTerm $ fromSemiPureTerm MTyUnit unitOpenTerm
{-
monadifyTerm' _ (asCtor -> Just (ec, args)) =
  monadifyApply (ArgMonTerm $ mkCtorArgMonTerm ec) args
-}
monadifyTerm' _ (asApplyAll -> (asTypedGlobalDef -> Just glob, args)) =
  (Map.lookup (globalDefName glob) <$> monStMonTable <$> ask) >>= \case
  Just macro ->
    do let (macro_args, reg_args) = splitAt (macroNumArgs macro) args
       mtrm_f <- macroApply macro glob macro_args
       monadifyApply mtrm_f reg_args
  Nothing ->
    monadifyTypeM (globalDefType glob) >>= \glob_mtp ->
    if monTypeIsSemiPure glob_mtp then
      monadifyApply (ArgMonTerm $ fromSemiPureTerm glob_mtp $
                     globalDefOpenTerm glob) args
    else error ("Monadification failed: unhandled constant: "
                ++ globalDefString glob)
monadifyTerm' _ (asApp -> Just (f, arg)) =
  do mtrm_f <- monadifyTerm Nothing f
     monadifyApply mtrm_f [arg]
monadifyTerm' _ t =
  (monStCtx <$> ask) >>= \ctx ->
  fail ("Monadifiction failed: no case for term: " ++ ppTermInMonCtx ctx t)


-- | Monadify the application of a monadified term to a list of terms, using the
-- type of the already monadified to monadify the arguments
monadifyApply :: HasCallStack => MonTerm -> [Term] -> MonadifyM MonTerm
monadifyApply f (t : ts)
  | MTyArrow tp_in _ <- getMonType f =
    do mtrm <- monadifyArg (Just tp_in) t
       monadifyApply (applyMonTerm f (TrmArg mtrm)) ts
monadifyApply f (t : ts)
  | MTyForall _ _ _ <- getMonType f =
    do arg <- tpExprToArg <$> monadifyTpExprM t
       monadifyApply (applyMonTerm f arg) ts
monadifyApply _ (_:_) = fail "monadifyApply: application at incorrect type"
monadifyApply f [] = return f


-- | Monadify a nested lambda abstraction by monadifying its body. This is done
-- outside the 'MonadifyM' monad, since all of its state (including the eventual
-- return type) will be reset when we monadify this body.
monadifyLambdas :: HasCallStack => MonadifyEnv -> MonadifyCtx ->
                   MonType -> Term -> MonTerm
monadifyLambdas env ctx (MTyForall _ k tp_f) (asLambda ->
                                              Just (x, x_tp, body)) =
  -- FIXME: check that monadifyKind x_tp == k
  ArgMonTerm $ ForallMonTerm x k $ \mtp ->
  monadifyLambdas env ((x,x_tp,TpArg k mtp) : ctx) (tp_f mtp) body
monadifyLambdas env ctx (MTyArrow tp_in tp_out) (asLambda ->
                                                 Just (x, x_tp, body)) =
  -- FIXME: check that monadifyType x_tp == tp_in
  ArgMonTerm $ FunMonTerm x tp_in tp_out $ \arg ->
  monadifyLambdas env ((x,x_tp,TrmArg arg) : ctx) tp_out body
monadifyLambdas env ctx tp t =
  monadifyEtaExpand env ctx tp tp t []

-- | Monadify a term of functional type by lambda-abstracting its arguments,
-- monadifying it, and applying the result to those lambda-abstracted arguments;
-- i.e., by eta-expanding it. This ensures that the 'MonadifyM' computation is
-- run in a context where the return type is not functional, which in turn
-- ensures that any monadic binds inserted by 'argifyMonTerm' all happen inside
-- the function. The first 'MonType' is the top-level functional type of the
-- 'Term' being monadified, while the second 'MonType' is the type after the
-- 'Term' is applied to the list of 'MonArg's, which represents all the
-- variables generated by eta-expansion.
monadifyEtaExpand :: HasCallStack => MonadifyEnv -> MonadifyCtx ->
                     MonType -> MonType -> Term -> [MonArg] -> MonTerm
monadifyEtaExpand env ctx top_mtp (MTyForall x k tp_f) t args =
  ArgMonTerm $ ForallMonTerm x k $ \mtp ->
  monadifyEtaExpand env ctx top_mtp (tp_f mtp) t (args ++ [TpArg k mtp])
monadifyEtaExpand env ctx top_mtp (MTyArrow tp_in tp_out) t args =
  ArgMonTerm $ FunMonTerm "_" tp_in tp_out $ \arg ->
  monadifyEtaExpand env ctx top_mtp tp_out t (args ++ [TrmArg arg])
monadifyEtaExpand env ctx top_mtp mtp t args =
  let ?specMEvType = monEnvEvType env in
  applyMonTermMulti (runMonadifyM env ctx mtp
                     (monadifyTerm (Just top_mtp) t)) args


----------------------------------------------------------------------
-- * Handling the Primitives
----------------------------------------------------------------------

-- | The macro for unsafeAssert, which checks the type of the objects being
-- compared and dispatches to the proper comparison function
unsafeAssertMacro :: MonMacro
unsafeAssertMacro = MonMacro 1 $ \_ ts ->
  usingEvType $
  let numFunType =
        MTyForall "n" MKNumRepr $ \n -> MTyForall "m" MKNumRepr $ \m ->
        MTyIndesc $
        dataTypeOpenTerm "Prelude.Eq"
        [dataTypeOpenTerm "Cryptol.Num" [],
         numExprVal n, numExprVal m] in
  case ts of
    [(asDataType -> Just (num, []))]
      | primName num == "Cryptol.Num" ->
        return $ ArgMonTerm $
        mkGlobalArgMonTerm numFunType "CryptolM.numAssertEqS" True
    _ ->
      fail "Monadification failed: unsafeAssert applied to non-Num type"

-- | The macro for if-then-else, which contains any binds in a branch to that
-- branch
iteMacro :: MonMacro
iteMacro = MonMacro 4 $ \_ args -> usingEvType $
  do let (tp, cond, branch1, branch2) =
           case args of
             [t1, t2, t3, t4] -> (t1, t2, t3, t4)
             _ -> error "iteMacro: wrong number of arguments!"
     atrm_cond <- monadifyArg (Just MTyBool) cond
     mtp <- monadifyTypeM tp
     mtrm1 <- resetMonadifyM mtp $ monadifyTerm (Just mtp) branch1
     mtrm2 <- resetMonadifyM mtp $ monadifyTerm (Just mtp) branch2
     case (mtrm1, mtrm2) of
       (ArgMonTerm atrm1, ArgMonTerm atrm2) ->
         return $ fromArgTerm mtp $
         applyOpenTermMulti (globalOpenTerm "Prelude.ite")
         [toArgType mtp, toArgTerm atrm_cond, toArgTerm atrm1, toArgTerm atrm2]
       _ ->
         return $ fromCompTerm mtp $
         applyOpenTermMulti (globalOpenTerm "Prelude.ite")
         [toCompType mtp, toArgTerm atrm_cond,
          toCompTerm mtrm1, toCompTerm mtrm2]

-- | The macro for the either elimination function, which converts the
-- application @either a b c@ to @either a b (CompM c)@
eitherMacro :: MonMacro
eitherMacro = MonMacro 3 $ \_ args ->
  usingEvType $
  do let (tp_a, tp_b, tp_c) =
           case args of
             [t1, t2, t3] -> (t1, t2, t3)
             _ -> error "eitherMacro: wrong number of arguments!"
     mtp_a <- monadifyTypeM tp_a
     mtp_b <- monadifyTypeM tp_b
     mtp_c <- monadifyTypeM tp_c
     let eith_app = applyGlobalOpenTerm "Prelude.either" [toArgType mtp_a,
                                                          toArgType mtp_b,
                                                          toCompType mtp_c]
     return $ fromCompTerm (MTyArrow (MTyArrow mtp_a mtp_c)
                            (MTyArrow (MTyArrow mtp_b mtp_c)
                             (MTyArrow (MTySum mtp_a mtp_b) mtp_c))) eith_app

-- | The macro for uncurry, which converts the application @uncurry a b c@
-- to @uncurry a b (CompM c)@
uncurryMacro :: MonMacro
uncurryMacro = MonMacro 3 $ \_ args ->
  usingEvType $
  do let (tp_a, tp_b, tp_c) =
           case args of
             [t1, t2, t3] -> (t1, t2, t3)
             _ -> error "uncurryMacro: wrong number of arguments!"
     mtp_a <- monadifyTypeM tp_a
     mtp_b <- monadifyTypeM tp_b
     mtp_c <- monadifyTypeM tp_c
     let unc_app = applyGlobalOpenTerm "Prelude.uncurry" [toArgType mtp_a,
                                                          toArgType mtp_b,
                                                          toCompType mtp_c]
     return $ fromCompTerm (MTyArrow (MTyArrow mtp_a (MTyArrow mtp_b mtp_c))
                            (MTyArrow (MTyPair mtp_a mtp_b) mtp_c)) unc_app

-- | The macro for invariantHint, which converts @invariantHint a cond m@
-- to @invariantHint (CompM a) cond m@ and which contains any binds in the body
-- to the body
invariantHintMacro :: MonMacro
invariantHintMacro = MonMacro 3 $ \_ args -> usingEvType $
  do let (tp, cond, m) =
           case args of
             [t1, t2, t3] -> (t1, t2, t3)
             _ -> error "invariantHintMacro: wrong number of arguments!"
     atrm_cond <- monadifyArg (Just MTyBool) cond
     mtp <- monadifyTypeM tp
     mtrm <- resetMonadifyM mtp $ monadifyTerm (Just mtp) m
     return $ fromCompTerm mtp $
       applyOpenTermMulti (globalOpenTerm "SpecM.invariantHint")
       [toCompType mtp, toArgTerm atrm_cond, toCompTerm mtrm]

-- | The macro for @asserting@ or @assuming@, which converts @asserting@ to
-- @assertingM@ or @assuming@ to @assumingM@ (depending on whether the given
-- 'Bool' is true or false, respectively) and which contains any binds in the
-- body to the body
assertingOrAssumingMacro :: Bool -> MonMacro
assertingOrAssumingMacro doAsserting = MonMacro 3 $ \_ args ->
  usingEvType $
  do let (tp, cond, m) =
           case args of
             [t1, t2, t3] -> (t1, t2, t3)
             _ -> error "assertingOrAssumingMacro: wrong number of arguments!"
     atrm_cond <- monadifyArg (Just MTyBool) cond
     mtp <- monadifyTypeM tp
     mtrm <- resetMonadifyM mtp $ monadifyTerm (Just mtp) m
     ev <- askEvType
     let ident = if doAsserting then "SpecM.assertingS"
                                else "SpecM.assumingS"
     return $ fromCompTerm mtp $
       applyOpenTermMulti (globalOpenTerm ident)
       [evTypeTerm ev, toArgType mtp, toArgTerm atrm_cond, toCompTerm mtrm]

-- | @finMacro b i j from to params_p@ makes a 'MonMacro' that maps a named
-- global @from@ whose @i@th through @(i+j-1)@th arguments are @Num@s, to a
-- named global @to@, which is of semi-pure type if and only if @b@ is 'True',
-- that takes an additional argument of type @isFinite n@ after each of the
-- aforementioned @Num@ arguments. The @params_p@ flag indicates whether the
-- current 'EventType' should be passed as the first argument to @to@.
finMacro :: Bool -> Int -> Int -> Ident -> Ident -> Bool -> MonMacro
finMacro isSemiPure i j from to params_p =
  MonMacro (i+j) $ \glob args -> usingEvType $
  do if globalDefName glob == ModuleIdentifier from && length args == i+j then
       return ()
       else error ("Monadification macro for " ++ show from ++
                   " applied incorrectly")
     let (init_args_tms, fin_args_tms) = splitAt i args
     -- Monadify the first @i@ args
     init_args <- mapM monadifyTpExprM init_args_tms
     -- Monadify the @i@th through @(i+j-1)@th args and build proofs that they are finite
     fin_args <- mapM monadifyNumM fin_args_tms
     fin_pfs <- mapM assertIsFinite fin_args
     -- Apply the type of @glob@ to the monadified arguments and apply @to@ to the
     -- monadified arguments along with the proofs that the latter arguments are finite
     let glob_tp = monadifyType [] $ globalDefType glob
     let glob_args = map tpExprToArg init_args ++ map numToArg fin_args
     let glob_tp_app = foldl applyMonType glob_tp glob_args
     let to_args =
           map someTpExprVal init_args ++
           concatMap (\(n,pf) -> [numExprVal n,
                                  toArgTerm pf]) (zip fin_args fin_pfs)
     let to_app =
           applyOpenTermMulti (globalOpenTerm to)
           ((if params_p then (evTypeTerm ?specMEvType :) else id) to_args)
     -- Finally, return the result as semi-pure dependent on @isSemiPure@
     return $ if isSemiPure
              then ArgMonTerm $ fromSemiPureTerm glob_tp_app to_app
              else ArgMonTerm $ fromArgTerm glob_tp_app to_app

-- FIXME HERE NOW: add a case for a fix of a record type of functions, which
-- should translate to MultiFixS

-- | The macro for fix
--
-- FIXME: does not yet handle mutual recursion
fixMacro :: MonMacro
fixMacro = MonMacro 2 $ \_ args -> case args of
  [tp@(asPi -> Just _), f] ->
    do ev <- askEvType
       mtp <- monadifyTypeM tp
       usingEvType $ do
         amtrm_f <- monadifyArg (Just $ MTyArrow mtp mtp) f
         return $ fromCompTerm mtp $
           applyOpenTermMulti (globalOpenTerm "SpecM.FixS")
           [evTypeTerm ev, toTpDesc mtp, toCompTerm amtrm_f]
  [(asRecordType -> Just _), _] ->
    fail "Monadification failed: cannot yet handle mutual recursion"
  _ -> error "fixMacro: malformed arguments!"

-- | A "macro mapping" maps a single pure identifier to a 'MonMacro' for it
type MacroMapping = (NameInfo, MonMacro)

-- | Build a 'MacroMapping' for an identifier to a semi-pure named function
mmSemiPure :: Ident -> Ident -> Bool -> MacroMapping
mmSemiPure from_id to_id params_p =
  (ModuleIdentifier from_id, semiPureGlobalMacro from_id to_id params_p)

-- | Build a 'MacroMapping' for an identifier to a semi-pure named function
-- whose @i@th through @(i+j-1)@th arguments are @Num@s that require
-- @isFinite@ proofs
mmSemiPureFin :: Int -> Int -> Ident -> Ident -> Bool -> MacroMapping
mmSemiPureFin i j from_id to_id params_p =
  (ModuleIdentifier from_id, finMacro True i j from_id to_id params_p)

-- | Build a 'MacroMapping' for an identifier to itself as a semi-pure function
mmSelf :: Ident -> MacroMapping
mmSelf self_id =
  (ModuleIdentifier self_id, semiPureGlobalMacro self_id self_id False)

-- | Build a 'MacroMapping' from an identifier to a function of argument type,
-- where the 'Bool' flag indicates whether the current 'SpecMArgs' should be
-- passed as additional arguments to the "to" identifier
mmArg :: Ident -> Ident -> Bool -> MacroMapping
mmArg from_id to_id params_p =
  (ModuleIdentifier from_id,
   argGlobalMacro (ModuleIdentifier from_id) to_id params_p)

-- | Build a 'MacroMapping' for an identifier to a function of argument type,
-- whose @i@th through @(i+j-1)@th arguments are @Num@s that require
-- @isFinite@ proofs, where the 'Bool' flag indicates whether the current
-- 'SpecMArgs' should be passed as additional arguments to the "to" identifier
mmArgFin :: Int -> Int -> Ident -> Ident -> Bool -> MacroMapping
mmArgFin i j from_id to_id params_p =
  (ModuleIdentifier from_id, finMacro False i j from_id to_id params_p)

-- | Build a 'MacroMapping' from an identifier and a custom 'MonMacro'
mmCustom :: Ident -> MonMacro -> MacroMapping
mmCustom from_id macro = (ModuleIdentifier from_id, macro)

-- | The default monadification environment
defaultMonEnv :: MonadifyEnv
defaultMonEnv = MonadifyEnv { monEnvMonTable = defaultMonTable,
                              monEnvEvType = defaultSpecMEventType }

-- | The default primitive monadification table
defaultMonTable :: Map NameInfo MonMacro
defaultMonTable =
  Map.fromList
  [
    -- Prelude functions
    mmCustom "Prelude.unsafeAssert" unsafeAssertMacro
  , mmCustom "Prelude.ite" iteMacro
  , mmCustom "Prelude.fix" fixMacro
  , mmCustom "Prelude.either" eitherMacro
  , mmCustom "Prelude.uncurry" uncurryMacro
  , mmCustom "SpecM.invariantHint" invariantHintMacro
  , mmCustom "SpecM.asserting" (assertingOrAssumingMacro True)
  , mmCustom "SpecM.assuming" (assertingOrAssumingMacro False)

    -- Top-level sequence functions
  , mmArg "Cryptol.seqMap" "CryptolM.seqMapM" True
  , mmSemiPure "Cryptol.seq_cong1" "CryptolM.mseq_cong1" True
  , mmArg "Cryptol.eListSel" "CryptolM.eListSelM" True

    -- List comprehensions
  , mmArg "Cryptol.from" "CryptolM.fromM" True
  , mmArg "Cryptol.mlet" "CryptolM.mletM" True
  , mmArg "Cryptol.seqZip" "CryptolM.seqZipM" True
  , mmSemiPure "Cryptol.seqZipSame" "CryptolM.seqZipSameM" True

    -- PEq constraints
  , mmSemiPureFin 0 1 "Cryptol.PEqSeq" "CryptolM.PEqMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PEqSeqBool" "CryptolM.PEqMSeqBool" True

    -- PCmp constraints
  , mmSemiPureFin 0 1 "Cryptol.PCmpSeq" "CryptolM.PCmpMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PCmpSeqBool" "CryptolM.PCmpMSeqBool" True

    -- PSignedCmp constraints
  , mmSemiPureFin 0 1 "Cryptol.PSignedCmpSeq" "CryptolM.PSignedCmpMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PSignedCmpSeqBool" "CryptolM.PSignedCmpMSeqBool" True

    -- PZero constraints
  , mmSemiPure "Cryptol.PZeroSeq" "CryptolM.PZeroMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PZeroSeqBool" "CryptolM.PZeroMSeqBool" True

    -- PLogic constraints
  , mmSemiPure "Cryptol.PLogicSeq" "CryptolM.PLogicMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PLogicSeqBool" "CryptolM.PLogicMSeqBool" True

    -- PRing constraints
  , mmSemiPure "Cryptol.PRingSeq" "CryptolM.PRingMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PRingSeqBool" "CryptolM.PRingMSeqBool" True

    -- PIntegral constraints
  , mmSemiPureFin 0 1 "Cryptol.PIntegeralSeqBool" "CryptolM.PIntegeralMSeqBool" True

    -- PLiteral constraints
  , mmSemiPureFin 0 1 "Cryptol.PLiteralSeqBool" "CryptolM.PLiteralSeqBoolM" True

    -- The Cryptol Literal primitives
  , mmSelf "Cryptol.ecNumber"
  , mmSelf "Cryptol.ecFromZ"

    -- The Ring primitives
  , mmSelf "Cryptol.ecPlus"
  , mmSelf "Cryptol.ecMinus"
  , mmSelf "Cryptol.ecMul"
  , mmSelf "Cryptol.ecNeg"
  , mmSelf "Cryptol.ecToInteger"

    -- The comparison primitives
  , mmSelf "Cryptol.ecEq"
  , mmSelf "Cryptol.ecNotEq"
  , mmSelf "Cryptol.ecLt"
  , mmSelf "Cryptol.ecLtEq"
  , mmSelf "Cryptol.ecGt"
  , mmSelf "Cryptol.ecGtEq"

    -- Sequences
  , mmSemiPure "Cryptol.ecShiftL" "CryptolM.ecShiftLM" True
  , mmSemiPure "Cryptol.ecShiftR" "CryptolM.ecShiftRM" True
  , mmSemiPure "Cryptol.ecSShiftR" "CryptolM.ecSShiftRM" True
  , mmSemiPureFin 0 1 "Cryptol.ecRotL" "CryptolM.ecRotLM" True
  , mmSemiPureFin 0 1 "Cryptol.ecRotR" "CryptolM.ecRotRM" True
  , mmSemiPureFin 0 1 "Cryptol.ecCat" "CryptolM.ecCatM" True
  , mmArg "Cryptol.ecTake" "CryptolM.ecTakeM" True
  , mmSemiPureFin 0 1 "Cryptol.ecDrop" "CryptolM.ecDropM" True
  , mmSemiPureFin 0 1 "Cryptol.ecDrop" "CryptolM.ecDropM" True
  , mmSemiPureFin 1 1 "Cryptol.ecJoin" "CryptolM.ecJoinM" True
  , mmSemiPureFin 1 1 "Cryptol.ecSplit" "CryptolM.ecSplitM" True
  , mmSemiPureFin 0 1 "Cryptol.ecReverse" "CryptolM.ecReverseM" True
  , mmSemiPure "Cryptol.ecTranspose" "CryptolM.ecTransposeM" True
  , mmArg "Cryptol.ecAt" "CryptolM.ecAtM" True
  , mmArg "Cryptol.ecUpdate" "CryptolM.ecUpdateM" True
  , mmArgFin 0 1 "Cryptol.ecAtBack" "CryptolM.ecAtBackM" True
  , mmSemiPureFin 0 2 "Cryptol.ecFromTo" "CryptolM.ecFromToM" True
  , mmSemiPureFin 0 1 "Cryptol.ecFromToLessThan" "CryptolM.ecFromToLessThanM" True
  , mmSemiPureFin 4 1 "Cryptol.ecFromThenTo" "CryptolM.ecFromThenToM" True
  , mmSemiPure "Cryptol.ecInfFrom" "CryptolM.ecInfFromM" True
  , mmSemiPure "Cryptol.ecInfFromThen" "CryptolM.ecInfFromThenM" True
  , mmArg "Cryptol.ecError" "CryptolM.ecErrorM" True
  ]


----------------------------------------------------------------------
-- * Top-Level Entrypoints
----------------------------------------------------------------------

-- | Ensure that the @CryptolM@ module is loaded
ensureCryptolMLoaded :: SharedContext -> IO ()
ensureCryptolMLoaded sc =
  scModuleIsLoaded sc (mkModuleName ["CryptolM"]) >>= \is_loaded ->
  if is_loaded then return () else
    scLoadSpecMModule sc >> scLoadCryptolMModule sc

-- | Monadify a type to its argument type and complete it to a 'Term',
-- additionally quantifying over the event type and function stack if the
-- supplied 'Bool' is 'True'
monadifyCompleteArgType :: SharedContext -> MonadifyEnv -> Term -> Bool ->
                           IO Term
monadifyCompleteArgType sc env tp poly_p =
  (ensureCryptolMLoaded sc >>) $
  completeOpenTerm sc $
  if poly_p then
    -- Parameter polymorphism means pi-quantification over E
    (piOpenTerm "E" (dataTypeOpenTerm "SpecM.EvType" []) $ \e ->
      let ?specMEvType = EventType e in
      -- NOTE: even though E is a free variable here, it can not be free in tp,
      -- which is a closed term, so we do not list it in the MonadifyTypeCtx
      -- argument of monadifyTypeArgType
      monadifyTypeArgType [] tp)
  else
    let ?specMEvType = monEnvEvType env in monadifyTypeArgType [] tp

-- | Monadify a term of the specified type to a 'MonTerm' and then complete that
-- 'MonTerm' to a SAW core 'Term', or 'fail' if this is not possible
monadifyCompleteTerm :: SharedContext -> MonadifyEnv -> Term -> Term -> IO Term
monadifyCompleteTerm sc env trm tp =
  (ensureCryptolMLoaded sc >>) $
  runCompleteMonadifyM sc env tp $ usingEvType $
  monadifyTerm (Just $ monadifyType [] tp) trm

-- | Convert a name of a definition to the name of its monadified version
monadifyName :: NameInfo -> IO NameInfo
monadifyName (ModuleIdentifier ident) =
  return $ ModuleIdentifier $ mkIdent (identModule ident) $
  T.append (identBaseName ident) (T.pack "M")
monadifyName (ImportedName uri aliases) =
  do frag <- URI.mkFragment (T.pack "M")
     let aliases' = concatMap (\a -> [a, T.append a (T.pack "#M")]) aliases
     return $ ImportedName (uri { URI.uriFragment = Just frag }) aliases'

-- | The implementation of 'monadifyNamedTerm' in the @StateT MonadifyEnv IO@ monad
monadifyNamedTermH :: SharedContext -> NameInfo -> Maybe Term -> Term ->
                      StateT MonadifyEnv IO MonTerm
monadifyNamedTermH sc nmi maybe_trm tp =
  -- trace ("Monadifying " ++ T.unpack (toAbsoluteName nmi)) $
  get >>= \env -> let ?specMEvType = monEnvEvType env in
  do let mtp = monadifyType [] tp
     nmi' <- lift $ monadifyName nmi
     comp_tp <- lift $ completeOpenTerm sc $ toCompType mtp
     const_trm <-
       case maybe_trm of
         Just trm ->
          --  trace ("" ++ ppTermInMonCtx env trm ++ "\n\n") $
           do trm' <- monadifyTermInEnvH sc trm tp
              lift $ scConstant' sc nmi' trm' comp_tp
         Nothing -> lift $ scOpaqueConstant sc nmi' comp_tp
     return $ fromCompTerm mtp $ closedOpenTerm const_trm

-- | Monadify a 'Term' of the specified type with an optional body, bind the
-- result to a fresh SAW core constant generated from the supplied name, and
-- then convert that constant back to a 'MonTerm'. Like 'monadifyTermInEnv',
-- this function also monadifies all constants the body contains, and adds
-- the monadifications of those constants to the monadification environment.
monadifyNamedTerm :: SharedContext -> MonadifyEnv ->
                     NameInfo -> Maybe Term -> Term ->
                     IO (MonTerm, MonadifyEnv)
monadifyNamedTerm sc env nmi maybe_trm tp =
  (ensureCryptolMLoaded sc >>) $
  flip runStateT env $ monadifyNamedTermH sc nmi maybe_trm tp

-- | The implementation of 'monadifyTermInEnv' in the @StateT MonadifyEnv IO@ monad
monadifyTermInEnvH :: SharedContext -> Term -> Term ->
                      StateT MonadifyEnv IO Term
monadifyTermInEnvH sc top_trm top_tp =
  do lift $ ensureCryptolMLoaded sc
     mm <- lift $ scGetModuleMap sc
     let const_infos = Map.toAscList $ getConstantSet top_trm
     forM_ const_infos $ \(vi, (nmi, tp)) ->
       do let maybe_body =
                case lookupVarIndexInMap vi mm of
                  Just (ResolvedDef d) -> defBody d
                  _ -> Nothing
          env <- get
          unless (isPreludeName nmi || Map.member nmi (monEnvMonTable env)) $
            do mtrm <- monadifyNamedTermH sc nmi maybe_body tp
               modify $ monEnvAdd nmi (monMacro0 mtrm)
     env <- get
     lift $ monadifyCompleteTerm sc env top_trm top_tp
  where preludeModules = mkModuleName <$> [["Prelude"], ["Cryptol"]]
        isPreludeName = \case
          ModuleIdentifier ident -> identModule ident `elem` preludeModules
          _ -> False

-- | Monadify a term with the specified type along with all constants it
-- contains, adding the monadifications of those constants to the monadification
-- environment
monadifyTermInEnv :: SharedContext -> MonadifyEnv ->
                     Term -> Term -> IO (Term, MonadifyEnv)
monadifyTermInEnv sc top_env top_trm top_tp =
  flip runStateT top_env $ monadifyTermInEnvH sc top_trm top_tp

-- | The implementation of 'monadifyCryptolModule' in the @StateT MonadifyEnv IO@ monad
monadifyCryptolModuleH :: SharedContext -> Env -> CryptolModule ->
                          StateT MonadifyEnv IO CryptolModule
monadifyCryptolModuleH sc cry_env (CryptolModule tysyns top_tts) =
  fmap (CryptolModule tysyns) $ flip mapM top_tts $ \top_tt ->
    do let top_tm = ttTerm top_tt
       top_tp <- lift $ ttTypeAsTerm sc cry_env top_tt
       tm <- monadifyTermInEnvH sc top_tm top_tp
       tm' <- lift $ mkTypedTerm sc tm
       return tm'

-- | Monadify each term in the given 'CryptolModule' along with all constants each
-- contains, returning a new module which each term monadified, and adding the
-- monadifications of all encountered constants to the monadification environment
monadifyCryptolModule :: SharedContext -> Env -> MonadifyEnv ->
                         CryptolModule -> IO (CryptolModule, MonadifyEnv)
monadifyCryptolModule sc cry_env top_env cry_mod =
  flip runStateT top_env $ monadifyCryptolModuleH sc cry_env cry_mod
