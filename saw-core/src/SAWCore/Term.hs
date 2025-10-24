{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWCore.Term
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Term
  ( -- * Certified terms
    Term -- abstract
  , rawTerm
  , rawType
  , rawCtx
  , scTypeCheckWHNF
  , SharedContext
  , Name(..)
  , VarName(..)
  , FieldName
  , Sort(..)
  , scFreshVarName
  , scGetModuleMap
    -- * Global declarations
  , scFreshConstant
  , scDefineConstant
  , scOpaqueConstant
    -- * Term operations
  , scTypeOf
  , scInstantiate
  --, betaNormalize
  --, scUnfoldConstants
  --, scUnfoldConstants'
  --, scUnfoldConstantSet
  --, scUnfoldConstantSet'
  , scWHNF
  , scWhnf
  , scAscribe
    -- * Building terms
    -- ** Basic lambda calculus
  , scVariable
  , scFreshVariable
  , scApply
  , scApplyAll
  , scApplyBeta
  , scApplyAllBeta
  , scLambda
  , scLambdaList
  , scAbstract
  , scAbstractTerms
  , scPi
  , scPiList
  , scGeneralize
  , scGeneralizeTerms
  , scFun
  , scFunAll
  , scConstant
  , scConstApply
  , scGlobal
  , scGlobalDef
  , scGlobalApply
    -- ** Tuples and records
  , scUnitValue
  , scUnitType
  , scPairValue
  , scPairType
  , scPairLeft
  , scPairRight
  , scTuple
  , scTupleType
  , scTupleSelector
  -- , scTupleReduced
  , scRecord
  , scRecordType
  , scRecordValue
  , scRecordProj
  , scRecordSelect
    -- ** Recursors
  , scRecursor
    -- ** Sorts
  , scSort
  , scISort
  , scSortWithFlags
    -- ** Booleans
  , scEqTrue
  , scBool
  , scBoolType
  --, scTrue
  --, scFalse
  , scNot
  , scAnd
  , scOr
  , scImplies
  , scXor
  , scBoolEq
  , scIte
  , scAndList
  , scOrList
  -- ** Natural numbers
  , scNat
  , scNatType
  , scAddNat
  , scSubNat
  , scMulNat
  , scDivNat
  , scModNat
  , scDivModNat
  , scEqualNat
  , scLtNat
  , scMinNat
  , scMaxNat
  , scUpdNatFun
    -- ** Integers
  , scIntegerType
  , scIntegerConst
  , scIntAdd, scIntSub, scIntMul
  , scIntDiv, scIntMod, scIntNeg
  , scIntAbs, scIntMin, scIntMax
  , scIntEq, scIntLe, scIntLt
  , scIntToNat, scNatToInt
  , scIntToBv, scBvToInt, scSbvToInt
    -- ** IntMod
  , scIntModType
  , scToIntMod
  , scFromIntMod
  , scIntModEq
  , scIntModAdd
  , scIntModSub
  , scIntModMul
  , scIntModNeg
    -- ** Strings
  , scString
  , scStringType
    -- ** Vectors
  , scVector
  , scVecType
  --, scVectorReduced
  , scAppend
  , scJoin
  , scSplit
  , scGet
  , scAtWithDefault
  , scAt
  , scSingle
  , scSlice
    -- ** Bitvectors
  , scBitvector
  , scBvNat
  , scBvToNat
  , scBvAt
  , scBvConst
  , scBvLit
  , scBvForall
  , scUpdBvFun
  , scBvNonzero, scBvBool
  , scBvAdd, scBvSub, scBvMul, scBvNeg
  , scBvURem, scBvUDiv, scBvSRem, scBvSDiv
  , scBvOr, scBvAnd, scBvXor
  , scBvNot
  , scBvEq, scBvUGe, scBvUGt, scBvULe, scBvULt
  , scBvSGt, scBvSGe, scBvSLt, scBvSLe
  , scBvShl, scBvShr, scBvSShr
  , scBvUExt, scBvSExt
  , scBvTrunc
  , scBvLg2
  , scBvPopcount
  , scBvCountLeadingZeros
  , scBvCountTrailingZeros
  , scLsb, scMsb
    -- ** Arrays
  , scArrayType
  , scArrayConstant
  , scArrayLookup
  , scArrayUpdate
  , scArrayEq
  , scArrayCopy
  , scArraySet
  , scArrayRangeEq
  ) where

import Data.Bits
import qualified Data.Foldable as Fold
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import Numeric.Natural (Natural)

import SAWCore.Name
import SAWCore.Prelude.Constants
import SAWCore.Recognizer
import SAWCore.SharedTerm
  ( SharedContext
  , scFreshVarName
  , scGetModuleMap
  )
import qualified SAWCore.SharedTerm as Raw
import SAWCore.Term.Certified
import SAWCore.Term.Functor

scApplyAll :: SharedContext -> Term -> [Term] -> IO Term
scApplyAll sc = Fold.foldlM (scApply sc)

scApplyAllBeta :: SharedContext -> Term -> [Term] -> IO Term
scApplyAllBeta sc = Fold.foldlM (scApplyBeta sc)

scConstApply :: SharedContext -> Name -> [Term] -> IO Term
scConstApply sc nm ts =
  do c <- scConstant sc nm
     scApplyAll sc c ts

scGlobalDef :: SharedContext -> Ident -> IO Term
scGlobalDef = scGlobal

scGlobalApply :: SharedContext -> Ident -> [Term] -> IO Term
scGlobalApply sc i ts =
  do c <- scGlobal sc i
     scApplyAll sc c ts

scLambdaList :: SharedContext -> [(VarName, Term)] -> Term -> IO Term
scLambdaList _ [] body = pure body
scLambdaList sc ((x, t) : xts) body =
  scLambda sc x t =<< scLambdaList sc xts body

scPiList :: SharedContext -> [(VarName, Term)] -> Term -> IO Term
scPiList _ [] body = pure body
scPiList sc ((x, t) : xts) body =
  scPi sc x t =<< scPiList sc xts body

scAbstractTerms :: SharedContext -> [Term] -> Term -> IO Term
scAbstractTerms _ [] body = pure body
scAbstractTerms sc (var : vars) body =
  scAbstract sc var =<< scAbstractTerms sc vars body

scGeneralizeTerms :: SharedContext -> [Term] -> Term -> IO Term
scGeneralizeTerms _ [] body = pure body
scGeneralizeTerms sc (var : vars) body =
  scGeneralize sc var =<< scGeneralizeTerms sc vars body

scISort :: SharedContext -> Sort -> IO Term
scISort sc s = scSortWithFlags sc s $ noFlags { flagInhabited = True }

scFreshVariable :: SharedContext -> Text -> Term -> IO Term
scFreshVariable sc x tp =
  do vn <- Raw.scFreshVarName sc x
     scVariable sc vn tp

scTuple :: SharedContext -> [Term] -> IO Term
scTuple sc [] = scUnitValue sc
scTuple _ [t] = pure t
scTuple sc (t : ts) = scPairValue sc t =<< scTuple sc ts

scTupleType :: SharedContext -> [Term] -> IO Term
scTupleType sc [] = scUnitType sc
scTupleType _ [t] = pure t
scTupleType sc (t : ts) = scPairType sc t =<< scTupleType sc ts

scTupleSelector :: SharedContext -> Term -> Int -> Int -> IO Term
scTupleSelector sc t i n
  | n == 1    = pure t
  | i == 1    = scPairLeft sc t
  | i > 1     = do t' <- scPairRight sc t
                   scTupleSelector sc t' (i - 1) (n - 1)
  | otherwise = fail "scTupleSelector: non-positive index"

scFunAll :: SharedContext -> [Term] -> Term -> IO Term
scFunAll sc argTypes resultType = Fold.foldrM (scFun sc) resultType argTypes

scRecord :: SharedContext -> Map FieldName Term -> IO Term
scRecord sc tm = scRecordValue sc (Map.assocs tm)

scRecordSelect :: SharedContext -> Term -> FieldName -> IO Term
scRecordSelect = scRecordProj

------------------------------------------------------------
-- Building terms using prelude functions

-- | Create a term applying @Prelude.EqTrue@ to the given term.
--
-- > EqTrue : Bool -> sort 1;
scEqTrue :: SharedContext -> Term -> IO Term
scEqTrue sc t = scGlobalApply sc "Prelude.EqTrue" [t]

-- | Create a @Prelude.Bool@-typed term from the given Boolean: @Prelude.True@
-- for @True@, @Prelude.False@ for @False@.
scBool :: SharedContext -> Bool -> IO Term
scBool sc True  = scGlobal sc "Prelude.True"
scBool sc False = scGlobal sc "Prelude.False"

-- | Create a term representing the prelude Boolean type, @Prelude.Bool@.
scBoolType :: SharedContext -> IO Term
scBoolType sc = scGlobal sc "Prelude.Bool"

-- | Create a term representing the prelude Natural type.
scNatType :: SharedContext -> IO Term
scNatType sc = scGlobal sc preludeNatIdent

-- | Create a term representing a vector type, from a term giving the length
-- and a term giving the element type.
scVecType ::
  SharedContext ->
  Term {- ^ length -} ->
  Term {- ^ element type -} ->
  IO Term
scVecType sc n e = scGlobalApply sc preludeVecIdent [n, e]

-- | Create a term applying @Prelude.not@ to the given term.
--
-- > not : Bool -> Bool;
scNot :: SharedContext -> Term -> IO Term
scNot sc t = scGlobalApply sc "Prelude.not" [t]

-- | Create a term applying @Prelude.and@ to the two given terms.
--
-- > and : Bool -> Bool -> Bool;
scAnd :: SharedContext -> Term -> Term -> IO Term
scAnd sc x y = scGlobalApply sc "Prelude.and" [x, y]

-- | Create a term applying @Prelude.or@ to the two given terms.
--
-- > or : Bool -> Bool -> Bool;
scOr :: SharedContext -> Term -> Term -> IO Term
scOr sc x y = scGlobalApply sc "Prelude.or" [x, y]

-- | Create a term applying @Prelude.implies@ to the two given terms.
--
-- > implies : Bool -> Bool -> Bool;
scImplies :: SharedContext -> Term -> Term -> IO Term
scImplies sc x y = scGlobalApply sc "Prelude.implies" [x, y]

-- | Create a term applying @Prelude.xor@ to the two given terms.
--
-- > xor : Bool -> Bool -> Bool;
scXor :: SharedContext -> Term -> Term -> IO Term
scXor sc x y = scGlobalApply sc "Prelude.xor" [x, y]

-- | Create a term applying @Prelude.boolEq@ to the two given terms.
--
-- > boolEq : Bool -> Bool -> Bool;
scBoolEq :: SharedContext -> Term -> Term -> IO Term
scBoolEq sc x y = scGlobalApply sc "Prelude.boolEq" [x, y]

-- | Create a universally quantified bitvector term.
--
-- > bvForall : (n : Nat) -> (Vec n Bool -> Bool) -> Bool;
scBvForall :: SharedContext -> Term -> Term -> IO Term
scBvForall sc w f = scGlobalApply sc "Prelude.bvForall" [w, f]

-- | Create a non-dependent if-then-else term.
--
-- > ite : (a : sort 1) -> Bool -> a -> a -> a;
scIte :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scIte sc t b x y = scGlobalApply sc "Prelude.ite" [t, b, x, y]

-- | Build a conjunction from a list of boolean terms.
scAndList :: SharedContext -> [Term] -> IO Term
scAndList sc = conj . filter nontrivial
  where
    nontrivial x = asBool (rawTerm x) /= Just True
    conj [] = scBool sc True
    conj [x] = return x
    conj (x : xs) = Fold.foldlM (scAnd sc) x xs

-- | Build a conjunction from a list of boolean terms.
scOrList :: SharedContext -> [Term] -> IO Term
scOrList sc = disj . filter nontrivial
  where
    nontrivial x = asBool (rawTerm x) /= Just False
    disj [] = scBool sc False
    disj [x] = return x
    disj (x : xs) = Fold.foldlM (scOr sc) x xs


-- | Create a term applying @Prelude.append@ to two vectors.
--
-- > append : (m n : Nat) -> (e : sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
scAppend :: SharedContext -> Term -> Term -> Term -> Term -> Term -> IO Term
scAppend sc m n t x y = scGlobalApply sc "Prelude.append" [m, n, t, x, y]

-- | Create a term applying @Prelude.join@ to a vector of vectors.
--
-- > join  : (m n : Nat) -> (a : sort 0) -> Vec m (Vec n a) -> Vec (mulNat m n) a;
scJoin :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scJoin sc m n a v = scGlobalApply sc "Prelude.join" [m, n, a, v]

-- | Create a term splitting a vector with @Prelude.split@.
--
-- > split : (m n : Nat) -> (a : sort 0) -> Vec (mulNat m n) a -> Vec m (Vec n a);
scSplit :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scSplit sc m n a v = scGlobalApply sc "Prelude.split" [m, n, a, v]

-- | Create a term selecting a range of values from a vector with @Prelude.slice@.
--
-- > slice : (e : sort 1) -> (i n o : Nat) -> Vec (addNat (addNat i n) o) e -> Vec n e;
scSlice :: SharedContext -> Term -> Term -> Term -> Term -> Term -> IO Term
scSlice sc e i n o a = scGlobalApply sc "Prelude.slice" [e, i, n, o, a]

-- | Create a term accessing a particular element of a vector with @get@.
--
-- > get : (n : Nat) -> (e : sort 0) -> Vec n e -> Fin n -> e;
scGet :: SharedContext -> Term -> Term ->
         Term -> Term -> IO Term
scGet sc n e v i = scGlobalApply sc (mkIdent preludeName "get") [n, e, v, i]

-- | Create a term accessing a particular element of a vector with @bvAt@,
-- which uses a bitvector for indexing.
--
-- > bvAt : (n : Nat) -> (a : sort 0) -> (w : Nat) -> Vec n a -> Vec w Bool -> a;
scBvAt :: SharedContext -> Term -> Term -> Term -> Term -> Term -> IO Term
scBvAt sc n a i xs idx = scGlobalApply sc (mkIdent preludeName "bvAt") [n, a, i, xs, idx]

-- | Create a term accessing a particular element of a vector, with a default
-- to return if the index is out of bounds.
--
-- > atWithDefault : (n : Nat) -> (a : sort 0) -> a -> Vec n a -> Nat -> a;
scAtWithDefault :: SharedContext -> Term -> Term -> Term -> Term -> Term -> IO Term
scAtWithDefault sc n a v xs idx = scGlobalApply sc (mkIdent preludeName "atWithDefault") [n, a, v, xs, idx]

-- | Create a term accessing a particular element of a vector, failing if the
-- index is out of bounds.
--
-- > at : (n : Nat) -> (a : sort 0) -> Vec n a -> Nat -> a;
scAt :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scAt sc n a xs idx = scGlobalApply sc (mkIdent preludeName "at") [n, a, xs, idx]

-- | Create a term evaluating to a vector containing a single element.
--
-- > single : (e : sort 1) -> e -> Vec 1 e;
scSingle :: SharedContext -> Term -> Term -> IO Term
scSingle sc e x = scGlobalApply sc (mkIdent preludeName "single") [e, x]

-- | Create a term computing the least significant bit of a bitvector, given a
-- length and bitvector.
--
-- > lsb : (n : Nat) -> Vec (Succ n) Bool -> Bool;
scLsb :: SharedContext -> Term -> Term -> IO Term
scLsb sc n x = scGlobalApply sc (mkIdent preludeName "lsb") [n, x]

-- | Create a term computing the most significant bit of a bitvector, given a
-- length and bitvector.
--
-- > msb : (n : Nat) -> Vec (Succ n) Bool -> Bool;
scMsb :: SharedContext -> Term -> Term -> IO Term
scMsb sc n x = scGlobalApply sc (mkIdent preludeName "lsb") [n, x]

-- Primitive operations on nats

-- | Create a term computing the sum of the two given (natural number) terms.
--
-- > addNat : Nat -> Nat -> Nat;
scAddNat :: SharedContext -> Term -> Term -> IO Term
scAddNat sc x y = scGlobalApply sc "Prelude.addNat" [x, y]

-- | Create a term computing the difference between the two given
-- (natural number) terms.
--
-- > subNat : Nat -> Nat -> Nat
scSubNat :: SharedContext -> Term -> Term -> IO Term
scSubNat sc x y = scGlobalApply sc "Prelude.subNat" [x, y]

-- | Create a term computing the product of the two given (natural number)
-- terms.
--
-- > mulNat : Nat -> Nat -> Nat;
scMulNat :: SharedContext -> Term -> Term -> IO Term
scMulNat sc x y = scGlobalApply sc "Prelude.mulNat" [x, y]

-- | Create a term computing the quotient of the two given (natural number)
-- terms.
--
-- > divNat : Nat -> Nat -> Nat;
scDivNat :: SharedContext -> Term -> Term -> IO Term
scDivNat sc x y = scGlobalApply sc "Prelude.divNat" [x, y]

-- | Create a term computing the remainder upon division of the two given
-- (natural number) terms.
--
-- > modNat : Nat -> Nat -> Nat;
scModNat :: SharedContext -> Term -> Term -> IO Term
scModNat sc x y = scGlobalApply sc "Prelude.modNat" [x, y]

-- | Create a term computing the quotient and remainder upon division of the
-- two given (natural number) terms, giving the result as a pair.
--
-- > divModNat : Nat -> Nat -> Nat * Nat;
scDivModNat :: SharedContext -> Term -> Term -> IO Term
scDivModNat sc x y = scGlobalApply sc "Prelude.divModNat" [x, y]

-- | Create a term computing whether the two given (natural number) terms are
-- equal.
--
-- > equalNat : Nat -> Nat -> Bool;
scEqualNat :: SharedContext -> Term -> Term -> IO Term
scEqualNat sc x y = scGlobalApply sc "Prelude.equalNat" [x, y]

-- | Create a term computing whether the first term (a natural number) is less
-- than the second term (also a natural number).
--
-- > ltNat : Nat -> Nat -> Bool;
scLtNat :: SharedContext -> Term -> Term -> IO Term
scLtNat sc x y = scGlobalApply sc "Prelude.ltNat" [x, y]

-- | Create a term computing the minimum of the two given (natural number)
-- terms.
--
-- > minNat : Nat -> Nat -> Nat
scMinNat :: SharedContext -> Term -> Term -> IO Term
scMinNat sc x y = scGlobalApply sc "Prelude.minNat" [x, y]

-- | Create a term computing the maximum of the two given (natural number)
-- terms.
--
-- > maxNat : Nat -> Nat -> Nat;
scMaxNat :: SharedContext -> Term -> Term -> IO Term
scMaxNat sc x y = scGlobalApply sc "Prelude.maxNat" [x, y]

-- Primitive operations on Integer

-- | Create a term representing the prelude Integer type.
scIntegerType :: SharedContext -> IO Term
scIntegerType sc = scGlobal sc preludeIntegerIdent

-- | Create an integer constant term from an 'Integer'.
scIntegerConst :: SharedContext -> Integer -> IO Term
scIntegerConst sc i
  | i >= 0    = scNatToInt sc =<< scNat sc (fromInteger i)
  | otherwise = scIntNeg sc =<< scNatToInt sc =<< scNat sc (fromInteger (- i))

-- | Create a term applying the integer addition primitive.
--
-- > intAdd : Integer -> Integer -> Integer
scIntAdd :: SharedContext -> Term -> Term -> IO Term
scIntAdd sc x y = scGlobalApply sc "Prelude.intAdd" [x, y]

-- | Create a term applying the integer subtraction primitive.
--
-- > intSub : Integer -> Integer -> Integer
scIntSub :: SharedContext -> Term -> Term -> IO Term
scIntSub sc x y = scGlobalApply sc "Prelude.intSub" [x, y]

-- | Create a term applying the integer multiplication primitive.
--
-- > intMul : Integer -> Integer -> Integer
scIntMul :: SharedContext -> Term -> Term -> IO Term
scIntMul sc x y = scGlobalApply sc "Prelude.intMul" [x, y]

-- | Create a term applying the integer division primitive.
--
-- > intDiv : Integer -> Integer -> Integer
scIntDiv :: SharedContext -> Term -> Term -> IO Term
scIntDiv sc x y = scGlobalApply sc "Prelude.intDiv" [x, y]

-- | Create a term applying the integer modulus primitive.
--
-- > intMod : Integer -> Integer -> Integer
scIntMod :: SharedContext -> Term -> Term -> IO Term
scIntMod sc x y = scGlobalApply sc "Prelude.intMod" [x, y]

-- | Create a term applying the integer min primitive.
--
-- > intMin : Integer -> Integer -> Integer
scIntMin :: SharedContext -> Term -> Term -> IO Term
scIntMin sc x y = scGlobalApply sc "Prelude.intMin" [x, y]

-- | Create a term applying the integer max primitive.
--
-- > intMax : Integer -> Integer -> Integer
scIntMax :: SharedContext -> Term -> Term -> IO Term
scIntMax sc x y = scGlobalApply sc "Prelude.intMax" [x, y]

-- | Create a term applying the negation integer primitive.
--
-- > intNeg : Integer -> Integer;
scIntNeg :: SharedContext -> Term -> IO Term
scIntNeg sc x = scGlobalApply sc "Prelude.intNeg" [x]

-- | Create a term applying the absolute value integer primitive.
--
-- > intAbs : Integer -> Integer;
scIntAbs :: SharedContext -> Term -> IO Term
scIntAbs sc x = scGlobalApply sc "Prelude.intAbs" [x]

-- | Create a term applying the integer equality testing primitive.
--
-- > intEq : Integer -> Integer -> Bool;
scIntEq :: SharedContext -> Term -> Term -> IO Term
scIntEq sc x y = scGlobalApply sc "Prelude.intEq" [x, y]

-- | Create a term applying the integer less-than-or-equal primitive.
--
-- > intLe : Integer -> Integer -> Bool;
scIntLe :: SharedContext -> Term -> Term -> IO Term
scIntLe sc x y = scGlobalApply sc "Prelude.intLe" [x, y]

-- | Create a term applying the integer less-than primitive.
--
-- > intLt : Integer -> Integer -> Bool;
scIntLt :: SharedContext -> Term -> Term -> IO Term
scIntLt sc x y = scGlobalApply sc "Prelude.intLt" [x, y]

-- | Create a term computing a @Nat@ from an @Integer@, if possible.
--
-- > intToNat : Integer -> Nat;
scIntToNat :: SharedContext -> Term -> IO Term
scIntToNat sc x = scGlobalApply sc "Prelude.intToNat" [x]

-- | Create a term computing an @Integer@ from a @Nat@.
--
-- > natToInt : Nat -> Integer;
scNatToInt :: SharedContext -> Term -> IO Term
scNatToInt sc x = scGlobalApply sc "Prelude.natToInt" [x]

-- | Create a term computing a bitvector of length n from an @Integer@, if
-- possible.
--
-- > intToBv : (n::Nat) -> Integer -> Vec n Bool;
scIntToBv :: SharedContext -> Term -> Term -> IO Term
scIntToBv sc n x = scGlobalApply sc "Prelude.intToBv" [n, x]

-- | Create a term computing an @Integer@ from a bitvector of length n.
-- This produces the unsigned value of the bitvector.
--
-- > bvToInt : (n : Nat) -> Vec n Bool -> Integer;
scBvToInt :: SharedContext -> Term -> Term -> IO Term
scBvToInt sc n x = scGlobalApply sc "Prelude.bvToInt" [n, x]

-- | Create a term computing an @Integer@ from a bitvector of length n.
-- This produces the 2's complement signed value of the bitvector.
--
-- > sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
scSbvToInt :: SharedContext -> Term -> Term -> IO Term
scSbvToInt sc n x = scGlobalApply sc "Prelude.sbvToInt" [n, x]


-- Primitive operations on IntMod

-- | Create a term representing the prelude @IntMod@ type.
--
-- > IntMod : Nat -> sort 0;
scIntModType :: SharedContext -> Term -> IO Term
scIntModType sc n = scGlobalApply sc "Prelude.IntMod" [n]

-- | Convert an integer to an integer mod n.
--
-- > toIntMod : (n : Nat) -> Integer -> IntMod n;
scToIntMod :: SharedContext -> Term -> Term -> IO Term
scToIntMod sc n x = scGlobalApply sc "Prelude.toIntMod" [n, x]

-- | Convert an integer mod n to an integer.
--
-- > fromIntMod : (n : Nat) -> IntMod n -> Integer;
scFromIntMod :: SharedContext -> Term -> Term -> IO Term
scFromIntMod sc n x = scGlobalApply sc "Prelude.fromIntMod" [n, x]

-- | Equality test on the @IntMod@ type
--
-- > intModEq  : (n : Nat) -> IntMod n -> IntMod n -> Bool;
scIntModEq :: SharedContext -> Term -> Term -> Term -> IO Term
scIntModEq sc n x y = scGlobalApply sc "Prelude.intModEq" [n, x, y]

-- | Addition of @IntMod@ values
--
-- > intModAdd : (n : Nat) -> IntMod n -> IntMod n -> IntMod n;
scIntModAdd :: SharedContext -> Term -> Term -> Term -> IO Term
scIntModAdd sc n x y = scGlobalApply sc "Prelude.intModAdd" [n, x, y]

-- | Subtraction of @IntMod@ values
--
-- > intModSub : (n : Nat) -> IntMod n -> IntMod n -> IntMod n;
scIntModSub :: SharedContext -> Term -> Term -> Term -> IO Term
scIntModSub sc n x y = scGlobalApply sc "Prelude.intModSub" [n, x, y]

-- | Multiplication of @IntMod@ values
--
-- > intModMul : (n : Nat) -> IntMod n -> IntMod n -> IntMod n;
scIntModMul :: SharedContext -> Term -> Term -> Term -> IO Term
scIntModMul sc n x y = scGlobalApply sc "Prelude.intModMul" [n, x, y]

-- | Negation (additive inverse) of @IntMod@ values
--
-- > intModNeg : (n : Nat) -> IntMod n -> IntMod n;
scIntModNeg :: SharedContext -> Term -> Term -> IO Term
scIntModNeg sc n x = scGlobalApply sc "Prelude.intModNeg" [n, x]

-- | Create a term representing the primitive saw-core type @String@.
scStringType :: SharedContext -> IO Term
scStringType sc = scGlobal sc preludeStringIdent


-- Primitive operations on bitvectors

-- | Create a term computing the type of a length-n bitvector.
--
-- > bitvector : (n : Nat) -> sort 1
scBitvector :: SharedContext -> Natural -> IO Term
scBitvector sc size =
  do s <- scNat sc size
     t <- scBoolType sc
     scVecType sc s t

-- | Create a term computing a bitvector of length x from a @Nat@, if possible.
--
-- > bvNat : (n : Nat) -> Nat -> Vec n Bool;
scBvNat :: SharedContext -> Term -> Term -> IO Term
scBvNat sc x y = scGlobalApply sc "Prelude.bvNat" [x, y]

-- | Create a term computing a @Nat@ from a bitvector of length n.
--
-- > bvToNat : (n : Nat) -> Vec n Bool -> Nat;
scBvToNat :: SharedContext -> Natural -> Term -> IO Term
scBvToNat sc n x =
  do n' <- scNat sc n
     scGlobalApply sc "Prelude.bvToNat" [n', x]

-- | Create a @bvNat@ term computing a bitvector of the given length
-- representing the given 'Integer' value (if possible).
scBvConst :: SharedContext -> Natural -> Integer -> IO Term
scBvConst sc w v =
  do x <- scNat sc w
     y <- scNat sc $ fromInteger $ v .&. (1 `shiftL` fromIntegral w - 1)
     scGlobalApply sc "Prelude.bvNat" [x, y]

-- | Create a vector literal term computing a bitvector of the given length
-- representing the given 'Integer' value (if possible).
scBvLit :: SharedContext -> Natural -> Integer -> IO Term
scBvLit sc w v =
  do bool_tp <- scBoolType sc
     bits <- mapM (scBool sc . testBit v)
                  [(fromIntegral w - 1), (fromIntegral w - 2) .. 0]
     scVector sc bool_tp bits

-- | Create a term computing the bitvector of given length representing 0 if
-- the other given term evaluates to @False@ and representing 1 if the other
-- given term evaluates to @True@.
--
-- > bvBool : (n : Nat) -> Bool -> Vec n Bool;
scBvBool :: SharedContext -> Term -> Term -> IO Term
scBvBool sc n x = scGlobalApply sc "Prelude.bvBool" [n, x]

-- | Create a term returning true if and only if the given bitvector represents
-- a nonzero value.
--
-- > bvNonzero : (n : Nat) -> Vec n Bool -> Bool;
scBvNonzero :: SharedContext -> Term -> Term -> IO Term
scBvNonzero sc n x = scGlobalApply sc "Prelude.bvNonzero" [n, x]

-- | Create a term computing the 2's complement negation of the given
-- bitvector.
-- > bvNeg : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvNeg :: SharedContext -> Term -> Term -> IO Term
scBvNeg sc n x = scGlobalApply sc "Prelude.bvNeg" [n, x]

-- | Create a term applying the bitvector addition primitive.
--
-- > bvAdd : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvAdd :: SharedContext -> Term -> Term -> Term -> IO Term
scBvAdd sc n x y = scGlobalApply sc "Prelude.bvAdd" [n, x, y]

-- | Create a term applying the bitvector subtraction primitive.
--
-- > bvSub : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvSub :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSub sc n x y = scGlobalApply sc "Prelude.bvSub" [n, x, y]

-- | Create a term applying the bitvector multiplication primitive.
--
-- > bvMul : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvMul :: SharedContext -> Term -> Term -> Term -> IO Term
scBvMul sc n x y = scGlobalApply sc "Prelude.bvMul" [n, x, y]

-- | Create a term applying the bitvector (unsigned) modulus primitive.
--
-- > bvURem : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvURem :: SharedContext -> Term -> Term -> Term -> IO Term
scBvURem sc n x y = scGlobalApply sc "Prelude.bvURem" [n, x, y]

-- | Create a term applying the bitvector (unsigned) division primitive.
--
-- > bvUDiv : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvUDiv :: SharedContext -> Term -> Term -> Term -> IO Term
scBvUDiv sc n x y = scGlobalApply sc "Prelude.bvUDiv" [n, x, y]

-- | Create a term applying the bitvector (signed) modulus primitive.
--
-- > bvSRem : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvSRem :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSRem sc n x y = scGlobalApply sc "Prelude.bvSRem" [n, x, y]

-- | Create a term applying the bitvector (signed) division primitive.
--
-- > bvSDiv : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvSDiv :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSDiv sc n x y = scGlobalApply sc "Prelude.bvSDiv" [n, x, y]

-- | Create a term applying the lg2 bitvector primitive.
--
-- > bvLg2 : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvLg2 :: SharedContext -> Term -> Term -> IO Term
scBvLg2 sc n x = scGlobalApply sc "Prelude.bvLg2" [n, x]

-- | Create a term applying the population count bitvector primitive.
--
-- > bvPopcount : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvPopcount :: SharedContext -> Term -> Term -> IO Term
scBvPopcount sc n x = scGlobalApply sc "Prelude.bvPopcount" [n, x]

-- | Create a term applying the leading zero counting bitvector primitive.
--
-- > bvCountLeadingZeros : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvCountLeadingZeros :: SharedContext -> Term -> Term -> IO Term
scBvCountLeadingZeros sc n x = scGlobalApply sc "Prelude.bvCountLeadingZeros" [n, x]

-- | Create a term applying the trailing zero counting bitvector primitive.
--
-- > bvCountTrailingZeros : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvCountTrailingZeros :: SharedContext -> Term -> Term -> IO Term
scBvCountTrailingZeros sc n x = scGlobalApply sc "Prelude.bvCountTrailingZeros" [n, x]

-- | Create a term applying the bit-wise and primitive.
--
-- > bvAnd : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvAnd :: SharedContext -> Term -> Term -> Term -> IO Term
scBvAnd sc n x y = scGlobalApply sc "Prelude.bvAnd" [n, x, y]

-- | Create a term applying the bit-wise xor primitive.
--
-- > bvXor : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvXor :: SharedContext -> Term -> Term -> Term -> IO Term
scBvXor sc n x y = scGlobalApply sc "Prelude.bvXor" [n, x, y]

-- | Create a term applying the bit-wise or primitive.
--
-- > bvOr : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvOr :: SharedContext -> Term -> Term -> Term -> IO Term
scBvOr  sc n x y = scGlobalApply sc "Prelude.bvOr"  [n, x, y]

-- | Create a term applying the bit-wise negation primitive.
--
-- > bvNot : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvNot :: SharedContext -> Term -> Term -> IO Term
scBvNot sc n x = scGlobalApply sc "Prelude.bvNot" [n, x]

-- | Create a term computing whether the two given bitvectors (of equal length)
-- are equal.
--
-- > bvEq : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvEq :: SharedContext -> Term -> Term -> Term -> IO Term
scBvEq sc n x y = scGlobalApply sc "Prelude.bvEq"  [n, x, y]

-- | Create a term applying the bitvector (unsigned) greater-than-or-equal
-- primitive.
--
-- > bvuge : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvUGe :: SharedContext -> Term -> Term -> Term -> IO Term
scBvUGe sc n x y = scGlobalApply sc "Prelude.bvuge" [n, x, y]

-- | Create a term applying the bitvector (unsigned) less-than-or-equal
-- primitive.
--
-- > bvule : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvULe :: SharedContext -> Term -> Term -> Term -> IO Term
scBvULe sc n x y = scGlobalApply sc "Prelude.bvule" [n, x, y]

-- | Create a term applying the bitvector (unsigned) greater-than primitive.
--
-- > bvugt : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvUGt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvUGt sc n x y = scGlobalApply sc "Prelude.bvugt" [n, x, y]

-- | Create a term applying the bitvector (unsigned) less-than primitive.
--
-- > bvult : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvULt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvULt sc n x y = scGlobalApply sc "Prelude.bvult" [n, x, y]

-- | Create a term applying the bitvector (signed) greater-than-or-equal
-- primitive.
--
-- > bvsge : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvSGe :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSGe sc n x y = scGlobalApply sc "Prelude.bvsge" [n, x, y]

-- | Create a term applying the bitvector (signed) less-than-or-equal
-- primitive.
--
-- > bvsle : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvSLe :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSLe sc n x y = scGlobalApply sc "Prelude.bvsle" [n, x, y]

-- | Create a term applying the bitvector (signed) greater-than primitive.
--
-- > bvsgt : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvSGt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSGt sc n x y = scGlobalApply sc "Prelude.bvsgt" [n, x, y]

-- | Create a term applying the bitvector (signed) less-than primitive.
--
-- > bvslt : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvSLt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSLt sc n x y = scGlobalApply sc "Prelude.bvslt" [n, x, y]

-- | Create a term applying the left-shift primitive.
--
-- > bvShl : (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool;
scBvShl :: SharedContext -> Term -> Term -> Term -> IO Term
scBvShl sc n x y = scGlobalApply sc "Prelude.bvShl" [n, x, y]

-- | Create a term applying the logical right-shift primitive.
--
-- > bvShr : (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool;
scBvShr :: SharedContext -> Term -> Term -> Term -> IO Term
scBvShr sc n x y = scGlobalApply sc "Prelude.bvShr" [n, x, y]

-- | Create a term applying the arithmetic/signed right-shift primitive.
--
-- > bvSShr : (w : Nat) -> Vec (Succ w) Bool -> Nat -> Vec (Succ w) Bool;
scBvSShr :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSShr sc n x y = scGlobalApply sc "Prelude.bvSShr" [n, x, y]

-- | Create a term applying the unsigned bitvector extension primitive.
--
-- > bvUExt : (m n : Nat) -> Vec n Bool -> Vec (addNat m n) Bool;
scBvUExt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvUExt sc n m x = scGlobalApply sc "Prelude.bvUExt" [n, m, x]

-- | Create a term applying the signed bitvector extension primitive.
--
-- > bvSExt : (m n : Nat) -> Vec (Succ n) Bool -> Vec (addNat m (Succ n)) Bool;
scBvSExt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSExt sc n m x = scGlobalApply sc "Prelude.bvSExt" [n, m, x]

-- | Create a term applying the bitvector truncation primitive. Note that this
-- truncates starting from the most significant bit.
--
-- > bvTrunc : (m n : Nat) -> Vec (addNat m n) Bool -> Vec n Bool;
scBvTrunc :: SharedContext -> Term -> Term -> Term -> IO Term
scBvTrunc sc n m x = scGlobalApply sc "Prelude.bvTrunc" [n, m, x]

-- | Create a term applying the @updNatFun@ primitive, which satisfies the
-- following laws:
--
-- > updNatFun : (a : sort 0) -> (Nat -> a) -> Nat -> a -> (Nat -> a);
-- > updNatFun a _ i v i == v
-- > updNatFun a f i v x == f x, when i != x
scUpdNatFun :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scUpdNatFun sc a f i v = scGlobalApply sc "Prelude.updNatFun" [a, f, i, v]

-- | Create a term applying the @updBvFun@ primitive, which has the same
-- behavior as @updNatFun@ but acts on bitvectors.
--
-- > updBvFun : (n : Nat) -> (a : sort 0) -> (Vec n Bool -> a) -> Vec n Bool -> a -> (Vec n Bool -> a);
scUpdBvFun :: SharedContext -> Term -> Term -> Term -> Term -> Term -> IO Term
scUpdBvFun sc n a f i v = scGlobalApply sc "Prelude.updBvFun" [n, a, f, i, v]

-- | Create a term representing the type of arrays, given an index type and
-- element type (as 'Term's).
--
-- > Array : sort 0 -> sort 0 -> sort 0
scArrayType :: SharedContext -> Term -> Term -> IO Term
scArrayType sc a b = scGlobalApply sc "Prelude.Array" [a, b]

-- | Create a term computing a constant array, given an index type, element type, 
-- and element (all as 'Term's).
--
-- > arrayConstant : (a b : sort 0) -> b -> (Array a b);
scArrayConstant :: SharedContext -> Term -> Term -> Term -> IO Term
scArrayConstant sc a b e = scGlobalApply sc "Prelude.arrayConstant" [a, b, e]

-- | Create a term computing the value at a particular index of an array.
--
-- > arrayLookup : (a b : sort 0) -> (Array a b) -> a -> b;
scArrayLookup :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scArrayLookup sc a b f i = scGlobalApply sc "Prelude.arrayLookup" [a, b, f, i]

-- | Create a term computing an array updated at a particular index.
--
-- > arrayUpdate : (a b : sort 0) -> (Array a b) -> a -> b -> (Array a b);
scArrayUpdate :: SharedContext -> Term -> Term -> Term -> Term -> Term -> IO Term
scArrayUpdate sc a b f i e = scGlobalApply sc "Prelude.arrayUpdate" [a, b, f, i, e]

-- | Create a term computing the equality of two arrays.
--
-- > arrayEq : (a b : sort 0) -> (Array a b) -> (Array a b) -> Bool;
scArrayEq :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scArrayEq sc a b x y = scGlobalApply sc "Prelude.arrayEq" [a, b, x, y]

-- > arrayCopy : (n : Nat) -> (a : sort 0) -> Array (Vec n Bool) a -> Vec n Bool -> Array (Vec n Bool) a -> Vec n Bool -> Vec n Bool -> Array (Vec n Bool) a;
-- > arrayCopy n a dest_arr dest_idx src_arr src_idx len
scArrayCopy :: SharedContext -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> IO Term
scArrayCopy sc n a f i g j l = scGlobalApply sc "Prelude.arrayCopy" [n, a, f, i, g, j, l]

-- > arraySet : (n : Nat) -> (a : sort 0) -> Array (Vec n Bool) a -> Vec n Bool -> a -> Vec n Bool -> Array (Vec n Bool) a;
-- > arraySet n a arr idx val len
scArraySet :: SharedContext -> Term -> Term -> Term -> Term -> Term -> Term -> IO Term
scArraySet sc n a f i e l = scGlobalApply sc "Prelude.arraySet" [n, a, f, i, e, l]

-- > arrayRangeEq : (n : Nat) -> (a : sort 0) -> Array (Vec n Bool) a -> Vec n Bool -> Array (Vec n Bool) a -> Vec n Bool -> Vec n Bool -> Bool;
-- > arrayRangeEq n a lhs_arr lhs_idx rhs_arr rhs_idx len
scArrayRangeEq :: SharedContext -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> IO Term
scArrayRangeEq sc n a f i g j l = scGlobalApply sc "Prelude.arrayRangeEq" [n, a, f, i, g, j, l]
