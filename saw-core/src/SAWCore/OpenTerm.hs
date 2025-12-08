{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

{- |
Module      : SAWCore.OpenTerm
Copyright   : Galois, Inc. 2018
License     : BSD3
Stability   : experimental
Portability : non-portable (language extensions)

This module defines a convenient DSL for building terms in a pure way,
where sub-terms can be freely composed and combined into super-terms
without monadic sequencing or 'IO' computations; the 'IO' computation
is only run at the top level when all the term-building is complete.

Users of this interface can also build binding constructs like lambda-
and pi-abstractions using higher-order abstract syntax, meaning that
the bodies of these term constructs are specified as Haskell functions
that take in terms for the bound variables.

Since many function names are short and may clash with names from
other modules, this module is intended to be imported @qualified@,
e.g.

>  import SAWCore.OpenTerm (OpenTerm)
>  import qualified SAWCore.OpenTerm as OpenTerm

To use the 'OpenTerm' API, the caller builds up 'OpenTerm's using a
variety of combinators that mirror the SAW core 'Term' structure.
As some useful examples of 'OpenTerm' operations, 'apply' applies one
'OpenTerm' to another, 'global' builds an 'OpenTerm' for a global
identifier, and 'lambda' builds a lambda-abstraction. For instance,
the SAW core term

> \ (f : Bool -> Bool) (x : Bool) -> f x

can be built with the 'OpenTerm' expression

> let boolTy = global "Prelude.Bool" in
> lambda "f" (arrow boolTy boolTy) $ \f ->
> lambda "x" boolTy $ \x ->
> apply f x

Existing SAW core 'Term's can be used in 'OpenTerm' by applying 'term'.
At the top level, 'complete' then "completes" an 'OpenTerm' by running
its underlying 'IO' computation to build and type-check the resulting
SAW core 'Term'.
-}

module SAWCore.OpenTerm (
  -- * Open terms and converting to closed terms
  OpenTerm(..), complete, completeType,
  -- * Basic operations for building open terms
  term,
  typeOf,
  flat, sort, nat,
  unit, unitType,
  stringLit, stringType,
  true, false, bool, boolType,
  arrayValue, vectorType, bvLit, bvType,
  pair, pairType, pairLeft, pairRight,
  tuple, tupleType, projTuple,
  tuple', tupleType', projTuple',
  record, recordType, projRecord,
  global, variable,
  app, apply, applyGlobal,
  lambda, lambdas,
  piType, piMulti, arrow, mkLet, sawLet,
  bitvectorType, list, eitherType,
  ) where

import qualified Data.Vector as V
import Data.Text (Text)
import Numeric.Natural

import SAWCore.Name
import SAWCore.Panic
import SAWCore.Term.Functor
import SAWCore.SharedTerm
import qualified SAWCore.Term.Certified as SC
import SAWCore.SCTypeCheck


-- | An open term is represented as a type-checking computation that computes a
-- SAW core term and its type
newtype OpenTerm = OpenTerm { unOpenTerm :: TCM SC.Term }

-- | \"Complete\" an 'OpenTerm' to a closed term or 'fail' on type-checking
-- error
complete :: SharedContext -> OpenTerm -> IO Term
complete sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM termM sc

-- | \"Complete\" an 'OpenTerm' to a closed term for its type
completeType :: SharedContext -> OpenTerm -> IO Term
completeType sc ot = scTypeOf sc =<< complete sc ot

-- | Embed a 'Term' into an 'OpenTerm'.
term :: Term -> OpenTerm
term t = OpenTerm $ pure t

-- | Return type of an 'OpenTerm' as an 'OpenTerm'.
typeOf :: OpenTerm -> OpenTerm
typeOf (OpenTerm m) =
  OpenTerm $ do t <- m
                liftTCM SC.scTypeOf t

-- | Build an 'OpenTerm' from a 'FlatTermF'
flat :: FlatTermF OpenTerm -> OpenTerm
flat ftf = OpenTerm $
  (sequence (fmap unOpenTerm ftf) >>= inferFlatTermF)

-- | Build an 'OpenTerm' for a sort
sort :: Sort -> OpenTerm
sort s = flat (Sort s noFlags)

-- | Build an 'OpenTerm' for a natural number literal
nat :: Natural -> OpenTerm
nat n = OpenTerm $ liftTCM SC.scNat n

-- | The 'OpenTerm' for the unit value
unit :: OpenTerm
unit = flat UnitValue

-- | The 'OpenTerm' for the unit type
unitType :: OpenTerm
unitType = flat UnitType

-- | Build a SAW core string literal.
stringLit :: Text -> OpenTerm
stringLit = flat . StringLit

-- | Return the SAW core type @String@ of strings.
stringType :: OpenTerm
stringType = global "Prelude.String"

-- | The 'True' value as a SAW core term
true :: OpenTerm
true = global "Prelude.True"

-- | The 'False' value as a SAW core term
false :: OpenTerm
false = global "Prelude.False"

-- | Convert a 'Bool' to a SAW core term
bool :: Bool -> OpenTerm
bool True = global "Prelude.True"
bool False = global "Prelude.False"

-- | The 'Bool' type as a SAW core term
boolType :: OpenTerm
boolType = global "Prelude.Bool"

-- | Build an 'OpenTerm' for an array literal
arrayValue :: OpenTerm -> [OpenTerm] -> OpenTerm
arrayValue tp elems =
  flat $ ArrayValue tp $ V.fromList elems

-- | Create a SAW core term for a bitvector literal
bvLit :: [Bool] -> OpenTerm
bvLit bits =
  arrayValue boolType $ map bool bits

-- | Create a SAW core term for a vector type
vectorType :: OpenTerm -> OpenTerm -> OpenTerm
vectorType n a = applyGlobal "Prelude.Vec" [n,a]

-- | Create a SAW core term for the type of a bitvector
bvType :: Integral a => a -> OpenTerm
bvType n =
  apply (global "Prelude.Vec")
  [nat (fromIntegral n), boolType]

-- | Build an 'OpenTerm' for a pair
pair :: OpenTerm -> OpenTerm -> OpenTerm
pair t1 t2 = flat $ PairValue t1 t2

-- | Build an 'OpenTerm' for a pair type
pairType :: OpenTerm -> OpenTerm -> OpenTerm
pairType t1 t2 = flat $ PairType t1 t2

-- | Build an 'OpenTerm' for the left projection of a pair
pairLeft :: OpenTerm -> OpenTerm
pairLeft t = flat $ PairLeft t

-- | Build an 'OpenTerm' for the right projection of a pair
pairRight :: OpenTerm -> OpenTerm
pairRight t = flat $ PairRight t

-- | Build a right-nested tuple as an 'OpenTerm'
tuple :: [OpenTerm] -> OpenTerm
tuple = foldr pair unit

-- | Build a right-nested tuple type as an 'OpenTerm'
tupleType :: [OpenTerm] -> OpenTerm
tupleType = foldr pairType unitType

-- | Project the @n@th element of a right-nested tuple type
projTuple :: Integer -> OpenTerm -> OpenTerm
projTuple 0 t = pairLeft t
projTuple i t = projTuple (i-1) (pairRight t)

-- | Build a right-nested tuple as an 'OpenTerm' but without adding a final unit
-- as the right-most element
tuple' :: [OpenTerm] -> OpenTerm
tuple' [] = unit
tuple' ts = foldr1 pair ts

-- | Build a right-nested tuple type as an 'OpenTerm' but without adding a final
-- unit type as the right-most element
tupleType' :: [OpenTerm] -> OpenTerm
tupleType' [] = unitType
tupleType' ts = foldr1 pairType ts

-- | Project the @i@th element from a term of a right-nested tuple term that
-- does not have a final unit type as the right-most type. The first argument is
-- the number of types used to make the tuple type and the second is the index.
projTuple' :: Natural -> Natural -> OpenTerm -> OpenTerm
projTuple' 0 _ _ =
  panic "projTupleOpenTerm'" ["Projection of empty tuple!"]
projTuple' 1 0 tup = tup
projTuple' _ 0 tup = pairLeft tup
projTuple' len i tup =
  projTuple' (len-1) (i-1) $ pairRight tup

-- | Build a record value as an 'OpenTerm'
record :: [(FieldName, OpenTerm)] -> OpenTerm
record flds_ts =
  OpenTerm $ do let (flds,ots) = unzip flds_ts
                ts <- mapM unOpenTerm ots
                inferFlatTermF $ RecordValue $ zip flds ts

-- | Build a record type as an 'OpenTerm'
recordType :: [(FieldName, OpenTerm)] -> OpenTerm
recordType flds_ts =
  OpenTerm $ do let (flds,ots) = unzip flds_ts
                ts <- mapM unOpenTerm ots
                inferFlatTermF $ RecordType $ zip flds ts

-- | Project a field from a record
projRecord :: OpenTerm -> FieldName -> OpenTerm
projRecord (OpenTerm m) f =
  OpenTerm $ do t <- m
                inferFlatTermF $ RecordProj t f

-- | Build an 'OpenTerm' for a global name with a definition
global :: Ident -> OpenTerm
global ident =
  OpenTerm (liftTCM SC.scGlobal ident)

-- | Build an 'OpenTerm' for a named variable.
variable :: VarName -> Term -> OpenTerm
variable x t = OpenTerm (liftTCM scVariable x t)

-- | Apply an 'OpenTerm' to another.
app :: OpenTerm -> OpenTerm -> OpenTerm
app (OpenTerm f) (OpenTerm arg) =
  OpenTerm ((App <$> f <*> arg) >>= inferTermF)

-- | Apply an 'OpenTerm' to a list of zero or more arguments.
apply :: OpenTerm -> [OpenTerm] -> OpenTerm
apply = foldl app

-- | Apply a named global to a list of zero or more arguments.
applyGlobal :: Ident -> [OpenTerm] -> OpenTerm
applyGlobal ident = apply (global ident)

-- | Build a lambda abstraction as an 'OpenTerm'
lambda :: LocalName -> OpenTerm -> (OpenTerm -> OpenTerm) -> OpenTerm
lambda x (OpenTerm tpM) body_f = OpenTerm $
  do tp <- tpM
     vn <- liftTCM scFreshVarName x
     var <- inferTermF $ Variable vn tp
     body <- unOpenTerm (body_f (OpenTerm (pure var)))
     inferTermF $ Lambda vn tp body

-- | Build a nested sequence of lambda abstractions as an 'OpenTerm'
lambdas :: [(LocalName, OpenTerm)] -> ([OpenTerm] -> OpenTerm) ->
                       OpenTerm
lambdas xs_tps body_f =
  foldr (\(x,tp) rest_f xs ->
          lambda x tp (rest_f . (:xs))) (body_f . reverse) xs_tps []

-- | Build a Pi abstraction as an 'OpenTerm'
piType :: LocalName -> OpenTerm -> (OpenTerm -> OpenTerm) -> OpenTerm
piType x (OpenTerm tpM) body_f = OpenTerm $
  do tp <- tpM
     nm <- liftTCM scFreshVarName x
     var <- inferTermF $ Variable nm tp
     body <- unOpenTerm (body_f (OpenTerm (pure var)))
     inferTermF $ Pi nm tp body

-- | Build a non-dependent function type.
arrow :: OpenTerm -> OpenTerm -> OpenTerm
arrow t1 t2 =
  OpenTerm $
  do t1' <- unOpenTerm t1
     t2' <- unOpenTerm t2
     inferTermF $ Pi wildcardVarName t1' t2'

-- | Build a nested sequence of Pi abstractions as an 'OpenTerm'
piMulti :: [(LocalName, OpenTerm)] -> ([OpenTerm] -> OpenTerm) ->
                   OpenTerm
piMulti xs_tps body_f =
  foldr (\(x,tp) rest_f xs ->
          piType x tp (rest_f . (:xs))) (body_f . reverse) xs_tps []

-- | Build a let expression as an 'OpenTerm'. This is equivalent to
-- > 'apply' ('lambda' x tp body) rhs
mkLet ::
  LocalName -> OpenTerm -> OpenTerm -> (OpenTerm -> OpenTerm) -> OpenTerm
mkLet x tp rhs body_f = app (lambda x tp body_f) rhs

-- | Build a let expression as an 'OpenTerm'. This is equivalent to
-- > 'apply' ('lambda' x tp body) rhs
sawLet ::
  LocalName -> OpenTerm -> OpenTerm -> OpenTerm ->
  (OpenTerm -> OpenTerm) -> OpenTerm
sawLet x tp tp_ret rhs body_f =
  apply (global "Prelude.sawLet")
  [tp, tp_ret, rhs, lambda x tp body_f]

-- | Build a bitvector type with the given length
bitvectorType :: OpenTerm -> OpenTerm
bitvectorType w =
  applyGlobal "Prelude.Vec" [w, global "Prelude.Bool"]

-- | Build a SAW core term for a list with the given element type
list :: OpenTerm -> [OpenTerm] -> OpenTerm
list tp elems =
  foldr (\x l -> applyGlobal "Prelude.Cons" [tp, x, l])
  (applyGlobal "Prelude.Nil" [tp]) elems

-- | Build the type @Either a b@ from types @a@ and @b@
eitherType :: OpenTerm -> OpenTerm -> OpenTerm
eitherType a b = applyGlobal "Prelude.Either" [a, b]
