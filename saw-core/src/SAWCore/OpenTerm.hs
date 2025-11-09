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

To use the 'OpenTerm' API, the caller builds up 'OpenTerm's using a variety of
combinators that mirror the SAW core 'Term' structure. As some useful examples
of 'OpenTerm' operations, 'applyOpenTerm' applies one 'OpenTerm' to another,
'globalOpenTerm' builds an 'OpenTerm' for a global identifier, and
'lambdaOpenTerm' builds a lambda-abstraction. For instance, the SAW core term

> \ (f : Bool -> Bool) (x : Bool) -> f x

can be built with the 'OpenTerm' expression

> let bool = globalOpenTerm "Prelude.Bool" in
> lambdaOpenTerm "f" (arrowOpenTerm bool bool) $ \f ->
> lambdaOpenTerm "x" (globalOpenTerm "Prelude.Bool") $ \x ->
> applyOpenTerm f x

Existing SAW core 'Term's can be used in 'OpenTerm' by applying 'mkOpenTerm'.
At the top level, 'completeOpenTerm' then "completes" an 'OpenTerm'
by running its underlying 'IO' computation to build and type-check the resulting
SAW core 'Term'.
-}

module SAWCore.OpenTerm (
  -- * Open terms and converting to closed terms
  OpenTerm(..), completeOpenTerm, completeOpenTermType,
  -- * Basic operations for building open terms
  mkOpenTerm,
  openTermType,
  flatOpenTerm, sortOpenTerm, natOpenTerm,
  unitOpenTerm, unitTypeOpenTerm,
  stringLitOpenTerm, stringTypeOpenTerm,
  trueOpenTerm, falseOpenTerm, boolOpenTerm, boolTypeOpenTerm,
  arrayValueOpenTerm, vectorTypeOpenTerm, bvLitOpenTerm, bvTypeOpenTerm,
  pairOpenTerm, pairTypeOpenTerm, pairLeftOpenTerm, pairRightOpenTerm,
  tupleOpenTerm, tupleTypeOpenTerm, projTupleOpenTerm,
  tupleOpenTerm', tupleTypeOpenTerm', projTupleOpenTerm',
  recordOpenTerm, recordTypeOpenTerm, projRecordOpenTerm,
  globalOpenTerm, identOpenTerm, variableOpenTerm,
  applyOpenTerm, applyOpenTermMulti, applyGlobalOpenTerm,
  applyPiOpenTerm, piArgOpenTerm, lambdaOpenTerm, lambdaOpenTermMulti,
  piOpenTerm, piOpenTermMulti, arrowOpenTerm, letOpenTerm, sawLetOpenTerm,
  bitvectorTypeOpenTerm, listOpenTerm, eitherTypeOpenTerm,
  ) where

import qualified Data.Vector as V
import Data.Text (Text)
import Numeric.Natural

import qualified SAWSupport.Pretty as PPS (defaultOpts)

import SAWCore.Name
import SAWCore.Panic
import SAWCore.Term.Functor
import SAWCore.Term.Pretty
import SAWCore.Term.Raw
import SAWCore.SharedTerm
import qualified SAWCore.Term.Certified as SC
import SAWCore.SCTypeCheck


-- | An open term is represented as a type-checking computation that computes a
-- SAW core term and its type
newtype OpenTerm = OpenTerm { unOpenTerm :: TCM SC.Term }

-- | \"Complete\" an 'OpenTerm' to a closed term or 'fail' on type-checking
-- error
completeOpenTerm :: SharedContext -> OpenTerm -> IO Term
completeOpenTerm sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (SC.rawTerm <$> termM) sc

-- | \"Complete\" an 'OpenTerm' to a closed term for its type
completeOpenTermType :: SharedContext -> OpenTerm -> IO Term
completeOpenTermType sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (SC.rawType <$> termM) sc

-- | Embed a 'Term' into an 'OpenTerm'.
mkOpenTerm :: Term -> OpenTerm
mkOpenTerm t = OpenTerm $ typeInferComplete t

-- | Return type of an 'OpenTerm' as an 'OpenTerm'.
openTermType :: OpenTerm -> OpenTerm
openTermType (OpenTerm m) =
  OpenTerm $ do t <- m
                liftTCM SC.scTypeOf t

-- | Build an 'OpenTerm' from a 'FlatTermF'
flatOpenTerm :: FlatTermF OpenTerm -> OpenTerm
flatOpenTerm ftf = OpenTerm $
  (sequence (fmap unOpenTerm ftf) >>= typeInferComplete)

-- | Build an 'OpenTerm' for a sort
sortOpenTerm :: Sort -> OpenTerm
sortOpenTerm s = flatOpenTerm (Sort s noFlags)

-- | Build an 'OpenTerm' for a natural number literal
natOpenTerm :: Natural -> OpenTerm
natOpenTerm = flatOpenTerm . NatLit

-- | The 'OpenTerm' for the unit value
unitOpenTerm :: OpenTerm
unitOpenTerm = flatOpenTerm UnitValue

-- | The 'OpenTerm' for the unit type
unitTypeOpenTerm :: OpenTerm
unitTypeOpenTerm = flatOpenTerm UnitType

-- | Build a SAW core string literal.
stringLitOpenTerm :: Text -> OpenTerm
stringLitOpenTerm = flatOpenTerm . StringLit

-- | Return the SAW core type @String@ of strings.
stringTypeOpenTerm :: OpenTerm
stringTypeOpenTerm = globalOpenTerm "Prelude.String"

-- | The 'True' value as a SAW core term
trueOpenTerm :: OpenTerm
trueOpenTerm = globalOpenTerm "Prelude.True"

-- | The 'False' value as a SAW core term
falseOpenTerm :: OpenTerm
falseOpenTerm = globalOpenTerm "Prelude.False"

-- | Convert a 'Bool' to a SAW core term
boolOpenTerm :: Bool -> OpenTerm
boolOpenTerm True = globalOpenTerm "Prelude.True"
boolOpenTerm False = globalOpenTerm "Prelude.False"

-- | The 'Bool' type as a SAW core term
boolTypeOpenTerm :: OpenTerm
boolTypeOpenTerm = globalOpenTerm "Prelude.Bool"

-- | Build an 'OpenTerm' for an array literal
arrayValueOpenTerm :: OpenTerm -> [OpenTerm] -> OpenTerm
arrayValueOpenTerm tp elems =
  flatOpenTerm $ ArrayValue tp $ V.fromList elems

-- | Create a SAW core term for a bitvector literal
bvLitOpenTerm :: [Bool] -> OpenTerm
bvLitOpenTerm bits =
  arrayValueOpenTerm boolTypeOpenTerm $ map boolOpenTerm bits

-- | Create a SAW core term for a vector type
vectorTypeOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
vectorTypeOpenTerm n a = applyGlobalOpenTerm "Prelude.Vec" [n,a]

-- | Create a SAW core term for the type of a bitvector
bvTypeOpenTerm :: Integral a => a -> OpenTerm
bvTypeOpenTerm n =
  applyOpenTermMulti (globalOpenTerm "Prelude.Vec")
  [natOpenTerm (fromIntegral n), boolTypeOpenTerm]

-- | Build an 'OpenTerm' for a pair
pairOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
pairOpenTerm t1 t2 = flatOpenTerm $ PairValue t1 t2

-- | Build an 'OpenTerm' for a pair type
pairTypeOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
pairTypeOpenTerm t1 t2 = flatOpenTerm $ PairType t1 t2

-- | Build an 'OpenTerm' for the left projection of a pair
pairLeftOpenTerm :: OpenTerm -> OpenTerm
pairLeftOpenTerm t = flatOpenTerm $ PairLeft t

-- | Build an 'OpenTerm' for the right projection of a pair
pairRightOpenTerm :: OpenTerm -> OpenTerm
pairRightOpenTerm t = flatOpenTerm $ PairRight t

-- | Build a right-nested tuple as an 'OpenTerm'
tupleOpenTerm :: [OpenTerm] -> OpenTerm
tupleOpenTerm = foldr pairOpenTerm unitOpenTerm

-- | Build a right-nested tuple type as an 'OpenTerm'
tupleTypeOpenTerm :: [OpenTerm] -> OpenTerm
tupleTypeOpenTerm = foldr pairTypeOpenTerm unitTypeOpenTerm

-- | Project the @n@th element of a right-nested tuple type
projTupleOpenTerm :: Integer -> OpenTerm -> OpenTerm
projTupleOpenTerm 0 t = pairLeftOpenTerm t
projTupleOpenTerm i t = projTupleOpenTerm (i-1) (pairRightOpenTerm t)

-- | Build a right-nested tuple as an 'OpenTerm' but without adding a final unit
-- as the right-most element
tupleOpenTerm' :: [OpenTerm] -> OpenTerm
tupleOpenTerm' [] = unitOpenTerm
tupleOpenTerm' ts = foldr1 pairOpenTerm ts

-- | Build a right-nested tuple type as an 'OpenTerm' but without adding a final
-- unit type as the right-most element
tupleTypeOpenTerm' :: [OpenTerm] -> OpenTerm
tupleTypeOpenTerm' [] = unitTypeOpenTerm
tupleTypeOpenTerm' ts = foldr1 pairTypeOpenTerm ts

-- | Project the @i@th element from a term of a right-nested tuple term that
-- does not have a final unit type as the right-most type. The first argument is
-- the number of types used to make the tuple type and the second is the index.
projTupleOpenTerm' :: Natural -> Natural -> OpenTerm -> OpenTerm
projTupleOpenTerm' 0 _ _ =
  panic "projTupleOpenTerm'" ["Projection of empty tuple!"]
projTupleOpenTerm' 1 0 tup = tup
projTupleOpenTerm' _ 0 tup = pairLeftOpenTerm tup
projTupleOpenTerm' len i tup =
  projTupleOpenTerm' (len-1) (i-1) $ pairRightOpenTerm tup

-- | Build a record value as an 'OpenTerm'
recordOpenTerm :: [(FieldName, OpenTerm)] -> OpenTerm
recordOpenTerm flds_ts =
  OpenTerm $ do let (flds,ots) = unzip flds_ts
                ts <- mapM unOpenTerm ots
                typeInferComplete $ RecordValue $ zip flds ts

-- | Build a record type as an 'OpenTerm'
recordTypeOpenTerm :: [(FieldName, OpenTerm)] -> OpenTerm
recordTypeOpenTerm flds_ts =
  OpenTerm $ do let (flds,ots) = unzip flds_ts
                ts <- mapM unOpenTerm ots
                typeInferComplete $ RecordType $ zip flds ts

-- | Project a field from a record
projRecordOpenTerm :: OpenTerm -> FieldName -> OpenTerm
projRecordOpenTerm (OpenTerm m) f =
  OpenTerm $ do t <- m
                typeInferComplete $ RecordProj t f

-- | Build an 'OpenTerm' for a global name with a definition
globalOpenTerm :: Ident -> OpenTerm
globalOpenTerm ident =
  OpenTerm (liftTCM SC.scGlobal ident)

-- | Build an 'OpenTerm' for an 'Ident', which can either refer to a definition,
-- a constructor, or a datatype
identOpenTerm :: Ident -> OpenTerm
identOpenTerm ident =
  OpenTerm (liftTCM SC.scGlobal ident)

-- | Build an 'OpenTerm' for a named variable.
variableOpenTerm :: VarName -> Term -> OpenTerm
variableOpenTerm x t = OpenTerm (liftTCM scVariable x t >>= typeInferComplete)

-- | Apply an 'OpenTerm' to another
applyOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
applyOpenTerm (OpenTerm f) (OpenTerm arg) =
  OpenTerm ((App <$> f <*> arg) >>= typeInferComplete)

-- | Apply an 'OpenTerm' to 0 or more arguments
applyOpenTermMulti :: OpenTerm -> [OpenTerm] -> OpenTerm
applyOpenTermMulti = foldl applyOpenTerm

-- | Apply a named global to 0 or more arguments
applyGlobalOpenTerm :: Ident -> [OpenTerm] -> OpenTerm
applyGlobalOpenTerm ident = applyOpenTermMulti (globalOpenTerm ident)

-- | Compute the output type of applying a function of a given type to an
-- argument. That is, given @tp@ and @arg@, compute the type of applying any @f@
-- of type @tp@ to @arg@.
applyPiOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
applyPiOpenTerm (OpenTerm m_f) (OpenTerm m_arg) =
  OpenTerm $
  do f <- m_f
     arg <- m_arg
     ret <- applyPiTyped (NotFuncTypeInApp f arg) (SC.rawTerm f) arg
     typeInferComplete ret

-- | Get the argument type of a function type, 'fail'ing if the input term is
-- not a function type
piArgOpenTerm :: OpenTerm -> OpenTerm
piArgOpenTerm (OpenTerm m) =
  OpenTerm $ m >>= \case
  (unwrapTermF . SC.rawTerm -> Pi _ tp _) -> typeInferComplete tp
  t ->
    fail ("piArgOpenTerm: not a pi type: " ++
          scPrettyTermInCtx PPS.defaultOpts [] (SC.rawTerm t))

-- | Build a lambda abstraction as an 'OpenTerm'
lambdaOpenTerm :: LocalName -> OpenTerm -> (OpenTerm -> OpenTerm) -> OpenTerm
lambdaOpenTerm x (OpenTerm tpM) body_f = OpenTerm $
  do tp <- tpM
     vn <- liftTCM scFreshVarName x
     var <- typeInferComplete $ Variable vn tp
     body <- unOpenTerm (body_f (OpenTerm (pure var)))
     typeInferComplete $ Lambda vn tp body

-- | Build a nested sequence of lambda abstractions as an 'OpenTerm'
lambdaOpenTermMulti :: [(LocalName, OpenTerm)] -> ([OpenTerm] -> OpenTerm) ->
                       OpenTerm
lambdaOpenTermMulti xs_tps body_f =
  foldr (\(x,tp) rest_f xs ->
          lambdaOpenTerm x tp (rest_f . (:xs))) (body_f . reverse) xs_tps []

-- | Build a Pi abstraction as an 'OpenTerm'
piOpenTerm :: LocalName -> OpenTerm -> (OpenTerm -> OpenTerm) -> OpenTerm
piOpenTerm x (OpenTerm tpM) body_f = OpenTerm $
  do tp <- tpM
     nm <- liftTCM scFreshVarName x
     var <- typeInferComplete $ Variable nm tp
     body <- unOpenTerm (body_f (OpenTerm (pure var)))
     typeInferComplete $ Pi nm tp body

-- | Build a non-dependent function type.
arrowOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
arrowOpenTerm t1 t2 =
  OpenTerm $
  do t1' <- unOpenTerm t1
     t2' <- unOpenTerm t2
     typeInferComplete $ Pi wildcardVarName t1' t2'

-- | Build a nested sequence of Pi abstractions as an 'OpenTerm'
piOpenTermMulti :: [(LocalName, OpenTerm)] -> ([OpenTerm] -> OpenTerm) ->
                   OpenTerm
piOpenTermMulti xs_tps body_f =
  foldr (\(x,tp) rest_f xs ->
          piOpenTerm x tp (rest_f . (:xs))) (body_f . reverse) xs_tps []

-- | Build a let expression as an 'OpenTerm'. This is equivalent to
-- > 'applyOpenTerm' ('lambdaOpenTerm' x tp body) rhs
letOpenTerm :: LocalName -> OpenTerm -> OpenTerm -> (OpenTerm -> OpenTerm) ->
               OpenTerm
letOpenTerm x tp rhs body_f = applyOpenTerm (lambdaOpenTerm x tp body_f) rhs

-- | Build a let expression as an 'OpenTerm'. This is equivalent to
-- > 'applyOpenTerm' ('lambdaOpenTerm' x tp body) rhs
sawLetOpenTerm :: LocalName -> OpenTerm -> OpenTerm -> OpenTerm ->
                  (OpenTerm -> OpenTerm) -> OpenTerm
sawLetOpenTerm x tp tp_ret rhs body_f =
  applyOpenTermMulti (globalOpenTerm "Prelude.sawLet")
  [tp, tp_ret, rhs, lambdaOpenTerm x tp body_f]

-- | Build a bitvector type with the given length
bitvectorTypeOpenTerm :: OpenTerm -> OpenTerm
bitvectorTypeOpenTerm w =
  applyGlobalOpenTerm "Prelude.Vec" [w, globalOpenTerm "Prelude.Bool"]

-- | Build a SAW core term for a list with the given element type
listOpenTerm :: OpenTerm -> [OpenTerm] -> OpenTerm
listOpenTerm tp elems =
  foldr (\x l -> applyGlobalOpenTerm "Prelude.Cons" [tp, x, l])
  (applyGlobalOpenTerm "Prelude.Nil" [tp]) elems

-- | Build the type @Either a b@ from types @a@ and @b@
eitherTypeOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
eitherTypeOpenTerm a b = applyGlobalOpenTerm "Prelude.Either" [a, b]
