{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{- |
Module      : SAWCore.OpenTerm
Copyright   : Galois, Inc. 2018
License     : BSD3
Stability   : experimental
Portability : non-portable (language extensions)

This module defines an interface to building SAW core terms in an incrementally
type-checked way, meaning that type-checking is performed as the terms are
built. The interface provides a convenient DSL for building terms in a pure way,
where sub-terms can be freely composed and combined into super-terms without
monadic sequencing or 'IO' computations; the 'IO' computation is only run at the
top level when all the term-building is complete. Users of this interface can
also build binding constructs like lambda- and pi-abstractions without worrying
about deBruijn indices, lifting, and free variables. Instead, a key feature of
this interface is that it uses higher-order abstract syntax for lambda- and
pi-abstractions, meaning that the bodies of these term constructs are specified
as Haskell functions that take in terms for the bound variables. The library
takes care of all the deBruijn indices under the hood.

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

Existing SAW core 'Term's can be used in 'OpenTerm' by applying 'closedOpenTerm'
if the 'Term' is closed (meaning it has no free variables) or 'openOpenTerm' if
it does, where the latter requires the context of free variables to be
specified. At the top level, 'completeOpenTerm' then "completes" an 'OpenTerm'
by running its underlying 'IO' computation to build and type-check the resulting
SAW core 'Term'.
-}

module SAWCore.OpenTerm (
  -- * Open terms and converting to closed terms
  OpenTerm(..), completeOpenTerm, completeOpenTermType,
  -- * Basic operations for building open terms
  closedOpenTerm, openOpenTerm, failOpenTerm,
  bindTCMOpenTerm, bindPPOpenTerm, openTermType,
  flatOpenTerm, sortOpenTerm, natOpenTerm,
  unitOpenTerm, unitTypeOpenTerm,
  stringLitOpenTerm, stringTypeOpenTerm,
  trueOpenTerm, falseOpenTerm, boolOpenTerm, boolTypeOpenTerm,
  arrayValueOpenTerm, vectorTypeOpenTerm, bvLitOpenTerm, bvTypeOpenTerm,
  pairOpenTerm, pairTypeOpenTerm, pairLeftOpenTerm, pairRightOpenTerm,
  tupleOpenTerm, tupleTypeOpenTerm, projTupleOpenTerm,
  tupleOpenTerm', tupleTypeOpenTerm', projTupleOpenTerm',
  recordOpenTerm, recordTypeOpenTerm, projRecordOpenTerm,
  ctorOpenTerm, dataTypeOpenTerm, globalOpenTerm, identOpenTerm, variableOpenTerm,
  applyOpenTerm, applyOpenTermMulti, applyGlobalOpenTerm,
  applyPiOpenTerm, piArgOpenTerm, lambdaOpenTerm, lambdaOpenTermMulti,
  piOpenTerm, piOpenTermMulti, arrowOpenTerm, letOpenTerm, sawLetOpenTerm,
  bitvectorTypeOpenTerm, listOpenTerm, eitherTypeOpenTerm,
  -- * Types that provide similar operations to 'OpenTerm'
  OpenTermLike(..), lambdaTermLikeMulti, applyTermLikeMulti, failTermLike,
  globalTermLike, applyGlobalTermLike,
  natTermLike, unitTermLike, unitTypeTermLike,
  stringLitTermLike, stringTypeTermLike, trueTermLike, falseTermLike,
  boolTermLike, boolTypeTermLike,
  arrayValueTermLike, bvLitTermLike, vectorTypeTermLike, bvTypeTermLike,
  pairTermLike, pairTypeTermLike, pairLeftTermLike, pairRightTermLike,
  tupleTermLike, tupleTypeTermLike, projTupleTermLike,
  letTermLike, sawLetTermLike,
  ) where

import qualified Data.Vector as V
import Control.Monad.Reader
import Data.Text (Text)
import Numeric.Natural

import qualified SAWSupport.Pretty as PPS (defaultOpts, render)

import SAWCore.Name
import SAWCore.Panic
import SAWCore.Term.Functor
import SAWCore.Term.Pretty
import SAWCore.Term.Raw
import SAWCore.SharedTerm
import qualified SAWCore.Term.Certified as SC
import SAWCore.SCTypeCheck
import SAWCore.Module
  ( ctorName
  , dtName
  )


-- | An open term is represented as a type-checking computation that computes a
-- SAW core term and its type
newtype OpenTerm = OpenTerm { unOpenTerm :: TCM SC.Term }

-- | \"Complete\" an 'OpenTerm' to a closed term or 'fail' on type-checking
-- error
completeOpenTerm :: SharedContext -> OpenTerm -> IO Term
completeOpenTerm sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (SC.rawTerm <$> termM) sc mempty

-- | \"Complete\" an 'OpenTerm' to a closed term for its type
completeOpenTermType :: SharedContext -> OpenTerm -> IO Term
completeOpenTermType sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (SC.rawType <$> termM) sc mempty

-- | Embed a closed 'Term' into an 'OpenTerm'
closedOpenTerm :: Term -> OpenTerm
closedOpenTerm t = OpenTerm $ typeInferComplete t

-- | Embed a 'Term' in the given typing context into an 'OpenTerm'
openOpenTerm :: [(VarName, Term)] -> Term -> OpenTerm
openOpenTerm ctx t =
  -- Extend the local type-checking context, wherever this OpenTerm gets used,
  -- by appending ctx to the end, so that variables 0..length ctx-1 all get
  -- type-checked with ctx. If these are really the only free variables, then it
  -- won't matter what the rest of the ambient context is.
  --
  -- FIXME: we should check that the free variables of t are all < length ctx
  OpenTerm $ withCtx ctx $ typeInferComplete t

-- | Build an 'OpenTerm' that 'fail's in the underlying monad when completed
failOpenTerm :: String -> OpenTerm
failOpenTerm str = OpenTerm $ fail str

-- | Bind the result of a type-checking computation in building an 'OpenTerm'.
-- NOTE: this operation should be considered \"unsafe\" because it can create
-- malformed 'OpenTerm's if the result of the 'TCM' computation is used as part
-- of the resulting 'OpenTerm'. For instance, @a@ should not be 'OpenTerm'.
bindTCMOpenTerm :: TCM a -> (a -> OpenTerm) -> OpenTerm
bindTCMOpenTerm m f = OpenTerm (m >>= unOpenTerm . f)

-- | Bind the result of pretty-printing an 'OpenTerm' while building another
bindPPOpenTerm :: OpenTerm -> (String -> OpenTerm) -> OpenTerm
bindPPOpenTerm (OpenTerm m) f =
  OpenTerm $
  do t <- SC.rawTerm <$> m
     -- XXX: this could use scPrettyTermInCtx (which builds in the call to
     -- PPS.render) except that it's slightly different under the covers
     -- (in its use of the "global" flag, and it isn't entirely clear what
     -- that actually does)
     unOpenTerm $ f $ PPS.render PPS.defaultOpts $
       ppTermInCtx PPS.defaultOpts [] t

-- | Return type type of an 'OpenTerm' as an 'OpenTerm
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

-- | Build an 'OpenTerm' for a constructor applied to its arguments
ctorOpenTerm :: Ident -> [OpenTerm] -> OpenTerm
ctorOpenTerm c all_args = applyOpenTermMulti ctor_open_term all_args
  where
    ctor_open_term =
      OpenTerm $
      do maybe_ctor <- liftTCM scFindCtor c
         ctor <- case maybe_ctor of
                   Just ctor -> pure ctor
                   Nothing -> throwTCError $ NoSuchCtor (ModuleIdentifier c)
         typeInferComplete (Constant (ctorName ctor) :: TermF Term)

-- | Build an 'OpenTerm' for a datatype applied to its arguments
dataTypeOpenTerm :: Ident -> [OpenTerm] -> OpenTerm
dataTypeOpenTerm d all_args = applyOpenTermMulti dt_open_term all_args
  where
    dt_open_term =
      OpenTerm $
      do maybe_dt <- liftTCM scFindDataType d
         dt <- case maybe_dt of
                 Just dt -> pure dt
                 Nothing -> throwTCError $ NoSuchDataType (ModuleIdentifier d)
         typeInferComplete (Constant (dtName dt) :: TermF Term)

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
variableOpenTerm :: ExtCns Term -> OpenTerm
variableOpenTerm (EC x t) = OpenTerm (liftTCM scVariable x t >>= typeInferComplete)

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
arrowOpenTerm :: LocalName -> OpenTerm -> OpenTerm -> OpenTerm
arrowOpenTerm x tp body = piOpenTerm x tp (const body)

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
  foldr (\x l -> ctorOpenTerm "Prelude.Cons" [tp, x, l])
  (ctorOpenTerm "Prelude.Nil" [tp]) elems

-- | Build the type @Either a b@ from types @a@ and @b@
eitherTypeOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
eitherTypeOpenTerm a b = dataTypeOpenTerm "Prelude.Either" [a,b]

--------------------------------------------------------------------------------
-- Types that provide similar operations to 'OpenTerm'

class OpenTermLike t where
  -- | Convert an 'OpenTerm' to a @t@
  openTermLike :: OpenTerm -> t
  -- | Get the type of a @t@
  typeOfTermLike :: t -> t
  -- | Build a @t@ from a 'FlatTermF'
  flatTermLike :: FlatTermF t -> t
  -- | Apply a @t@ to another @t@
  applyTermLike :: t -> t -> t
  -- | Build a lambda abstraction as a @t@
  lambdaTermLike :: LocalName -> t -> (t -> t) -> t
  -- | Build a pi abstraction as a @t@
  piTermLike :: LocalName -> t -> (t -> t) -> t
  -- | Build a @t@ for a constructor applied to its arguments
  ctorTermLike :: Ident -> [t] -> t
  -- | Build a @t@ for a datatype applied to its arguments
  dataTypeTermLike :: Ident -> [t] -> t

instance OpenTermLike OpenTerm where
  openTermLike = id
  typeOfTermLike = openTermType
  flatTermLike = flatOpenTerm
  applyTermLike = applyOpenTerm
  lambdaTermLike = lambdaOpenTerm
  piTermLike = piOpenTerm
  ctorTermLike = ctorOpenTerm
  dataTypeTermLike = dataTypeOpenTerm

-- Lift an OpenTermLike instance from t to functions from some type a to t,
-- where the OpenTermLike methods pass the same input a argument to all subterms
instance OpenTermLike t => OpenTermLike (a -> t) where
  openTermLike t = const $ openTermLike t
  typeOfTermLike t = \x -> typeOfTermLike (t x)
  flatTermLike ftf = \x -> flatTermLike (fmap ($ x) ftf)
  applyTermLike f arg = \x -> applyTermLike (f x) (arg x)
  lambdaTermLike nm tp bodyF =
    \x -> lambdaTermLike nm (tp x) (\y -> bodyF (const y) x)
  piTermLike nm tp bodyF =
    \x -> piTermLike nm (tp x) (\y -> bodyF (const y) x)
  ctorTermLike c args = \x -> ctorTermLike c (map ($ x) args)
  dataTypeTermLike d args = \x -> dataTypeTermLike d (map ($ x) args)

-- This is the same as the function instance above
instance OpenTermLike t => OpenTermLike (Reader r t) where
  openTermLike t = reader $ openTermLike t
  typeOfTermLike t = reader $ typeOfTermLike $ runReader t
  flatTermLike ftf = reader $ flatTermLike $ fmap runReader ftf
  applyTermLike f arg = reader $ applyTermLike (runReader f) (runReader arg)
  lambdaTermLike x tp body =
    reader $ lambdaTermLike x (runReader tp) (runReader . body . reader)
  piTermLike x tp body =
    reader $ piTermLike x (runReader tp) (runReader . body . reader)
  ctorTermLike c args = reader $ ctorTermLike c $ map runReader args
  dataTypeTermLike d args = reader $ dataTypeTermLike d $ map runReader args

-- | Build a nested sequence of lambda abstractions
lambdaTermLikeMulti :: OpenTermLike t => [(LocalName, t)] -> ([t] -> t) -> t
lambdaTermLikeMulti xs_tps body_f =
  foldr (\(x,tp) rest_f xs ->
          lambdaTermLike x tp (rest_f . (:xs))) (body_f . reverse) xs_tps []

-- | Apply a term to 0 or more arguments
applyTermLikeMulti :: OpenTermLike t => t -> [t] -> t
applyTermLikeMulti = foldl applyTermLike

-- | Build a term that 'fail's in the underlying monad when completed
failTermLike :: OpenTermLike t => String -> t
failTermLike str = openTermLike $ failOpenTerm str

-- | Build a term for a global name with a definition
globalTermLike :: OpenTermLike t => Ident -> t
globalTermLike ident = openTermLike $ globalOpenTerm ident

-- | Apply a named global to 0 or more arguments
applyGlobalTermLike :: OpenTermLike t => Ident -> [t] -> t
applyGlobalTermLike ident = applyTermLikeMulti (globalTermLike ident)

-- | Build a term for a natural number literal
natTermLike :: OpenTermLike t => Natural -> t
natTermLike = flatTermLike . NatLit

-- | The term for the unit value
unitTermLike :: OpenTermLike t => t
unitTermLike = flatTermLike UnitValue

-- | The term for the unit type
unitTypeTermLike :: OpenTermLike t => t
unitTypeTermLike = flatTermLike UnitType

-- | Build a SAW core string literal.
stringLitTermLike :: OpenTermLike t => Text -> t
stringLitTermLike = flatTermLike . StringLit

-- | Return the SAW core type @String@ of strings.
stringTypeTermLike :: OpenTermLike t => t
stringTypeTermLike = globalTermLike "Prelude.String"

-- | The 'True' value as a SAW core term
trueTermLike :: OpenTermLike t => t
trueTermLike = globalTermLike "Prelude.True"

-- | The 'False' value as a SAW core term
falseTermLike :: OpenTermLike t => t
falseTermLike = globalTermLike "Prelude.False"

-- | Convert a 'Bool' to a SAW core term
boolTermLike :: OpenTermLike t => Bool -> t
boolTermLike True = globalTermLike "Prelude.True"
boolTermLike False = globalTermLike "Prelude.False"

-- | The 'Bool' type as a SAW core term
boolTypeTermLike :: OpenTermLike t => t
boolTypeTermLike = globalTermLike "Prelude.Bool"

-- | Build an term for an array literal
arrayValueTermLike :: OpenTermLike t => t -> [t] -> t
arrayValueTermLike tp elems =
  flatTermLike $ ArrayValue tp $ V.fromList elems

-- | Create a SAW core term for a bitvector literal
bvLitTermLike :: OpenTermLike t => [Bool] -> t
bvLitTermLike bits =
  arrayValueTermLike boolTypeTermLike $ map boolTermLike bits

-- | Create a SAW core term for a vector type
vectorTypeTermLike :: OpenTermLike t => t -> t -> t
vectorTypeTermLike n a = applyGlobalTermLike "Prelude.Vec" [n,a]

-- | Create a SAW core term for the type of a bitvector
bvTypeTermLike :: OpenTermLike t => Integral n => n -> t
bvTypeTermLike n =
  applyTermLikeMulti (globalTermLike "Prelude.Vec")
  [natTermLike (fromIntegral n), boolTypeTermLike]

-- | Build a term for a pair
pairTermLike :: OpenTermLike t => t -> t -> t
pairTermLike t1 t2 = flatTermLike $ PairValue t1 t2

-- | Build a term for a pair type
pairTypeTermLike :: OpenTermLike t => t -> t -> t
pairTypeTermLike t1 t2 = flatTermLike $ PairType t1 t2

-- | Build a term for the left projection of a pair
pairLeftTermLike :: OpenTermLike t => t -> t
pairLeftTermLike t = flatTermLike $ PairLeft t

-- | Build a term for the right projection of a pair
pairRightTermLike :: OpenTermLike t => t -> t
pairRightTermLike t = flatTermLike $ PairRight t

-- | Build a right-nested tuple as a term
tupleTermLike :: OpenTermLike t => [t] -> t
tupleTermLike = foldr pairTermLike unitTermLike

-- | Build a right-nested tuple type as a term
tupleTypeTermLike :: OpenTermLike t => [t] -> t
tupleTypeTermLike = foldr pairTypeTermLike unitTypeTermLike

-- | Project the @n@th element of a right-nested tuple type
projTupleTermLike :: OpenTermLike t => Integer -> t -> t
projTupleTermLike 0 t = pairLeftTermLike t
projTupleTermLike i t = projTupleTermLike (i-1) (pairRightTermLike t)

-- | Build a let expression as a term. This is equivalent to
-- > 'applyTermLike' ('lambdaTermLike' x tp body) rhs
letTermLike :: OpenTermLike t => LocalName -> t -> t -> (t -> t) -> t
letTermLike x tp rhs body_f = applyTermLike (lambdaTermLike x tp body_f) rhs

-- | Build a let expression as a term using the @sawLet@ combinator. This
-- is equivalent to the term @sawLet tp tp_ret rhs (\ (x : tp) -> body_f)@
sawLetTermLike :: OpenTermLike t => LocalName -> t -> t -> t -> (t -> t) -> t
sawLetTermLike x tp tp_ret rhs body_f =
  applyTermLikeMulti (globalTermLike "Prelude.sawLet")
  [tp, tp_ret, rhs, lambdaTermLike x tp body_f]
