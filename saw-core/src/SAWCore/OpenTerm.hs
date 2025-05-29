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
  OpenTerm(..), completeOpenTerm, completeNormOpenTerm, completeOpenTermType,
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
  ctorOpenTerm, dataTypeOpenTerm, globalOpenTerm, identOpenTerm, extCnsOpenTerm,
  applyOpenTerm, applyOpenTermMulti, applyGlobalOpenTerm,
  applyPiOpenTerm, piArgOpenTerm, lambdaOpenTerm, lambdaOpenTermMulti,
  piOpenTerm, piOpenTermMulti, arrowOpenTerm, letOpenTerm, sawLetOpenTerm,
  bitvectorTypeOpenTerm, bvVecTypeOpenTerm, listOpenTerm, list1OpenTerm,
  eitherTypeOpenTerm, sigmaTypeOpenTerm, sigmaTypeOpenTermMulti, sigmaOpenTerm,
  sigmaOpenTermMulti, sigmaElimOpenTermMulti,
  -- * Operations for building @SpecM@ computations
  EventType (..), defaultSpecMEventType, unitKindDesc, bvExprKind,
  tpDescTypeOpenTerm, kindToTpDesc, unitTpDesc,
  boolExprKind, boolKindDesc, boolTpDesc, natExprKind, natKindDesc,
  numExprKind, numKindDesc, bvKindDesc, bvTpDesc, tpKindDesc,
  pairTpDesc, tupleTpDesc, sumTpDesc, bvVecTpDesc,
  constTpExpr, bvConstTpExpr, binOpTpExpr, bvSumTpExprs,
  bvMulTpExpr, sigmaTpDesc, sigmaTpDescMulti, seqTpDesc, arrowTpDesc,
  arrowTpDescMulti, mTpDesc, funTpDesc, piTpDesc, piTpDescMulti, voidTpDesc,
  varTpDesc, varTpExpr, varKindExpr, constKindExpr, indTpDesc,
  substTpDesc, substTpDescMulti, substIdTpDescMulti, substIndIdTpDescMulti,
  tpElemTypeOpenTerm,
  substEnvTpDesc, tpEnvOpenTerm, specMTypeOpenTerm, retSOpenTerm,
  bindSOpenTerm, errorSOpenTerm, letRecSOpenTerm, multiFixBodiesOpenTerm,
  -- * Monadic operations for building terms including 'IO' actions
  OpenTermM(..), completeOpenTermM,
  dedupOpenTermM, lambdaOpenTermM, piOpenTermM,
  lambdaOpenTermAuxM, piOpenTermAuxM,
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
  -- * Other exported helper functions
  sawLetMinimize
  ) where

import qualified Data.Vector as V
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import qualified Data.Text as Text
import Data.Text (Text)
import Numeric.Natural

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import qualified SAWSupport.Pretty as PPS (defaultOpts, render)

import SAWCore.Panic
import SAWCore.Term.Functor
import SAWCore.Term.Pretty
import SAWCore.SharedTerm
import SAWCore.SCTypeCheck
import SAWCore.Module
  ( ctorNumParams
  , ctorPrimName
  , dtNumParams
  , dtPrimName
  , Ctor(..)
  , DataType(..)
  )
import SAWCore.Recognizer


-- | An open term is represented as a type-checking computation that computes a
-- SAW core term and its type
newtype OpenTerm = OpenTerm { unOpenTerm :: TCM SCTypedTerm }

-- | \"Complete\" an 'OpenTerm' to a closed term or 'fail' on type-checking
-- error
completeOpenTerm :: SharedContext -> OpenTerm -> IO Term
completeOpenTerm sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (typedVal <$> termM) sc Nothing []

-- | \"Complete\" an 'OpenTerm' to a closed term and 'betaNormalize' the result
completeNormOpenTerm :: SharedContext -> OpenTerm -> IO Term
completeNormOpenTerm sc m =
  completeOpenTerm sc m >>= sawLetMinimize sc >>= betaNormalize sc

-- | \"Complete\" an 'OpenTerm' to a closed term for its type
completeOpenTermType :: SharedContext -> OpenTerm -> IO Term
completeOpenTermType sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (typedType <$> termM) sc Nothing []

-- | Embed a closed 'Term' into an 'OpenTerm'
closedOpenTerm :: Term -> OpenTerm
closedOpenTerm t = OpenTerm $ typeInferComplete t

-- | Embed a 'Term' in the given typing context into an 'OpenTerm'
openOpenTerm :: [(LocalName, Term)] -> Term -> OpenTerm
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
  do ctx <- askCtx
     t <- typedVal <$> m
     -- XXX: this could use scPrettyTermInCtx (which builds in the call to
     -- PPS.render) except that it's slightly different under the covers
     -- (in its use of the "global" flag, and it isn't entirely clear what
     -- that actually does)
     unOpenTerm $ f $ PPS.render PPS.defaultOpts $
       ppTermInCtx PPS.defaultOpts (map fst ctx) t

-- | Return type type of an 'OpenTerm' as an 'OpenTerm
openTermType :: OpenTerm -> OpenTerm
openTermType (OpenTerm m) =
  OpenTerm $ do SCTypedTerm _ tp <- m
                ctx <- askCtx
                tp_tp <- liftTCM scTypeOf' (map snd ctx) tp
                return (SCTypedTerm tp tp_tp)

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
ctorOpenTerm c all_args = OpenTerm $ do
  maybe_ctor <- liftTCM scFindCtor c
  ctor <- case maybe_ctor of
            Just ctor -> pure ctor
            Nothing -> throwTCError $ NoSuchCtor c
  (params, args) <- splitAt (ctorNumParams ctor) <$> mapM unOpenTerm all_args
  c' <- traverse typeInferComplete (ctorPrimName ctor)
  typeInferComplete $ CtorApp c' params args

-- | Build an 'OpenTerm' for a datatype applied to its arguments
dataTypeOpenTerm :: Ident -> [OpenTerm] -> OpenTerm
dataTypeOpenTerm d all_args = OpenTerm $ do
  maybe_dt <- liftTCM scFindDataType d
  dt <- case maybe_dt of
          Just dt -> pure dt
          Nothing -> throwTCError $ NoSuchDataType d
  (params, args) <- splitAt (dtNumParams dt) <$> mapM unOpenTerm all_args
  d' <- traverse typeInferComplete (dtPrimName dt)
  typeInferComplete $ DataTypeApp d' params args

-- | Build an 'OpenTerm' for a global name with a definition
globalOpenTerm :: Ident -> OpenTerm
globalOpenTerm ident =
  OpenTerm (do trm <- liftTCM scGlobalDef ident
               tp <- liftTCM scTypeOfGlobal ident
               return $ SCTypedTerm trm tp)

-- | Build an 'OpenTerm' for an 'Ident', which can either refer to a definition,
-- a constructor, or a datatype
identOpenTerm :: Ident -> OpenTerm
identOpenTerm ident =
  OpenTerm $
  do maybe_ctor <- liftTCM scFindCtor ident
     maybe_dt <- liftTCM scFindDataType ident

     -- First, determine the variables we need to abstract over and the function
     -- for building an application of this identifier dependent on the class of
     -- identifier
     let (var_ctx, app_fun) =
           case (maybe_ctor, maybe_dt) of
             (Just ctor, _) -> (fst (asPiList (ctorType ctor)), scCtorApp)
             (_, Just dt) -> (dtParams dt ++ dtIndices dt, scDataTypeApp)
             (Nothing, Nothing) -> ([], scGlobalApply)

     -- Build the term \ (x1:tp1) ... (xn:tpn) -> ident x1 ... xn as follows:
     -- 1. Construct vars as the list x1 ... xn of terms, noting that xn has
     --    deBruijn index 0 and x1 has deBruijn index (length var_ctx) - 1;
     -- 2. Apply ident to those variables; and
     -- 3. Lambda-abstract the variables.
     vars <- reverse <$> mapM (liftTCM scLocalVar) [0 .. (length var_ctx) - 1]
     ident_app <- liftTCM app_fun ident vars
     lam <- liftTCM scLambdaList var_ctx ident_app
     typeInferComplete lam

-- | Build an 'OpenTerm' for an external constant
extCnsOpenTerm :: ExtCns Term -> OpenTerm
extCnsOpenTerm ec = OpenTerm (liftTCM scExtCns ec >>= typeInferComplete)

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
     ret <- applyPiTyped (NotFuncTypeInApp f arg) (typedVal f) arg
     ctx <- askCtx
     ret_tp <- liftTCM scTypeOf' (map snd ctx) ret
     return (SCTypedTerm ret ret_tp)

-- | Get the argument type of a function type, 'fail'ing if the input term is
-- not a function type
piArgOpenTerm :: OpenTerm -> OpenTerm
piArgOpenTerm (OpenTerm m) =
  OpenTerm $ m >>= \case
  (unwrapTermF . typedVal -> Pi _ tp _) -> typeInferComplete tp
  t ->
    do ctx <- askCtx
       fail ("piArgOpenTerm: not a pi type: " ++
             scPrettyTermInCtx PPS.defaultOpts (map fst ctx) (typedVal t))

-- | Build an 'OpenTerm' for the top variable in the current context, by
-- building the 'TCM' computation which checks how much longer the context has
-- gotten since the variable was created and uses this to compute its deBruijn
-- index
openTermTopVar :: TCM OpenTerm
openTermTopVar =
  do outer_ctx <- askCtx
     return $ OpenTerm $ do
       inner_ctx <- askCtx
       typeInferComplete (LocalVar (length inner_ctx
                                    - length outer_ctx) :: TermF Term)

-- | Build an open term inside a binder of a variable with the given name and
-- type, where the binder is represented as a Haskell function on 'OpenTerm's
bindOpenTerm :: LocalName -> SCTypedTerm -> (OpenTerm -> OpenTerm) ->
                TCM SCTypedTerm
bindOpenTerm x tp body_f =
  do tp_whnf <- typeCheckWHNF $ typedVal tp
     withVar x tp_whnf (openTermTopVar >>= (unOpenTerm . body_f))

-- | Build a lambda abstraction as an 'OpenTerm'
lambdaOpenTerm :: LocalName -> OpenTerm -> (OpenTerm -> OpenTerm) -> OpenTerm
lambdaOpenTerm x (OpenTerm tpM) body_f = OpenTerm $
  do tp <- tpM
     body <- bindOpenTerm x tp body_f
     typeInferComplete $ Lambda x tp body

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
     body <- bindOpenTerm x tp body_f
     typeInferComplete $ Pi x tp body

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

-- | Build the SAW core type @BVVec n len d@
bvVecTypeOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm
bvVecTypeOpenTerm w_term len_term elem_tp =
  applyGlobalOpenTerm "Prelude.BVVec" [w_term, len_term, elem_tp]

-- | Build a SAW core term for a list with the given element type
listOpenTerm :: OpenTerm -> [OpenTerm] -> OpenTerm
listOpenTerm tp elems =
  foldr (\x l -> ctorOpenTerm "Prelude.Cons" [tp, x, l])
  (ctorOpenTerm "Prelude.Nil" [tp]) elems

-- | Build an 'OpenTerm' of type @List1 tp@ from 'OpenTerm's of type @tp@
list1OpenTerm :: OpenTerm -> [OpenTerm] -> OpenTerm
list1OpenTerm tp xs =
  foldr (\hd tl -> ctorOpenTerm "Prelude.Cons1" [tp, hd, tl])
  (ctorOpenTerm "Prelude.Nil1" [tp])
  xs

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
sigmaOpenTermMulti _ tps _ trms _ =
  panic "sigmaOpenTermMulti" [
     "The number of types and arguments disagree:",
     Text.pack (show $ length tps) <> " Remaining types",
     Text.pack (show $ length trms) <> " remaining terms",
     "(sorry, the values themselves are unresolved monadic computations)"
  ]

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


--------------------------------------------------------------------------------
-- Operations for building SpecM computations

-- | A SAW core term that indicates an event type for the @SpecM@ monad
newtype EventType = EventType { evTypeTerm :: OpenTerm }

-- | The default event type uses the @Void@ type for events
defaultSpecMEventType :: EventType
defaultSpecMEventType = EventType $ globalOpenTerm "SpecM.VoidEv"

-- | The kind description for the unit type
unitKindDesc :: OpenTerm
unitKindDesc = ctorOpenTerm "SpecM.Kind_Expr" [ctorOpenTerm
                                               "SpecM.Kind_unit" []]

-- | The @ExprKind@ for the bitvector type with width @w@
bvExprKind :: Natural -> OpenTerm
bvExprKind w = ctorOpenTerm "SpecM.Kind_bv" [natOpenTerm w]

-- | The type @TpDesc@ of type descriptions
tpDescTypeOpenTerm :: OpenTerm
tpDescTypeOpenTerm = dataTypeOpenTerm "SpecM.TpDesc" []

-- | Convert a kind description to a type description with the @Tp_Kind@
-- constructor
kindToTpDesc :: OpenTerm -> OpenTerm
kindToTpDesc d = ctorOpenTerm "SpecM.Tp_Kind" [d]

-- | The type description for the unit type
unitTpDesc :: OpenTerm
unitTpDesc = ctorOpenTerm "SpecM.Tp_Kind" [unitKindDesc]

-- | The expression kind for the Boolean type
boolExprKind :: OpenTerm
boolExprKind = ctorOpenTerm "SpecM.Kind_bool" []

-- | The kind description for the Boolean type
boolKindDesc :: OpenTerm
boolKindDesc = ctorOpenTerm "SpecM.Kind_Expr" [boolExprKind]

-- | The type description for the Boolean type
boolTpDesc :: OpenTerm
boolTpDesc = ctorOpenTerm "SpecM.Tp_Kind" [boolKindDesc]

-- | The expression kind for the @Nat@ type
natExprKind :: OpenTerm
natExprKind = ctorOpenTerm "SpecM.Kind_nat" []

-- | The expression kind for the @Num@ type
numExprKind :: OpenTerm
numExprKind = ctorOpenTerm "SpecM.Kind_num" []

-- | The kind description for the @Nat@ type
natKindDesc :: OpenTerm
natKindDesc = ctorOpenTerm "SpecM.Kind_Expr" [natExprKind]

-- | The kind description for the @Num@ type
numKindDesc :: OpenTerm
numKindDesc = ctorOpenTerm "SpecM.Kind_Expr" [numExprKind]

-- | The kind description for the type @bitvector w@
bvKindDesc :: Natural -> OpenTerm
bvKindDesc w = ctorOpenTerm "SpecM.Kind_Expr" [bvExprKind w]

-- | The type description for thhe type @bitvector w@
bvTpDesc :: Natural -> OpenTerm
bvTpDesc w = applyGlobalOpenTerm "SpecM.Tp_bitvector" [natOpenTerm w]

-- | The kind description for the type of type descriptions
tpKindDesc :: OpenTerm
tpKindDesc = ctorOpenTerm "SpecM.Kind_Tp" []

-- | Build a pair type description from two type descriptions
pairTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
pairTpDesc d1 d2 = ctorOpenTerm "SpecM.Tp_Pair" [d1,d2]

-- | Build a tuple type description from a list of type descriptions
tupleTpDesc :: [OpenTerm] -> OpenTerm
tupleTpDesc [] = unitTpDesc
tupleTpDesc [d] = d
tupleTpDesc (d : ds) = pairTpDesc d (tupleTpDesc ds)

-- | Build a sum type description from two type descriptions
sumTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
sumTpDesc d1 d2 = ctorOpenTerm "SpecM.Tp_Sum" [d1,d2]

-- | Build a type description for the type @BVVec n len d@ from a SAW core term
-- @n@ of type @Nat@, a type expression @len@ for the length, and a type
-- description @d@ for the element type
bvVecTpDesc :: OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm
bvVecTpDesc w_term len_term elem_d =
  applyGlobalOpenTerm "SpecM.Tp_BVVec" [w_term, len_term, elem_d]

-- | Build a type expression of type @TpExpr EK@ of kind description @EK@ from a
-- type-level value of type @exprKindElem EK@
constTpExpr :: OpenTerm -> OpenTerm -> OpenTerm
constTpExpr k_d v = ctorOpenTerm "SpecM.TpExpr_Const" [k_d, v]

-- | Build a type description expression from a bitvector value of a given width
bvConstTpExpr :: Natural -> OpenTerm -> OpenTerm
bvConstTpExpr w bv = constTpExpr (bvExprKind w) bv

-- | Build a type expression from a binary operation, the given input kinds and
-- output kind, and the given expression arguments
binOpTpExpr :: OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm ->
               OpenTerm -> OpenTerm -> OpenTerm
binOpTpExpr op k1 k2 k3 e1 e2 =
  ctorOpenTerm "SpecM.TpExpr_BinOp" [k1, k2, k3, op, e1, e2]

-- | Build a type expression for the bitvector sum of a list of type
-- expressions, all of the given width
bvSumTpExprs :: Natural -> [OpenTerm] -> OpenTerm
bvSumTpExprs w [] = bvConstTpExpr w (natOpenTerm 0)
bvSumTpExprs _ [bv] = bv
bvSumTpExprs w (bv:bvs) =
  ctorOpenTerm "SpecM.TpExpr_BinOp"
  [bvExprKind w, bvExprKind w, bvExprKind w,
   ctorOpenTerm "SpecM.BinOp_AddBV" [natOpenTerm w], bv, bvSumTpExprs w bvs]

-- | Build a type expression for the bitvector product of two type expressions
bvMulTpExpr :: Natural -> OpenTerm -> OpenTerm -> OpenTerm
bvMulTpExpr w bv1 bv2 =
  ctorOpenTerm "SpecM.TpExpr_BinOp"
  [bvExprKind w, bvExprKind w, bvExprKind w,
   ctorOpenTerm "SpecM.BinOp_MulBV" [natOpenTerm w], bv1, bv2]

-- | Build a type description for a sigma type from a kind description for the
-- first element and a type description with an additional free variable for the
-- second
sigmaTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
sigmaTpDesc k d = ctorOpenTerm "SpecM.Tp_Sigma" [k,d]

-- | Build a type description for 0 or more nested sigma types over a list of
-- kind descriptions
sigmaTpDescMulti :: [OpenTerm] -> OpenTerm -> OpenTerm
sigmaTpDescMulti [] d = d
sigmaTpDescMulti (k:ks) d = sigmaTpDesc k $ sigmaTpDescMulti ks d

-- | Build a type description for a sequence
seqTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
seqTpDesc n d = ctorOpenTerm "SpecM.Tp_Seq" [n, d]

-- | Build an arrow type description for left- and right-hand type descriptions
arrowTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
arrowTpDesc d_in d_out = ctorOpenTerm "SpecM.Tp_Arr" [d_in, d_out]

-- | Build a multi-arity nested arrow type description
arrowTpDescMulti :: [OpenTerm] -> OpenTerm -> OpenTerm
arrowTpDescMulti ds_in d_out = foldr arrowTpDesc d_out ds_in

-- | Build a monadic type description, i.e., a nullary monadic function
mTpDesc :: OpenTerm -> OpenTerm
mTpDesc d = ctorOpenTerm "SpecM.Tp_M" [d]

-- | Build the type description @Tp_Arr d1 (... (Tp_Arr dn (Tp_M d_ret)))@ for a
-- monadic function that takes in the types described by @d1@ through @dn@ and
-- returns the type described by @d_ret@
funTpDesc :: [OpenTerm] -> OpenTerm -> OpenTerm
funTpDesc ds_in d_ret = arrowTpDescMulti ds_in (mTpDesc d_ret)

-- | Build the type description for a pi-abstraction over a kind description
piTpDesc :: OpenTerm -> OpenTerm -> OpenTerm
piTpDesc kd tpd = ctorOpenTerm "SpecM.Tp_Pi" [kd, tpd]

-- | Build the type description for a multi-arity pi-abstraction over a sequence
-- of kind descriptions, i.e., SAW core terms of type @KindDesc@
piTpDescMulti :: [OpenTerm] -> OpenTerm -> OpenTerm
piTpDescMulti ks tp = foldr piTpDesc tp ks

-- | The type description for the @Void@ type
voidTpDesc :: OpenTerm
voidTpDesc = ctorOpenTerm "SpecM.Tp_Void" []

-- | Build a type description for a free deBruijn index
varTpDesc :: Natural -> OpenTerm
varTpDesc ix = ctorOpenTerm "SpecM.Tp_Var" [natOpenTerm ix]

-- | Build a type-level expression with a given @ExprKind@ for a free variable
varTpExpr :: OpenTerm -> Natural -> OpenTerm
varTpExpr ek ix = ctorOpenTerm "SpecM.TpExpr_Var" [ek, natOpenTerm ix]

-- | Build a kind expression of a given kind from a deBruijn index
varKindExpr :: OpenTerm -> Natural -> OpenTerm
varKindExpr d ix = applyGlobalOpenTerm "SpecM.varKindExpr" [d,natOpenTerm ix]

-- | Build a kind expression of a given kind from an element of that kind
constKindExpr :: OpenTerm -> OpenTerm -> OpenTerm
constKindExpr d e = applyGlobalOpenTerm "SpecM.constKindExpr" [d,e]

-- | Build the type description @Tp_Ind T@ that represents a recursively-defined
-- inductive type that unfolds to @[Tp_Ind T/x]T@
indTpDesc :: OpenTerm -> OpenTerm
indTpDesc d = ctorOpenTerm "SpecM.Tp_Ind" [d]

-- | Build the type description @Tp_Subst T K e@ that represents an explicit
-- substitution of expression @e@ of kind @K@ into type description @T@
substTpDesc :: OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm
substTpDesc d k_d e = applyGlobalOpenTerm "SpecM.Tp_Subst" [d,k_d,e]

-- | Build the type description that performs 0 or more explicit substitutions
substTpDescMulti :: OpenTerm -> [OpenTerm] -> [OpenTerm] -> OpenTerm
substTpDescMulti d [] [] = d
substTpDescMulti d (k_d:k_ds) (e:es) =
  substTpDescMulti (substTpDesc d k_d e) k_ds es
substTpDescMulti _ ks es =
  panic "substTpDescMulti" [
      "Mismatched number of kinds versus expressions",
      Text.pack (show $ length ks) <> " remaining kinds",
      Text.pack (show $ length es) <> " remaining exprs",
      "(sorry, the terms themselves are unresolved monadic computations)"
  ]

-- | Build the type description that performs 0 or more explicit substitutions
-- into a type description given by an identifier
substIdTpDescMulti :: Ident -> [OpenTerm] -> [OpenTerm] -> OpenTerm
substIdTpDescMulti i = substTpDescMulti (globalOpenTerm i)

-- | Build the type description that performs 0 or more explicit substitutions
-- into an inductive type description @Tp_Ind T@ where the body @T@ is given by
-- an identifier
substIndIdTpDescMulti :: Ident -> [OpenTerm] -> [OpenTerm] -> OpenTerm
substIndIdTpDescMulti i = substTpDescMulti (indTpDesc (globalOpenTerm i))

-- | Map from type description @T@ to the type @T@ describes
tpElemTypeOpenTerm :: EventType -> OpenTerm -> OpenTerm
tpElemTypeOpenTerm ev d =
  applyGlobalOpenTerm "SpecM.tpElem" [evTypeTerm ev, d]

-- | Apply the @tpSubst@ combinator to substitute a type-level environment
-- (built by applying 'tpEnvOpenTerm' to the supplied list) at the supplied
-- natural number lifting level to a type description
substEnvTpDesc :: Natural -> [(OpenTerm,OpenTerm)] -> OpenTerm -> OpenTerm
substEnvTpDesc n ks_elems d =
  applyGlobalOpenTerm "SpecM.tpSubst" [natOpenTerm n,
                                       tpEnvOpenTerm ks_elems, d]

-- | Build a SAW core term for a type-level environment, i.e., a term of type
-- @TpEnv@, from a list of kind descriptions and elements of those kind
-- descriptions
tpEnvOpenTerm :: [(OpenTerm,OpenTerm)] -> OpenTerm
tpEnvOpenTerm =
  foldr (\(k,v) env -> applyGlobalOpenTerm "SpecM.envConsElem" [k,v,env])
  (ctorOpenTerm "Prelude.Nil" [globalOpenTerm "SpecM.TpEnvElem"])

-- | Build the computation type @SpecM E A@
specMTypeOpenTerm :: EventType -> OpenTerm -> OpenTerm
specMTypeOpenTerm ev tp =
  applyGlobalOpenTerm "SpecM.SpecM" [evTypeTerm ev, tp]

-- | Build a @SpecM@ computation that returns a value
retSOpenTerm :: EventType -> OpenTerm -> OpenTerm -> OpenTerm
retSOpenTerm ev tp x =
  applyGlobalOpenTerm "SpecM.retS" [evTypeTerm ev, tp, x]

-- | Build a @SpecM@ computation using a bind
bindSOpenTerm :: EventType -> OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm ->
                 OpenTerm
bindSOpenTerm ev a b m f =
  applyGlobalOpenTerm "SpecM.bindS" [evTypeTerm ev, a, b, m, f]

-- | Build a @SpecM@ error computation with the given error message
errorSOpenTerm :: EventType -> OpenTerm -> String -> OpenTerm
errorSOpenTerm ev ret_tp msg =
  applyGlobalOpenTerm "SpecM.errorS"
  [evTypeTerm ev, ret_tp, stringLitOpenTerm (Text.pack msg)]

-- | Build a @SpecM@ computation that uses @LetRecS@ to bind multiple
-- corecursive functions in a body computation
letRecSOpenTerm :: EventType -> [OpenTerm] -> OpenTerm -> OpenTerm ->
                   OpenTerm -> OpenTerm
letRecSOpenTerm ev ds ret_tp bodies body =
  applyGlobalOpenTerm "SpecM.LetRecS"
  [evTypeTerm ev, listOpenTerm tpDescTypeOpenTerm ds, ret_tp, bodies, body]

-- | Build the type @MultiFixBodies E Ts@ from an event type and a list of type
-- descriptions for @Ts@
multiFixBodiesOpenTerm :: EventType -> [OpenTerm] -> OpenTerm
multiFixBodiesOpenTerm ev ds =
  applyGlobalOpenTerm "SpecM.MultiFixBodies"
  [evTypeTerm ev, listOpenTerm tpDescTypeOpenTerm ds]


--------------------------------------------------------------------------------
-- Monadic operations for building terms including 'IO' actions

-- | The monad for building 'OpenTerm's if you want to add in 'IO' actions. This
-- is just the type-checking monad, but we give it a new name to keep this
-- module self-contained.
newtype OpenTermM a = OpenTermM { unOpenTermM :: TCM a }
                    deriving (Functor, Applicative, Monad)

instance MonadIO OpenTermM where
  liftIO = OpenTermM . liftIO

-- | \"Run\" an 'OpenTermM' computation to produce an 'OpenTerm'
runOpenTermM :: OpenTermM OpenTerm -> OpenTerm
runOpenTermM (OpenTermM m) =
  OpenTerm $ join $ fmap unOpenTerm m

-- | \"Complete\" an 'OpenTerm' build in 'OpenTermM' to a closed term, or 'fail'
-- on a type-checking error
completeOpenTermM :: SharedContext -> OpenTermM OpenTerm -> IO Term
completeOpenTermM sc m = completeOpenTerm sc (runOpenTermM m)

-- | \"De-duplicate\" an open term, so that duplicating the returned 'OpenTerm'
-- does not lead to duplicated WHNF work
dedupOpenTermM :: OpenTerm -> OpenTermM OpenTerm
dedupOpenTermM (OpenTerm trmM) =
  OpenTermM $ do trm <- trmM
                 return $ OpenTerm $ return trm

-- | Build an open term inside a binder of a variable with the given name and
-- type, where the binder is represented as a monadic Haskell function on
-- 'OpenTerm's that also returns an auxiliary value. Returns the normalized type
-- and the body, along with the auxiliary result returned by the body-generating
-- function.
bindOpenTermAuxM ::
  LocalName -> OpenTerm ->
  (OpenTerm -> OpenTermM (OpenTerm, a)) ->
  OpenTermM (SCTypedTerm, SCTypedTerm, a)
bindOpenTermAuxM x (OpenTerm tpM) body_f =
  OpenTermM $
  do SCTypedTerm tp tp_tp <- tpM
     tp_whnf <- typeCheckWHNF tp
     (OpenTerm bodyM, a) <-
       withVar x tp_whnf (openTermTopVar >>= (unOpenTermM . body_f))
     body <- bodyM
     return (SCTypedTerm tp_whnf tp_tp, body, a)

-- | Build a lambda abstraction in the 'OpenTermM' monad
lambdaOpenTermM ::
  LocalName -> OpenTerm -> (OpenTerm -> OpenTermM OpenTerm) ->
  OpenTermM OpenTerm
lambdaOpenTermM x tp body_f =
  fst <$> lambdaOpenTermAuxM x tp (body_f >=> (\t -> return (t, ())))

-- | Build a pi abstraction in the 'OpenTermM' monad
piOpenTermM ::
  LocalName -> OpenTerm -> (OpenTerm -> OpenTermM OpenTerm) ->
  OpenTermM OpenTerm
piOpenTermM x tp body_f =
  fst <$> piOpenTermAuxM x tp (body_f >=> (\t -> return (t, ())))

-- | Build a lambda abstraction with an auxiliary return value in the
-- 'OpenTermM' monad
lambdaOpenTermAuxM ::
  LocalName -> OpenTerm ->
  (OpenTerm -> OpenTermM (OpenTerm, a)) ->
  OpenTermM (OpenTerm, a)
lambdaOpenTermAuxM x tp body_f =
  do (tp', body, a) <- bindOpenTermAuxM x tp body_f
     return (OpenTerm (typeInferComplete $ Lambda x tp' body), a)

-- | Build a pi abstraction with an auxiliary return value in the 'OpenTermM'
-- monad
piOpenTermAuxM ::
  LocalName -> OpenTerm -> (OpenTerm -> OpenTermM (OpenTerm, a)) ->
  OpenTermM (OpenTerm, a)
piOpenTermAuxM x tp body_f =
  do (tp', body, a) <- bindOpenTermAuxM x tp body_f
     return (OpenTerm (typeInferComplete $ Pi x tp' body), a)


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


--------------------------------------------------------------------------------
-- sawLet-minimization

-- | A map from each deBruijn index to a count of its occurrences in a term
newtype VarOccs = VarOccs [Integer]

-- | Make a 'VarOccs' with a single occurrence of a deBruijn index
varOccs1 :: DeBruijnIndex -> VarOccs
varOccs1 i = VarOccs (take i (repeat 0) ++ [1])

-- | Move a 'VarOccs' out of a binder by returning the number of occurrences of
-- deBruijn index 0 along with the result of subtracting 1 from all other indices
unconsVarOccs :: VarOccs -> (Integer, VarOccs)
unconsVarOccs (VarOccs []) = (0, VarOccs [])
unconsVarOccs (VarOccs (cnt:occs)) = (cnt, VarOccs occs)

-- | Multiply every index in a 'VarOccs' by a constant
multVarOccs :: Integer -> VarOccs -> VarOccs
multVarOccs i (VarOccs occs) = VarOccs $ map (* i) occs

-- | The infinite list of zeroes
zeroes :: [Integer]
zeroes = 0:zeroes

instance Semigroup VarOccs where
  (VarOccs occs1) <> (VarOccs occs2)
    | length occs1 < length occs2
    = VarOccs (zipWith (+) (occs1 ++ zeroes) occs2)
  (VarOccs occs1) <> (VarOccs occs2)
    = VarOccs (zipWith (+) occs1 (occs2 ++ zeroes))

instance Monoid VarOccs where
  mempty = VarOccs []

-- | 'listen' to the output of a writer computation and return that output but
-- drop it from the writer output of the computation
listenDrop :: MonadWriter w m => m a -> m (a, w)
listenDrop m = pass (listen m >>= \aw -> return (aw, const mempty))

-- | The monad for sawLet minimization
type SLMinM = StateT (IntMap (Term, VarOccs)) (WriterT VarOccs IO)

-- | Find every subterm of the form @sawLet a b rhs (\ x -> body)@ and, whenever
-- @x@ occurs at most once in @body@, unfold the @sawLet@ by substituting @rhs@
-- into @body@
sawLetMinimize :: SharedContext -> Term -> IO Term
sawLetMinimize sc t_top =
  fst <$> runWriterT (evalStateT (slMinTerm t_top) IntMap.empty) where
  slMinTerm :: Term -> SLMinM Term
  slMinTerm (Unshared tf) = slMinTermF tf
  slMinTerm t@(STApp { stAppIndex = i }) =
    do memo_table <- get
       case IntMap.lookup i memo_table of
         Just (t', occs) ->
           -- NOTE: the fact that we explicitly tell occs here means that we are
           -- going to double-count variable occurrences for multiple
           -- occurrences of the same subterm. That is, a variable occurence
           -- counts for each copy of a shared subterm.
           tell occs >> return t'
         Nothing ->
           do (t', occs) <- listen $ slMinTermF (unwrapTermF t)
              modify $ IntMap.insert i (t', occs)
              return t'

  slMinTermF :: TermF Term -> SLMinM Term
  slMinTermF tf@(App (asApplyAll ->
                      (isGlobalDef "Prelude.sawLet" -> Just _, [_a, _b, rhs]))
                 (asLambda -> Just (_, _, body))) =
    do (body', (unconsVarOccs ->
                (x_cnt, body_occs))) <- listenDrop $ slMinTerm body
       if x_cnt > 1 then slMinTermF' tf else
         do (rhs', rhs_occs) <- listenDrop $ slMinTerm rhs
            tell (multVarOccs x_cnt rhs_occs <> body_occs)
            liftIO $ instantiateVar sc 0 rhs' body'
  slMinTermF tf = slMinTermF' tf

  slMinTermF' :: TermF Term -> SLMinM Term
  slMinTermF' (FTermF ftf) = slMinFTermF ftf
  slMinTermF' (App f arg) =
    do f' <- slMinTerm f
       arg' <- slMinTerm arg
       liftIO $ scTermF sc (App f' arg')
  slMinTermF' (Lambda x tp body) =
    do tp' <- slMinTerm tp
       (body', body_occs) <- listenDrop $ slMinTerm body
       tell $ snd $ unconsVarOccs body_occs
       liftIO $ scTermF sc (Lambda x tp' body')
  slMinTermF' (Pi x tp body) =
    do tp' <- slMinTerm tp
       (body', body_occs) <- listenDrop $ slMinTerm body
       tell $ snd $ unconsVarOccs body_occs
       liftIO $ scTermF sc (Pi x tp' body')
  slMinTermF' tf@(LocalVar i) =
    tell (varOccs1 i) >> liftIO (scTermF sc tf)
  slMinTermF' tf@(Constant _ _) = liftIO (scTermF sc tf)

  slMinFTermF :: FlatTermF Term -> SLMinM Term
  slMinFTermF ftf@(ExtCns _) = liftIO $ scFlatTermF sc ftf
  slMinFTermF ftf = traverse slMinTerm ftf >>= liftIO . scFlatTermF sc
