{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{- |
Module      : Verifier.SAW.OpenTerm
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

module Verifier.SAW.OpenTerm (
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
  tupleOpenTerm', tupleTypeOpenTerm',
  recordOpenTerm, recordTypeOpenTerm, projRecordOpenTerm,
  ctorOpenTerm, dataTypeOpenTerm, globalOpenTerm, identOpenTerm, extCnsOpenTerm,
  applyOpenTerm, applyOpenTermMulti, applyGlobalOpenTerm,
  applyPiOpenTerm, piArgOpenTerm, lambdaOpenTerm, lambdaOpenTermMulti,
  piOpenTerm, piOpenTermMulti,
  arrowOpenTerm, letOpenTerm, sawLetOpenTerm, list1OpenTerm,
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
  -- * Building SpecM computations
  SpecTerm(), defineSpecOpenTerm, lambdaPureSpecTerm, lambdaPureSpecTermMulti,
  lrtClosTypeSpecTerm, sawLetPureSpecTerm, lrtToTypeSpecTerm,
  mkBaseClosSpecTerm, mkFreshClosSpecTerm, callClosSpecTerm, applyClosSpecTerm,
  callDefSpecTerm, monadicSpecOp,
  specMTypeSpecTerm, returnSpecTerm, bindSpecTerm, errorSpecTerm,
  ) where

import qualified Data.Vector as V
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Data.Text (Text)
import Numeric.Natural

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import Verifier.SAW.Utils (panic)
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty
import Verifier.SAW.SharedTerm
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.Module
import Verifier.SAW.Recognizer

-- | An open term is represented as a type-checking computation that computes a
-- SAW core term and its type
newtype OpenTerm = OpenTerm { unOpenTerm :: TCM TypedTerm }

-- | "Complete" an 'OpenTerm' to a closed term or 'fail' on type-checking error
completeOpenTerm :: SharedContext -> OpenTerm -> IO Term
completeOpenTerm sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (typedVal <$> termM) sc Nothing []

-- | "Complete" an 'OpenTerm' to a closed term and 'betaNormalize' the result
completeNormOpenTerm :: SharedContext -> OpenTerm -> IO Term
completeNormOpenTerm sc m =
  completeOpenTerm sc m >>= sawLetMinimize sc >>= betaNormalize sc

-- | "Complete" an 'OpenTerm' to a closed term for its type
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
-- NOTE: this operation should be considered "unsafe" because it can create
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
     unOpenTerm $ f $ renderSawDoc defaultPPOpts $
       ppTermInCtx defaultPPOpts (map fst ctx) t

-- | Return type type of an 'OpenTerm' as an 'OpenTerm
openTermType :: OpenTerm -> OpenTerm
openTermType (OpenTerm m) =
  OpenTerm $ do TypedTerm _ tp <- m
                ctx <- askCtx
                tp_tp <- liftTCM scTypeOf' (map snd ctx) tp
                return (TypedTerm tp tp_tp)

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
tupleOpenTerm' ts = foldr1 pairTypeOpenTerm ts

-- | Build a right-nested tuple type as an 'OpenTerm'
tupleTypeOpenTerm' :: [OpenTerm] -> OpenTerm
tupleTypeOpenTerm' [] = unitTypeOpenTerm
tupleTypeOpenTerm' ts = foldr1 pairTypeOpenTerm ts

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
               return $ TypedTerm trm tp)

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
     return (TypedTerm ret ret_tp)

-- | Get the argument type of a function type, 'fail'ing if the input term is
-- not a function type
piArgOpenTerm :: OpenTerm -> OpenTerm
piArgOpenTerm (OpenTerm m) =
  OpenTerm $ m >>= \case
  (unwrapTermF . typedVal -> Pi _ tp _) -> typeInferComplete tp
  t ->
    do ctx <- askCtx
       fail ("piArgOpenTerm: not a pi type: " ++
             scPrettyTermInCtx defaultPPOpts (map fst ctx) (typedVal t))

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
bindOpenTerm :: LocalName -> TypedTerm -> (OpenTerm -> OpenTerm) ->
                TCM TypedTerm
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

-- | Build an 'OpenTerm' of type @List1 tp@ from 'OpenTerm's of type @tp@
list1OpenTerm :: OpenTerm -> [OpenTerm] -> OpenTerm
list1OpenTerm tp xs =
  foldr (\hd tl -> ctorOpenTerm "Prelude.Cons1" [tp, hd, tl])
  (ctorOpenTerm "Prelude.Nil1" [tp])
  xs


-- | The monad for building 'OpenTerm's if you want to add in 'IO' actions. This
-- is just the type-checking monad, but we give it a new name to keep this
-- module self-contained.
newtype OpenTermM a = OpenTermM { unOpenTermM :: TCM a }
                    deriving (Functor, Applicative, Monad)

instance MonadIO OpenTermM where
  liftIO = OpenTermM . liftIO

-- | "Run" an 'OpenTermM' computation to produce an 'OpenTerm'
runOpenTermM :: OpenTermM OpenTerm -> OpenTerm
runOpenTermM (OpenTermM m) =
  OpenTerm $ join $ fmap unOpenTerm m

-- | "Complete" an 'OpenTerm' build in 'OpenTermM' to a closed term, or 'fail'
-- on a type-checking error
completeOpenTermM :: SharedContext -> OpenTermM OpenTerm -> IO Term
completeOpenTermM sc m = completeOpenTerm sc (runOpenTermM m)

-- | "De-duplicate" an open term, so that duplicating the returned 'OpenTerm'
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
  OpenTermM (TypedTerm, TypedTerm, a)
bindOpenTermAuxM x (OpenTerm tpM) body_f =
  OpenTermM $
  do TypedTerm tp tp_tp <- tpM
     tp_whnf <- typeCheckWHNF tp
     (OpenTerm bodyM, a) <-
       withVar x tp_whnf (openTermTopVar >>= (unOpenTermM . body_f))
     body <- bodyM
     return (TypedTerm tp_whnf tp_tp, body, a)

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
-- Building SpecM computations

-- | When creating a SAW core term of type @PolySpecFun@ or @PolyStackTuple@,
-- the body or bodies are relative to: the current event type (or @EvType@); the
-- @FunStack@ of @LetRecType@s of the locally-defined corecursive functions; the
-- list of imported spec definitions; an extended stack that specifies the
-- @FunStack@ of any future @SpecDef@ that this object will be used in; and a
-- stack inclusion between the @FunStack@ defined by the local stack plus
-- imports and the extended stack. These are captured by the 'SpecInfo' type.
data SpecInfo =
  SpecInfo { specInfoEvType :: OpenTerm,
             specInfoLocalsStack :: OpenTerm,
             specInfoImps :: OpenTerm,
             specInfoExtStack :: OpenTerm,
             specInfoIncl :: OpenTerm }

-- | An 'OpenTerm' that depends on a 'SpecInfo'. These are used for the bodies
-- of terms of type @PolySpecFun@ or @PolyStackTuple@.
type SpecInfoTerm = Reader SpecInfo OpenTerm

-- | Apply a 'SpecInfoTerm' to another
applySpecInfoTerm :: SpecInfoTerm -> SpecInfoTerm -> SpecInfoTerm
applySpecInfoTerm f arg = applyOpenTerm <$> f <*> arg

-- | Apply an operator to the event type, locals stack, imports, extended
-- function stack, and tsack inclusion in the current 'SpecInfo'
applyStackInclOp :: Ident -> SpecInfoTerm
applyStackInclOp f =
  do info <- ask
     return $ applyGlobalOpenTerm f
       [specInfoEvType info, specInfoLocalsStack info, specInfoImps info,
        specInfoExtStack info, specInfoIncl info]

-- | Apply an operator to the current event type and extended function stack
applyExtStackOp :: Ident -> SpecInfoTerm
applyExtStackOp f =
  do info <- ask
     return $ applyGlobalOpenTerm f
       [specInfoEvType info, specInfoExtStack info]

-- | Build the 'SpecInfoTerm' for the extended function stack
extStackSpecInfoTerm :: SpecInfoTerm
extStackSpecInfoTerm = ask >>= (return . specInfoExtStack)

-- | FIXME: docs
bindSpecInfoTerm :: (LocalName -> TypedTerm -> TypedTerm -> TermF TypedTerm) ->
                    LocalName -> SpecInfoTerm -> SpecInfoTerm -> SpecInfoTerm
bindSpecInfoTerm f x tpM bodyM =
  do tpOT <- tpM
     bodyOT <- bodyM
     return $ OpenTerm $ do
      -- First we compute the type of the variable by running its underlying TCM
      -- computation and normalizing it; normalization is required here because
      -- the typeInferComplete instance for TermF TypedTerm, which we use below,
      -- assumes that the variable type is normalized
       TypedTerm tp tp_tp <- unOpenTerm tpOT
       tp_whnf <- typeCheckWHNF tp
       let tp' = TypedTerm tp_whnf tp_tp

       -- Next, we run the body TCM computation to get its TypedTerm, making
       -- sure to run that computation in an extended typing context with x
       body <- withVar x tp_whnf $ unOpenTerm bodyOT

       -- Finally, build and return the required lambda-abstraction
       typeInferComplete $ f x tp' body


-- | In order to create a recursive function in a @SpecDef@, we need its
-- @LetRecType@ and its definition as a @PolySpecFun E stk lrt@. The difficulty
-- is that the function stack @stk@ is only known after we have fully processed
-- all the recursive function definitions in the entire @SpecDef@, so we make
-- the body depend on the @stk@ value; that is, 'specRecFunBody' should take in
-- @stk@ and return a SAW core term of type @PolySpecFun E stk lrt@, where @lrt@
-- is the value of 'specRecFunLRT'.
data SpecRecFun = SpecRecFun { specRecFunLRT :: OpenTerm,
                               specRecFunBody :: Maybe SpecInfoTerm }

tempSpecRecFun :: OpenTerm -> SpecRecFun
tempSpecRecFun lrt = SpecRecFun { specRecFunLRT = lrt,
                                  specRecFunBody = Nothing }

-- | The state that is built up when building a 'SpecTerm' that is needed to
-- make the top-level @defineSpec@ call; all the lists are accumulated in
-- reverse order, so that the final index of elements already in the lists don't
-- change as we add new elements
data SpecTermState =
  SpecTermState { specStEvType :: OpenTerm,
                  specStNumBaseRecs :: Natural,
                  specStCtxLen :: Int,
                  specStExtraRecsRev :: [SpecRecFun],
                  specStImportsRev :: [OpenTerm] }

-- | Return the local corecursive functions in a 'SpecTermState' in the correct
-- order, by reversing the reversed 'specStExtraRecsRev' list
specStExtraRecs :: SpecTermState -> [SpecRecFun]
specStExtraRecs st = reverse $ specStExtraRecsRev st

-- | Return the spec imports in a 'SpecTermState' in the correct order, by
-- reversing the reversed 'specStImportsRev' list
specStImports :: SpecTermState -> [OpenTerm]
specStImports st = reverse (specStImportsRev st)

-- | Increment the context length of a 'SpecTermState'
specStIncCtx :: SpecTermState -> SpecTermState
specStIncCtx st = st { specStCtxLen = specStCtxLen st + 1 }

-- | Decrement the context length of a 'SpecTermState'
specStDecCtx :: SpecTermState -> SpecTermState
specStDecCtx st = st { specStCtxLen = specStCtxLen st - 1 }

specStInsTempClos :: OpenTerm -> SpecTermState -> (Natural, SpecTermState)
specStInsTempClos lrt st =
  (specStNumBaseRecs st + fromIntegral (length $ specStExtraRecsRev st),
   st { specStExtraRecsRev = tempSpecRecFun lrt : specStExtraRecsRev st })

setNthClosBody :: Int -> SpecInfoTerm -> [SpecRecFun] -> [SpecRecFun]
setNthClosBody i _ recFuns
  | i >= length recFuns || i < 0 =
    panic "setNthClosBody" ["Index out of range"]
setNthClosBody i body recFuns =
  let new_recFun = case recFuns!!i of
        SpecRecFun lrt Nothing -> SpecRecFun lrt (Just body)
        SpecRecFun _ (Just _) ->
          panic "setNthClosBody" ["Closure body already set"] in
  take i recFuns ++ new_recFun : drop (i+1) recFuns

setNthClosBodyRev :: Int -> SpecInfoTerm -> [SpecRecFun] -> [SpecRecFun]
setNthClosBodyRev i body recFuns =
  setNthClosBody (length recFuns - i) body recFuns

specStSetClosBody :: Natural -> SpecInfoTerm -> SpecTermState -> SpecTermState
specStSetClosBody clos_ix body st =
  st { specStExtraRecsRev =
         setNthClosBodyRev (fromIntegral clos_ix) body (specStExtraRecsRev st) }

specStInsImport :: OpenTerm -> SpecTermState -> (Natural, SpecTermState)
specStInsImport def st =
  (fromIntegral (length $ specStImportsRev st),
   st { specStImportsRev = def : specStImportsRev st })

initSpecTermState :: OpenTerm -> Natural -> Int -> SpecTermState
initSpecTermState ev n ctx_len =
  SpecTermState { specStEvType = ev, specStNumBaseRecs = n,
                  specStCtxLen = ctx_len,
                  specStExtraRecsRev = [], specStImportsRev = [] }

-- | High-level idea: while building a @SpecM@ computation, you have to keep
-- track of the imported SpecDefs and the co-recursive functions that are
-- created by defunctionalization, and this is tracked in this monad
type SpecTermM = State SpecTermState

runSpecTermM :: OpenTerm -> Natural -> SpecTermM OpenTerm -> OpenTerm
runSpecTermM ev n m = OpenTerm $
  do ctx_len <- length <$> askCtx
     unOpenTerm $ evalState m $ initSpecTermState ev n ctx_len

-- | A 'SpecTerm' is a term representation used to build @SpecM@ computations to
-- be used in spec definitions, i.e., terms of type @SpecDef E@ for some given
-- @E@. Any monadic functions or calls to functions that have been previously
-- defined are lifted to the top level using the 'SpecTermM' monad. The
-- resulting terms will always be inside a @PolySpecFun@ or @PolyStackTuple@,
-- and so are in the context of the information provided by a 'SpecInfoTerm',
-- thus the use of the 'SpecInfoTerm' type.
newtype SpecTerm = SpecTerm { unSpecTerm :: SpecTermM SpecInfoTerm }

instance OpenTermLike SpecTerm where
  openTermLike = openTermSpecTerm
  typeOfTermLike = specTermType
  flatTermLike = flatSpecTerm
  applyTermLike = applySpecTerm
  lambdaTermLike = lambdaSpecTerm
  piTermLike = piSpecTerm
  ctorTermLike = ctorSpecTerm
  dataTypeTermLike = dataTypeSpecTerm

applySpecTerm :: SpecTerm -> SpecTerm -> SpecTerm
applySpecTerm (SpecTerm f) (SpecTerm arg) =
  SpecTerm (applySpecInfoTerm <$> f <*> arg)

applySpecTermMulti :: SpecTerm -> [SpecTerm] -> SpecTerm
applySpecTermMulti = foldl applySpecTerm

specInfoTermTerm :: SpecInfoTerm -> SpecTerm
specInfoTermTerm t = SpecTerm $ return t

-- | Convert an 'OpenTerm' to a 'SpecTerm'
openTermSpecTerm :: OpenTerm -> SpecTerm
openTermSpecTerm t =
  SpecTerm $
  do ctx_len <- specStCtxLen <$> get
     return $ return $
       OpenTerm $
       do ctx <- askCtx
          if length ctx == ctx_len then unOpenTerm t else
            panic "openTermSpecTerm" ["Typing context not of expected length"]

-- | Return the type of a 'SpecTerm' as a 'SpecTerm'
specTermType :: SpecTerm -> SpecTerm
specTermType (SpecTerm m) =
  SpecTerm $ flip fmap m $ \info_tm -> fmap openTermType info_tm

-- | Build the 'SpecTerm' for the extended function stack
extStackSpecTerm :: SpecTerm
extStackSpecTerm = specInfoTermTerm extStackSpecInfoTerm

-- | Build an 'OpenTerm' for the top variable in a 'SpecTermM' computation
topVarSpecTerm :: SpecTermM OpenTerm
topVarSpecTerm =
  do outer_ctx_len <- specStCtxLen <$> get
     return $ OpenTerm $
         do inner_ctx_len <- length <$> askCtx
            typeInferComplete (LocalVar (inner_ctx_len
                                         - outer_ctx_len) :: TermF Term)

-- | Run a 'SpecTermM' computation in a context with an extra bound variable
withVarSpecTermM :: SpecTermM a -> SpecTermM a
withVarSpecTermM m =
  do modify specStIncCtx
     a <- m
     modify specStDecCtx
     return a

-- | Build a lambda abstraction as a 'SpecTerm' from a function that takes in a
-- pure 'OpenTerm'
lambdaPureSpecTerm :: LocalName -> SpecTerm -> (OpenTerm -> SpecTerm) -> SpecTerm
lambdaPureSpecTerm x (SpecTerm tpM) body_f = SpecTerm $
  do tp <- tpM
     body <- withVarSpecTermM (topVarSpecTerm >>= (unSpecTerm . body_f))
     return $ bindSpecInfoTerm Lambda x tp body

-- | Build a nested sequence of pure lambda abstractions as a 'SpecTerm'
lambdaPureSpecTermMulti :: [(LocalName, SpecTerm)] ->
                           ([OpenTerm] -> SpecTerm) -> SpecTerm
lambdaPureSpecTermMulti xs_tps body_f =
  foldr (\(x,tp) rest_f xs ->
          lambdaPureSpecTerm x tp (rest_f . (:xs))) (body_f . reverse) xs_tps []

-- | Build a lambda abstraction as a 'SpecTerm'
lambdaSpecTerm :: LocalName -> SpecTerm -> (SpecTerm -> SpecTerm) -> SpecTerm
lambdaSpecTerm x tp body_f =
  lambdaPureSpecTerm x tp (body_f . openTermSpecTerm)

-- | Build a pi abstraction as a 'SpecTerm'
piSpecTerm :: LocalName -> SpecTerm -> (SpecTerm -> SpecTerm) -> SpecTerm
piSpecTerm x (SpecTerm tpM) body_f = SpecTerm $
  do tp <- tpM
     body <- withVarSpecTermM (fmap openTermSpecTerm topVarSpecTerm >>=
                               (unSpecTerm . body_f))
     return $ bindSpecInfoTerm Pi x tp body

-- | Convert a term @lrt@ of type @LetRecType@ to the type it represents by
-- forming the term @LRTArg stk lrt@
lrtToTypeSpecTerm :: OpenTerm -> SpecTerm
lrtToTypeSpecTerm lrt =
  applyGlobalTermLike "Prelude.LRTArg"
  [specInfoTermTerm (specInfoExtStack <$> ask), openTermSpecTerm lrt]

funStackTypeOpenTerm :: OpenTerm
funStackTypeOpenTerm = globalOpenTerm "Prelude.FunStack"

letRecTypeOpenTerm :: OpenTerm
letRecTypeOpenTerm = dataTypeOpenTerm "Prelude.LetRecType" []

specImpOpenTerm :: OpenTerm -> OpenTerm
specImpOpenTerm ev = dataTypeOpenTerm "Prelude.SpecImp" [ev]

defineSpecStackOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm -> OpenTerm
defineSpecStackOpenTerm ev local_stk imps =
  applyGlobalOpenTerm "Prelude.defineSpecStack" [ev, local_stk, imps]

mkPolySpecLambda :: OpenTerm -> OpenTerm -> OpenTerm -> SpecInfoTerm -> OpenTerm
mkPolySpecLambda ev local_stk imps t =
  let stk = defineSpecStackOpenTerm ev local_stk imps in
  lambdaOpenTerm "stk'" funStackTypeOpenTerm $ \stk' ->
  lambdaOpenTerm "incl" (applyGlobalOpenTerm
                         "Prelude.stackIncl" [stk, stk']) $ \incl ->
  runReader t $ SpecInfo { specInfoEvType = ev,
                           specInfoLocalsStack = local_stk,
                           specInfoImps = imps,
                           specInfoExtStack = stk',
                           specInfoIncl = incl }

mkSpecRecFunM :: OpenTerm -> SpecTerm -> SpecTermM SpecRecFun
mkSpecRecFunM lrt (SpecTerm m) = SpecRecFun lrt <$> Just <$> m

specRecFunsStack :: [SpecRecFun] -> OpenTerm
specRecFunsStack recFuns =
  list1OpenTerm letRecTypeOpenTerm $ map specRecFunLRT recFuns

specRecFunsTuple :: [SpecRecFun] -> SpecInfoTerm
specRecFunsTuple recFuns =
  tupleOpenTerm <$> forM recFuns
  (\rf -> case specRecFunBody rf of
      Just body -> body
      Nothing -> panic "specRecFunsTuple" ["Recursive function body not defined"])

-- | Build a spec definition, i.e., a term of type @SpecDef E@, given: an event
-- type @E@; a list of corecursive functions that can be called in that spec
-- definition, given as pairs of a @LetRecType@ and a 'SpecTerm' of that type;
-- and a @LetRecType@ plus a body for the entire definition.
defineSpecOpenTerm :: OpenTerm -> [(OpenTerm,SpecTerm)] ->
                      OpenTerm -> SpecTerm -> OpenTerm
defineSpecOpenTerm ev base_recs_in lrt body_in =
  runSpecTermM ev (fromIntegral $ length base_recs_in) $
  do base_recs <-
       forM base_recs_in $ \(fun_lrt,fun_tm) -> mkSpecRecFunM fun_lrt fun_tm
     body <- unSpecTerm body_in
     final_st <- get
     let all_recs = base_recs ++ specStExtraRecs final_st
     let local_stk = specRecFunsStack all_recs
     let imps = list1OpenTerm (specImpOpenTerm ev) (specStImports final_st)
     return $ applyGlobalOpenTerm "Prelude.defineSpec"
       [ev, local_stk, lrt, imps,
        mkPolySpecLambda ev local_stk imps (specRecFunsTuple all_recs),
        mkPolySpecLambda ev local_stk imps body]

-- | Build the type @LRTClos stk lrt@ from @lrt@ in the current stack
lrtClosTypeSpecTerm :: OpenTerm -> SpecTerm
lrtClosTypeSpecTerm lrt =
  applyGlobalTermLike "Prelude.LRTClos" [extStackSpecTerm,
                                         openTermSpecTerm lrt]

-- | Internal-only helper function
mkClosSpecInfoTerm :: Natural -> SpecInfoTerm
mkClosSpecInfoTerm n =
  applySpecInfoTerm (applyStackInclOp "Prelude.mkLocalLRTClos")
  (return $ natOpenTerm n)

-- | Build a closure that calls one of the "base" recursive functions in the
-- current spec definition
mkBaseClosSpecTerm :: Natural -> SpecTerm
mkBaseClosSpecTerm clos_ix = SpecTerm $
  do st <- get
     if clos_ix < specStNumBaseRecs st then return () else
       panic "mkBaseClosSpec" ["Closure index out of bounds"]
     return $ mkClosSpecInfoTerm clos_ix

-- | Build a closure that calls a new corecursive function with the given
-- @LetRecType@ and body, that can call itself using the term passed to it
mkFreshClosSpecTerm :: OpenTerm -> (SpecTerm -> SpecTerm) -> SpecTerm
mkFreshClosSpecTerm lrt body_f = SpecTerm $
  do (clos_ix, st) <- specStInsTempClos lrt <$> get
     put st
     body <- unSpecTerm $ body_f (SpecTerm $ return $
                                  mkClosSpecInfoTerm clos_ix)
     modify $ specStSetClosBody clos_ix body
     return $ mkClosSpecInfoTerm clos_ix

-- | Apply a closure of a given @LetRecType@ to a list of arguments
applyClosSpecTerm :: OpenTerm -> SpecTerm -> [SpecTerm] -> SpecTerm
applyClosSpecTerm lrt clos args =
  applyGlobalTermLike "Prelude.applyLRTClosN"
  (extStackSpecTerm : natTermLike (fromIntegral $ length args)
   : openTermSpecTerm lrt : clos : args)

-- | Build a @SpecM@ computation that calls a closure with the given return
-- type specified as a @LetRecType@
callClosSpecTerm :: OpenTerm -> SpecTerm -> SpecTerm
callClosSpecTerm tp clos =
  applySpecTermMulti (monadicSpecOp "Prelude.CallS")
  [openTermSpecTerm tp, clos]

-- | Call another spec definition inside a spec definition, by importing it
callDefSpecTerm :: OpenTerm -> SpecTerm
callDefSpecTerm def = SpecTerm $
  do (imp_ix, st) <- specStInsImport def <$> get
     put st
     return $
       applySpecInfoTerm (applyStackInclOp "Prelude.callNthImportS")
       (return $ natOpenTerm imp_ix)

-- | Build a 'SpecTerm' for a monadic operation that takes the current event
-- type and extended function stack
monadicSpecOp :: Ident -> SpecTerm
monadicSpecOp f = specInfoTermTerm $ applyExtStackOp f

-- | Build the type @SpecM ev stk tp@ from the type @tp@
specMTypeSpecTerm :: SpecTerm -> SpecTerm
specMTypeSpecTerm = applySpecTerm (monadicSpecOp "Prelude.SpecM")

-- | Build a @SpecM@ computation that returns a value of a given type
returnSpecTerm :: SpecTerm -> SpecTerm -> SpecTerm
returnSpecTerm tp val =
  applySpecTermMulti (monadicSpecOp "Prelude.retS") [tp, val]

-- | Build a @SpecM@ computation that does a monadic bind
bindSpecTerm :: SpecTerm -> SpecTerm -> SpecTerm ->
                SpecTerm -> SpecTerm
bindSpecTerm tp1 tp2 m f =
  applySpecTermMulti (monadicSpecOp "Prelude.bindS") [tp1, tp2, m, f]

-- | Build a @SpecM@ error computation at the given type with the given message
errorSpecTerm :: SpecTerm -> Text -> SpecTerm
errorSpecTerm tp msg =
  applySpecTermMulti (monadicSpecOp "Prelude.errorS")
  [tp, openTermSpecTerm (stringLitOpenTerm msg)]

-- | Build a 'SpecInfoTerm' from a 'FlatTermF'
flatSpecInfoTerm :: FlatTermF SpecInfoTerm -> SpecInfoTerm
flatSpecInfoTerm ftf = fmap flatOpenTerm $ sequence ftf

-- | Build a 'SpecTerm' from a 'FlatTermF'
flatSpecTerm :: FlatTermF SpecTerm -> SpecTerm
flatSpecTerm ftf =
  SpecTerm $ fmap flatSpecInfoTerm $ sequence (fmap unSpecTerm ftf)

-- | Build a 'SpecInfoTerm' for a constructor applied to its arguments
ctorSpecInfoTerm :: Ident -> [SpecInfoTerm] -> SpecInfoTerm
ctorSpecInfoTerm c args = fmap (ctorOpenTerm c) (sequence args)

-- | Build a 'SpecTerm' for a constructor applied to its arguments
ctorSpecTerm :: Ident -> [SpecTerm] -> SpecTerm
ctorSpecTerm c args =
  SpecTerm $ fmap (ctorSpecInfoTerm c) $ sequence $ map unSpecTerm args

-- | Build a 'SpecInfoTerm' for a datatype applied to its arguments
dataTypeSpecInfoTerm :: Ident -> [SpecInfoTerm] -> SpecInfoTerm
dataTypeSpecInfoTerm d args = fmap (dataTypeOpenTerm d) (sequence args)

-- | Build a 'SpecTerm' for a datatype applied to its arguments
dataTypeSpecTerm :: Ident -> [SpecTerm] -> SpecTerm
dataTypeSpecTerm d args =
  SpecTerm $ fmap (dataTypeSpecInfoTerm d) $ sequence $ map unSpecTerm args

-- | Build a let expression as an 'SpecTerm'. This is equivalent to
-- > 'applySpecTerm' ('lambdaSpecTerm' x tp body) rhs
sawLetPureSpecTerm :: LocalName -> SpecTerm -> SpecTerm -> SpecTerm ->
                      (OpenTerm -> SpecTerm) -> SpecTerm
sawLetPureSpecTerm x tp tp_ret rhs body_f =
  applySpecTermMulti (globalTermLike "Prelude.sawLet")
  [tp, tp_ret, rhs, lambdaPureSpecTerm x tp body_f]



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
