{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Verifier.SAW.OpenTerm
Copyright   : Galois, Inc. 2018
License     : BSD3
Stability   : experimental
Portability : non-portable (language extensions)

This module defines an interface to building SAW core terms in an incrementally
type-checked way, meaning that type-checking is performed as the terms are
built.
-}

module Verifier.SAW.OpenTerm (
  -- * Open terms and converting to closed terms
  OpenTerm(..), completeOpenTerm, completeOpenTermType,
  -- * Basic operations for building open terms
  closedOpenTerm, flatOpenTerm, sortOpenTerm, natOpenTerm,
  unitOpenTerm, unitTypeOpenTerm,
  stringLitOpenTerm, stringTypeOpenTerm,
  pairOpenTerm, pairTypeOpenTerm, pairLeftOpenTerm, pairRightOpenTerm,
  tupleOpenTerm, tupleTypeOpenTerm, projTupleOpenTerm,
  ctorOpenTerm, dataTypeOpenTerm, globalOpenTerm,
  applyOpenTerm, applyOpenTermMulti,
  lambdaOpenTerm, lambdaOpenTermMulti, piOpenTerm, piOpenTermMulti,
  arrowOpenTerm,
  letOpenTerm,
  -- * Monadic operations for building terms with binders
  OpenTermM(..), completeOpenTermM,
  dedupOpenTermM, lambdaOpenTermM, piOpenTermM,
  lambdaOpenTermAuxM, piOpenTermAuxM
  ) where

import Control.Monad
import Control.Monad.IO.Class
import Data.Text (Text)
import Numeric.Natural

import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.Module

-- | An open term is represented as a type-checking computation that computes a
-- SAW core term and its type
newtype OpenTerm = OpenTerm { unOpenTerm :: TCM TypedTerm }

-- | "Complete" an 'OpenTerm' to a closed term or 'fail' on type-checking error
completeOpenTerm :: SharedContext -> OpenTerm -> IO Term
completeOpenTerm sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (typedVal <$> termM) sc Nothing []

-- | "Complete" an 'OpenTerm' to a closed term for its type
completeOpenTermType :: SharedContext -> OpenTerm -> IO Term
completeOpenTermType sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (typedType <$> termM) sc Nothing []

-- | Embed a closed 'Term' into an 'OpenTerm'
closedOpenTerm :: Term -> OpenTerm
closedOpenTerm t = OpenTerm $ typeInferComplete t

-- | Build an 'OpenTerm' from a 'FlatTermF'
flatOpenTerm :: FlatTermF OpenTerm -> OpenTerm
flatOpenTerm ftf = OpenTerm $
  (sequence (fmap unOpenTerm ftf) >>= typeInferComplete)

-- | Build an 'OpenTerm' for a sort
sortOpenTerm :: Sort -> OpenTerm
sortOpenTerm s = flatOpenTerm (Sort s)

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

-- | Build an 'OpenTerm' for a global name.
globalOpenTerm :: Ident -> OpenTerm
globalOpenTerm ident =
  OpenTerm (liftTCM scGlobalDef ident >>= typeInferComplete)

-- | Apply an 'OpenTerm' to another
applyOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
applyOpenTerm (OpenTerm f) (OpenTerm arg) =
  OpenTerm ((App <$> f <*> arg) >>= typeInferComplete)

-- | Apply an 'OpenTerm' to 0 or more arguments
applyOpenTermMulti :: OpenTerm -> [OpenTerm] -> OpenTerm
applyOpenTermMulti = foldl applyOpenTerm

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
bindOpenTerm :: LocalName -> TypedTerm -> (OpenTerm -> OpenTerm) -> TCM TypedTerm
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

-- | The monad for building 'OpenTerm's if you want to add in 'IO' actions. This
-- is just the type-checking monad, but we give it a new name to keep this
-- module self-contained.
newtype OpenTermM a = OpenTermM { unOpenTermM :: TCM a }
                    deriving (Functor, Applicative, Monad)

instance MonadIO OpenTermM where
  liftIO = OpenTermM . liftIO

-- | "Complete" an 'OpenTerm' build in 'OpenTermM' to a closed term, or 'fail'
-- on a type-checking error
completeOpenTermM :: SharedContext -> OpenTermM OpenTerm -> IO Term
completeOpenTermM sc (OpenTermM termM) =
  either (fail . show) return =<<
  runTCM (typedVal <$> join (fmap unOpenTerm termM)) sc Nothing []

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
