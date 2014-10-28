{-# LANGUAGE ScopedTypeVariables #-}
{- |
Module      : Verifier.SAW.SCTypeCheck
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.SCTypeCheck
  ( scTypeCheck
  , scTypeCheckError
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.State.Strict as State

import Data.Foldable (maximum)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable ()
import qualified Data.Vector as V
import Prelude hiding (mapM, maximum)

import Verifier.SAW.Prelude.Constants
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding (incVars, instantiateVarList)

type TCState s = Map TermIndex (SharedTerm s)
type TCM s a = State.StateT (TCState s) (ExceptT String IO) a

scTypeCheckError :: forall s. SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scTypeCheckError sc t0 = either error id <$> scTypeCheck sc t0

-- | This version of the type checking function makes sure that the
-- entire term is well-formed, and that all internal type annotations
-- are correct. Types are evaluated to WHNF as necessary, and the
-- returned type is in WHNF.
scTypeCheck :: forall s. SharedContext s -> SharedTerm s
            -> IO (Either String (SharedTerm s))
scTypeCheck sc t0 = runExceptT (scTypeCheck' sc [] t0)

-- The TODO notes in the body are mostly commented-out checks for type
-- equivalence that currently tend to fail for two reasons: 1)
-- functions from the Cryptol module not being evaluated, and 2)
-- natural number primitives not being evaluated.
scTypeCheck' :: forall s. SharedContext s -> [SharedTerm s] -> SharedTerm s
             -> ExceptT String IO (SharedTerm s)
scTypeCheck' sc env t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: SharedTerm s -> TCM s (SharedTerm s)
    memo (Unshared tf) = termf tf
    memo _t@(STApp i tf) =
      do table <- State.get
         case Map.lookup i table of
           Just x  -> return x
           Nothing ->
             do x <- termf tf
                x' <- io $ scWhnf sc x
                State.modify (Map.insert i x')
                return x'
    sort :: SharedTerm s -> TCM s Sort
    sort t = asSort =<< memo t
    io = lift . lift
    whnf t = io $ scWhnf sc t
    checkPi tx y = do
      ty <- memo y
      case asPi tx of
        Just (_, aty, rty) -> do
          _ <- sort aty -- TODO: do we care about the level?
          aty' <- whnf aty
          checkEqTy ty aty' $ "Argument has type " ++ show ty ++
                              " instead of expected type " ++ show aty'
          io $ instantiateVar sc 0 y rty
        _ -> fail "Left hand side of application does not have function type"
    checkEqTy ty ty' msg = unless (alphaEquiv ty ty') (fail msg)
    termf :: TermF (SharedTerm s) -> TCM s (SharedTerm s)
    termf tf =
      case tf of
        FTermF ftf -> ftermf ftf
        App x y ->
          do tx <- memo x
             checkPi tx y
        Lambda x a rhs ->
          do b <- lift $ scTypeCheck' sc (a : env) rhs
             io $ scTermF sc (Pi x a b)
        Pi _ a rhs ->
          do s1 <- asSort =<< memo a
             s2 <- asSort =<< lift (scTypeCheck' sc (a : env) rhs)
             io $ scSort sc (max s1 s2)
        -- TODO: this won't support dependent Let bindings
        -- TODO: should the bindings be reversed?
        -- TODO: check that all defs have the annotated type
        Let defs rhs -> lift $ scTypeCheck' sc (reverse dtys ++ env) rhs
          where dtys = map defType defs
        LocalVar i
          | i < length env -> io $ incVars sc 0 (i + 1) (env !! i)
          | otherwise      -> fail $ "Dangling bound variable: " ++ show (i - length env)
        Constant _ t _ -> memo t
    ftermf :: FlatTermF (SharedTerm s) -> TCM s (SharedTerm s)
    ftermf tf =
      case tf of
        GlobalDef d -> do
          ty <- io $ scTypeOfGlobal sc d
          _ <- sort ty
          whnf ty
        TupleValue l -> io . scTupleType sc =<< traverse memo l
        TupleType l -> io . scSort sc . maximum =<< traverse sort l
        TupleSelector t i -> do
          ty <- memo t
          case ty of
            STApp _ (FTermF (TupleType ts)) -> do
              unless (i <= length ts) $ fail $ "Tuple index " ++ show i ++ " out of bounds"
              whnf (ts !! (i-1))
            _ -> fail "Left hand side of tuple selector has non-tuple type"
        RecordValue m -> io . scRecordType sc =<< traverse memo m
        RecordSelector t f -> do
          ty <- memo t
          case ty of
            STApp _ (FTermF (RecordType m)) -> 
              case Map.lookup f m of
                Nothing -> fail $ "Record field " ++ f ++ " not found"
                Just tp -> whnf tp
            _ -> fail "Left hand side of record selector has non-record type"
        RecordType m -> io . scSort sc . maximum =<< traverse sort m
        CtorApp c args -> do
          t <- io $ scTypeOfCtor sc c
          _ <- sort t -- TODO: do we care about the level?
          t' <- whnf t
          foldM (\ a b -> checkPi a b) t' args
        DataTypeApp dt args -> do
          t <- io $ scTypeOfDataType sc dt
          _ <- sort t -- TODO: do we care about the level?
          t' <- whnf t
          foldM (\ a b -> checkPi a b) t' args
        Sort s -> io $ scSort sc (sortOf s)
        NatLit _ -> io $ scNatType sc
        ArrayValue tp vs -> do
          n <- io $ scNat sc (fromIntegral (V.length vs))
          _ <- sort tp -- TODO: do we care about the level?
          tp' <- whnf tp
          tys <- traverse memo vs
          let msg = "Array elements have differing types. Expected " ++ show tp' ++ " but got "
          V.mapM_ (\ty -> checkEqTy tp' ty (msg ++ show ty)) tys
          io $ scFlatTermF sc (DataTypeApp preludeVecIdent [n, tp'])
        FloatLit{}  -> io $ scFlatTermF sc (DataTypeApp preludeFloatIdent  [])
        DoubleLit{} -> io $ scFlatTermF sc (DataTypeApp preludeDoubleIdent [])
        StringLit{} -> io $ scFlatTermF sc (DataTypeApp preludeStringIdent [])
        ExtCns ec   -> whnf $ ecType ec
