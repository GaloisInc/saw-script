{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Simulator
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Evaluator for SAWCore terms, with lazy evaluation order.
-}

module Verifier.SAW.Simulator where

import Prelude hiding (mapM)

import Control.Monad (foldM, liftM, when)
import Control.Monad.Fix (MonadFix(mfix))
import Control.Monad.IO.Class
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import Data.Traversable
import qualified Data.Vector as V

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import Verifier.SAW.Simulator.Value

------------------------------------------------------------
-- Simulator configuration

data SimulatorConfig m e =
  SimulatorConfig
  { simGlobal :: Ident -> m (Value m e), 
    simUninterpreted :: forall t. (Termlike t, Show t) => Ident -> t -> Maybe (m (Value m e))
  }

------------------------------------------------------------
-- Evaluation of function definitions

-- | Pattern matching for values.
matchThunk :: MonadIO m => Pat t -> Thunk m e -> m (Maybe (Map Int (Thunk m e)))
matchThunk p x =
  case p of
    PVar _ i _  -> return $ Just (Map.singleton i x)
    PUnused _ _ -> return $ Just Map.empty
    PTuple ps   -> do v <- force x
                      case v of
                        VTuple xv -> matchThunks ps (V.toList xv)
                        _         -> return Nothing
    PRecord _   -> fail "matchThunk PRecord unimplemented"
    PCtor i ps  -> do v <- force x
                      case v of
                        VCtorApp s xv | i == s -> matchThunks ps (V.toList xv)
                        _                      -> return Nothing

-- | Simultaneous pattern matching for lists of values.
matchThunks :: MonadIO m => [Pat t] -> [Thunk m e] -> m (Maybe (Map Int (Thunk m e)))
matchThunks [] [] = return $ Just Map.empty
matchThunks [] (_ : _) = return Nothing
matchThunks (_ : _) [] = return Nothing
matchThunks (p : ps) (x : xs) = do
  mm1 <- matchThunk p x
  case mm1 of
    Nothing -> return Nothing
    Just m1 -> do
      mm2 <- matchThunks ps xs
      case mm2 of
        Nothing -> return Nothing
        Just m2 -> return $ Just (Map.union m1 m2)

-- | Evaluator for pattern-matching function definitions,
-- parameterized by an evaluator for right-hand sides.
evalDef :: forall m e n t. (MonadIO m, Show n) =>
           ([Thunk m e] -> t -> m (Value m e)) -> GenericDef n t -> m (Value m e)
evalDef rec (Def ident _ eqns) = vFuns [] arity
  where
    arity :: Int
    arity = lengthDefEqn (head eqns)
    lengthDefEqn :: DefEqn t -> Int
    lengthDefEqn (DefEqn ps _) = length ps
    vFuns :: [Thunk m e] -> Int -> m (Value m e)
    vFuns xs 0 = tryEqns eqns (reverse xs)
    vFuns xs n = return $ VFun (\x -> vFuns (x : xs) (n - 1))
    tryEqns :: [DefEqn t] -> [Thunk m e] -> m (Value m e)
    tryEqns [] _ = fail $ "Pattern match failure: " ++ show ident
    tryEqns (eqn : eqns') xs =
      do mm <- tryEqn eqn xs
         case mm of
           Just m -> return m
           Nothing -> tryEqns eqns' xs
    tryEqn :: DefEqn t -> [Thunk m e] -> m (Maybe (Value m e))
    tryEqn (DefEqn ps rhs) xs =
      do minst <- matchThunks ps xs
         case minst of
           Nothing -> return Nothing
           Just inst -> let env = reverse (Map.elems inst) in liftM Just (rec env rhs)

------------------------------------------------------------
-- Evaluation of terms

-- | Generic evaluator for TermFs.
evalTermF :: forall t m e. (Show t, MonadIO m, MonadFix m, Termlike t, Show e) =>
             SimulatorConfig m e                  -- ^ Evaluator for global constants
          -> ([Thunk m e] -> t -> m (Value m e))  -- ^ Evaluator for subterms under binders
          -> (t -> m (Value m e))                 -- ^ Evaluator for subterms in the same bound variable context
          -> [Thunk m e]                          -- ^ Environment of bound variables
          -> TermF t -> m (Value m e)
evalTermF cfg lam rec env tf =
  case tf of
    App t1 t2               -> do v <- rec t1
                                  x <- rec' t2
                                  apply v x
    Lambda _ _ t            -> return $ VFun (\x -> lam (x : env) t)
    Pi {}                   -> return $ VType
    Let ds t                -> do env' <- mfix $ \env' -> do
                                            xs <- mapM (delay . evalDef (\ys -> lam (ys ++ env'))) (reverse ds)
                                            return (xs ++ env)
                                  lam env' t
    LocalVar i              -> force (env !! i)
    Constant i t ty         -> maybe (rec t) id (simUninterpreted cfg i ty)
    FTermF ftf              ->
      case ftf of
        GlobalDef ident     -> simGlobal cfg ident
        TupleValue ts       -> liftM VTuple $ mapM rec' (V.fromList ts)
        TupleType {}        -> return VType
        TupleSelector t j   -> valTupleSelect j =<< rec t
        RecordValue tm      -> liftM VRecord $ mapM rec' tm
        RecordSelector t k  -> valRecordSelect k =<< rec t
        RecordType {}       -> return VType
        CtorApp ident ts    -> do v <- simGlobal cfg ident
                                  xs <- mapM rec' ts
                                  foldM apply v xs
        DataTypeApp {}      -> return VType
        Sort {}             -> return VType
        NatLit n            -> return $ VNat n
        ArrayValue _ tv     -> liftM VVector $ mapM rec' tv
        FloatLit float      -> return $ VFloat float
        DoubleLit double    -> return $ VDouble double
        StringLit s         -> return $ VString s
        ExtCns _            -> fail "evalTermF ExtCns unimplemented"
  where
    rec' :: t -> m (Thunk m e)
    rec' = delay . rec


-- | Evaluator for unshared terms.
evalTerm :: (MonadIO m, MonadFix m, Show e) =>
            SimulatorConfig m e -> [Thunk m e] -> Term -> m (Value m e)
evalTerm cfg env (Term tf) = evalTermF cfg lam rec env tf
  where
    lam = evalTerm cfg
    rec = evalTerm cfg env

evalTypedDef :: (MonadIO m, MonadFix m, Show e) =>
                SimulatorConfig m e -> TypedDef -> m (Value m e)
evalTypedDef cfg = evalDef (evalTerm cfg)

evalGlobal :: forall m e. (MonadIO m, MonadFix m, Show e) =>
              Module -> Map Ident (Value m e) ->
              (forall t. (Termlike t, Show t) => Ident -> t -> Maybe (m (Value m e))) -> 
              SimulatorConfig m e
evalGlobal m prims uninterpreted = cfg
  where
    cfg :: SimulatorConfig m e
    cfg = SimulatorConfig global uninterpreted

    global :: Ident -> m (Value m e)
    global ident =
      case Map.lookup ident prims of
        Just v -> return v
        Nothing ->
          case findCtor m ident of
            Just ct -> return (vCtor ident [] (ctorType ct))
            Nothing ->
              case findDef m ident of
                Just td | not (null (defEqs td)) -> evalTypedDef cfg td
                _ -> fail $ "Unimplemented global: " ++ show ident

    vCtor :: Ident -> [Thunk m e] -> Term -> Value m e
    vCtor ident xs (Term (Pi _ _ t)) = VFun (\x -> return (vCtor ident (x : xs) t))
    vCtor ident xs _ = VCtorApp ident (V.fromList (reverse xs))

------------------------------------------------------------
-- The evaluation strategy for SharedTerms involves two memo tables:
-- The first, @memoClosed@, is precomputed and contains the result of
-- evaluating all _closed_ subterms. The same @memoClosed@ table is
-- used for evaluation under lambdas, since the meaning of a closed
-- term does not depend on the local variable context. The second memo
-- table is @memoLocal@, which caches the result of evaluating _open_
-- terms in the current variable context. It is created anew whenever
-- we descend under a lambda binder.

-- | Evaluator for shared terms.
evalSharedTerm :: (MonadIO m, MonadFix m, Show e) =>
                  SimulatorConfig m e -> SharedTerm s -> m (Value m e)
evalSharedTerm cfg t = do
  memoClosed <- mkMemoClosed cfg t
  evalOpen cfg memoClosed [] t

-- | Precomputing the memo table for closed subterms.
mkMemoClosed :: forall m e s. (MonadIO m, MonadFix m, Show e) =>
                SimulatorConfig m e -> SharedTerm s -> m (IntMap (Thunk m e))
mkMemoClosed cfg t =
  mfix $ \memoClosed -> do
    bref <- liftIO (newIORef IMap.empty)
    xref <- liftIO (newIORef IMap.empty)
    let go :: SharedTerm s -> m BitSet
        go (Unshared tf) = liftM freesTermF $ mapM go tf
        go (STApp i tf) = do
          bmemo <- liftIO (readIORef bref)
          case IMap.lookup i bmemo of
            Just b -> return b
            Nothing -> do
              b <- liftM freesTermF $ mapM go tf
              liftIO (modifyIORef' bref (IMap.insert i b))
              when (b == 0) $ do
                x <- delay (evalClosedTermF cfg memoClosed tf)
                liftIO (modifyIORef' xref (IMap.insert i x))
              return b
    _ <- go t
    liftIO (readIORef xref)

-- | Evaluator for closed terms, used to populate @memoClosed@.
evalClosedTermF :: (MonadIO m, MonadFix m, Show e) =>
                   SimulatorConfig m e
                -> IntMap (Thunk m e)
                -> TermF (SharedTerm s) -> m (Value m e)
evalClosedTermF cfg memoClosed tf = evalTermF cfg lam rec [] tf
  where
    lam = evalOpen cfg memoClosed
    rec (Unshared tf') = evalTermF cfg lam rec [] tf'
    rec (STApp i _) =
      case IMap.lookup i memoClosed of
        Just x -> force x
        Nothing -> fail "evalClosedTermF: internal error"

-- | Evaluator for open terms; parameterized by a precomputed table @memoClosed@.
evalOpen :: forall m e s. (MonadIO m, MonadFix m, Show e) =>
            SimulatorConfig m e
         -> IntMap (Thunk m e)
         -> [Thunk m e]
         -> SharedTerm s -> m (Value m e)
evalOpen cfg memoClosed env t =
  do ref <- liftIO (newIORef IMap.empty)
     go ref t
  where
    go :: IORef (IntMap (Value m e)) -> SharedTerm s -> m (Value m e)
    go ref (Unshared tf) = evalF ref tf
    go ref (STApp i tf) =
      case IMap.lookup i memoClosed of
        Just x -> force x
        Nothing -> do
          memoLocal <- liftIO (readIORef ref)
          case IMap.lookup i memoLocal of
            Just v -> return v
            Nothing -> do
              v <- evalF ref tf
              liftIO (modifyIORef' ref (IMap.insert i v))
              return v
    evalF :: IORef (IntMap (Value m e)) -> TermF (SharedTerm s) -> m (Value m e)
    evalF ref tf = evalTermF cfg (evalOpen cfg memoClosed) (go ref) env tf
