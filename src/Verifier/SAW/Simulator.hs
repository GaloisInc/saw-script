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

import Control.Applicative ((<$>), (*>))
import Control.Lens ((^.))
import Control.Monad (foldM, liftM)
import Control.Monad.Fix (MonadFix(mfix))
import qualified Control.Monad.State as State
import Data.Foldable (traverse_)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
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
matchThunk :: Monad m => Pat t -> Thunk m e -> m (Maybe (Map Int (Thunk m e)))
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
matchThunks :: Monad m => [Pat t] -> [Thunk m e] -> m (Maybe (Map Int (Thunk m e)))
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
evalDef :: forall m e n t. (Monad m, Show n) =>
           (t -> OpenValue m e) -> GenericDef n t -> m (Value m e)
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
           Just inst -> let env = reverse (Map.elems inst) in liftM Just (rec rhs env)

------------------------------------------------------------
-- Evaluation of terms

-- | Meaning of an open term, parameterized by environment of bound variables
type OpenValue m e = [Thunk m e] -> m (Value m e)

-- | Generic evaluator for TermFs.
evalTermF :: forall t m e. (Show t, MonadLazy m, MonadFix m, Termlike t, Show e) =>
             SimulatorConfig m e                  -- ^ Evaluator for global constants
          -> (t -> OpenValue m e)                 -- ^ Evaluator for subterms under binders
          -> (t -> m (Value m e))                 -- ^ Evaluator for subterms in the same bound variable context
          -> TermF t -> OpenValue m e
evalTermF cfg lam rec tf env =
  case tf of
    App t1 t2               -> do v <- rec t1
                                  x <- rec' t2
                                  apply v x
    Lambda _ _ t            -> return $ VFun (\x -> lam t (x : env))
    Pi {}                   -> return $ VType
    Let ds t                -> do env' <- mfix $ \env' -> do
                                            xs <- mapM (delay . evalDef (\t' ys -> lam t' (ys ++ env'))) (reverse ds)
                                            return (xs ++ env)
                                  lam t env'
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
evalTerm :: (MonadLazy m, MonadFix m, Show e) =>
            SimulatorConfig m e -> Term -> OpenValue m e
evalTerm cfg (Term tf) env = evalTermF cfg lam rec tf env
  where
    lam = evalTerm cfg
    rec t = evalTerm cfg t env

evalTypedDef :: (MonadLazy m, MonadFix m, Show e) =>
                SimulatorConfig m e -> TypedDef -> m (Value m e)
evalTypedDef cfg = evalDef (evalTerm cfg)

evalGlobal :: forall m e. (MonadLazy m, MonadFix m, Show e) =>
              Module -> Map Ident (Value m e) ->
              (forall t. (Termlike t, Show t) => Ident -> t -> Maybe (m (Value m e))) ->
              SimulatorConfig m e
evalGlobal m0 prims uninterpreted = cfg
  where
    cfg :: SimulatorConfig m e
    cfg = SimulatorConfig global uninterpreted

    ms :: [Module]
    ms = m0 : Map.elems (m0^.moduleImports)

    global :: Ident -> m (Value m e)
    global ident =
      case HashMap.lookup ident globals of
        Just v -> v
        Nothing -> fail $ "Unimplemented global: " ++ show ident

    globals :: HashMap Ident (m (Value m e))
    globals =
      HashMap.fromList $
      [ (ctorName ct, return (vCtor (ctorName ct) [] (ctorType ct))) |
        m <- ms, ct <- moduleCtors m ] ++
      [ (defIdent td, evalTypedDef cfg td) |
        m <- ms, td <- moduleDefs m, not (null (defEqs td)) ] ++
      Map.assocs (fmap return prims) -- Later mappings take precedence

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
evalSharedTerm :: (MonadLazy m, MonadFix m, Show e) =>
                  SimulatorConfig m e -> SharedTerm s -> m (Value m e)
evalSharedTerm cfg t = do
  memoClosed <- mkMemoClosed cfg t
  evalOpen cfg memoClosed t []

-- | Precomputing the memo table for closed subterms.
mkMemoClosed :: forall m e s. (MonadLazy m, MonadFix m, Show e) =>
                SimulatorConfig m e -> SharedTerm s -> m (IntMap (Thunk m e))
mkMemoClosed cfg t =
  mfix $ \memoClosed -> mapM (delay . evalClosedTermF cfg memoClosed) subterms
  where
    -- | Map of all closed subterms of t.
    subterms :: IntMap (TermF (SharedTerm s))
    subterms = fmap fst $ IMap.filter ((== 0) . snd) $ State.execState (go t) IMap.empty

    go :: SharedTerm s -> State.State (IntMap (TermF (SharedTerm s), BitSet)) BitSet
    go (Unshared tf) = freesTermF <$> traverse go tf
    go (STApp i tf) = do
      memo <- State.get
      case IMap.lookup i memo of
        Just (_, b) -> return b
        Nothing -> do
          b <- freesTermF <$> traverse go tf
          State.modify (IMap.insert i (tf, b))
          return b

-- | Evaluator for closed terms, used to populate @memoClosed@.
evalClosedTermF :: (MonadLazy m, MonadFix m, Show e) =>
                   SimulatorConfig m e
                -> IntMap (Thunk m e)
                -> TermF (SharedTerm s) -> m (Value m e)
evalClosedTermF cfg memoClosed tf = evalTermF cfg lam rec tf []
  where
    lam = evalOpen cfg memoClosed
    rec (Unshared tf') = evalTermF cfg lam rec tf' []
    rec (STApp i _) =
      case IMap.lookup i memoClosed of
        Just x -> force x
        Nothing -> fail "evalClosedTermF: internal error"

-- | Precomputing the memo table for open subterms in the current context.
mkMemoLocal :: forall m e s. (MonadLazy m, MonadFix m, Show e) =>
               SimulatorConfig m e -> IntMap (Thunk m e) ->
               SharedTerm s -> [Thunk m e] -> m (IntMap (Thunk m e))
mkMemoLocal cfg memoClosed t env =
  mfix $ \memoLocal -> mapM (\tf -> delay (evalLocalTermF cfg memoClosed memoLocal tf env)) subterms
  where
    -- | Map of all shared subterms in the same local variable context.
    subterms :: IntMap (TermF (SharedTerm s))
    subterms = State.execState (go t) IMap.empty

    go :: SharedTerm s -> State.State (IntMap (TermF (SharedTerm s))) ()
    go (Unshared tf) = goTermF tf
    go (STApp i tf) = do
      memo <- State.get
      case IMap.lookup i memo of
        Just _ -> return ()
        Nothing -> do
          goTermF tf
          State.modify (IMap.insert i tf)

    goTermF :: TermF (SharedTerm s) -> State.State (IntMap (TermF (SharedTerm s))) ()
    goTermF tf =
      case tf of
        FTermF ftf      -> traverse_ go ftf
        App t1 t2       -> go t1 *> go t2
        Lambda _ t1 _   -> go t1
        Pi _ t1 _       -> go t1
        Let _ _         -> return ()
        LocalVar _      -> return ()
        Constant _ t1 _ -> go t1

-- | Evaluator for open terms, used to populate @memoLocal@.
evalLocalTermF :: (MonadLazy m, MonadFix m, Show e) =>
                   SimulatorConfig m e
                -> IntMap (Thunk m e) -> IntMap (Thunk m e)
                -> TermF (SharedTerm s) -> OpenValue m e
evalLocalTermF cfg memoClosed memoLocal tf0 env = evalTermF cfg lam rec tf0 env
  where
    lam = evalOpen cfg memoClosed
    rec (Unshared tf) = evalTermF cfg lam rec tf env
    rec (STApp i _) =
      case IMap.lookup i memoClosed of
        Just x -> force x
        Nothing ->
          case IMap.lookup i memoLocal of
            Just x -> force x
            Nothing -> fail "evalLocalTermF: internal error"

-- | Evaluator for open terms; parameterized by a precomputed table @memoClosed@.
evalOpen :: forall m e s. (MonadLazy m, MonadFix m, Show e) =>
            SimulatorConfig m e
         -> IntMap (Thunk m e)
         -> SharedTerm s -> OpenValue m e
evalOpen cfg memoClosed t env = do
  memoLocal <- mkMemoLocal cfg memoClosed t env
  let eval :: SharedTerm s -> m (Value m e)
      eval (Unshared tf) = evalF tf
      eval (STApp i tf) =
        case IMap.lookup i memoClosed of
          Just x -> force x
          Nothing -> do
            case IMap.lookup i memoLocal of
              Just x -> force x
              Nothing -> evalF tf
      evalF :: TermF (SharedTerm s) -> m (Value m e)
      evalF tf = evalTermF cfg (evalOpen cfg memoClosed) eval tf env
  eval t
