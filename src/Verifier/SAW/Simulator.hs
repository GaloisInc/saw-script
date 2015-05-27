{-# LANGUAGE CPP #-}
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

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif
import Control.Lens ((^.))
import Control.Monad (foldM, liftM)
import Control.Monad.Fix (MonadFix(mfix))
import Control.Monad.Identity (Identity)
import qualified Control.Monad.State as State
import Data.Foldable (foldlM)
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

type Id = Identity

------------------------------------------------------------
-- Simulator configuration

data SimulatorConfig m b w e =
  SimulatorConfig
  { simGlobal :: Ident -> m (Value m b w e)
  , simExtCns :: VarIndex -> String -> Value m b w e -> m (Value m b w e)
  , simUninterpreted :: String -> Value m b w e -> Maybe (m (Value m b w e))
  }

------------------------------------------------------------
-- Evaluation of function definitions

{-# SPECIALIZE matchThunk :: Pat t -> Thunk Id b w e -> Id (Maybe (Map Int (Thunk Id b w e))) #-}
{-# SPECIALIZE matchThunk :: Pat t -> Thunk IO b w e -> IO (Maybe (Map Int (Thunk IO b w e))) #-}

-- | Pattern matching for values.
matchThunk :: Monad m => Pat t -> Thunk m b w e -> m (Maybe (Map Int (Thunk m b w e)))
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

{-# SPECIALIZE matchThunks :: [Pat t] -> [Thunk Id b w e] -> Id (Maybe (Map Int (Thunk Id b w e))) #-}
{-# SPECIALIZE matchThunks :: [Pat t] -> [Thunk IO b w e] -> IO (Maybe (Map Int (Thunk IO b w e))) #-}

-- | Simultaneous pattern matching for lists of values.
matchThunks :: Monad m => [Pat t] -> [Thunk m b w e] -> m (Maybe (Map Int (Thunk m b w e)))
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


{-# SPECIALIZE evalDef :: forall b w e n t. Show n => (t -> OpenValue Id b w e) -> GenericDef n t -> Id (Value Id b w e) #-}
{-# SPECIALIZE evalDef :: forall b w e n t. Show n => (t -> OpenValue IO b w e) -> GenericDef n t -> IO (Value IO b w e) #-}

-- | Evaluator for pattern-matching function definitions,
-- parameterized by an evaluator for right-hand sides.
evalDef :: forall m b w e n t. (Monad m, Show n) =>
           (t -> OpenValue m b w e) -> GenericDef n t -> m (Value m b w e)
evalDef rec (Def ident NoQualifier _ eqns) = vFuns [] arity
  where
    arity :: Int
    arity = lengthDefEqn (head eqns)
    lengthDefEqn :: DefEqn t -> Int
    lengthDefEqn (DefEqn ps _) = length ps
    vFuns :: [Thunk m b w e] -> Int -> m (Value m b w e)
    vFuns xs 0 = tryEqns eqns (reverse xs)
    vFuns xs n = return $ VFun (\x -> vFuns (x : xs) (n - 1))
    tryEqns :: [DefEqn t] -> [Thunk m b w e] -> m (Value m b w e)
    tryEqns [] _ = fail $ "Pattern match failure: " ++ show ident
    tryEqns (eqn : eqns') xs =
      do mm <- tryEqn eqn xs
         case mm of
           Just m -> return m
           Nothing -> tryEqns eqns' xs
    tryEqn :: DefEqn t -> [Thunk m b w e] -> m (Maybe (Value m b w e))
    tryEqn (DefEqn ps rhs) xs =
      do minst <- matchThunks ps xs
         case minst of
           Nothing -> return Nothing
           Just inst -> let env = reverse (Map.elems inst) in liftM Just (rec rhs env)

evalDef _ (Def ident PrimQualifier _ _) = fail $ unwords ["attempted to evaluate primitive", show ident]
evalDef _ (Def ident AxiomQualifier _ _) = fail $ unwords ["attempted to evaluate axiom", show ident]


------------------------------------------------------------
-- Evaluation of terms

-- | Meaning of an open term, parameterized by environment of bound variables
type OpenValue m b w e = [Thunk m b w e] -> m (Value m b w e)

{-# SPECIALIZE evalTermF :: (Show t, Termlike t, Show e) => SimulatorConfig Id b w e -> (t -> OpenValue Id b w e) -> (t -> Id (Value Id b w e)) -> TermF t -> OpenValue Id b w e #-}
{-# SPECIALIZE evalTermF :: (Show t, Termlike t, Show e) => SimulatorConfig IO b w e -> (t -> OpenValue IO b w e) -> (t -> IO (Value IO b w e)) -> TermF t -> OpenValue IO b w e #-}

-- | Generic evaluator for TermFs.
evalTermF :: forall t m b w e. (Show t, MonadLazy m, MonadFix m, Termlike t, Show e) =>
             SimulatorConfig m b w e                  -- ^ Evaluator for global constants
          -> (t -> OpenValue m b w e)                 -- ^ Evaluator for subterms under binders
          -> (t -> m (Value m b w e))                 -- ^ Evaluator for subterms in the same bound variable context
          -> TermF t -> OpenValue m b w e
evalTermF cfg lam rec tf env =
  case tf of
    App t1 t2               -> do v <- rec t1
                                  x <- rec' t2
                                  apply v x
    Lambda _ _ t            -> return $ VFun (\x -> lam t (x : env))
    Pi _ t1 t2              -> do v <- rec t1
                                  return $ VPiType v (\x -> lam t2 (x : env))
    Let ds t                -> do env' <- mfix $ \env' -> do
                                            xs <- mapM (delay . evalDef (\t' ys -> lam t' (ys ++ env'))) (reverse ds)
                                            return (xs ++ env)
                                  lam t env'
    LocalVar i              -> force (env !! i)
    Constant i t ty         -> do v <- rec ty
                                  maybe (rec t) id (simUninterpreted cfg i v)
    FTermF ftf              ->
      case ftf of
        GlobalDef ident     -> simGlobal cfg ident
        TupleValue ts       -> liftM VTuple $ mapM rec' (V.fromList ts)
        TupleType ts        -> liftM VTupleType $ mapM rec ts
        TupleSelector t j   -> valTupleSelect j =<< rec t
        RecordValue tm      -> liftM VRecord $ mapM rec' tm
        RecordSelector t k  -> valRecordSelect k =<< rec t
        RecordType tm       -> liftM VRecordType $ mapM rec tm
        CtorApp ident ts    -> do v <- simGlobal cfg ident
                                  xs <- mapM rec' ts
                                  foldM apply v xs
        DataTypeApp i ts    -> liftM (VDataType i) $ mapM rec ts
        Sort {}             -> return VType
        NatLit n            -> return $ VNat n
        ArrayValue _ tv     -> liftM VVector $ mapM rec' tv
        FloatLit float      -> return $ VFloat float
        DoubleLit double    -> return $ VDouble double
        StringLit s         -> return $ VString s
        ExtCns ec           -> do v <- rec (ecType ec)
                                  simExtCns cfg (ecVarIndex ec) (ecName ec) v
  where
    rec' :: t -> m (Thunk m b w e)
    rec' = delay . rec


{-# SPECIALIZE evalTerm :: (Show e) => SimulatorConfig Id b w e -> Term -> OpenValue Id b w e #-}
{-# SPECIALIZE evalTerm :: (Show e) => SimulatorConfig IO b w e -> Term -> OpenValue IO b w e #-}

-- | Evaluator for unshared terms.
evalTerm :: (MonadLazy m, MonadFix m, Show e) =>
            SimulatorConfig m b w e -> Term -> OpenValue m b w e
evalTerm cfg (Term tf) env = evalTermF cfg lam rec tf env
  where
    lam = evalTerm cfg
    rec t = evalTerm cfg t env

{-# SPECIALIZE evalTypedDef :: (Show e) => SimulatorConfig Id b w e -> TypedDef -> Id (Value Id b w e) #-}
{-# SPECIALIZE evalTypedDef :: (Show e) => SimulatorConfig IO b w e -> TypedDef -> IO (Value IO b w e) #-}

evalTypedDef :: (MonadLazy m, MonadFix m, Show e) =>
                SimulatorConfig m b w e -> TypedDef -> m (Value m b w e)
evalTypedDef cfg = evalDef (evalTerm cfg)

{-# SPECIALIZE evalGlobal :: (Show e) => Module -> Map Ident (Value Id b w e) -> (String -> Value Id b w e -> Maybe (Id (Value Id b w e))) -> Id (SimulatorConfig Id b w e) #-}
{-# SPECIALIZE evalGlobal :: (Show e) => Module -> Map Ident (Value IO b w e) -> (String -> Value IO b w e -> Maybe (IO (Value IO b w e))) -> IO (SimulatorConfig IO b w e) #-}

evalGlobal :: forall m b w e. (MonadLazy m, MonadFix m, Show e) =>
              Module -> Map Ident (Value m b w e) ->
              (String -> Value m b w e -> Maybe (m (Value m b w e))) ->
              m (SimulatorConfig m b w e)
evalGlobal m0 prims uninterpreted =
  mfix $ \cfg -> do
    thunks <- mapM delay (globals cfg)
    return (SimulatorConfig (global thunks) noExtCns uninterpreted)
  where
    ms :: [Module]
    ms = m0 : Map.elems (m0^.moduleImports)

    global :: HashMap Ident (Thunk m b w e) -> Ident -> m (Value m b w e)
    global thunks ident =
      case HashMap.lookup ident thunks of
        Just v -> force v
        Nothing -> fail $ "Unimplemented global: " ++ show ident

    globals :: SimulatorConfig m b w e -> HashMap Ident (m (Value m b w e))
    globals cfg =
      HashMap.fromList $
      [ (ctorName ct, return (vCtor (ctorName ct) [] (ctorType ct))) |
        m <- ms, ct <- moduleCtors m ] ++
      [ (defIdent td, evalTypedDef cfg td) |
        m <- ms, td <- moduleDefs m, not (null (defEqs td)) ] ++
      Map.assocs (fmap return prims) -- Later mappings take precedence

    vCtor :: Ident -> [Thunk m b w e] -> Term -> Value m b w e
    vCtor ident xs (Term (Pi _ _ t)) = VFun (\x -> return (vCtor ident (x : xs) t))
    vCtor ident xs _ = VCtorApp ident (V.fromList (reverse xs))

noExtCns :: Monad m => VarIndex -> String -> Value m b w e -> m (Value m b w e)
noExtCns _ name _ = fail $ "evalTermF ExtCns unimplemented (" ++ name ++ ")"

----------------------------------------------------------------------
-- The evaluation strategy for SharedTerms involves two memo tables:
-- The first, @memoClosed@, is precomputed and contains the result of
-- evaluating all _closed_ subterms. The same @memoClosed@ table is
-- used for evaluation under lambdas, since the meaning of a closed
-- term does not depend on the local variable context. The second memo
-- table is @memoLocal@, which additionally includes the result of
-- evaluating _open_ terms in the current variable context. It is
-- reinitialized to @memoClosed@ whenever we descend under a lambda
-- binder.

{-# SPECIALIZE evalSharedTerm :: (Show e) => SimulatorConfig Id b w e -> SharedTerm s -> Id (Value Id b w e) #-}
{-# SPECIALIZE evalSharedTerm :: (Show e) => SimulatorConfig IO b w e -> SharedTerm s -> IO (Value IO b w e) #-}

-- | Evaluator for shared terms.
evalSharedTerm :: (MonadLazy m, MonadFix m, Show e) =>
                  SimulatorConfig m b w e -> SharedTerm s -> m (Value m b w e)
evalSharedTerm cfg t = do
  memoClosed <- mkMemoClosed cfg t
  evalOpen cfg memoClosed t []

{-# SPECIALIZE mkMemoClosed :: (Show e) => SimulatorConfig Id b w e -> SharedTerm s -> Id (IntMap (Thunk Id b w e)) #-}
{-# SPECIALIZE mkMemoClosed :: (Show e) => SimulatorConfig IO b w e -> SharedTerm s -> IO (IntMap (Thunk IO b w e)) #-}

-- | Precomputing the memo table for closed subterms.
mkMemoClosed :: forall m b w e s. (MonadLazy m, MonadFix m, Show e) =>
                SimulatorConfig m b w e -> SharedTerm s -> m (IntMap (Thunk m b w e))
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

{-# SPECIALIZE evalClosedTermF :: (Show e) => SimulatorConfig Id b w e -> IntMap (Thunk Id b w e) -> TermF (SharedTerm s) -> Id (Value Id b w e) #-}
{-# SPECIALIZE evalClosedTermF :: (Show e) => SimulatorConfig IO b w e -> IntMap (Thunk IO b w e) -> TermF (SharedTerm s) -> IO (Value IO b w e) #-}

-- | Evaluator for closed terms, used to populate @memoClosed@.
evalClosedTermF :: (MonadLazy m, MonadFix m, Show e) =>
                   SimulatorConfig m b w e
                -> IntMap (Thunk m b w e)
                -> TermF (SharedTerm s) -> m (Value m b w e)
evalClosedTermF cfg memoClosed tf = evalTermF cfg lam rec tf []
  where
    lam = evalOpen cfg memoClosed
    rec (Unshared tf') = evalTermF cfg lam rec tf' []
    rec (STApp i _) =
      case IMap.lookup i memoClosed of
        Just x -> force x
        Nothing -> fail "evalClosedTermF: internal error"

{-# SPECIALIZE mkMemoLocal :: (Show e) => SimulatorConfig Id b w e -> IntMap (Thunk Id b w e) -> SharedTerm s -> [Thunk Id b w e] -> Id (IntMap (Thunk Id b w e)) #-}
{-# SPECIALIZE mkMemoLocal :: (Show e) => SimulatorConfig IO b w e -> IntMap (Thunk IO b w e) -> SharedTerm s -> [Thunk IO b w e] -> IO (IntMap (Thunk IO b w e)) #-}

-- | Precomputing the memo table for open subterms in the current context.
mkMemoLocal :: forall m b w e s. (MonadLazy m, MonadFix m, Show e) =>
               SimulatorConfig m b w e -> IntMap (Thunk m b w e) ->
               SharedTerm s -> [Thunk m b w e] -> m (IntMap (Thunk m b w e))
mkMemoLocal cfg memoClosed t env = go memoClosed t
  where
    go :: IntMap (Thunk m b w e) -> SharedTerm s -> m (IntMap (Thunk m b w e))
    go memo (Unshared tf) = goTermF memo tf
    go memo (STApp i tf) =
      case IMap.lookup i memo of
        Just _ -> return memo
        Nothing -> do
          memo' <- goTermF memo tf
          thunk <- delay (evalLocalTermF cfg memoClosed memo' tf env)
          return (IMap.insert i thunk memo')

    goTermF :: IntMap (Thunk m b w e) -> TermF (SharedTerm s) -> m (IntMap (Thunk m b w e))
    goTermF memo tf =
      case tf of
        FTermF ftf      -> foldlM go memo ftf
        App t1 t2       -> do memo' <- go memo t1
                              go memo' t2
        Lambda _ t1 _   -> go memo t1
        Pi _ t1 _       -> go memo t1
        Let _ _         -> return memo
        LocalVar _      -> return memo
        Constant _ t1 _ -> go memo t1

{-# SPECIALIZE evalLocalTermF :: (Show e) => SimulatorConfig Id b w e -> IntMap (Thunk Id b w e) -> IntMap (Thunk Id b w e) -> TermF (SharedTerm s) -> OpenValue Id b w e #-}
{-# SPECIALIZE evalLocalTermF :: (Show e) => SimulatorConfig IO b w e -> IntMap (Thunk IO b w e) -> IntMap (Thunk IO b w e) -> TermF (SharedTerm s) -> OpenValue IO b w e #-}

-- | Evaluator for open terms, used to populate @memoLocal@.
evalLocalTermF :: (MonadLazy m, MonadFix m, Show e) =>
                   SimulatorConfig m b w e
                -> IntMap (Thunk m b w e) -> IntMap (Thunk m b w e)
                -> TermF (SharedTerm s) -> OpenValue m b w e
evalLocalTermF cfg memoClosed memoLocal tf0 env = evalTermF cfg lam rec tf0 env
  where
    lam = evalOpen cfg memoClosed
    rec (Unshared tf) = evalTermF cfg lam rec tf env
    rec (STApp i _) =
      case IMap.lookup i memoLocal of
        Just x -> force x
        Nothing -> fail "evalLocalTermF: internal error"

{-# SPECIALIZE evalOpen :: Show e => SimulatorConfig Id b w e -> IntMap (Thunk Id b w e) -> SharedTerm s -> OpenValue Id b w e #-}
{-# SPECIALIZE evalOpen :: Show e => SimulatorConfig IO b w e -> IntMap (Thunk IO b w e) -> SharedTerm s -> OpenValue IO b w e #-}

-- | Evaluator for open terms; parameterized by a precomputed table @memoClosed@.
evalOpen :: forall m b w e s. (MonadLazy m, MonadFix m, Show e) =>
            SimulatorConfig m b w e
         -> IntMap (Thunk m b w e)
         -> SharedTerm s -> OpenValue m b w e
evalOpen cfg memoClosed t env = do
  memoLocal <- mkMemoLocal cfg memoClosed t env
  let eval :: SharedTerm s -> m (Value m b w e)
      eval (Unshared tf) = evalF tf
      eval (STApp i tf) =
        case IMap.lookup i memoLocal of
          Just x -> force x
          Nothing -> evalF tf
      evalF :: TermF (SharedTerm s) -> m (Value m b w e)
      evalF tf = evalTermF cfg (evalOpen cfg memoClosed) eval tf env
  eval t
