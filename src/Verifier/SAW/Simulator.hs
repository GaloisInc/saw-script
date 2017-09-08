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
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Evaluator for SAWCore terms, with lazy evaluation order.
-}

module Verifier.SAW.Simulator
  ( SimulatorConfig(..)
  , evalSharedTerm
  , evalGlobal
  , noExtCns
  , checkPrimitives
  ) where

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
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import Data.Traversable
import qualified Data.Vector as V
--import qualified Debug.Trace as Debug

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import Verifier.SAW.Simulator.Value

type Id = Identity

------------------------------------------------------------
-- Simulator configuration

data SimulatorConfig m b w i e =
  SimulatorConfig
  { simGlobal :: Ident -> m (Value m b w i e)
  , simExtCns :: VarIndex -> String -> Value m b w i e -> m (Value m b w i e)
  , simUninterpreted :: String -> Value m b w i e -> Maybe (m (Value m b w i e))
  }

------------------------------------------------------------
-- Evaluation of function definitions

{-# SPECIALIZE matchThunk :: Pat t -> Thunk Id b w i e -> Id (Maybe (Map Int (Thunk Id b w i e))) #-}
{-# SPECIALIZE matchThunk :: Pat t -> Thunk IO b w i e -> IO (Maybe (Map Int (Thunk IO b w i e))) #-}

-- | Pattern matching for values.
matchThunk :: Monad m => Pat t -> Thunk m b w i e -> m (Maybe (Map Int (Thunk m b w i e)))
matchThunk p x =
  case p of
    PVar _ i _  -> return $ Just (Map.singleton i x)
    PUnused _ _ -> return $ Just Map.empty
    PUnit       -> do v <- force x
                      case v of
                        VUnit -> matchThunks [] []
                        _ -> return Nothing
    PPair p1 p2 -> do v <- force x
                      case v of
                        VPair x1 x2 -> matchThunks [p1, p2] [x1, x2]
                        _ -> return Nothing
    PEmpty      -> do v <- force x
                      case v of
                        VEmpty -> matchThunks [] []
                        _ -> return Nothing
    PField p1 p2 p3 -> do v <- force x
                          case v of
                            VField x1 x2 x3 -> matchThunks [p1, p2, p3] [ready (VString x1), x2, ready x3]
                            _ -> return Nothing
    PCtor i ps  -> do v <- force x
                      case v of
                        VCtorApp s xv | i == s -> matchThunks ps (V.toList xv)
                        _                      -> return Nothing
    PString s   -> do v <- force x
                      case v of
                        VString s' | s == s' -> matchThunks [] []
                        _ -> return Nothing

{-# SPECIALIZE matchThunks :: [Pat t] -> [Thunk Id b w i e] -> Id (Maybe (Map Int (Thunk Id b w i e))) #-}
{-# SPECIALIZE matchThunks :: [Pat t] -> [Thunk IO b w i e] -> IO (Maybe (Map Int (Thunk IO b w i e))) #-}

-- | Simultaneous pattern matching for lists of values.
matchThunks :: Monad m => [Pat t] -> [Thunk m b w i e] -> m (Maybe (Map Int (Thunk m b w i e)))
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


{-# SPECIALIZE evalDef :: forall b w i e. (Term -> OpenValue Id b w i e) -> Def -> Id (Value Id b w i e) #-}
{-# SPECIALIZE evalDef :: forall b w i e. (Term -> OpenValue IO b w i e) -> Def -> IO (Value IO b w i e) #-}

-- | Evaluator for pattern-matching function definitions,
-- parameterized by an evaluator for right-hand sides.
evalDef :: forall m b w i e. Monad m =>
           (Term -> OpenValue m b w i e) -> Def -> m (Value m b w i e)
evalDef rec (Def ident NoQualifier _ eqns) = vFuns [] arity
  where
    arity :: Int
    arity = lengthDefEqn (head eqns)

    lengthDefEqn :: DefEqn -> Int
    lengthDefEqn (DefEqn ps _) = length ps

    vFuns :: [Thunk m b w i e] -> Int -> m (Value m b w i e)
    vFuns xs 0 = tryEqns eqns (reverse xs)
    vFuns xs n = return $ VFun (\x -> vFuns (x : xs) (n - 1))

    tryEqns :: [DefEqn] -> [Thunk m b w i e] -> m (Value m b w i e)
    tryEqns [] _ = fail $ "Pattern match failure: " ++ show ident
    tryEqns (eqn : eqns') xs =
      do mm <- tryEqn eqn xs
         case mm of
           Just m -> return m
           Nothing -> tryEqns eqns' xs

    tryEqn :: DefEqn -> [Thunk m b w i e] -> m (Maybe (Value m b w i e))
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
type OpenValue m b w i e = [Thunk m b w i e] -> m (Value m b w i e)

{-# SPECIALIZE evalTermF :: (Show e) => SimulatorConfig Id b w i e -> (Term -> OpenValue Id b w i e) -> (Term -> Id (Value Id b w i e)) -> TermF Term -> OpenValue Id b w i e #-}
{-# SPECIALIZE evalTermF :: (Show e) => SimulatorConfig IO b w i e -> (Term -> OpenValue IO b w i e) -> (Term -> IO (Value IO b w i e)) -> TermF Term -> OpenValue IO b w i e #-}

-- | Generic evaluator for TermFs.
evalTermF :: forall m b w i e. (MonadLazy m, MonadFix m, Show e) =>
             SimulatorConfig m b w i e          -- ^ Evaluator for global constants
          -> (Term -> OpenValue m b w i e)      -- ^ Evaluator for subterms under binders
          -> (Term -> m (Value m b w i e))      -- ^ Evaluator for subterms in the same bound variable context
          -> TermF Term -> OpenValue m b w i e
evalTermF cfg lam rec tf env =
  case tf of
    App t1 t2               -> do v <- rec t1
                                  x <- rec' t2
                                  apply v x
    Lambda _ _ t            -> return $ VFun (\x -> lam t (x : env))
    Pi _ t1 t2              -> do v <- rec t1
                                  return $ VPiType v (\x -> lam t2 (x : env))
    LocalVar i              -> force (env !! i)
    Constant i t ty         -> do v <- rec ty
                                  maybe (rec t) id (simUninterpreted cfg i v)
    FTermF ftf              ->
      case ftf of
        GlobalDef ident     -> simGlobal cfg ident
        UnitValue           -> return VUnit
        UnitType            -> return VUnitType
        PairValue x y       -> do tx <- rec' x
                                  ty <- rec' y
                                  return $ VPair tx ty
        PairType x y        -> do vx <- rec x
                                  vy <- rec y
                                  return $ VPairType vx vy
        PairLeft x          -> valPairLeft =<< rec x
        PairRight x         -> valPairRight =<< rec x
        EmptyValue          -> return VEmpty
        EmptyType           -> return VEmptyType
        FieldValue f x y    -> do VString s <- rec f
                                  tx <- rec' x
                                  vy <- rec y
                                  return $ VField s tx vy
        FieldType f x y     -> do VString s <- rec f
                                  vx <- rec x
                                  vy <- rec y
                                  return $ VFieldType s vx vy
        RecordSelector t k  -> do vt <- rec t
                                  VString s <- rec k
                                  valRecordSelect s vt
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
    rec' :: Term -> m (Thunk m b w i e)
    rec' = delay . rec


{-# SPECIALIZE evalTerm :: (Show e) => SimulatorConfig Id b w i e -> Term -> OpenValue Id b w i e #-}
{-# SPECIALIZE evalTerm :: (Show e) => SimulatorConfig IO b w i e -> Term -> OpenValue IO b w i e #-}

-- | Evaluator for unshared terms.
evalTerm :: (MonadLazy m, MonadFix m, Show e) =>
            SimulatorConfig m b w i e -> Term -> OpenValue m b w i e
evalTerm cfg t env = evalTermF cfg lam rec (unwrapTermF t) env
  where
    lam = evalTerm cfg
    rec t' = evalTerm cfg t' env

{-# SPECIALIZE evalTypedDef :: (Show e) => SimulatorConfig Id b w i e -> Def -> Id (Value Id b w i e) #-}
{-# SPECIALIZE evalTypedDef :: (Show e) => SimulatorConfig IO b w i e -> Def -> IO (Value IO b w i e) #-}

evalTypedDef :: (MonadLazy m, MonadFix m, Show e) =>
                SimulatorConfig m b w i e -> Def -> m (Value m b w i e)
evalTypedDef cfg = evalDef (evalTerm cfg)

{-# SPECIALIZE evalGlobal :: (Show e) => Module -> Map Ident (Value Id b w i e) -> (VarIndex -> String -> Value Id b w i e -> Id (Value Id b w i e)) -> (String -> Value Id b w i e -> Maybe (Id (Value Id b w i e))) -> Id (SimulatorConfig Id b w i e) #-}
{-# SPECIALIZE evalGlobal :: (Show e) => Module -> Map Ident (Value IO b w i e) -> (VarIndex -> String -> Value IO b w i e -> IO (Value IO b w i e)) -> (String -> Value IO b w i e -> Maybe (IO (Value IO b w i e))) -> IO (SimulatorConfig IO b w i e) #-}

evalGlobal :: forall m b w i e. (MonadLazy m, MonadFix m, Show e) =>
              Module -> Map Ident (Value m b w i e) ->
              (VarIndex -> String -> Value m b w i e -> m (Value m b w i e)) ->
              (String -> Value m b w i e -> Maybe (m (Value m b w i e))) ->
              m (SimulatorConfig m b w i e)
evalGlobal m0 prims extcns uninterpreted = do
   checkPrimitives m0 prims
   mfix $ \cfg -> do
     thunks <- mapM delay (globals cfg)
     return (SimulatorConfig (global thunks) extcns uninterpreted)
  where
    ms :: [Module]
    ms = m0 : Map.elems (m0^.moduleImports)

    global :: HashMap Ident (Thunk m b w i e) -> Ident -> m (Value m b w i e)
    global thunks ident =
      case HashMap.lookup ident thunks of
        Just v -> force v
        Nothing -> fail $ "Unimplemented global: " ++ show ident

    globals :: SimulatorConfig m b w i e -> HashMap Ident (m (Value m b w i e))
    globals cfg =
      HashMap.fromList $
      [ (ctorName ct, return (vCtor (ctorName ct) [] (ctorType ct))) |
        m <- ms, ct <- moduleCtors m ] ++
      [ (defIdent td, evalTypedDef cfg td) |
        m <- ms, td <- moduleDefs m, not (null (defEqs td)) ] ++
      Map.assocs (fmap return prims) -- Later mappings take precedence

    vCtor :: Ident -> [Thunk m b w i e] -> Term -> Value m b w i e
    vCtor ident xs (unwrapTermF -> (Pi _ _ t)) = VFun (\x -> return (vCtor ident (x : xs) t))
    vCtor ident xs _ = VCtorApp ident (V.fromList (reverse xs))

noExtCns :: Monad m => VarIndex -> String -> Value m b w i e -> m (Value m b w i e)
noExtCns _ name _ = fail $ "evalTermF ExtCns unimplemented (" ++ name ++ ")"


-- | Check that all the primitives declared in the given module
--   are implemented, and that terms with implementations are not
--   overridden.
checkPrimitives :: forall m b w i e. (MonadLazy m, MonadFix m, Show e)
                => Module
                -> Map Ident (Value m b w i e)
                -> m ()
checkPrimitives m0 prims = do
   -- FIXME this is downgraded to a warning temporarily while we work out a
   -- solution to issue GaloisInc/saw-script#48
   --   when (not $ null unimplementedPrims) (fail $ unimplementedMsg)
   -- (if null unimplementedPrims then id else Debug.trace (unimplementedMsg++"\n")) $
--   (if null overridePrims then id else Debug.trace (overrideMsg++"\n")) $
     return ()

  where _unimplementedMsg = unwords $
            ("WARNING unimplemented primitives:" : (map show unimplementedPrims))
        _overrideMsg = unwords $
            ("WARNING overridden definitions:" : (map show overridePrims))

        primSet = Set.fromList $ map defIdent $ allModulePrimitives m0
        defSet  = Set.fromList $ map defIdent $ allModuleActualDefs m0
        implementedPrims = Map.keysSet prims

        unimplementedPrims = Set.toList $ Set.difference primSet implementedPrims
        overridePrims = Set.toList $ Set.intersection defSet implementedPrims


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

{-# SPECIALIZE evalSharedTerm :: (Show e) => SimulatorConfig Id b w i e -> Term -> Id (Value Id b w i e) #-}
{-# SPECIALIZE evalSharedTerm :: (Show e) => SimulatorConfig IO b w i e -> Term -> IO (Value IO b w i e) #-}

-- | Evaluator for shared terms.
evalSharedTerm :: (MonadLazy m, MonadFix m, Show e) =>
                  SimulatorConfig m b w i e -> Term -> m (Value m b w i e)
evalSharedTerm cfg t = do
  memoClosed <- mkMemoClosed cfg t
  evalOpen cfg memoClosed t []

{-# SPECIALIZE mkMemoClosed :: (Show e) => SimulatorConfig Id b w i e -> Term -> Id (IntMap (Thunk Id b w i e)) #-}
{-# SPECIALIZE mkMemoClosed :: (Show e) => SimulatorConfig IO b w i e -> Term -> IO (IntMap (Thunk IO b w i e)) #-}

-- | Precomputing the memo table for closed subterms.
mkMemoClosed :: forall m b w i e. (MonadLazy m, MonadFix m, Show e) =>
                SimulatorConfig m b w i e -> Term -> m (IntMap (Thunk m b w i e))
mkMemoClosed cfg t =
  mfix $ \memoClosed -> mapM (delay . evalClosedTermF cfg memoClosed) subterms
  where
    -- | Map of all closed subterms of t.
    subterms :: IntMap (TermF Term)
    subterms = fmap fst $ IMap.filter ((== 0) . snd) $ State.execState (go t) IMap.empty

    go :: Term -> State.State (IntMap (TermF Term, BitSet)) BitSet
    go (Unshared tf) = freesTermF <$> traverse go tf
    go (STApp{ stAppIndex = i, stAppTermF = tf }) = do
      memo <- State.get
      case IMap.lookup i memo of
        Just (_, b) -> return b
        Nothing -> do
          b <- freesTermF <$> traverse go tf
          State.modify (IMap.insert i (tf, b))
          return b

{-# SPECIALIZE evalClosedTermF :: (Show e) => SimulatorConfig Id b w i e -> IntMap (Thunk Id b w i e) -> TermF Term -> Id (Value Id b w i e) #-}
{-# SPECIALIZE evalClosedTermF :: (Show e) => SimulatorConfig IO b w i e -> IntMap (Thunk IO b w i e) -> TermF Term -> IO (Value IO b w i e) #-}

-- | Evaluator for closed terms, used to populate @memoClosed@.
evalClosedTermF :: (MonadLazy m, MonadFix m, Show e) =>
                   SimulatorConfig m b w i e
                -> IntMap (Thunk m b w i e)
                -> TermF Term -> m (Value m b w i e)
evalClosedTermF cfg memoClosed tf = evalTermF cfg lam rec tf []
  where
    lam = evalOpen cfg memoClosed
    rec (Unshared tf') = evalTermF cfg lam rec tf' []
    rec (STApp{ stAppIndex = i }) =
      case IMap.lookup i memoClosed of
        Just x -> force x
        Nothing -> fail "evalClosedTermF: internal error"

{-# SPECIALIZE mkMemoLocal :: (Show e) => SimulatorConfig Id b w i e -> IntMap (Thunk Id b w i e) -> Term -> [Thunk Id b w i e] -> Id (IntMap (Thunk Id b w i e)) #-}
{-# SPECIALIZE mkMemoLocal :: (Show e) => SimulatorConfig IO b w i e -> IntMap (Thunk IO b w i e) -> Term -> [Thunk IO b w i e] -> IO (IntMap (Thunk IO b w i e)) #-}

-- | Precomputing the memo table for open subterms in the current context.
mkMemoLocal :: forall m b w i e. (MonadLazy m, MonadFix m, Show e) =>
               SimulatorConfig m b w i e -> IntMap (Thunk m b w i e) ->
               Term -> [Thunk m b w i e] -> m (IntMap (Thunk m b w i e))
mkMemoLocal cfg memoClosed t env = go memoClosed t
  where
    go :: IntMap (Thunk m b w i e) -> Term -> m (IntMap (Thunk m b w i e))
    go memo (Unshared tf) = goTermF memo tf
    go memo (STApp{ stAppIndex = i, stAppTermF = tf }) =
      case IMap.lookup i memo of
        Just _ -> return memo
        Nothing -> do
          memo' <- goTermF memo tf
          thunk <- delay (evalLocalTermF cfg memoClosed memo' tf env)
          return (IMap.insert i thunk memo')

    goTermF :: IntMap (Thunk m b w i e) -> TermF Term -> m (IntMap (Thunk m b w i e))
    goTermF memo tf =
      case tf of
        FTermF ftf      -> foldlM go memo ftf
        App t1 t2       -> do memo' <- go memo t1
                              go memo' t2
        Lambda _ t1 _   -> go memo t1
        Pi _ t1 _       -> go memo t1
        LocalVar _      -> return memo
        Constant _ t1 _ -> go memo t1

{-# SPECIALIZE evalLocalTermF :: (Show e) => SimulatorConfig Id b w i e -> IntMap (Thunk Id b w i e) -> IntMap (Thunk Id b w i e) -> TermF Term -> OpenValue Id b w i e #-}
{-# SPECIALIZE evalLocalTermF :: (Show e) => SimulatorConfig IO b w i e -> IntMap (Thunk IO b w i e) -> IntMap (Thunk IO b w i e) -> TermF Term -> OpenValue IO b w i e #-}

-- | Evaluator for open terms, used to populate @memoLocal@.
evalLocalTermF :: (MonadLazy m, MonadFix m, Show e) =>
                   SimulatorConfig m b w i e
                -> IntMap (Thunk m b w i e) -> IntMap (Thunk m b w i e)
                -> TermF Term -> OpenValue m b w i e
evalLocalTermF cfg memoClosed memoLocal tf0 env = evalTermF cfg lam rec tf0 env
  where
    lam = evalOpen cfg memoClosed
    rec (Unshared tf) = evalTermF cfg lam rec tf env
    rec (STApp{ stAppIndex = i }) =
      case IMap.lookup i memoLocal of
        Just x -> force x
        Nothing -> fail "evalLocalTermF: internal error"

{-# SPECIALIZE evalOpen :: Show e => SimulatorConfig Id b w i e -> IntMap (Thunk Id b w i e) -> Term -> OpenValue Id b w i e #-}
{-# SPECIALIZE evalOpen :: Show e => SimulatorConfig IO b w i e -> IntMap (Thunk IO b w i e) -> Term -> OpenValue IO b w i e #-}

-- | Evaluator for open terms; parameterized by a precomputed table @memoClosed@.
evalOpen :: forall m b w i e. (MonadLazy m, MonadFix m, Show e) =>
            SimulatorConfig m b w i e
         -> IntMap (Thunk m b w i e)
         -> Term -> OpenValue m b w i e
evalOpen cfg memoClosed t env = do
  memoLocal <- mkMemoLocal cfg memoClosed t env
  let eval :: Term -> m (Value m b w i e)
      eval (Unshared tf) = evalF tf
      eval (STApp{ stAppIndex = i, stAppTermF = tf }) =
        case IMap.lookup i memoLocal of
          Just x -> force x
          Nothing -> evalF tf
      evalF :: TermF Term -> m (Value m b w i e)
      evalF tf = evalTermF cfg (evalOpen cfg memoClosed) eval tf env
  eval t
