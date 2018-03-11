{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
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

import Verifier.SAW.Prelude.Constants

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import Verifier.SAW.Simulator.Value

type Id = Identity

type ThunkIn m l           = Thunk (WithM m l)
type OpenValueIn m l       = OpenValue (WithM m l)
type ValueIn m l           = Value (WithM m l)
type MValueIn m l          = MValue (WithM m l)
type SimulatorConfigIn m l = SimulatorConfig (WithM m l)

------------------------------------------------------------
-- Simulator configuration

data SimulatorConfig l =
  SimulatorConfig
  { simGlobal :: Ident -> MValue l
  , simExtCns :: VarIndex -> String -> Value l -> MValue l
  , simUninterpreted :: String -> Value l -> Maybe (MValue l)
  }

------------------------------------------------------------
-- Evaluation of function definitions

{-# SPECIALIZE
  matchThunk :: Pat -> ThunkIn Id l -> Id (Maybe (Map Int (ThunkIn Id l))) #-}
{-# SPECIALIZE
  matchThunk :: Pat -> ThunkIn IO l -> IO (Maybe (Map Int (ThunkIn IO l))) #-}

-- | Pattern matching for values.
matchThunk :: VMonad l => Pat -> Thunk l -> EvalM l (Maybe (Map Int (Thunk l)))
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
                        VNat 0 | i == preludeZeroIdent -> matchThunks ps []
                        VNat n | i == preludeSuccIdent ->
                          matchThunks ps [ready (VNat (n-1))]
                        _                      -> return Nothing
    PString s   -> do v <- force x
                      case v of
                        VString s' | s == s' -> matchThunks [] []
                        _ -> return Nothing

{-# SPECIALIZE
  matchThunks ::
    [Pat] -> [ThunkIn Id l] -> Id (Maybe (Map Int (ThunkIn Id l))) #-}
{-# SPECIALIZE
  matchThunks ::
    [Pat] -> [ThunkIn IO l] -> IO (Maybe (Map Int (ThunkIn IO l))) #-}

-- | Simultaneous pattern matching for lists of values.
matchThunks :: VMonad l =>
  [Pat] -> [Thunk l] -> EvalM l (Maybe (Map Int (Thunk l)))
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


{-# SPECIALIZE evalDef :: (Term -> OpenValueIn Id l) -> Def -> MValueIn Id l #-}
{-# SPECIALIZE evalDef :: (Term -> OpenValueIn IO l) -> Def -> MValueIn IO l #-}

-- | Evaluator for pattern-matching function definitions,
-- parameterized by an evaluator for right-hand sides.
evalDef :: forall l. VMonad l => (Term -> OpenValue l) -> Def -> MValue l
evalDef rec (Def ident NoQualifier _ eqns) = vFuns [] arity
  where
    arity :: Int
    arity = lengthDefEqn (head eqns)

    lengthDefEqn :: DefEqn -> Int
    lengthDefEqn (DefEqn ps _) = length ps

    vFuns :: [Thunk l] -> Int -> MValue l
    vFuns xs 0 = tryEqns eqns (reverse xs)
    vFuns xs n = return $ VFun (\x -> vFuns (x : xs) (n - 1))

    tryEqns :: [DefEqn] -> [Thunk l] -> MValue l
    tryEqns [] _ = fail $ "Pattern match failure: " ++ show ident
    tryEqns (eqn : eqns') xs =
      do mm <- tryEqn eqn xs
         case mm of
           Just m -> return m
           Nothing -> tryEqns eqns' xs

    tryEqn :: DefEqn -> [Thunk l] -> EvalM l (Maybe (Value l))
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
type OpenValue l = [Thunk l] -> MValue l

{-# SPECIALIZE
  evalTermF :: Show (Extra l) =>
    SimulatorConfigIn Id l ->
    (Term -> OpenValueIn Id l) ->
    (Term -> MValueIn Id l) ->
    TermF Term ->
    OpenValueIn Id l #-}

{-# SPECIALIZE
  evalTermF :: Show (Extra l) =>
    SimulatorConfigIn IO l ->
    (Term -> OpenValueIn IO l) ->
    (Term -> MValueIn IO l) ->
    TermF Term ->
    OpenValueIn IO l #-}

-- | Generic evaluator for TermFs.
evalTermF :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
             SimulatorConfig l          -- ^ Evaluator for global constants
          -> (Term -> OpenValue l)      -- ^ Evaluator for subterms under binders
          -> (Term -> MValue l)         -- ^ Evaluator for subterms in the same bound variable context
          -> TermF Term -> OpenValue l
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
    rec' :: Term -> EvalM l (Thunk l)
    rec' = delay . rec


{-# SPECIALIZE evalTerm ::
    Show (Extra l) => SimulatorConfigIn Id l -> Term -> OpenValueIn Id l #-}
{-# SPECIALIZE evalTerm ::
    Show (Extra l) => SimulatorConfigIn IO l -> Term -> OpenValueIn IO l #-}

-- | Evaluator for unshared terms.
evalTerm :: (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
            SimulatorConfig l -> Term -> OpenValue l
evalTerm cfg t env = evalTermF cfg lam rec (unwrapTermF t) env
  where
    lam = evalTerm cfg
    rec t' = evalTerm cfg t' env

{-# SPECIALIZE evalTypedDef ::
  Show (Extra l) => SimulatorConfigIn Id l -> Def -> MValueIn Id l #-}
{-# SPECIALIZE evalTypedDef ::
  Show (Extra l) => SimulatorConfigIn IO l -> Def -> MValueIn IO l #-}

evalTypedDef :: (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
                SimulatorConfig l -> Def -> MValue l
evalTypedDef cfg = evalDef (evalTerm cfg)

{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  Module ->
  Map Ident (ValueIn Id l) ->
  (VarIndex -> String -> ValueIn Id l -> MValueIn Id l) ->
  (String -> ValueIn Id l -> Maybe (MValueIn Id l)) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  Module ->
  Map Ident (ValueIn IO l) ->
  (VarIndex -> String -> ValueIn IO l -> MValueIn IO l) ->
  (String -> ValueIn IO l -> Maybe (MValueIn IO l)) ->
  IO (SimulatorConfigIn IO l) #-}
evalGlobal :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
              Module -> Map Ident (Value l) ->
              (VarIndex -> String -> Value l -> MValue l) ->
              (String -> Value l -> Maybe (EvalM l (Value l))) ->
              EvalM l (SimulatorConfig l)
evalGlobal m0 prims extcns uninterpreted = do
   checkPrimitives m0 prims
   mfix $ \cfg -> do
     thunks <- mapM delay (globals cfg)
     return (SimulatorConfig (global thunks) extcns uninterpreted)
  where
    ms :: [Module]
    ms = m0 : Map.elems (m0^.moduleImports)

    global :: HashMap Ident (Thunk l) -> Ident -> MValue l
    global thunks ident =
      case HashMap.lookup ident thunks of
        Just v -> force v
        Nothing -> fail $ "Unimplemented global: " ++ show ident

    globals :: SimulatorConfig l -> HashMap Ident (MValue l)
    globals cfg =
      HashMap.fromList $
      [ (ctorName ct, return (vCtor (ctorName ct) [] (ctorType ct))) |
        m <- ms, ct <- moduleCtors m ] ++
      [ (defIdent td, evalTypedDef cfg td) |
        m <- ms, td <- moduleDefs m, not (null (defEqs td)) ] ++
      Map.assocs (fmap return prims) -- Later mappings take precedence

    -- Convert a constructor to a value by creating a function that takes in one
    -- argument for each nested pi type of the constructor
    vCtor :: Ident -> [Thunk l] -> Term -> Value l
    vCtor ident xs (unwrapTermF -> (Pi _ _ t)) = VFun (\x -> return (vCtor ident (x : xs) t))
    vCtor ident xs _ = VCtorApp ident (V.fromList (reverse xs))

noExtCns :: VMonad l => VarIndex -> String -> Value l -> MValue l
noExtCns _ name _ = fail $ "evalTermF ExtCns unimplemented (" ++ name ++ ")"


-- | Check that all the primitives declared in the given module
--   are implemented, and that terms with implementations are not
--   overridden.
checkPrimitives :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l))
                => Module
                -> Map Ident (Value l)
                -> EvalM l ()
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

{-# SPECIALIZE evalSharedTerm ::
  Show (Extra l) => SimulatorConfigIn Id l -> Term -> MValueIn Id l #-}
{-# SPECIALIZE evalSharedTerm ::
  Show (Extra l) => SimulatorConfigIn IO l -> Term -> MValueIn IO l #-}

-- | Evaluator for shared terms.
evalSharedTerm :: (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
                  SimulatorConfig l -> Term -> MValue l
evalSharedTerm cfg t = do
  memoClosed <- mkMemoClosed cfg t
  evalOpen cfg memoClosed t []

{-# SPECIALIZE mkMemoClosed ::
  Show (Extra l) =>
  SimulatorConfigIn Id l -> Term -> Id (IntMap (ThunkIn Id l)) #-}
{-# SPECIALIZE mkMemoClosed ::
  Show (Extra l) =>
  SimulatorConfigIn IO l -> Term -> IO (IntMap (ThunkIn IO l)) #-}

-- | Precomputing the memo table for closed subterms.
mkMemoClosed :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
                SimulatorConfig l -> Term -> EvalM l (IntMap (Thunk l))
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

{-# SPECIALIZE evalClosedTermF ::
  Show (Extra l) =>
  SimulatorConfigIn Id l ->
  IntMap (ThunkIn Id l) ->
  TermF Term ->
  MValueIn Id l #-}
{-# SPECIALIZE evalClosedTermF ::
  Show (Extra l) =>
  SimulatorConfigIn IO l ->
  IntMap (ThunkIn IO l) ->
  TermF Term ->
  MValueIn IO l #-}

-- | Evaluator for closed terms, used to populate @memoClosed@.
evalClosedTermF :: (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
                   SimulatorConfig l
                -> IntMap (Thunk l)
                -> TermF Term -> MValue l
evalClosedTermF cfg memoClosed tf = evalTermF cfg lam rec tf []
  where
    lam = evalOpen cfg memoClosed
    rec (Unshared tf') = evalTermF cfg lam rec tf' []
    rec (STApp{ stAppIndex = i }) =
      case IMap.lookup i memoClosed of
        Just x -> force x
        Nothing -> fail "evalClosedTermF: internal error"

{-# SPECIALIZE mkMemoLocal ::
  Show (Extra l) =>
  SimulatorConfigIn Id l ->
  IntMap (ThunkIn Id l) ->
  Term ->
  [ThunkIn Id l] ->
  Id (IntMap (ThunkIn Id l)) #-}
{-# SPECIALIZE mkMemoLocal ::
  Show (Extra l) =>
  SimulatorConfigIn IO l ->
  IntMap (ThunkIn IO l) ->
  Term ->
  [ThunkIn IO l] ->
  IO (IntMap (ThunkIn IO l)) #-}

-- | Precomputing the memo table for open subterms in the current context.
mkMemoLocal :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
               SimulatorConfig l -> IntMap (Thunk l) ->
               Term -> [Thunk l] -> EvalM l (IntMap (Thunk l))
mkMemoLocal cfg memoClosed t env = go memoClosed t
  where
    go :: IntMap (Thunk l) -> Term -> EvalM l (IntMap (Thunk l))
    go memo (Unshared tf) = goTermF memo tf
    go memo (STApp{ stAppIndex = i, stAppTermF = tf }) =
      case IMap.lookup i memo of
        Just _ -> return memo
        Nothing -> do
          memo' <- goTermF memo tf
          thunk <- delay (evalLocalTermF cfg memoClosed memo' tf env)
          return (IMap.insert i thunk memo')

    goTermF :: IntMap (Thunk l) -> TermF Term -> EvalM l (IntMap (Thunk l))
    goTermF memo tf =
      case tf of
        FTermF ftf      -> foldlM go memo ftf
        App t1 t2       -> do memo' <- go memo t1
                              go memo' t2
        Lambda _ t1 _   -> go memo t1
        Pi _ t1 _       -> go memo t1
        LocalVar _      -> return memo
        Constant _ t1 _ -> go memo t1

{-# SPECIALIZE evalLocalTermF ::
  Show (Extra l) =>
  SimulatorConfigIn Id l ->
  IntMap (ThunkIn Id l) ->
  IntMap (ThunkIn Id l) ->
  TermF Term ->
  OpenValueIn Id l #-}
{-# SPECIALIZE evalLocalTermF ::
  Show (Extra l) =>
  SimulatorConfigIn IO l ->
  IntMap (ThunkIn IO l) ->
  IntMap (ThunkIn IO l) ->
  TermF Term ->
  OpenValueIn IO l #-}
-- | Evaluator for open terms, used to populate @memoLocal@.
evalLocalTermF :: (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
                   SimulatorConfig l
                -> IntMap (Thunk l) -> IntMap (Thunk l)
                -> TermF Term -> OpenValue l
evalLocalTermF cfg memoClosed memoLocal tf0 env = evalTermF cfg lam rec tf0 env
  where
    lam = evalOpen cfg memoClosed
    rec (Unshared tf) = evalTermF cfg lam rec tf env
    rec (STApp{ stAppIndex = i }) =
      case IMap.lookup i memoLocal of
        Just x -> force x
        Nothing -> fail "evalLocalTermF: internal error"

{-# SPECIALIZE evalOpen ::
  Show (Extra l) =>
  SimulatorConfigIn Id l ->
  IntMap (ThunkIn Id l) ->
  Term ->
  OpenValueIn Id l #-}

{-# SPECIALIZE evalOpen ::
  Show (Extra l) =>
  SimulatorConfigIn IO l ->
  IntMap (ThunkIn IO l) ->
  Term ->
  OpenValueIn IO l #-}

-- | Evaluator for open terms; parameterized by a precomputed table @memoClosed@.
evalOpen :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
            SimulatorConfig l
         -> IntMap (Thunk l)
         -> Term -> OpenValue l
evalOpen cfg memoClosed t env = do
  memoLocal <- mkMemoLocal cfg memoClosed t env
  let eval :: Term -> MValue l
      eval (Unshared tf) = evalF tf
      eval (STApp{ stAppIndex = i, stAppTermF = tf }) =
        case IMap.lookup i memoLocal of
          Just x -> force x
          Nothing -> evalF tf
      evalF :: TermF Term -> MValue l
      evalF tf = evalTermF cfg (evalOpen cfg memoClosed) eval tf env
  eval t
