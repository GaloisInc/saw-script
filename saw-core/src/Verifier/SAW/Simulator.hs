{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

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
  , evalGlobal'
  , checkPrimitives
  ) where

import Prelude hiding (mapM)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif
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

import qualified Verifier.SAW.Utils as Panic (panic)

import Verifier.SAW.Module
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import Verifier.SAW.Simulator.Value

type Id = Identity

type ThunkIn m l           = Thunk (WithM m l)
type OpenValueIn m l       = OpenValue (WithM m l)
type ValueIn m l           = Value (WithM m l)
type MValueIn m l          = MValue (WithM m l)
type SimulatorConfigIn m l = SimulatorConfig (WithM m l)

panic :: String -> a
panic msg = Panic.panic "Verifier.SAW.Simulator" [msg]

------------------------------------------------------------
-- Simulator configuration

data SimulatorConfig l =
  SimulatorConfig
  { simGlobal :: Ident -> MValue l
  , simExtCns :: TermF Term -> ExtCns (Value l) -> MValue l
  , simUninterpreted :: TermF Term -> ExtCns (Value l) -> Maybe (MValue l)
  , simModMap :: ModuleMap
  }

------------------------------------------------------------
-- Evaluation of function definitions

{-# SPECIALIZE evalDef :: (Term -> OpenValueIn Id l) -> Def -> MValueIn Id l #-}
{-# SPECIALIZE evalDef :: (Term -> OpenValueIn IO l) -> Def -> MValueIn IO l #-}

-- | Evaluator for pattern-matching function definitions,
-- parameterized by an evaluator for right-hand sides.
evalDef :: forall l. VMonad l => (Term -> OpenValue l) -> Def -> MValue l
evalDef recEval (Def _ NoQualifier _ (Just body)) = recEval body []
evalDef _ (Def ident NoQualifier _ Nothing) =
  panic $ unwords ["attempted to evaluate definition with no body", show ident]
evalDef _ (Def ident PrimQualifier _ _) =
  panic $ unwords ["attempted to evaluate primitive", show ident]
evalDef _ (Def ident AxiomQualifier _ _) =
  panic $ unwords ["attempted to evaluate axiom", show ident]


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
evalTermF cfg lam recEval tf env =
  case tf of
    App t1 t2               -> do v <- recEval t1
                                  x <- recEvalDelay t2
                                  apply v x
    Lambda _ _ t            -> return $ VFun (\x -> lam t (x : env))
    Pi _ t1 t2              -> do v <- recEval t1
                                  return $ VPiType v (\x -> lam t2 (x : env))
    LocalVar i              -> force (env !! i)
    Constant ec t           -> do ec' <- traverse recEval ec
                                  maybe (recEval t) id (simUninterpreted cfg tf ec')
    FTermF ftf              ->
      case ftf of
        GlobalDef ident     -> simGlobal cfg ident
        UnitValue           -> return VUnit
        UnitType            -> return VUnitType
        PairValue x y       -> do tx <- recEvalDelay x
                                  ty <- recEvalDelay y
                                  return $ VPair tx ty
        PairType x y        -> do vx <- recEval x
                                  vy <- recEval y
                                  return $ VPairType vx vy
        PairLeft x          -> valPairLeft =<< recEval x
        PairRight x         -> valPairRight =<< recEval x
        CtorApp ident ps ts -> do v <- simGlobal cfg ident
                                  ps' <- mapM recEvalDelay ps
                                  ts' <- mapM recEvalDelay ts
                                  foldM apply v (ps' ++ ts')
        DataTypeApp i ps ts -> liftM (VDataType i) $ mapM recEval (ps ++ ts)
        RecursorApp _d ps p_ret cs_fs _ixs arg ->
          do ps_th <- mapM recEvalDelay ps
             p_ret_th <- recEvalDelay p_ret
             cs_fs_th <- mapM (\(c,f) -> (c,) <$> recEvalDelay f) cs_fs
             arg_v <- recEval arg
             evalRecursorApp (simModMap cfg) lam ps_th p_ret_th cs_fs_th arg_v
        RecordType elem_tps ->
          VRecordType <$> mapM (\(fld,t) -> (fld,) <$> recEval t) elem_tps
        RecordValue elems   ->
          VRecordValue <$> mapM (\(fld,t) -> (fld,) <$> recEvalDelay t) elems
        RecordProj t fld    -> recEval t >>= flip valRecordProj fld
        Sort {}             -> return VType
        NatLit n            -> return $ VNat (toInteger n)
        ArrayValue _ tv     -> liftM VVector $ mapM recEvalDelay tv
        StringLit s         -> return $ VString s
        ExtCns ec           -> do ec' <- traverse recEval ec
                                  simExtCns cfg tf ec'
  where
    recEvalDelay :: Term -> EvalM l (Thunk l)
    recEvalDelay = delay . recEval


{-# SPECIALIZE evalTerm ::
    Show (Extra l) => SimulatorConfigIn Id l -> Term -> OpenValueIn Id l #-}
{-# SPECIALIZE evalTerm ::
    Show (Extra l) => SimulatorConfigIn IO l -> Term -> OpenValueIn IO l #-}

-- | Evaluator for unshared terms.
evalTerm :: (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
            SimulatorConfig l -> Term -> OpenValue l
evalTerm cfg t env = evalTermF cfg lam recEval (unwrapTermF t) env
  where
    lam = evalTerm cfg
    recEval t' = evalTerm cfg t' env

{-# SPECIALIZE evalTypedDef ::
  Show (Extra l) => SimulatorConfigIn Id l -> Def -> MValueIn Id l #-}
{-# SPECIALIZE evalTypedDef ::
  Show (Extra l) => SimulatorConfigIn IO l -> Def -> MValueIn IO l #-}

evalTypedDef :: (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
                SimulatorConfig l -> Def -> MValue l
evalTypedDef cfg = evalDef (evalTerm cfg)

{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (ValueIn Id l) ->
  (ExtCns (ValueIn Id l) -> MValueIn Id l) ->
  (ExtCns (ValueIn Id l) -> Maybe (MValueIn Id l)) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (ValueIn IO l) ->
  (ExtCns (ValueIn IO l) -> MValueIn IO l) ->
  (ExtCns (ValueIn IO l) -> Maybe (MValueIn IO l)) ->
  IO (SimulatorConfigIn IO l) #-}
evalGlobal :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
              ModuleMap -> Map Ident (Value l) ->
              (ExtCns (Value l) -> MValue l) ->
              (ExtCns (Value l) -> Maybe (EvalM l (Value l))) ->
              EvalM l (SimulatorConfig l)
evalGlobal modmap prims extcns uninterpreted =
  evalGlobal' modmap prims (const extcns) (const uninterpreted)

{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (ValueIn Id l) ->
  (TermF Term -> ExtCns (ValueIn Id l) -> MValueIn Id l) ->
  (TermF Term -> ExtCns (ValueIn Id l) -> Maybe (MValueIn Id l)) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (ValueIn IO l) ->
  (TermF Term -> ExtCns (ValueIn IO l) -> MValueIn IO l) ->
  (TermF Term -> ExtCns (ValueIn IO l) -> Maybe (MValueIn IO l)) ->
  IO (SimulatorConfigIn IO l) #-}
-- | A variant of 'evalGlobal' that lets the uninterpreted function
-- symbol and external-constant callbacks have access to the 'TermF'.
evalGlobal' ::
  forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
  ModuleMap -> Map Ident (Value l) ->
  (TermF Term -> ExtCns (Value l) -> MValue l) ->
  (TermF Term -> ExtCns (Value l) -> Maybe (EvalM l (Value l))) ->
  EvalM l (SimulatorConfig l)
evalGlobal' modmap prims extcns uninterpreted = do
   checkPrimitives modmap prims
   mfix $ \cfg -> do
     thunks <- mapM delay (globals cfg)
     return (SimulatorConfig (global thunks) extcns uninterpreted modmap)
  where
    ms :: [Module]
    ms = HashMap.elems modmap

    global :: HashMap Ident (Thunk l) -> Ident -> MValue l
    global thunks ident =
      case HashMap.lookup ident thunks of
        Just v -> force v
        Nothing -> panic $ "Unimplemented global: " ++ show ident

    globals :: SimulatorConfig l -> HashMap Ident (MValue l)
    globals cfg =
      HashMap.fromList $
      [ (ctorName ct, return (vCtor (ctorName ct) [] (ctorType ct))) |
        m <- ms, ct <- moduleCtors m ] ++
      [ (defIdent td, evalTypedDef cfg td) |
        m <- ms, td <- moduleDefs m, defBody td /= Nothing ] ++
      Map.assocs (fmap return prims) -- Later mappings take precedence

    -- Convert a constructor to a value by creating a function that takes in one
    -- argument for each nested pi type of the constructor
    vCtor :: Ident -> [Thunk l] -> Term -> Value l
    vCtor ident xs (unwrapTermF -> (Pi _ _ t)) = VFun (\x -> return (vCtor ident (x : xs) t))
    vCtor ident xs _ = VCtorApp ident (V.fromList (reverse xs))

-- | Check that all the primitives declared in the given module
--   are implemented, and that terms with implementations are not
--   overridden.
checkPrimitives :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l))
                => ModuleMap
                -> Map Ident (Value l)
                -> EvalM l ()
checkPrimitives modmap prims = do
   -- FIXME this is downgraded to a warning temporarily while we work out a
   -- solution to issue GaloisInc/saw-script#48
   --   when (not $ null unimplementedPrims) (panic $ unimplementedMsg)
   -- (if null unimplementedPrims then id else Debug.trace (unimplementedMsg++"\n")) $
--   (if null overridePrims then id else Debug.trace (overrideMsg++"\n")) $
     return ()

  where _unimplementedMsg = unwords $
            ("WARNING unimplemented primitives:" : (map show unimplementedPrims))
        _overrideMsg = unwords $
            ("WARNING overridden definitions:" : (map show overridePrims))

        primSet = Set.fromList $ map defIdent $ allModulePrimitives modmap
        defSet  = Set.fromList $ map defIdent $ allModuleActualDefs modmap
        implementedPrims = Map.keysSet prims

        unimplementedPrims = Set.toList $ Set.difference primSet implementedPrims
        overridePrims = Set.toList $ Set.intersection defSet implementedPrims


-- | Evaluate a recursor application given a recursive way to evaluate terms,
-- the current 'RecursorInfo' structure, and thunks for the @p_ret@, eliminators
-- for the current inductive type, and the value being pattern-matched
evalRecursorApp :: (VMonad l, Show (Extra l)) =>
                   ModuleMap -> (Term -> OpenValue l) ->
                   [Thunk l] -> Thunk l -> [(Ident, Thunk l)] -> Value l ->
                   MValue l
evalRecursorApp modmap lam ps p_ret cs_fs (VCtorApp c all_args)
  | Just ctor <- findCtorInMap modmap c
  , Just dt <- findDataTypeInMap modmap (ctorDataTypeName ctor)
  = do elims <-
         mapM (\c' -> case lookup (ctorName c') cs_fs of
                  Just elim -> return elim
                  Nothing ->
                    panic ("evalRecursorApp: internal error: "
                          ++ "constructor not found in its own datatype: "
                          ++ show c')) $
         dtCtors dt
       let args = drop (length ps) $ V.toList all_args
       lam (ctorIotaReduction ctor) (reverse $ ps ++ [p_ret] ++ elims ++ args)
evalRecursorApp _ _ _ _ _ (VCtorApp c _) =
  panic $ ("evalRecursorApp: could not find info for constructor: " ++ show c)
evalRecursorApp modmap lam ps p_ret cs_fs (VNat 0) =
  evalRecursorApp modmap lam ps p_ret cs_fs (VCtorApp "Prelude.Zero" V.empty)
evalRecursorApp modmap lam ps p_ret cs_fs (VNat i) =
  evalRecursorApp modmap lam ps p_ret cs_fs
  (VCtorApp "Prelude.Succ" (V.singleton $ ready $ VNat $ i-1))
evalRecursorApp _modmap _lam _ps _p_ret _cs_fs (VToNat _bv) =
  panic $ "evalRecursorApp: VToNat!"
evalRecursorApp _ _ _ _ _ v =
  panic $ "evalRecursorApp: non-constructor value: " ++ show v


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
    subterms = fmap fst $ IMap.filter ((== emptyBitSet) . snd) $ State.execState (go t) IMap.empty

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
evalClosedTermF cfg memoClosed tf = evalTermF cfg lam recEval tf []
  where
    lam = evalOpen cfg memoClosed
    recEval (Unshared tf') = evalTermF cfg lam recEval tf' []
    recEval (STApp{ stAppIndex = i }) =
      case IMap.lookup i memoClosed of
        Just x -> force x
        Nothing -> panic "evalClosedTermF: internal error"

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
        Constant _ t1   -> go memo t1

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
evalLocalTermF cfg memoClosed memoLocal tf0 env = evalTermF cfg lam recEval tf0 env
  where
    lam = evalOpen cfg memoClosed
    recEval (Unshared tf) = evalTermF cfg lam recEval tf env
    recEval (STApp{ stAppIndex = i }) =
      case IMap.lookup i memoLocal of
        Just x -> force x
        Nothing -> panic "evalLocalTermF: internal error"

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
