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
type TValueIn m l          = TValue (WithM m l)
type MValueIn m l          = MValue (WithM m l)
type SimulatorConfigIn m l = SimulatorConfig (WithM m l)

panic :: String -> a
panic msg = Panic.panic "Verifier.SAW.Simulator" [msg]

------------------------------------------------------------
-- Simulator configuration

data SimulatorConfig l =
  SimulatorConfig
  { simPrimitive :: Ident -> MValue l
  -- ^ Interpretation of 'Primitive' terms.
  , simExtCns :: TermF Term -> ExtCns (TValue l) -> MValue l
  -- ^ Interpretation of 'ExtCns' terms.
  , simConstant :: TermF Term -> ExtCns (TValue l) -> Maybe (MValue l)
  -- ^ Interpretation of 'Constant' terms. 'Nothing' indicates that
  -- the body of the constant should be evaluated. 'Just' indicates
  -- that the constant's definition should be overridden.
  , simCtorApp :: Ident -> Maybe (MValue l)
  -- ^ Interpretation of 'Constant' terms. 'Nothing' indicates that
  -- the constructor is treated as normal. 'Just' replaces the
  -- constructor with a custom implementation.
  , simModMap :: ModuleMap
  }

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
evalTermF :: forall l. (VMonadLazy l, Show (Extra l)) =>
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
    Pi _ t1 t2              -> do v <- toTValue <$> recEval t1
                                  return $ TValue $ VPiType v (\x -> toTValue <$> lam t2 (x : env))
    LocalVar i              -> force (env !! i)
    Constant ec t           -> do ec' <- traverse (fmap toTValue . recEval) ec
                                  maybe (recEval t) id (simConstant cfg tf ec')
    FTermF ftf              ->
      case ftf of
        Primitive ec ->
          do ec' <- traverse (fmap toTValue . recEval) ec
             case ecName ec' of
               ModuleIdentifier ident -> simPrimitive cfg ident
               _ -> simExtCns cfg tf ec'
        UnitValue           -> return VUnit
        UnitType            -> return $ TValue VUnitType
        PairValue x y       -> do tx <- recEvalDelay x
                                  ty <- recEvalDelay y
                                  return $ VPair tx ty
        PairType x y        -> do vx <- toTValue <$> recEval x
                                  vy <- toTValue <$> recEval y
                                  return $ TValue $ VPairType vx vy
        PairLeft x          -> valPairLeft =<< recEval x
        PairRight x         -> valPairRight =<< recEval x
        CtorApp ident ps ts -> do ps' <- mapM recEvalDelay ps
                                  ts' <- mapM recEvalDelay ts
                                  case simCtorApp cfg ident of
                                    Just mv ->
                                      do v <- mv
                                         foldM apply v (ps' ++ ts')
                                    Nothing ->
                                      pure $ VCtorApp ident (V.fromList (ps' ++ ts'))
        DataTypeApp i ps ts -> TValue . VDataType i <$> mapM recEval (ps ++ ts)
        RecursorApp _d ps p_ret cs_fs _ixs arg ->
          do ps_th <- mapM recEvalDelay ps
             p_ret_th <- recEvalDelay p_ret
             cs_fs_th <- mapM (\(c,f) -> (c,) <$> recEvalDelay f) cs_fs
             arg_v <- recEval arg
             evalRecursorApp (simModMap cfg) lam ps_th p_ret_th cs_fs_th arg_v
        RecordType elem_tps ->
          TValue . VRecordType <$> traverse (traverse (fmap toTValue . recEval)) elem_tps
        RecordValue elems   ->
          VRecordValue <$> mapM (\(fld,t) -> (fld,) <$> recEvalDelay t) elems
        RecordProj t fld    -> recEval t >>= flip valRecordProj fld
        Sort s              -> return $ TValue (VSort s)
        NatLit n            -> return $ VNat n
        ArrayValue _ tv     -> liftM VVector $ mapM recEvalDelay tv
        StringLit s         -> return $ VString s
        ExtCns ec           -> do ec' <- traverse (fmap toTValue . recEval) ec
                                  simExtCns cfg tf ec'
  where
    recEvalDelay :: Term -> EvalM l (Thunk l)
    recEvalDelay = delay . recEval


{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (ValueIn Id l) ->
  (ExtCns (TValueIn Id l) -> MValueIn Id l) ->
  (ExtCns (TValueIn Id l) -> Maybe (MValueIn Id l)) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (ValueIn IO l) ->
  (ExtCns (TValueIn IO l) -> MValueIn IO l) ->
  (ExtCns (TValueIn IO l) -> Maybe (MValueIn IO l)) ->
  IO (SimulatorConfigIn IO l) #-}
evalGlobal :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
              ModuleMap -> Map Ident (Value l) ->
              (ExtCns (TValue l) -> MValue l) ->
              (ExtCns (TValue l) -> Maybe (EvalM l (Value l))) ->
              EvalM l (SimulatorConfig l)
evalGlobal modmap prims extcns uninterpreted =
  evalGlobal' modmap prims (const extcns) (const uninterpreted)

{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (ValueIn Id l) ->
  (TermF Term -> ExtCns (TValueIn Id l) -> MValueIn Id l) ->
  (TermF Term -> ExtCns (TValueIn Id l) -> Maybe (MValueIn Id l)) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (ValueIn IO l) ->
  (TermF Term -> ExtCns (TValueIn IO l) -> MValueIn IO l) ->
  (TermF Term -> ExtCns (TValueIn IO l) -> Maybe (MValueIn IO l)) ->
  IO (SimulatorConfigIn IO l) #-}
-- | A variant of 'evalGlobal' that lets the uninterpreted function
-- symbol and external-constant callbacks have access to the 'TermF'.
evalGlobal' ::
  forall l. (VMonadLazy l, Show (Extra l)) =>
  ModuleMap ->
  -- | Implementations of 'Primitive' terms, plus overrides for 'Constant' and 'CtorApp' terms
  Map Ident (Value l) ->
  -- | Implementations of ExtCns terms
  (TermF Term -> ExtCns (TValue l) -> MValue l) ->
  -- | Overrides for Constant terms (e.g. uninterpreted functions)
  (TermF Term -> ExtCns (TValue l) -> Maybe (MValue l)) ->
  EvalM l (SimulatorConfig l)
evalGlobal' modmap prims extcns constant =
  do checkPrimitives modmap prims
     return (SimulatorConfig primitive extcns constant' ctors modmap)
  where
    constant' :: TermF Term -> ExtCns (TValue l) -> Maybe (MValue l)
    constant' tf ec =
      case constant tf ec of
        Just v -> Just v
        Nothing ->
          case ecName ec of
            ModuleIdentifier ident -> pure <$> Map.lookup ident prims
            _ -> Nothing

    ctors :: Ident -> Maybe (MValue l)
    ctors ident = pure <$> Map.lookup ident prims

    primitive :: Ident -> MValue l
    primitive ident =
      case Map.lookup ident prims of
        Just v -> pure v
        Nothing -> panic $ "Unimplemented global: " ++ show ident

-- | Check that all the primitives declared in the given module
--   are implemented, and that terms with implementations are not
--   overridden.
checkPrimitives :: forall l. (VMonadLazy l, Show (Extra l))
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

evalRecursorApp _modmap _lam _ps _p_ret _cs_fs (VBVToNat _ _bv) =
  panic $ "evalRecursorApp: VBVToNat!"

evalRecursorApp _modmap _lam _ps _p_ret _cs_fs (VIntToNat _i) =
  panic $ "evalRecursorApp: VIntToNat!"

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
evalClosedTermF :: (VMonadLazy l, Show (Extra l)) =>
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
mkMemoLocal :: forall l. (VMonadLazy l, Show (Extra l)) =>
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
evalLocalTermF :: (VMonadLazy l, Show (Extra l)) =>
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
evalOpen :: forall l. (VMonadLazy l, Show (Extra l)) =>
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
