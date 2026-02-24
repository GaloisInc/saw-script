{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

{- |
Module      : SAWCore.Simulator
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Evaluator for SAWCore terms, with lazy evaluation order.
-}

module SAWCore.Simulator
  ( SimulatorConfig(..)
  , evalSharedTerm
  , evalGlobal
  , evalGlobal'
  , checkPrimitives
  , defaultPrimHandler
  ) where

import Prelude hiding (mapM)

import Control.Monad (liftM, void)
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Fix (MonadFix(mfix))
import Control.Monad.Identity (Identity)
import qualified Control.Monad.State as State
import Data.Foldable (foldlM)
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Traversable
import GHC.Stack

import SAWCore.Panic (panic)
import SAWCore.Module
  ( allModuleActualDefs
  , allModulePrimitives
  , ctorNumParams
  , ctorNumArgs
  , defName
  , dtNumIndices
  , dtNumParams
  , lookupVarIndexInMap
  , resolvedNameType
  , requireNameInMap
  , Ctor(..)
  , CtorArg(..)
  , CtorArgStruct(..)
  , Def(..)
  , ModuleMap
  , ResolvedName(..)
  )
import SAWCore.Name
import SAWCore.SharedTerm

import SAWCore.Simulator.Value
import SAWCore.Term.Functor
import qualified SAWCore.Simulator.Prims as Prims

type Id = Identity

type ThunkIn m l           = Thunk (WithM m l)
type OpenValueIn m l       = OpenValue (WithM m l)
--type ValueIn m l           = Value (WithM m l)
type PrimIn m l            = Prims.Prim (WithM m l)
type TValueIn m l          = TValue (WithM m l)
type MValueIn m l          = MValue (WithM m l)
type SimulatorConfigIn m l = SimulatorConfig (WithM m l)

------------------------------------------------------------
-- Simulator configuration

data SimulatorConfig l =
  SimulatorConfig
  { simPrimitive :: Name -> MValue l
  -- ^ Interpretation of 'Primitive' terms.
  , simVariable :: Term -> VarName -> TValue l -> MValue l
  -- ^ Interpretation of free 'Variable' terms.
  , simConstant :: Name -> TValue l -> Maybe (MValue l)
  -- ^ Interpretation of 'Constant' terms. 'Nothing' indicates that
  -- the body of the constant should be evaluated. 'Just' indicates
  -- that the constant's definition should be overridden.
  , simRecursor :: Name -> Sort -> Maybe (MValue l)
  -- ^ Interpretation of 'Recursor' terms. 'Nothing' indicates that
  -- the generic recursor implementation should be used, while 'Just'
  -- indicates that the recursor should be overridden.
  , simModMap :: ModuleMap
  , simLazyMux :: VBool l -> MValue l -> MValue l -> MValue l
  }

------------------------------------------------------------
-- Evaluation of terms

type Env l = IntMap (Thunk l) -- indexed by VarIndex
type EnvIn m l = Env (WithM m l)

-- | Meaning of an open term, parameterized by environment of bound variables
type OpenValue l = Env l -> MValue l

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
    App t1 t2               -> recEval t1 >>= \case
                                 VFun f ->
                                   do x <- recEvalDelay t2
                                      f x
                                 _ -> panic "evalTermF" ["Expected VFun"]
    Lambda nm _tp t         -> pure $ VFun (\x -> lam t (IntMap.insert (vnIndex nm) x env))
    Pi nm t1 t2             -> do v <- evalType t1
                                  body <-
                                    if IntSet.member (vnIndex nm) (freeVars t2) then
                                      pure (VDependentPi (\x -> toTValue <$> lam t2 (IntMap.insert (vnIndex nm) x env)))
                                    else
                                      VNondependentPi . toTValue <$> lam t2 env
                                  return $ TValue $ VPiType v body

    Constant nm             -> do let r = requireNameInMap nm (simModMap cfg)
                                  ty' <- evalType (resolvedNameType r)
                                  case simConstant cfg nm ty' of
                                    Just override -> override
                                    Nothing ->
                                      case r of
                                        ResolvedCtor ctor ->
                                          ctorValue nm (ctorMuxability ctor) (ctorNumParams ctor) (ctorNumArgs ctor)
                                        ResolvedDataType dt ->
                                          dtValue nm (dtNumParams dt) (dtNumIndices dt)
                                        ResolvedDef d ->
                                          case defBody d of
                                            Just t -> recEval t
                                            Nothing -> simPrimitive cfg nm

    Variable nm tp          -> case IntMap.lookup (vnIndex nm) env of
                                 Just x -> force x
                                 Nothing ->
                                   do tp' <- evalType tp
                                      simVariable cfg tp nm tp'
    FTermF ftf              ->
      case ftf of
        UnitValue           -> return VUnit

        UnitType            -> return $ TValue VUnitType

        PairValue x y       -> do tx <- recEvalDelay x
                                  ty <- recEvalDelay y
                                  return $ VPair tx ty

        PairType x y        -> do vx <- evalType x
                                  vy <- evalType y
                                  return $ TValue $ VPairType vx vy

        PairLeft x          -> recEval x >>= \case
                                 VPair l _r -> force l
                                 _ -> panic "evalTermF" ["Expected VPair"]

        PairRight x         -> recEval x >>= \case
                                 VPair _l r -> force r
                                 _ -> panic "evalTermF" ["Expected VPair"]

        Recursor r ->
          case simRecursor cfg (recursorDataType r) (recursorSort r) of
            Just v -> v
            Nothing ->
              do let dname = recursorDataType r
                 let nparams = recursorNumParams r
                 let nixs = recursorNumIxs r
                 let cnames = recursorCtorOrder r
                 vFunList nparams $ \_ps_thunks ->
                   pure $ VFun $ \_motive ->
                   vFunList (length cnames) $ \elim_thunks ->
                   do let es = Map.fromList (zip (map nameIndex cnames) elim_thunks)
                      let vrec = VRecursor dname nixs es
                      vFunList nixs (\_ixs -> pure (evalRecursor vrec))

        Sort s _h           -> return $ TValue (VSort s)

        ArrayValue _ tv     -> liftM VVector $ mapM recEvalDelay tv

        StringLit s         -> return $ VString s
  where
    evalType :: Term -> EvalM l (TValue l)
    evalType t = toTValue <$> recEval t

    toTValue :: HasCallStack => Value l -> TValue l
    toTValue (TValue x) = x
    toTValue t = panic "evalTermF / toTValue" ["Not a type value: " <> Text.pack (show t)]

    evalRecursor :: VRecursor l -> Value l
    evalRecursor vrec@(VRecursor d _nixs ps_fs) =
      vStrictFun $ \argv ->
      case evalConstructor argv of
        Just (ctor, args)
          | Just elim <- Map.lookup (nameIndex (ctorName ctor)) ps_fs ->
              do elimv <- force elim
                 reduceRecursor (evalRecursor vrec) elimv args (ctorArgStruct ctor)

          | otherwise ->
              panic "evalTermF / evalRecursor"
              ["Could not find info for constructor: " <> toAbsoluteName (nameInfo (ctorName ctor))]
        Nothing ->
          case argv of
            VCtorMux branches ->
              do alts <- traverse (evalCtorMuxBranch vrec) (IntMap.assocs branches)
                 combineAlts alts
            VBVToNat{} ->
              panic "evalTerF / evalRecursor"
              ["Unsupported symbolic recursor argument of type Nat"]
            _ ->
              panic "evalTermF / evalRecursor"
              ["Expected constructor for datatype: " <> toAbsoluteName (nameInfo d)]

    evalCtorMuxBranch ::
      VRecursor l ->
      (VarIndex, (VBool l, Muxability, [Thunk l])) ->
      EvalM l (VBool l, EvalM l (Value l))
    evalCtorMuxBranch r (i, (p, _m, args)) =
      case r of
        VRecursor _d _nixs ps_fs ->
          case (lookupVarIndexInMap i (simModMap cfg), Map.lookup i ps_fs) of
            (Just (ResolvedCtor ctor), Just elim) ->
              do elimv <- force elim
                 pure (p, reduceRecursor (evalRecursor r) elimv args (ctorArgStruct ctor))
            _ -> panic "evalTermF / evalCtorMuxBranch"
                 ["could not find info for constructor with index: " <> Text.pack (show i)]

    combineAlts :: [(VBool l, EvalM l (Value l))] -> EvalM l (Value l)
    combineAlts [] = panic "evalTermF / combineAlts" ["no alternatives"]
    combineAlts [(_, x)] = x
    combineAlts ((p, x) : alts) = simLazyMux cfg p x (combineAlts alts)

    evalConstructor :: Value l -> Maybe (Ctor, [Thunk l])
    evalConstructor (VCtorApp c _dep _ps args) =
      case lookupVarIndexInMap (nameIndex c) (simModMap cfg) of
        Just (ResolvedCtor ctor) -> Just (ctor, args)
        _ -> Nothing
    evalConstructor _ =
       Nothing

    recEvalDelay :: Term -> EvalM l (Thunk l)
    recEvalDelay = delay . recEval

    ctorValue :: Name -> Muxability -> Int -> Int -> MValue l
    ctorValue nm m i j =
      vFunList i $ \params ->
      vFunList j $ \args ->
      pure $ VCtorApp nm m params args

    dtValue :: Name -> Int -> Int -> MValue l
    dtValue nm i j =
      vStrictFunList i $ \params ->
      vStrictFunList j $ \idxs ->
      pure $ TValue $ VDataType nm params idxs

-- | Compute whether the 'Ctor' has a type that allows argument-wise
-- muxing.
ctorMuxability :: Ctor -> Muxability
ctorMuxability ctor =
  if nondep IntSet.empty (ctorArgs cas) then Muxable else NonMuxable
  where
    cas :: CtorArgStruct
    cas = ctorArgStruct ctor
    nondep :: IntSet -> [(VarName, CtorArg)] -> Bool
    nondep vs [] = all (IntSet.disjoint vs . freeVars) (ctorIndices cas)
    nondep vs ((vn, arg) : args) =
      IntSet.disjoint vs (freesCtorArg arg) &&
      nondep (IntSet.insert (vnIndex vn) vs) args

-- | Compute the set of 'VarIndex'es of free variables in a 'CtorArg'.
freesCtorArg :: CtorArg -> IntSet
freesCtorArg (ConstArg t) = freeVars t
freesCtorArg (RecursiveArg zs is) = go zs
  where
    go :: [(VarName, Term)] -> IntSet
    go [] = IntSet.unions (map freeVars is)
    go ((v, t) : ts) = freeVars t <> IntSet.delete (vnIndex v) (go ts)

-- | Evaluate a recursor applied to a specific data constructor.
reduceRecursor ::
  forall l. (VMonadLazy l, Show (Extra l)) =>
  Value l {- ^ recursor function expecting datatype argument -} ->
  Value l {- ^ constructor eliminator function -} ->
  [Thunk l] {- ^ constructor arguments -} ->
  CtorArgStruct {- ^ constructor formal argument descriptor -} ->
  MValue l
reduceRecursor r elim c_args argstruct = go elim c_args (map snd (ctorArgs argstruct))
  where
    go :: Value l -> [Thunk l] -> [CtorArg] -> MValue l
    go e [] [] = pure e
    go e (x : xs) (arg : args) =
      case arg of
        ConstArg _ ->
          do e' <- apply e x
             go e' xs args
        RecursiveArg zs _ixs ->
          do e1 <- apply e x
             recx <- delay (mk_rec_arg (length zs) x)
             e2 <- apply e1 recx
             go e2 xs args
    go _ _ _ = panic "reduceRecursor" ["Wrong number of constructor arguments"]

    -- For a recursive argument, we need a value of the form
    -- > \z1 .. zk -> r (x z1 .. zk)
    mk_rec_arg :: Int -> Thunk l -> MValue l
    mk_rec_arg k x =
      vFunList k $ \zs ->
      do x_zs <- delay (force x >>= \v -> applyAll v zs)
         apply r x_zs


{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn Id l) ->
  (VarName -> TValueIn Id l -> MValueIn Id l) ->
  (Name -> TValueIn Id l -> Maybe (MValueIn Id l)) ->
  (Name -> Sort -> Maybe (MValueIn Id l)) ->
  (Name -> Text -> [ThunkIn Id l] -> MValueIn Id l) ->
  (VBool (WithM Id l) -> MValueIn Id l -> MValueIn Id l -> MValueIn Id l) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn IO l) ->
  (VarName -> TValueIn IO l -> MValueIn IO l) ->
  (Name -> TValueIn IO l -> Maybe (MValueIn IO l)) ->
  (Name -> Sort -> Maybe (MValueIn IO l)) ->
  (Name -> Text -> [ThunkIn IO l] -> MValueIn IO l) ->
  (VBool (WithM IO l) -> MValueIn IO l -> MValueIn IO l -> MValueIn IO l) ->
  IO (SimulatorConfigIn IO l) #-}
evalGlobal ::
  forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
  ModuleMap ->
  -- | Implementations of 'Primitive' terms, plus overrides for 'Constant' and 'CtorApp' terms
  Map Ident (Prims.Prim l) ->
  -- | Implementations of free 'Variable' terms
  (VarName -> TValue l -> MValue l) ->
  -- | Overrides for Constant terms (e.g. uninterpreted functions)
  (Name -> TValue l -> Maybe (EvalM l (Value l))) ->
  -- | Overrides for Recursor terms
  (Name -> Sort -> Maybe (EvalM l (Value l))) ->
  -- | Handler for stuck primitives
  (Name -> Text -> [Thunk l] -> MValue l) ->
  -- | Lazy mux operation
  (VBool l -> MValue l -> MValue l -> MValue l) ->
  EvalM l (SimulatorConfig l)
evalGlobal modmap prims variable uninterpreted primHandler lazymux =
  evalGlobal' modmap prims (const variable) uninterpreted primHandler lazymux

{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn Id l) ->
  (Term -> VarName -> TValueIn Id l -> MValueIn Id l) ->
  (Name -> TValueIn Id l -> Maybe (MValueIn Id l)) ->
  (Name -> Sort -> Maybe (MValueIn Id l)) ->
  (Name -> Text -> [ThunkIn Id l] -> MValueIn Id l) ->
  (VBool l -> MValueIn Id l -> MValueIn Id l -> MValueIn Id l) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn IO l) ->
  (Term -> VarName -> TValueIn IO l -> MValueIn IO l) ->
  (Name -> TValueIn IO l -> Maybe (MValueIn IO l)) ->
  (Name -> Sort -> Maybe (MValueIn IO l)) ->
  (Name -> Text -> [ThunkIn IO l] -> MValueIn IO l) ->
  (VBool l -> MValueIn IO l -> MValueIn IO l -> MValueIn IO l) ->
  IO (SimulatorConfigIn IO l) #-}
-- | A variant of 'evalGlobal' that lets the uninterpreted function
-- symbol and external-constant callbacks have access to the 'TermF'.
evalGlobal' ::
  forall l. (VMonadLazy l, Show (Extra l)) =>
  ModuleMap ->
  -- | Implementations of 'Primitive' terms, plus overrides for 'Constant' and 'CtorApp' terms
  Map Ident (Prims.Prim l) ->
  -- | Implementations of free 'Variable' terms
  (Term -> VarName -> TValue l -> MValue l) ->
  -- | Overrides for Constant terms (e.g. uninterpreted functions)
  (Name -> TValue l -> Maybe (MValue l)) ->
  -- | Overrides for Recursor terms
  (Name -> Sort -> Maybe (MValue l)) ->
  -- | Handler for stuck primitives
  (Name -> Text -> [Thunk l] -> MValue l) ->
  -- | Lazy mux operation
  (VBool l -> MValue l -> MValue l -> MValue l) ->
  EvalM l (SimulatorConfig l)
evalGlobal' modmap prims variable constant recursor primHandler lazymux =
  do checkPrimitives modmap prims
     return (SimulatorConfig primitive variable constant' recursor modmap lazymux)
  where
    constant' :: Name -> TValue l -> Maybe (MValue l)
    constant' nm tv =
      case constant nm tv of
        Just v -> Just v
        Nothing ->
          case nameInfo nm of
            ModuleIdentifier ident ->
              evalPrim (primHandler nm) <$> Map.lookup ident prims
            ImportedName{} -> Nothing

    primitive :: Name -> MValue l
    primitive nm =
      case nameInfo nm of
        ImportedName {} ->
          panic "evalGlobal'" ["Unimplemented global: " <> toAbsoluteName (nameInfo nm)]
        ModuleIdentifier ident ->
          case Map.lookup ident prims of
            Just v  -> evalPrim (primHandler nm) v
            Nothing -> panic "evalGlobal'" ["Unimplemented global: " <> identText ident]

-- | Check that all the primitives declared in the given module
--   are implemented, and that terms with implementations are not
--   overridden.
checkPrimitives :: forall l. (VMonadLazy l, Show (Extra l))
                => ModuleMap
                -> Map Ident (Prims.Prim l)
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

        primSet = Set.fromList $ mapMaybe defIdent $ allModulePrimitives modmap
        defSet  = Set.fromList $ mapMaybe defIdent $ allModuleActualDefs modmap
        implementedPrims = Map.keysSet prims

        unimplementedPrims = Set.toList $ Set.difference primSet implementedPrims
        overridePrims = Set.toList $ Set.intersection defSet implementedPrims

defIdent :: Def -> Maybe Ident
defIdent d =
  case nameInfo (defName d) of
    ModuleIdentifier ident -> Just ident
    ImportedName{} -> Nothing

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
  evalOpen cfg memoClosed t IntMap.empty

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
    subterms = fmap fst $ IntMap.filter (IntSet.null . snd) $ State.execState (go t) IntMap.empty

    go :: Term -> State.State (IntMap (TermF Term, IntSet)) IntSet
    go t' =
      do memo <- State.get
         let i = termIndex t'
         case IntMap.lookup i memo of
           Just (_, b) -> pure b
           Nothing ->
             do let tf = unwrapTermF t'
                b <- termf tf
                State.modify (IntMap.insert i (tf, b))
                pure b

    termf :: TermF Term -> State.State (IntMap (TermF Term, IntSet)) IntSet
    termf tf =
      case tf of
        Constant nm ->
          -- if tf is a defined constant, traverse the definition body and type
          do let r = requireNameInMap nm (simModMap cfg)
             void $ go (resolvedNameType r)
             case r of
               ResolvedDef (defBody -> Just body) -> go body
               _ -> pure IntSet.empty
        Lambda x _ty body ->
          -- skip type, which is not used for simulation
          IntSet.delete (vnIndex x) <$> go body
        _ ->
          freesTermF <$> traverse go tf

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
evalClosedTermF cfg memoClosed tf = evalTermF cfg lam recEval tf IntMap.empty
  where
    lam = evalOpen cfg memoClosed
    recEval t =
      case IntMap.lookup (termIndex t) memoClosed of
        Just x -> force x
        Nothing -> panic "evalClosedTermF" ["internal error"]

{-# SPECIALIZE mkMemoLocal ::
  Show (Extra l) =>
  SimulatorConfigIn Id l ->
  IntMap (ThunkIn Id l) ->
  Term ->
  EnvIn Id l ->
  Id (IntMap (ThunkIn Id l)) #-}
{-# SPECIALIZE mkMemoLocal ::
  Show (Extra l) =>
  SimulatorConfigIn IO l ->
  IntMap (ThunkIn IO l) ->
  Term ->
  EnvIn IO l ->
  IO (IntMap (ThunkIn IO l)) #-}

-- | Precomputing the memo table for open subterms in the current context.
mkMemoLocal :: forall l. (VMonadLazy l, Show (Extra l)) =>
               SimulatorConfig l -> IntMap (Thunk l) ->
               Term -> Env l -> EvalM l (IntMap (Thunk l))
mkMemoLocal cfg memoClosed t env = go mempty t
  where
    go :: IntMap (Thunk l) -> Term -> EvalM l (IntMap (Thunk l))
    go memo t'
      | closedTerm t' = pure memo
      | otherwise =
        let i = termIndex t' in
        case IntMap.lookup i memo of
          Just _ -> pure memo
          Nothing ->
            do let tf = unwrapTermF t'
               memo' <- goTermF memo tf
               thunk <- delay (evalLocalTermF cfg memoClosed memo' tf env)
               pure (IntMap.insert i thunk memo')
    goTermF :: IntMap (Thunk l) -> TermF Term -> EvalM l (IntMap (Thunk l))
    goTermF memo tf =
      case tf of
        FTermF ftf      -> foldlM go memo ftf
        App t1 t2       -> do memo' <- goTermF memo (unwrapTermF t1)
                              go memo' t2
        Lambda{}        -> pure memo
        Pi _ t1 _       -> go memo t1
        Constant{}      -> pure memo
        Variable _nm tp -> go memo tp

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
    recEval t =
      case IntMap.lookup (termIndex t) memo of
        Just x -> force x
        Nothing -> evalTermF cfg lam recEval (unwrapTermF t) env
      where memo = if closedTerm t then memoClosed else memoLocal

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
      eval t' =
        case IntMap.lookup (termIndex t') memo of
          Just x -> force x
          Nothing -> evalF (unwrapTermF t')
        where memo = if closedTerm t' then memoClosed else memoLocal
      evalF :: TermF Term -> MValue l
      evalF tf = evalTermF cfg (evalOpen cfg memoClosed) eval tf env
  eval t


{-# SPECIALIZE evalPrim ::
  Show (Extra l) =>
  (Text -> [ThunkIn Id l] -> MValueIn Id l) ->
  PrimIn Id l ->
  MValueIn Id l
 #-}
{-# SPECIALIZE evalPrim ::
  Show (Extra l) =>
  (Text -> [ThunkIn IO l] -> MValueIn IO l) ->
  PrimIn IO l ->
  MValueIn IO l
 #-}
evalPrim :: forall l. (VMonadLazy l, Show (Extra l)) =>
  (Text -> [Thunk l] -> MValue l) ->
  Prims.Prim l ->
  MValue l
evalPrim fallback = loop []
  where
    loop :: [Thunk l] -> Prims.Prim l -> MValue l
    loop env (Prims.PrimFun f) =
      pure $ VFun $ \x ->
        loop (x : env) (f x)

    loop env (Prims.PrimStrict f) =
      pure $ vStrictFun $ \x ->
        loop (ready x : env) (f x)

    loop env (Prims.PrimFilterFun msg r f) =
      pure $ vStrictFun $ \x ->
        runMaybeT (r x) >>= \case
          Just v -> loop (ready x : env) (f v)
          _ -> fallback msg (ready x : env)

    loop env (Prims.PrimExcept m) =
      runExceptT m >>= \case
        Right v  -> pure v
        Left msg -> fallback msg env

    loop _env (Prims.Prim m) = m
    loop _env (Prims.PrimValue v) = pure v

-- | A basic handler for stuck primitives.
defaultPrimHandler ::
  (VMonadLazy l, MonadFail (EvalM l)) =>
  Name -> Text -> [Thunk l] -> MValue l
defaultPrimHandler nm msg env =
  fail $ unlines
  [ "Could not evaluate primitive " ++ Text.unpack (toAbsoluteName (nameInfo nm))
  , "On argument " ++ show (length env)
  , Text.unpack msg
  ]
