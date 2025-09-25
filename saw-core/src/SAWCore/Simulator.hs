{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

{- |
Module      : SAWCore.Simulator
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
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
import qualified Data.IntMap as IMap
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
  , findCtorInMap
  , lookupVarIndexInMap
  , resolvedNameType
  , requireNameInMap
  , Ctor(..)
  , Def(..)
  , DefQualifier(..)
  , ModuleMap
  , ResolvedName(..)
  )
import SAWCore.Name
import SAWCore.SharedTerm
import SAWCore.Prelude.Constants

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
  { simPrimitive :: Name -> TValue l -> MValue l
  -- ^ Interpretation of 'Primitive' terms.
  , simExtCns :: TermF Term -> ExtCns (TValue l) -> MValue l
  -- ^ Interpretation of 'ExtCns' terms.
  , simConstant :: TermF Term -> Name -> TValue l -> Maybe (MValue l)
  -- ^ Interpretation of 'Constant' terms. 'Nothing' indicates that
  -- the body of the constant should be evaluated. 'Just' indicates
  -- that the constant's definition should be overridden.
  , simCtorApp :: Name -> TValue l -> Maybe (MValue l)
  -- ^ Interpretation of constructor terms. 'Nothing' indicates that
  -- the constructor is treated as normal. 'Just' replaces the
  -- constructor with a custom implementation.
  , simNeutral :: Env l -> NeutralTerm -> MValue l
  -- ^ Handler that fires if the simulator encounters a term that it
  --   cannot otherwise evaluate because it is blocked. For some simulators,
  --   this is just an error condition; for others, sensible action can
  --   be taken.
  , simModMap :: ModuleMap
  , simLazyMux :: TValue l -> VBool l -> MValue l -> MValue l -> MValue l
  }

------------------------------------------------------------
-- Evaluation of terms

type Env l = [(Thunk l, TValue l)]
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
                                 VFun _ f ->
                                   do x <- recEvalDelay t2
                                      f x
                                 _ -> simNeutral cfg env (NeutralApp (NeutralBox t1) t2)
    Lambda nm tp t          -> do v <- evalType tp
                                  return $ VFun nm (\x -> lam t ((x,v) : env))
    Pi nm t1 t2             -> do v <- evalType t1
                                  body <-
                                    if inBitSet 0 (looseVars t2) then
                                      pure (VDependentPi (\x -> toTValue <$> lam t2 ((x,v) : env)))
                                    else
                                      do -- put dummy values in the environment; the term should never reference them
                                         let val = ready VUnit
                                         let tp  = VUnitType
                                         VNondependentPi . toTValue <$> lam t2 ((val,tp):env)
                                  return $ TValue $ VPiType nm v body

    LocalVar i              -> force (fst (env !! i))

    Constant nm             -> do let r = requireNameInMap nm (simModMap cfg)
                                  ty' <- evalType (resolvedNameType r)
                                  case simConstant cfg tf nm ty' of
                                    Just override -> override
                                    Nothing ->
                                      case r of
                                        ResolvedCtor ctor ->
                                          ctorValue nm ty' (ctorNumParams ctor) (ctorNumArgs ctor)
                                        ResolvedDataType dt ->
                                          dtValue nm ty' (dtNumParams dt) (dtNumIndices dt)
                                        ResolvedDef d ->
                                          case defBody d of
                                            Just t -> recEval t
                                            Nothing ->
                                              case defQualifier d of
                                                NoQualifier -> simNeutral cfg env (NeutralConstant nm)
                                                PrimQualifier -> simPrimitive cfg nm ty'
                                                AxiomQualifier -> simPrimitive cfg nm ty'

    Variable ec             -> do ec' <- traverse evalType ec
                                  simExtCns cfg tf ec'
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
                                 _ -> simNeutral cfg env (NeutralPairLeft (NeutralBox x))

        PairRight x         -> recEval x >>= \case
                                 VPair _l r -> force r
                                 _ -> simNeutral cfg env (NeutralPairRight (NeutralBox x))

        RecursorType d ps m mtp tp ->
          do dty <- evalType (resolvedNameType (requireNameInMap d (simModMap cfg)))
             TValue <$> (VRecursorType d dty <$>
               mapM recEval ps <*>
               recEval m <*>
               (evalType mtp) <*>
               (evalType tp))

        Recursor r ->
          do let f (e,ety) = do v  <- recEvalDelay e
                                ty <- evalType ety
                                pure (v,ty)
             let dname = recursorDataType r
             dty <- evalType (resolvedNameType (requireNameInMap dname (simModMap cfg)))
             ps  <- traverse recEval (recursorParams r)
             m   <- recEval (recursorMotive r)
             mty <- evalType (recursorMotiveTy r)
             es  <- traverse f (recursorElims r)
             ty  <- evalType (recursorType r)
             pure (VRecursor dname dty ps m mty es ty)

        RecursorApp rectm ixs ->
          do r <- recEval rectm
             case r of
               VRecursor d k ps motive motiveTy ps_fs ty ->
                 pure $ VFun "_" $ \arg_thunk ->
                 do argv <- force arg_thunk
                    case evalConstructor argv of
                      Just (ctor, args)
                        | Just (elim,elimTy) <- Map.lookup (nameIndex (ctorName ctor)) ps_fs
                        -> do let rTy = VRecursorType d k ps motive motiveTy ty
                              ctorTy <- toTValue <$> lam (ctorType ctor) []
                              allArgs <- processRecArgs ps args ctorTy [(elim,elimTy),(ready r,rTy)]
                              lam (ctorIotaTemplate ctor) allArgs

                        | otherwise -> panic "evalTermF / RecursorApp" ["could not find info for constructor: " <> Text.pack (show ctor)]
                      Nothing ->
                        case argv of
                          VCtorMux _ps branches ->
                            do alts <- traverse (evalCtorMuxBranch r) (IntMap.elems branches)
                               -- compute return type of recursor application
                               ixvs <- traverse recEval ixs
                               retTy <- toTValue <$> applyAll motive (map ready (ixvs ++ [argv]))
                               combineAlts retTy alts
                          _ -> panic "evalTermF / RecursorApp" ["Expected constructor for datatype: " <> toAbsoluteName (nameInfo d)]
               _ -> panic "evalTermF / RecursorApp" ["Expected recursor value"]

        RecordType elem_tps ->
          TValue . VRecordType <$> traverse (traverse evalType) elem_tps

        RecordValue elems   ->
          VRecordValue <$> mapM (\(fld,t) -> (fld,) <$> recEvalDelay t) elems

        RecordProj t fld    -> recEval t >>= \case
                                 v@VRecordValue{} -> valRecordProj v fld
                                 _ -> simNeutral cfg env (NeutralRecordProj (NeutralBox t) fld)

        Sort s _h           -> return $ TValue (VSort s)

        NatLit n            -> return $ VNat n

        ArrayValue _ tv     -> liftM VVector $ mapM recEvalDelay tv

        StringLit s         -> return $ VString s
  where
    evalType :: Term -> EvalM l (TValue l)
    evalType t = toTValue <$> recEval t

    toTValue :: HasCallStack => Value l -> TValue l
    toTValue (TValue x) = x
    toTValue t = panic "evalTermF / toTValue" ["Not a type value: " <> Text.pack (show t)]

    evalCtorMuxBranch ::
      Value l ->
      (VBool l, Name, TValue l, [Thunk l]) ->
      EvalM l (VBool l, EvalM l (Value l))
    evalCtorMuxBranch r (p, c, ct, args) =
      case r of
        VRecursor d k ps motive motiveTy ps_fs ty ->
          do let i = nameIndex c
             let rTy = VRecursorType d k ps motive motiveTy ty
             case (lookupVarIndexInMap i (simModMap cfg), Map.lookup i ps_fs) of
               (Just (ResolvedCtor ctor), Just (elim, elimTy)) ->
                 do allArgs <- processRecArgs ps args ct [(elim, elimTy), (ready r, rTy)]
                    pure (p, lam (ctorIotaTemplate ctor) allArgs)
               _ -> panic "evalTermF / evalCtorMuxBranch"
                    ["could not find info for constructor: " <> toAbsoluteName (nameInfo c)]
        _ -> panic "evalTermF / evalCtorMuxBranch" ["expected VRecursor"]

    combineAlts :: TValue l -> [(VBool l, EvalM l (Value l))] -> EvalM l (Value l)
    combineAlts _ [] = panic "evalTermF / combineAlts" ["no alternatives"]
    combineAlts _ [(_, x)] = x
    combineAlts tp ((p, x) : alts) = simLazyMux cfg tp p x (combineAlts tp alts)

    evalConstructor :: Value l -> Maybe (Ctor, [Thunk l])
    evalConstructor (VCtorApp c _tv _ps args) =
      case lookupVarIndexInMap (nameIndex c) (simModMap cfg) of
        Just (ResolvedCtor ctor) -> Just (ctor, args)
        _ -> Nothing
    evalConstructor (VNat 0) =
       do ctor <- findCtorInMap preludeZeroIdent (simModMap cfg)
          Just (ctor, [])
    evalConstructor (VNat n) =
       do ctor <- findCtorInMap preludeSuccIdent (simModMap cfg)
          Just (ctor, [ ready (VNat (pred n)) ])
    evalConstructor _ =
       Nothing

    recEvalDelay :: Term -> EvalM l (Thunk l)
    recEvalDelay = delay . recEval

    ctorValue :: Name -> TValue l -> Int -> Int -> MValue l
    ctorValue nm tv i j =
      vFunList (replicate i "_") $ \params ->
      vFunList (replicate j "_") $ \args ->
      pure $ VCtorApp nm tv params args

    dtValue :: Name -> TValue l -> Int -> Int -> MValue l
    dtValue nm tv i j =
      vStrictFunList (replicate i "_") $ \params ->
      vStrictFunList (replicate j "_") $ \idxs ->
      pure $ TValue $ VDataType nm tv params idxs

-- | Create a 'Value' for a lazy multi-argument function.
vFunList :: forall l. VMonad l => [LocalName] -> ([Thunk l] -> MValue l) -> MValue l
vFunList names k = go [] names
  where
    go :: [Thunk l] -> [LocalName] -> MValue l
    go args [] = k (reverse args)
    go args (n : ns) = pure $ VFun n (\x -> go (x : args) ns)

-- | Create a 'Value' for a strict multi-argument function.
vStrictFunList :: forall l. VMonad l => [LocalName] -> ([Value l] -> MValue l) -> MValue l
vStrictFunList names k = go [] names
  where
    go :: [Value l] -> [LocalName] -> MValue l
    go args [] = k (reverse args)
    go args (n : ns) = pure $ VFun n (\x -> force x >>= \v -> go (v : args) ns)

processRecArgs ::
  (VMonadLazy l, Show (Extra l)) =>
  [Value l] ->
  [Thunk l] ->
  TValue l ->
  Env l ->
  EvalM l (Env l)
processRecArgs (p:ps) args (VPiType _ _ body) env =
  do tp' <- applyPiBody body (ready p)
     processRecArgs ps args tp' env
processRecArgs [] (x:xs) (VPiType _ tp body) env =
  do tp' <- applyPiBody body x
     processRecArgs [] xs tp' ((x,tp):env)
processRecArgs [] [] _ env = pure env
processRecArgs _ _ ty _ =
  panic "processRegArgs" [
     "Expected Pi type!",
     "Found: " <> Text.pack (show ty) 
  ]


{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn Id l) ->
  (ExtCns (TValueIn Id l) -> MValueIn Id l) ->
  (Name -> TValueIn Id l -> Maybe (MValueIn Id l)) ->
  (EnvIn Id l -> NeutralTerm -> MValueIn Id l) ->
  (Name -> TValue (WithM Id l) -> Text -> EnvIn Id l -> TValue (WithM Id l) -> MValueIn Id l) ->
  (TValueIn Id l -> VBool (WithM Id l) -> MValueIn Id l -> MValueIn Id l -> MValueIn Id l) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn IO l) ->
  (ExtCns (TValueIn IO l) -> MValueIn IO l) ->
  (Name -> TValueIn IO l -> Maybe (MValueIn IO l)) ->
  (EnvIn IO l -> NeutralTerm -> MValueIn IO l) ->
  (Name -> TValue (WithM IO l) -> Text -> EnvIn IO l -> TValue (WithM IO l) -> MValueIn IO l) ->
  (TValueIn IO l -> VBool (WithM IO l) -> MValueIn IO l -> MValueIn IO l -> MValueIn IO l) ->
  IO (SimulatorConfigIn IO l) #-}
evalGlobal :: forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
              ModuleMap ->
              Map Ident (Prims.Prim l) ->
              (ExtCns (TValue l) -> MValue l) ->
              (Name -> TValue l -> Maybe (EvalM l (Value l))) ->
              (Env l -> NeutralTerm -> MValue l) ->
              (Name -> TValue l -> Text -> Env l -> TValue l -> MValue l) ->
              (TValue l -> VBool l -> MValue l -> MValue l -> MValue l) ->
              EvalM l (SimulatorConfig l)
evalGlobal modmap prims extcns uninterpreted neutral primHandler lazymux =
  evalGlobal' modmap prims (const extcns) (const uninterpreted) neutral primHandler lazymux

{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn Id l) ->
  (TermF Term -> ExtCns (TValueIn Id l) -> MValueIn Id l) ->
  (TermF Term -> Name -> TValueIn Id l -> Maybe (MValueIn Id l)) ->
  (EnvIn Id l -> NeutralTerm -> MValueIn Id l) ->
  (Name -> TValue (WithM Id l) -> Text -> EnvIn Id l -> TValue (WithM Id l) -> MValueIn Id l) ->
  (TValue (WithM Id l) -> VBool l -> MValueIn Id l -> MValueIn Id l -> MValueIn Id l) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn IO l) ->
  (TermF Term -> ExtCns (TValueIn IO l) -> MValueIn IO l) ->
  (TermF Term -> Name -> TValueIn IO l -> Maybe (MValueIn IO l)) ->
  (EnvIn IO l -> NeutralTerm -> MValueIn IO l) ->
  (Name -> TValue (WithM IO l) -> Text -> EnvIn IO l -> TValue (WithM IO l) -> MValueIn IO l) ->
  (TValueIn IO l -> VBool l -> MValueIn IO l -> MValueIn IO l -> MValueIn IO l) ->
  IO (SimulatorConfigIn IO l) #-}
-- | A variant of 'evalGlobal' that lets the uninterpreted function
-- symbol and external-constant callbacks have access to the 'TermF'.
evalGlobal' ::
  forall l. (VMonadLazy l, Show (Extra l)) =>
  ModuleMap ->
  -- | Implementations of 'Primitive' terms, plus overrides for 'Constant' and 'CtorApp' terms
  Map Ident (Prims.Prim l) ->
  -- | Implementations of ExtCns terms
  (TermF Term -> ExtCns (TValue l) -> MValue l) ->
  -- | Overrides for Constant terms (e.g. uninterpreted functions)
  (TermF Term -> Name -> TValue l -> Maybe (MValue l)) ->
  -- | Handler for neutral terms
  (Env l -> NeutralTerm -> MValue l) ->
  -- | Handler for stuck primitives
  (Name -> TValue l -> Text -> Env l -> TValue l -> MValue l) ->
  -- | Lazy mux operation
  (TValue l -> VBool l -> MValue l -> MValue l -> MValue l) ->
  EvalM l (SimulatorConfig l)
evalGlobal' modmap prims extcns constant neutral primHandler lazymux =
  do checkPrimitives modmap prims
     return (SimulatorConfig primitive extcns constant' ctors neutral modmap lazymux)
  where
    constant' :: TermF Term -> Name -> TValue l -> Maybe (MValue l)
    constant' tf nm tv =
      case constant tf nm tv of
        Just v -> Just v
        Nothing ->
          case nameInfo nm of
            ModuleIdentifier ident ->
              evalPrim (primHandler nm tv) nm tv <$> Map.lookup ident prims
            ImportedName{} -> Nothing

    ctors :: Name -> TValue l -> Maybe (MValue l)
    ctors nm tv =
      case nameInfo nm of
        ModuleIdentifier ident ->
          evalPrim (primHandler nm tv) nm tv <$> Map.lookup ident prims
        ImportedName{} -> Nothing

    primitive :: Name -> TValue l -> MValue l
    primitive nm tv =
      case nameInfo nm of
        ImportedName {} ->
          panic "evalGlobal'" ["Unimplemented global: " <> toAbsoluteName (nameInfo nm)]
        ModuleIdentifier ident ->
          case Map.lookup ident prims of
            Just v  -> evalPrim (primHandler nm tv) nm tv v
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
    go (Unshared tf) = termf tf
    go (STApp{ stAppIndex = i, stAppTermF = tf }) =
      do memo <- State.get
         case IMap.lookup i memo of
           Just (_, b) -> pure b
           Nothing ->
             do b <- termf tf
                State.modify (IMap.insert i (tf, b))
                pure b

    termf :: TermF Term -> State.State (IntMap (TermF Term, BitSet)) BitSet
    termf tf =
      do -- if tf is a defined constant, traverse the definition body and type
         case tf of
           Constant nm ->
             do let r = requireNameInMap nm (simModMap cfg)
                void $ go (resolvedNameType r)
                case r of
                  ResolvedDef (defBody -> Just body) -> void $ go body
                  _ -> pure ()
           _ -> pure ()
         looseTermF <$> traverse go tf

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
    go memo (Unshared tf) = goTermF memo tf
    go memo (t'@STApp{ stAppIndex = i, stAppTermF = tf })
      | termIsClosed t' = pure memo
      | otherwise =
        case IMap.lookup i memo of
          Just _ -> pure memo
          Nothing ->
            do memo' <- goTermF memo tf
               thunk <- delay (evalLocalTermF cfg memoClosed memo' tf env)
               pure (IMap.insert i thunk memo')
    goTermF :: IntMap (Thunk l) -> TermF Term -> EvalM l (IntMap (Thunk l))
    goTermF memo tf =
      case tf of
        FTermF ftf      -> foldlM go memo ftf
        App t1 t2       -> do memo' <- goTermF memo (unwrapTermF t1)
                              go memo' t2
        Lambda _ t1 _   -> go memo t1
        Pi _ t1 _       -> go memo t1
        LocalVar _      -> pure memo
        Constant{}      -> pure memo
        Variable ec     -> go memo (ecType ec)

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
    recEval (t@STApp{ stAppIndex = i, stAppTermF = tf }) =
      case IMap.lookup i memo of
        Just x -> force x
        Nothing -> evalTermF cfg lam recEval tf env
      where memo = if termIsClosed t then memoClosed else memoLocal

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
      eval (t'@STApp{ stAppIndex = i, stAppTermF = tf }) =
        case IMap.lookup i memo of
          Just x -> force x
          Nothing -> evalF tf
        where memo = if termIsClosed t' then memoClosed else memoLocal
      evalF :: TermF Term -> MValue l
      evalF tf = evalTermF cfg (evalOpen cfg memoClosed) eval tf env
  eval t


{-# SPECIALIZE evalPrim ::
  Show (Extra l) =>
  (Text -> EnvIn Id l -> TValue (WithM Id l) -> MValueIn Id l) ->
  Name ->
  TValue (WithM Id l) ->
  PrimIn Id l ->
  MValueIn Id l
 #-}
{-# SPECIALIZE evalPrim ::
  Show (Extra l) =>
  (Text -> EnvIn IO l -> TValue (WithM IO l) -> MValueIn IO l) ->
  Name ->
  TValue (WithM IO l) ->
  PrimIn IO l ->
  MValueIn IO l
 #-}
evalPrim :: forall l. (VMonadLazy l, Show (Extra l)) =>
  (Text -> Env l -> TValue l -> MValue l) ->
  Name ->
  TValue l ->
  Prims.Prim l ->
  MValue l
evalPrim fallback p tv = loop [] tv
  where
    loop :: Env l -> TValue l -> Prims.Prim l -> MValue l
    loop env (VPiType nm t body) (Prims.PrimFun f) =
      pure $ VFun nm $ \x ->
        do tp' <- applyPiBody body x
           loop ((x,t):env) tp' (f x)

    loop env (VPiType nm t body) (Prims.PrimStrict f) =
      pure $ VFun nm $ \x ->
        do tp' <- applyPiBody body x
           x'  <- force x
           loop ((ready x',t):env) tp' (f x')

    loop env (VPiType nm t body) (Prims.PrimFilterFun msg r f) =
      pure $ VFun nm $ \x ->
        do tp' <- applyPiBody body x
           x'  <- force x
           runMaybeT (r x') >>= \case
             Just v -> loop ((ready x',t):env) tp' (f v)
             _ -> fallback msg ((ready x',t):env) tp'

    loop env tp (Prims.PrimExcept m) =
      runExceptT m >>= \case
        Right v  -> pure v
        Left msg -> fallback msg env tp

    loop _env _tp (Prims.Prim m) = m
    loop _env _tp (Prims.PrimValue v) = pure v

    loop _env _tp _p =
      panic "evalPrim" [
          "Type mismatch in primitive: " <> toAbsoluteName (nameInfo p)]

-- | A basic handler for stuck primitives.
defaultPrimHandler ::
  (VMonadLazy l, MonadFail (EvalM l)) =>
  Name -> TValue l -> Text -> Env l -> TValue l -> MValue l
defaultPrimHandler nm _ msg env _tv =
  fail $ unlines
  [ "Could not evaluate primitive " ++ Text.unpack (toAbsoluteName (nameInfo nm))
  , "On argument " ++ show (length env)
  , Text.unpack msg
  ]
