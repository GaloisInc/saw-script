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

import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Fix (MonadFix(mfix))
import Control.Monad.Identity (Identity)
import qualified Control.Monad.State as State
import Data.Foldable (Foldable(..))
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
  , DataType(..)
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
-- Let-based terms

-- | A representation of SAWCore terms with explicit @let@ bindings
-- instead of using a 'TermIndex' on every subterm.
-- This representation is designed to support efficient evaluation.
-- Type 'TermIndex' is used to represent let-bound variable names.
--
-- Invariant: In any 'LLet', all let-variables occurring on the rhs of
-- any binding must be strictly less than the index of the lhs; this
-- ensures the term is well-founded.
data LTerm
  = LFlat !(FlatTermF LTerm)
  | LApp !LTerm !LTerm
  | LLam !TermIndex !LTerm
    -- ^ The type is omitted because it is not needed for evaluation.
  | LLet !(IntMap LTerm) !LTerm
    -- ^ A non-recursive let, where smaller indices are in scope for
    -- entries of larger indices, but not vice versa.
  | LFun !LTerm !LTerm -- ^ Non-dependent function type.
  | LPi !VarIndex !LTerm !LTerm -- ^ Dependent function type.
  | LConst !Name
  | LLetVar !TermIndex -- ^ A variable bound in a 'LLet' term.
  | LBoundVar !VarIndex -- ^ A variable bound in a 'LLam' or 'LPi' term.
  deriving Show

-- | The number of occurrences of a subterm.
data Multiplicity = Single | Multiple
  deriving Eq

-- | An 'LTerm' paired with the 'varTypes' field of the 'Term' it was
-- derived from and a multiplicity.
data LBinding = LBinding !LTerm !(IntMap Term) !Multiplicity

usesVarName :: VarName -> LBinding -> Bool
usesVarName vn (LBinding _ env _) = IntMap.member (vnIndex vn) env

-- | Apply a let-variable substitution to an 'LTerm'.
-- Only use entries marked as a single occurrence.
-- Precondition: No entries in the substitution may share keys with
-- any let-bindings in the term; this ensures that variable capture is
-- impossible when substituting under 'LLet'.
substLTerm :: IntMap LBinding -> LTerm -> LTerm
substLTerm s = go
  where
    go :: LTerm -> LTerm
    go t =
      case t of
        LFlat ftf ->
          LFlat (fmap go ftf)
        LApp t1 t2 ->
          LApp (go t1) (go t2)
        LLam x t1 ->
          LLam x (go t1)
        LLet binds body ->
          LLet (fmap go binds) (go body)
        LFun t1 t2 ->
          LFun (go t1) (go t2)
        LPi x t1 t2 ->
          LPi x (go t1) (go t2)
        LConst {} ->
          t
        LLetVar i ->
          case IntMap.lookup i s of
            Nothing -> t
            Just (LBinding t' _ n) ->
              if n == Single then go t' else t
        LBoundVar {} ->
          t

-- | Make a let expression after inlining all local bindings that are
-- used only once.
mkLLet :: IntMap LBinding -> LTerm -> LTerm
mkLLet s body =
  if IntMap.null s2 then body' else LLet s2 body'
  where
    body' = substLTerm s body
    s1 = IntMap.filter (\(LBinding _ _ n) -> n == Multiple) s
    s2 = fmap (\(LBinding t _ _) -> substLTerm s t) s1

toLTerm :: Term -> LTerm
toLTerm t0 =
  let (t', binds) = State.runState (go t0) mempty
  in mkLLet binds t'
  where
    go :: Term -> State.State (IntMap LBinding) LTerm
    go t =
      do binds <- State.get
         let i = termIndex t
         case IntMap.lookup i binds of
           Just (LBinding lt env _) ->
             -- Subterm has already been seen, so mark it as a multiple occurrence.
             do State.modify (IntMap.insert i (LBinding lt env Multiple))
                pure (LLetVar i)
           Nothing ->
             -- New subterm: Traverse it and then record a single occurrence.
             do t' <- termf (unwrapTermF t)
                State.modify (IntMap.insert i (LBinding t' (varTypes t) Single))
                pure (LLetVar i)

    termf :: TermF Term -> State.State (IntMap LBinding) LTerm
    termf tf =
      case tf of
        FTermF ftf ->
          do ftf' <- traverse go ftf
             pure (LFlat ftf')
        App t1 t2 ->
          do t1' <- go t1
             t2' <- go t2
             pure (LApp t1' t2')
        Lambda x _ty body ->
          localScope x $
          do body' <- go body
             locals <- getLocalBindings x
             pure (LLam (vnIndex x) (mkLLet locals body'))
        Pi x t1 t2
          | IntMap.member (vnIndex x) (varTypes t2) ->
              do t1' <- go t1
                 localScope x $
                   do t2' <- go t2
                      locals <- getLocalBindings x
                      pure (LPi (vnIndex x) t1' (mkLLet locals t2'))
          | otherwise ->
              do t1' <- go t1
                 t2' <- go t2
                 pure (LFun t1' t2')
        Constant nm ->
          pure (LConst nm)
        Variable x _ty ->
          pure (LBoundVar (vnIndex x))
        Label _text t1 ->
          go t1

    -- | Temporarily remove bindings that mention x, run the inner
    -- computation where those bindings would be shadowed, and then
    -- put them back.
    localScope :: VarName -> State.State (IntMap LBinding) a -> State.State (IntMap LBinding) a
    localScope x action =
      do binds <- State.get
         let (shadowed, binds1) = IntMap.partition (usesVarName x) binds
         State.put binds1
         result <- action
         binds2 <- State.get
         State.put (shadowed <> binds2)
         pure result

    -- | Filter out all bindings mentioning x and return them.
    getLocalBindings :: VarName -> State.State (IntMap LBinding) (IntMap LBinding)
    getLocalBindings x =
      do binds <- State.get
         let (locals, binds') = IntMap.partition (usesVarName x) binds
         State.put binds'
         pure locals

------------------------------------------------------------
-- Evaluation of terms

{-# SPECIALIZE
  evalLTerm ::
    Show (Extra l) =>
    SimulatorConfigIn Id l ->
    IntMap (ThunkIn Id l) ->
    IntMap (ThunkIn Id l) ->
    IntMap (ThunkIn Id l) ->
    LTerm -> MValueIn Id l #-}

{-# SPECIALIZE
  evalLTerm ::
    Show (Extra l) =>
    SimulatorConfigIn IO l ->
    IntMap (ThunkIn IO l) ->
    IntMap (ThunkIn IO l) ->
    IntMap (ThunkIn IO l) ->
    LTerm -> MValueIn IO l #-}

-- | Generic evaluator for 'LTerm's.
evalLTerm ::
  forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
  SimulatorConfig l ->
  IntMap (Thunk l) {- ^ Constant environment, indexed by 'VarIndex' -} ->
  IntMap (Thunk l) {- ^ Bound variable environment, indexed by 'VarIndex' -} ->
  IntMap (Thunk l) {- ^ Let-variable environment, indexed by 'TermIndex' -} ->
  LTerm -> MValue l
evalLTerm cfg consts vars lets t0 =
  case t0 of
    LFlat ftf ->
      case ftf of
        Recursor r ->
          case simRecursor cfg (recursorDataType r) (recursorSort r) of
            Just v -> v
            Nothing ->
              case lookupVarIndexInMap (nameIndex (recursorDataType r)) (simModMap cfg) of
                Just (ResolvedDataType dt) ->
                  do let nparams = recursorNumParams r
                     let nixs = recursorNumIxs r
                     let cnames = recursorCtorOrder r
                     vFunList nparams $ \_ps_thunks ->
                       pure $ VFun $ \_motive ->
                       vFunList (length cnames) $ \elim_thunks ->
                       do let vrec = VRecursor dt elim_thunks
                          vFunList nixs (\_ixs -> pure (evalRecursor vrec))
                _ ->
                  panic "evalTermF"
                  [ "Data type not found for recursor: " <>
                    toAbsoluteName (nameInfo (recursorDataType r)) ]
        Sort s _h ->
          pure $ TValue (VSort s)
        ArrayValue _ tv ->
          VVector <$> traverse (delay . recEval) tv
        StringLit s ->
          pure $ VString s

    LApp t1 t2 ->
      do v1 <- recEval t1
         case v1 of
           VFun f ->
             do x <- delay (recEval t2)
                f x
           _ -> panic "evalLTerm" ["Expected VFun"]

    LLam i t1 ->
      pure $ VFun (\x -> loop (IntMap.insert i x vars) lets t1)

    LLet binds body ->
      do lets' <-
           mfix $ \lets' ->
           do vs <- traverse (delay . loop vars lets') binds
              pure (lets <> vs)
         loop vars lets' body

    LFun t1 t2 ->
      do v1 <- toTValue <$> recEval t1
         v2 <- toTValue <$> recEval t2
         pure $ TValue $ VPiType v1 $ VNondependentPi v2

    LPi i t1 t2 ->
      do v1 <- toTValue <$> recEval t1
         pure $ TValue $ VPiType v1 $
           VDependentPi (\x -> toTValue <$> loop (IntMap.insert i x vars) lets t2)

    LConst nm ->
      case IntMap.lookup (nameIndex nm) consts of
        Just x -> force x
        Nothing -> panic "evalLTerm" ["Constant name not found", Text.pack (show nm)]

    LLetVar i ->
      case IntMap.lookup i lets of
        Just x -> force x
        Nothing ->
          panic "evalLTerm"
          ["Let variable not found", Text.pack (show i), Text.pack (show (IntMap.keys lets))]

    LBoundVar i ->
      case IntMap.lookup i vars of
        Just x -> force x
        Nothing ->
          panic "evalLTerm"
          ["Lambda/pi variable not found", Text.pack (show i), Text.pack (show (IntMap.keys vars))]
  where
    loop :: IntMap (Thunk l) -> IntMap (Thunk l) -> LTerm -> EvalM l (Value l)
    loop vars' lets' = evalLTerm cfg consts vars' lets'

    recEval :: LTerm -> EvalM l (Value l)
    recEval = loop vars lets

    toTValue :: HasCallStack => Value l -> TValue l
    toTValue (TValue x) = x
    toTValue t = panic "evalTermF / toTValue" ["Not a type value: " <> Text.pack (show t)]

    evalRecursor :: VRecursor l -> Value l
    evalRecursor vrec@(VRecursor dt elims) =
      vStrictFun $ \argv ->
      case argv of
        VCtorApp n _dep args
          | n < length elims ->
              do elimv <- force (elims !! n)
                 let ctor = dtCtors dt !! n
                 reduceRecursor (evalRecursor vrec) elimv args (ctorArgStruct ctor)
          | otherwise ->
              panic "evalTermF / evalRecursor"
              ["No eliminator for constructor: " <> Text.pack (show n)]
        VCtorMux branches ->
          do alts <- traverse (evalCtorMuxBranch vrec) (IntMap.assocs branches)
             combineAlts alts
        VBVToNat{} ->
          panic "evalTermF / evalRecursor"
          ["Unsupported symbolic recursor argument of type Nat"]
        _ ->
          panic "evalTermF / evalRecursor"
          ["Expected constructor for datatype: " <> toAbsoluteName (nameInfo (dtName dt))]

    evalCtorMuxBranch ::
      VRecursor l ->
      (Int, (VBool l, Muxability, [Thunk l])) ->
      EvalM l (VBool l, EvalM l (Value l))
    evalCtorMuxBranch r@(VRecursor dt elims) (i, (p, _m, args)) =
      do elimv <- force (elims !! i)
         let ctor = dtCtors dt !! i
         pure (p, reduceRecursor (evalRecursor r) elimv args (ctorArgStruct ctor))

    combineAlts :: [(VBool l, EvalM l (Value l))] -> EvalM l (Value l)
    combineAlts [] = panic "evalTermF / combineAlts" ["no alternatives"]
    combineAlts [(_, x)] = x
    combineAlts ((p, x) : alts) = simLazyMux cfg p x (combineAlts alts)

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
  (Name -> Sort -> Maybe (PrimIn Id l)) ->
  (Name -> Text -> [ThunkIn Id l] -> MValueIn Id l) ->
  (VBool (WithM Id l) -> MValueIn Id l -> MValueIn Id l -> MValueIn Id l) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn IO l) ->
  (VarName -> TValueIn IO l -> MValueIn IO l) ->
  (Name -> TValueIn IO l -> Maybe (MValueIn IO l)) ->
  (Name -> Sort -> Maybe (PrimIn IO l)) ->
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
  (Name -> Sort -> Maybe (Prims.Prim l)) ->
  -- | Handler for stuck primitives
  (Name -> Text -> [Thunk l] -> MValue l) ->
  -- | Lazy mux operation
  (VBool l -> MValue l -> MValue l -> MValue l) ->
  EvalM l (SimulatorConfig l)
evalGlobal modmap prims variable constant recursor primHandler lazymux =
  evalGlobal' modmap prims (const variable) constant recursor primHandler lazymux

{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn Id l) ->
  (Term -> VarName -> TValueIn Id l -> MValueIn Id l) ->
  (Name -> TValueIn Id l -> Maybe (MValueIn Id l)) ->
  (Name -> Sort -> Maybe (PrimIn Id l)) ->
  (Name -> Text -> [ThunkIn Id l] -> MValueIn Id l) ->
  (VBool l -> MValueIn Id l -> MValueIn Id l -> MValueIn Id l) ->
  Id (SimulatorConfigIn Id l) #-}
{-# SPECIALIZE evalGlobal' ::
  Show (Extra l) =>
  ModuleMap ->
  Map Ident (PrimIn IO l) ->
  (Term -> VarName -> TValueIn IO l -> MValueIn IO l) ->
  (Name -> TValueIn IO l -> Maybe (MValueIn IO l)) ->
  (Name -> Sort -> Maybe (PrimIn IO l)) ->
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
  (Name -> Sort -> Maybe (Prims.Prim l)) ->
  -- | Handler for stuck primitives
  (Name -> Text -> [Thunk l] -> MValue l) ->
  -- | Lazy mux operation
  (VBool l -> MValue l -> MValue l -> MValue l) ->
  EvalM l (SimulatorConfig l)
evalGlobal' modmap prims variable constant recursor primHandler lazymux =
  do checkPrimitives modmap prims
     return (SimulatorConfig primitive variable constant' recursor' modmap lazymux)
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

    recursor' :: Name -> Sort -> Maybe (MValue l)
    recursor' nm s = evalPrim (primHandler nm) <$> recursor nm s

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
-- The evaluation strategy for shared terms involves a preprocessing
-- phase, where each term is translated to a special term type with
-- explicit let bindings.
-- The let-terms are then evaluated recursively using a set of three
-- environment parameters:
--
-- * The constant environment contains a thunk for each constant used
-- in the term, or in the definition of another used constant.
--
-- * The bound variable environment has a thunk for each lambda- or
-- pi-bound variable in scope; it is pre-populated with translations
-- of variables free in the top-level term.
--
-- * The let-variable environment has a thunk for each let-binding in
-- scope.

{-# SPECIALIZE evalSharedTerm ::
  Show (Extra l) => SimulatorConfigIn Id l -> Term -> MValueIn Id l #-}
{-# SPECIALIZE evalSharedTerm ::
  Show (Extra l) => SimulatorConfigIn IO l -> Term -> MValueIn IO l #-}

-- | Evaluator for shared terms.
evalSharedTerm ::
  forall l. (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
  SimulatorConfig l -> Term -> MValue l
evalSharedTerm cfg t =
  do let names = collectConstants cfg t
     constThunks <-
       mfix $ \constThunks ->
       traverse (delay . evalConst constThunks) names
     let freevars = collectVariables t
     varThunks <-
       mfix $ \varThunks ->
       traverse (delay . evalVar constThunks varThunks) freevars
     evalLTerm cfg constThunks varThunks mempty (toLTerm t)
  where
    evalConst :: IntMap (Thunk l) -> Name -> MValue l
    evalConst consts nm =
      do let r = requireNameInMap nm (simModMap cfg)
         ty' <- toTValue <$> evalLTerm cfg consts mempty mempty (toLTerm (resolvedNameType r))
         case simConstant cfg nm ty' of
           Just override -> override
           Nothing ->
             case r of
               ResolvedCtor ctor ->
                 ctorValue (ctorNumber ctor) (ctorMuxability ctor) (ctorNumParams ctor) (ctorNumArgs ctor)
               ResolvedDataType dt ->
                 dtValue (nameInfo nm) (dtNumParams dt) (dtNumIndices dt)
               ResolvedDef d ->
                 case defBody d of
                   Just body -> evalLTerm cfg consts mempty mempty (toLTerm body)
                   Nothing -> simPrimitive cfg nm

    evalVar :: IntMap (Thunk l) -> IntMap (Thunk l) -> (VarName, Term) -> MValue l
    evalVar consts env (nm, tp) =
      do tv <- toTValue <$> evalLTerm cfg consts env mempty (toLTerm tp)
         simVariable cfg tp nm tv

    toTValue :: HasCallStack => Value l -> TValue l
    toTValue (TValue x) = x
    toTValue v = panic "evalTermF / toTValue" ["Not a type value: " <> Text.pack (show v)]

    ctorValue :: Int -> Muxability -> Int -> Int -> MValue l
    ctorValue k m i j =
      vFunList i $ \_params ->
      vFunList j $ \args ->
      pure $ VCtorApp k m args

    dtValue :: NameInfo -> Int -> Int -> MValue l
    dtValue nm i j =
      vStrictFunList i $ \params ->
      vStrictFunList j $ \idxs ->
      pure $ TValue $ VDataType nm params idxs

-- | Precompute the set of constant names (indexed by 'VarIndex')
-- required for evaluation of a 'Term'.
collectConstants :: SimulatorConfig l -> Term -> IntMap Name
collectConstants cfg t0 = snd $ go (IntSet.empty, IntMap.empty) t0
  where
    go :: (IntSet, IntMap Name) -> Term -> (IntSet, IntMap Name)
    go acc@(idxs, names) t
      | IntSet.member (termIndex t) idxs = acc
      | otherwise = termf (IntSet.insert (termIndex t) idxs, names) (unwrapTermF t)

    termf :: (IntSet, IntMap Name) -> TermF Term -> (IntSet, IntMap Name)
    termf acc@(idxs, names) tf =
      case tf of
        Constant nm ->
          case r of
            -- if tf is a defined constant, traverse the definition body and type
            ResolvedDef (defBody -> Just body) -> go (go acc' (resolvedNameType r)) body
            -- otherwise just traverse the type
            _ -> go acc' (resolvedNameType r)
          where
            acc' = (idxs, IntMap.insert (nameIndex nm) nm names)
            r = requireNameInMap nm (simModMap cfg)
        Lambda _x _ty body ->
          go acc body -- skip type, which is not used for simulation
        _ ->
          foldl' go acc tf

-- | Precompute the set of variables (indexed by 'VarIndex') occurring
-- free in a 'Term'.
collectVariables :: Term -> IntMap (VarName, Term)
collectVariables t0 =
  IntMap.fromList [ (vnIndex vn, (vn, t)) | (vn, t) <- Map.assocs (getAllVarsMap t0) ]


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
