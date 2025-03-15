{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}

module Mir.Compositional.Builder
where

import Control.Lens
    (makeLenses, (^.), (^?), (%=), (.=), (&), (.~), (%~), use, at, ix, _Wrapped)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import qualified Data.BitVector.Sized as BV
import Data.Foldable
import Data.Functor.Const
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Parameterized.Context (pattern Empty, pattern (:>), Assignment)
import Data.Parameterized.Nonce
import Data.Parameterized.Pair
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)
import qualified Prettyprinter as PP

import qualified What4.Expr.Builder as W4
import What4.FunctionName (functionNameFromText)
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import What4.ProgramLoc

import Lang.Crucible.Backend
import Lang.Crucible.Simulator
import Lang.Crucible.Types

import qualified Verifier.SAW.Prelude as SAW
import qualified Verifier.SAW.Recognizer as SAW (asExtCns)
import qualified Verifier.SAW.SharedTerm as SAW
import qualified SAWCoreWhat4.ReturnTrip as SAW
import qualified CryptolSAWCore.TypedTerm as SAW

import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import SAWCentral.Crucible.MIR.MethodSpecIR
import SAWCentral.Crucible.MIR.TypeShape

import Mir.DefId
import Mir.Generator (CollectionState, collection)
import Mir.Intrinsics hiding (MethodSpec, MethodSpecBuilder)
import qualified Mir.Intrinsics as M
import qualified Mir.Mir as M

import Mir.Compositional.Clobber
import Mir.Compositional.Convert
import Mir.Compositional.Override (MethodSpec(..))


data MethodSpecBuilder sym t = MethodSpecBuilder
    { _msbCollectionState :: CollectionState
    , _msbSharedContext :: SAW.SharedContext
    , _msbEval :: forall tp. W4.Expr t tp -> IO SAW.Term

    , _msbSpec :: MIRMethodSpec
    , _msbPre :: StateExtra sym t
    , _msbPost :: StateExtra sym t
    , _msbNextAlloc :: MS.AllocIndex
    , _msbSnapshotFrame :: FrameIdentifier
    , _msbVisitCache :: W4.IdxCache t (Const ())
    -- | Substitutions to apply to the entire `MethodSpec` after construction.
    -- These are generated in place of equality postconditions to improve
    -- performance.  Variables that appear on the LHS of an entry here will be
    -- removed from the `MethodSpec`'s fresh variable lists.  Substitutions are
    -- applied in the order listed.
    , _msbSubsts :: [(SAW.ExtCns SAW.Term, SAW.Term)]
    }

data StateExtra sym t = StateExtra
    { _seVars :: Set (Some (W4.ExprBoundVar t))
    , _seRefs :: Seq (Some (FoundRef sym))
    , _seNewRefs :: Seq (Some (FoundRef sym))
    }

data FoundRef sym tp = FoundRef
    { _frAlloc :: MS.AllocIndex
    , _frAllocSpec :: MirAllocSpec tp
    , _frRef :: MirReferenceMux sym tp
    }

initMethodSpecBuilder ::
    CollectionState ->
    SAW.SharedContext ->
    (forall tp. W4.Expr t tp -> IO SAW.Term) ->
    MIRMethodSpec ->
    FrameIdentifier ->
    W4.IdxCache t (Const ()) ->
    MethodSpecBuilder sym t
initMethodSpecBuilder cs sc eval spec snap cache = MethodSpecBuilder
    { _msbCollectionState = cs
    , _msbSharedContext = sc
    , _msbEval = eval
    , _msbSpec = spec
    , _msbPre = initStateExtra
    , _msbPost = initStateExtra
    , _msbNextAlloc = MS.AllocIndex 0
    , _msbSnapshotFrame = snap
    , _msbVisitCache = cache
    , _msbSubsts = []
    }

initStateExtra :: StateExtra sym t
initStateExtra = StateExtra
    { _seVars = Set.empty
    , _seRefs = Seq.empty
    , _seNewRefs = Seq.empty
    }

makeLenses ''MethodSpecBuilder
makeLenses ''StateExtra
makeLenses ''FoundRef

msbCollection :: Functor f =>
    (M.Collection -> f M.Collection) ->
    (MethodSpecBuilder sym t -> f (MethodSpecBuilder sym t))
msbCollection = msbCollectionState . collection

frType :: Functor f =>
    (TypeRepr tp -> f (TypeRepr tp)) ->
    (FoundRef sym tp -> f (FoundRef sym tp))
frType = frAllocSpec . maType

frMirType :: Functor f =>
    (M.Ty -> f M.Ty) ->
    (FoundRef sym tp -> f (FoundRef sym tp))
frMirType = frAllocSpec . maMirType


data PrePost = Pre | Post
    deriving (Show, Eq)

msbPrePost :: Functor f =>
    PrePost ->
    (StateExtra sym t -> f (StateExtra sym t)) ->
    MethodSpecBuilder sym t -> f (MethodSpecBuilder sym t)
msbPrePost Pre = msbPre
msbPrePost Post = msbPost

csPrePostState :: Functor f =>
    PrePost ->
    (MS.StateSpec MIR -> f (MS.StateSpec MIR)) ->
    MS.CrucibleMethodSpecIR MIR -> f (MS.CrucibleMethodSpecIR MIR)
csPrePostState Pre = MS.csPreState
csPrePostState Post = MS.csPostState

type BuilderT sym t m a = StateT (MethodSpecBuilder sym t) m a

execBuilderT :: Monad m =>
    MethodSpecBuilder sym t -> BuilderT sym t m () -> m (MethodSpecBuilder sym t)
execBuilderT s f = execStateT f s

-- | A `RegValue` and its associated `TypeRepr`.
data MethodSpecValue sym tp = MethodSpecValue (TypeRepr tp) (RegValue sym tp)


instance (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
        MethodSpecBuilderImpl sym (MethodSpecBuilder sym t) where
    msbAddArg = addArg
    msbSetReturn = setReturn
    msbGatherAssumes = gatherAssumes
    msbGatherAsserts = gatherAsserts
    msbFinish = finish


-- MethodSpecBuilder implementation.  This is the code that actually runs when
-- Rust invokes `msb.add_arg(...)` or similar.

builderNew :: forall sym p t st fs rtp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    CollectionState ->
    -- | `DefId` of the `builder_new` monomorphization.  Its `Instance` should
    -- have one type argument, which is the `TyFnDef` of the function that the
    -- spec applies to.
    DefId ->
    OverrideSim (p sym) sym MIR rtp
        EmptyCtx MethodSpecBuilderType (MethodSpecBuilder sym t)
builderNew cs defId =
  ovrWithBackend $ \bak -> do
    let sym = backendGetSym bak
    snapFrame <- liftIO $ pushAssumptionFrame bak

    let tyArg = cs ^? collection . M.intrinsics . ix defId .
            M.intrInst . M.inSubsts . _Wrapped . ix 0
    fnDefId <- case tyArg of
        Just (M.TyFnDef did) -> return did
        _ -> error $ "expected TyFnDef argument, but got " ++ show tyArg
    let sig = case cs ^? collection . M.functions . ix fnDefId . M.fsig of
            Just x -> x
            _ -> error $ "failed to look up sig of " ++ show fnDefId

    let loc = mkProgramLoc (functionNameFromText $ idText defId) InternalPos
    let ms :: MIRMethodSpec = MS.makeCrucibleMethodSpecIR fnDefId
            (sig ^. M.fsarg_tys) (Just $ sig ^. M.fsreturn_ty) loc cs
    visitCache <- W4.newIdxCache

    sc <- liftIO $ SAW.mkSharedContext
    liftIO $ SAW.scLoadPreludeModule sc
    scs <- liftIO $ SAW.newSAWCoreState sc

    let eval :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval x = SAW.toSC sym scs x

    return $ initMethodSpecBuilder cs sc eval ms snapFrame visitCache

-- | Add a value to the MethodSpec's argument list.  The value is obtained by
-- dereferencing `argRef`.
--
-- As a side effect, this clobbers any mutable memory reachable through the
-- argument.  For example, if `argRef` points to an `&mut i32`, the `i32` will
-- be overwritten with a fresh symbolic variable.
addArg :: forall sym p t st fs rtp args ret tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    TypeRepr tp -> MirReferenceMux sym tp -> MethodSpecBuilder sym t ->
    OverrideSim (p sym) sym MIR rtp args ret (MethodSpecBuilder sym t)
addArg tpr argRef msb =
  ovrWithBackend $ \bak ->
  execBuilderT msb $ do
    let sym = backendGetSym bak
    loc <- liftIO $ W4.getCurrentProgramLoc sym

    let idx = Map.size $ msb ^. msbSpec . MS.csArgBindings
    let ty = case msb ^? msbSpec . MS.csArgs . ix idx of
            Just x -> x
            Nothing -> error $ "arg index out of range: " ++ show idx
    let shp = tyToShapeEq col ty tpr

    rv <- lift $ readMirRefSim tpr argRef
    sv <- regToSetup bak Pre (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv

    void $ forNewRefs Pre $ \fr -> do
        let allocSpec = fr ^. frAllocSpec
        let len = allocSpec ^. maLen
        let md = allocSpec ^. maConditionMetadata
        svPairs <- forM [0 .. len - 1] $ \i -> do
            -- Record a points-to entry
            iSym <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $ fromIntegral i
            ref' <- lift $ mirRef_offsetSim (fr ^. frType) (fr ^. frRef) iSym
            rv <- lift $ readMirRefSim (fr ^. frType) ref'
            let shp = tyToShapeEq col (fr ^. frMirType) (fr ^. frType)
            sv <- regToSetup bak Pre (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv

            -- Clobber the current value
            rv' <- case fr ^. frAllocSpec . maMutbl of
                M.Mut -> lift $ clobberSymbolic sym loc "clobberArg" shp rv
                M.Immut -> lift $ clobberImmutSymbolic sym loc "clobberArg" shp rv
            lift $ writeMirRefSim (fr ^. frType) ref' rv'
            -- Gather fresh vars created by the clobber operation
            sv' <- regToSetup bak Post (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv'

            return (sv, sv')

        let (svs, svs') = unzip svPairs
        msbSpec . MS.csPreState . MS.csPointsTos %= (MirPointsTo md (MS.SetupVar (fr ^. frAlloc)) svs :)
        msbSpec . MS.csPostState . MS.csPointsTos %= (MirPointsTo md (MS.SetupVar (fr ^. frAlloc)) svs' :)

    msbSpec . MS.csArgBindings . at (fromIntegral idx) .= Just (ty, sv)
  where
    col = msb ^. msbCollection
    sc = msb ^. msbSharedContext
    eval :: forall tp. W4.Expr t tp -> IO SAW.Term
    eval = msb ^. msbEval

-- | Set the MethodSpec's return value.  The value to use is obtained by
-- dereferencing `argRef`.
setReturn :: forall sym t st fs p rtp args ret tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    TypeRepr tp -> MirReferenceMux sym tp -> MethodSpecBuilder sym t ->
    OverrideSim p sym MIR rtp args ret (MethodSpecBuilder sym t)
setReturn tpr argRef msb =
  ovrWithBackend $ \bak ->
  execBuilderT msb $ do
    let sym = backendGetSym bak
    let ty = case msb ^. msbSpec . MS.csRet of
            Just x -> x
            Nothing -> M.TyTuple []
    let shp = tyToShapeEq col ty tpr

    rv <- lift $ readMirRefSim tpr argRef
    sv <- regToSetup bak Post (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv

    void $ forNewRefs Post $ \fr -> do
        let allocSpec = fr ^. frAllocSpec
        let len = allocSpec ^. maLen
        let md = allocSpec ^. maConditionMetadata
        svs <- forM [0 .. len - 1] $ \i -> do
            -- Record a points-to entry
            iSym <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $ fromIntegral i
            ref' <- lift $ mirRef_offsetSim (fr ^. frType) (fr ^. frRef) iSym
            rv <- lift $ readMirRefSim (fr ^. frType) ref'
            let shp = tyToShapeEq col (fr ^. frMirType) (fr ^. frType)
            regToSetup bak Post (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv

        msbSpec . MS.csPostState . MS.csPointsTos %= (MirPointsTo md (MS.SetupVar (fr ^. frAlloc)) svs :)

    msbSpec . MS.csRetValue .= Just sv
  where
    col = msb ^. msbCollection
    sc = msb ^. msbSharedContext
    eval :: forall tp. W4.Expr t tp -> IO SAW.Term
    eval = msb ^. msbEval

-- | Gather assumptions from the current context to serve as the `MethodSpec`'s
-- preconditions.  We only include assumptions that constrain symbolic
-- variables seen in the function's inputs (arguments and memory reachable
-- through arguments).
gatherAssumes :: forall sym t st fs p rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    MethodSpecBuilder sym t ->
    OverrideSim p sym MIR rtp args ret (MethodSpecBuilder sym t)
gatherAssumes msb =
  ovrWithBackend $ \bak -> do
    let sym = backendGetSym bak

    -- Find all vars that are mentioned in the arguments.
    let vars = msb ^. msbPre . seVars

    -- Find all assumptions that mention a relevant variable.
    assumes <- liftIO $ collectAssumptions bak
    flatAssumes <- liftIO $ flattenAssumptions sym assumes
    optAssumes' <- liftIO $ relevantPreds sym vars $
        map (\a -> (assumptionPred a, show $ ppAssumption PP.viaShow a)) $ flatAssumes
    let assumes' = case optAssumes' of
            Left (pred, msg, Some v) ->
                error $ "assumption `" ++ show pred ++ "` (" ++ show msg ++
                    ") references variable " ++ show v ++ " (" ++ show (W4.bvarName v) ++ " at " ++
                    show (W4.bvarLoc v) ++ "), which does not appear in the function args"
            Right x -> map fst x

    let loc = msb ^. msbSpec . MS.csLoc
    assumeConds <- liftIO $ forM assumes' $ \pred -> do
        tt <- eval pred >>= SAW.mkTypedTerm sc
        let md = MS.ConditionMetadata
                 { MS.conditionLoc = loc
                 , MS.conditionTags = mempty
                 , MS.conditionType = "specification assertion"
                 , MS.conditionContext = ""
                 }
        return $ MS.SetupCond_Pred md tt
    newVars <- liftIO $ gatherVars sym [Some (MethodSpecValue BoolRepr pred) | pred <- assumes']

    return $ msb
        & msbSpec . MS.csPreState . MS.csConditions %~ (++ assumeConds)
        & msbPre . seVars %~ Set.union newVars
  where
    sc = msb ^. msbSharedContext
    eval :: forall tp. W4.Expr t tp -> IO SAW.Term
    eval = msb ^. msbEval

-- | Gather assertions from the current context to serve as the `MethodSpec`'s
-- postconditions.  We only include assertions that constraint symbolic
-- variables seen in the functions inputs or outputs (arguments, return value,
-- and memory reachable through either).
gatherAsserts :: forall sym t st fs p rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    MethodSpecBuilder sym t ->
    OverrideSim p sym MIR rtp args ret (MethodSpecBuilder sym t)
gatherAsserts msb =
  ovrWithBackend $ \bak -> do
    let sym = backendGetSym bak

    -- Find all vars that are mentioned in the arguments or return value.
    let vars = (msb ^. msbPre . seVars) `Set.union` (msb ^. msbPost . seVars)

    -- Find all assertions that mention a relevant variable.
    goals <- liftIO $ maybe [] goalsToList <$> getProofObligations bak
    let asserts = map proofGoal goals
    optAsserts' <- liftIO $ relevantPreds sym vars $
        map (\a -> (a ^. W4.labeledPred, a ^. W4.labeledPredMsg)) asserts
    let asserts' = case optAsserts' of
            Left (pred, msg, Some v) ->
                error $ "assertion `" ++ show pred ++ "` (" ++ show msg ++
                    ") references variable " ++ show v ++ " (" ++ show (W4.bvarName v) ++ " at " ++
                    show (W4.bvarLoc v) ++ "), which does not appear in the function args"
            Right x -> map fst x
    newVars <- liftIO $ gatherVars sym [Some (MethodSpecValue BoolRepr pred) | pred <- asserts']
    let postVars' = Set.union (msb ^. msbPost . seVars) newVars
    let postOnlyVars = postVars' `Set.difference` (msb ^. msbPre . seVars)

    (asserts'', substs) <- liftIO $
        gatherSubsts postOnlyVars vars [] [] asserts'
    substTerms <- forM substs $ \(Pair var expr) -> do
        varTerm <- liftIO $ eval $ W4.BoundVarExpr var
        varEc <- case SAW.asExtCns varTerm of
            Just ec -> return ec
            Nothing -> error $ "eval of BoundVarExpr produced non-ExtCns ?" ++ show varTerm
        exprTerm <- liftIO $ eval expr
        return (varEc, exprTerm)

    let loc = msb ^. msbSpec . MS.csLoc
    assertConds <- liftIO $ forM asserts'' $ \pred -> do
        tt <- eval pred >>= SAW.mkTypedTerm sc
        let md = MS.ConditionMetadata
                 { MS.conditionLoc = loc
                 , MS.conditionTags = mempty
                 , MS.conditionType = "specification condition"
                 , MS.conditionContext = ""
                 }
        return $ MS.SetupCond_Pred md tt

    return $ msb
        & msbSpec . MS.csPostState . MS.csConditions %~ (++ assertConds)
        & msbPost . seVars .~ postVars'
        & msbSubsts %~ (++ substTerms)

  where
    sc = msb ^. msbSharedContext
    eval :: forall tp. W4.Expr t tp -> IO SAW.Term
    eval = msb ^. msbEval

    -- | Find assertions of the form `var == expr` that are suitable for
    -- performing substitutions, and separate them from the list of assertions.
    gatherSubsts ::
        Set (Some (W4.ExprBoundVar t)) ->
        Set (Some (W4.ExprBoundVar t)) ->
        [W4.Expr t BaseBoolType] ->
        [Pair (W4.ExprBoundVar t) (W4.Expr t)] ->
        [W4.Expr t BaseBoolType] ->
        IO ([W4.Expr t BaseBoolType], [Pair (W4.ExprBoundVar t) (W4.Expr t)])
    gatherSubsts _lhsOk _rhsOk accPreds accSubsts [] =
        return (reverse accPreds, reverse accSubsts)
    gatherSubsts lhsOk rhsOk accPreds accSubsts (pred : preds)
      | Just (Pair var expr) <- asVarEqExpr pred = do
        rhsSeenRef <- newIORef Set.empty
        cache <- W4.newIdxCache
        visitExprVars cache expr $ \var -> modifyIORef rhsSeenRef $ Set.insert (Some var)
        rhsSeen <- readIORef rhsSeenRef
        let lhsOk' = Set.delete (Some var) lhsOk
        let rhsOk' = Set.delete (Some var) rhsOk
        -- We can't use `pred` as a substitution if the RHS contains variables
        -- that were deleted by a previous substitution.  Otherwise we'd end up
        -- re-introducing a deleted variable.  We also can't do substitutions
        -- where the RHS expression contains the LHS variable, which is why we
        -- check against `rhsOk'` here instead of `rhsOk`.
        if rhsSeen `Set.isSubsetOf` rhsOk' then
            gatherSubsts lhsOk' rhsOk' accPreds (Pair var expr : accSubsts) preds
          else
            gatherSubsts lhsOk rhsOk (pred : accPreds) accSubsts preds
      | otherwise =
        gatherSubsts lhsOk rhsOk (pred : accPreds) accSubsts preds
      where
        asVarEqExpr pred
          | Just (W4.BaseEq _btpr x y) <- W4.asApp pred
          , W4.BoundVarExpr v <- x
          , Set.member (Some v) lhsOk
          = Just (Pair v y)
          | Just (W4.BaseEq _btpr x y) <- W4.asApp pred
          , W4.BoundVarExpr v <- y
          , Set.member (Some v) lhsOk
          = Just (Pair v x)
          | otherwise = Nothing


-- | Collect all the symbolic variables that appear in `vals`.
gatherVars ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    [Some (MethodSpecValue sym)] ->
    IO (Set (Some (W4.ExprBoundVar t)))
gatherVars sym vals = do
    varsRef <- newIORef Set.empty
    cache <- W4.newIdxCache
    forM_ vals $ \(Some (MethodSpecValue tpr arg)) ->
        visitRegValueExprs sym tpr arg $ \expr ->
            visitExprVars cache expr $ \v ->
                modifyIORef' varsRef $ Set.insert (Some v)
    readIORef varsRef

-- | Collect all the predicates from `preds` that mention at least one variable
-- in `vars`.  Return `Left (pred, info, badVar)` if it finds a predicate
-- `pred` that mentions at least one variable in `vars` along with some
-- `badVar` not in `vars`.
relevantPreds :: forall sym t st fs a.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    Set (Some (W4.ExprBoundVar t)) ->
    [(W4.Pred sym, a)] ->
    IO (Either (W4.Pred sym, a, Some (W4.ExprBoundVar t)) [(W4.Pred sym, a)])
relevantPreds _sym vars preds = runExceptT $ filterM check preds
  where
    check (pred, info) = do
        sawRel <- lift $ newIORef False
        sawIrrel <- lift $ newIORef Nothing

        cache <- W4.newIdxCache
        lift $ visitExprVars cache pred $ \v ->
            if Set.member (Some v) vars then
                writeIORef sawRel True
            else
                writeIORef sawIrrel (Just $ Some v)
        sawRel' <- lift $ readIORef sawRel
        sawIrrel' <- lift $ readIORef sawIrrel

        case (sawRel', sawIrrel') of
            (True, Just badVar) -> throwError (pred, info, badVar)
            (True, Nothing) -> return True
            (False, _) -> return False


-- | Apply final adjustments to the MethodSpec being built and return it.
--
-- As a side effect, this discards the obligations established during
-- MethodSpec building.  The only purpose of assertions in a spec function is
-- to set up the MethodSpec postconditions, and once that's done, there is no
-- use for them.  Plus, they will almost certainly fail - we don't actually
-- invoke the subject function during MethodSpec building, so all its outputs
-- contain arbitrary (symbolic) values.
finish :: forall sym t st fs p rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    MethodSpecBuilder sym t ->
    OverrideSim p sym MIR rtp args ret (M.MethodSpec sym)
finish msb =
  ovrWithBackend $ \bak -> do
    let sym = backendGetSym bak
    let ng  = sym ^. W4.exprCounter

    -- TODO: also undo any changes to Crucible global variables / refcells
    -- (correct spec functions shouldn't make such changes, but it would be
    -- nice to warn the user if they accidentally do)
    _ <- liftIO $ popAssumptionFrameAndObligations bak (msb ^. msbSnapshotFrame)

    let preVars = msb ^. msbPre . seVars
    let postVars = msb ^. msbPost . seVars
    let postOnlyVars = postVars `Set.difference` preVars

    preVars' <- liftIO $ mapM (\(Some x) -> evalVar x) $ toList preVars
    postVars' <- liftIO $ mapM (\(Some x) -> evalVar x) $ toList postOnlyVars

    let preAllocs = Map.fromList [(fr ^. frAlloc, Some $ fr ^. frAllocSpec)
            | Some fr <- toList $ msb ^. msbPre . seRefs]
    let postAllocs = Map.fromList [(fr ^. frAlloc, Some $ fr ^. frAllocSpec)
            | Some fr <- toList $ msb ^. msbPost . seRefs]

    let ms = msb ^. msbSpec
            & MS.csPreState . MS.csFreshVars .~ preVars'
            & MS.csPreState . MS.csAllocs .~ preAllocs
            & MS.csPostState . MS.csFreshVars .~ postVars'
            & MS.csPostState . MS.csAllocs .~ postAllocs
    sm <- liftIO $ buildSubstMap (msb ^. msbSharedContext) (msb ^. msbSubsts)
    ms' <- liftIO $ substMethodSpec (msb ^. msbSharedContext) sm ms

    nonce <- liftIO $ freshNonce ng
    return $ M.MethodSpec (MethodSpec (msb ^. msbCollectionState) ms') (indexValue nonce)

  where
    sc = msb ^. msbSharedContext
    eval :: forall tp. W4.Expr t tp -> IO SAW.Term
    eval = msb ^. msbEval

    evalVar :: forall tp.
        W4.ExprBoundVar t tp -> IO SAW.TypedExtCns
    evalVar var = do
        tt <- eval (W4.BoundVarExpr var) >>= SAW.mkTypedTerm sc
        case SAW.asTypedExtCns tt of
            Just x -> return x
            Nothing -> error $ "BoundVarExpr translated to non-ExtCns term? " ++ show tt


buildSubstMap ::
    SAW.SharedContext ->
    [(SAW.ExtCns SAW.Term, SAW.Term)] ->
    IO (Map SAW.VarIndex SAW.Term)
buildSubstMap sc substs = go Map.empty substs
  where
    go sm [] = return sm
    go sm ((ec, term) : substs) = do
        -- Rewrite the RHSs of previous substitutions using the current one.
        let sm1 = Map.singleton (SAW.ecVarIndex ec) term
        sm' <- mapM (SAW.scInstantiateExt sc sm1) sm
        -- Add the current subst and continue.
        go (Map.insert (SAW.ecVarIndex ec) term sm') substs

substMethodSpec ::
    SAW.SharedContext ->
    Map SAW.VarIndex SAW.Term ->
    MIRMethodSpec ->
    IO MIRMethodSpec
substMethodSpec sc sm ms = do
    preState' <- goState $ ms ^. MS.csPreState
    postState' <- goState $ ms ^. MS.csPostState
    argBindings' <- mapM goArg $ ms ^. MS.csArgBindings
    retValue' <- mapM goSetupValue $ ms ^. MS.csRetValue
    return $ ms
        & MS.csPreState .~ preState'
        & MS.csPostState .~ postState'
        & MS.csArgBindings .~ argBindings'
        & MS.csRetValue .~ retValue'

  where
    goState ss = do
        pointsTos' <- mapM goPointsTo $ ss ^. MS.csPointsTos
        conditions' <- mapM goSetupCondition $ ss ^. MS.csConditions
        let freshVars' =
                filter (\tec -> not $ Map.member (SAW.ecVarIndex $ SAW.tecExt tec) sm) $
                    ss ^. MS.csFreshVars
        return $ ss
            & MS.csPointsTos .~ pointsTos'
            & MS.csConditions .~ conditions'
            & MS.csFreshVars .~ freshVars'

    goArg (ty, sv) = do
        sv' <- goSetupValue sv
        return (ty, sv')

    goPointsTo (MirPointsTo md alloc svs) = MirPointsTo md alloc <$> mapM goSetupValue svs

    goSetupValue sv = case sv of
        MS.SetupVar _ -> return sv
        MS.SetupTerm tt -> MS.SetupTerm <$> goTypedTerm tt
        MS.SetupNull _ -> return sv
        MS.SetupStruct b svs -> MS.SetupStruct b <$> mapM goSetupValue svs
        MS.SetupTuple b svs -> MS.SetupTuple b <$> mapM goSetupValue svs
        MS.SetupSlice slice -> MS.SetupSlice <$> goSetupSlice slice
        MS.SetupEnum enum_ -> MS.SetupEnum <$> goSetupEnum enum_
        MS.SetupArray b svs -> MS.SetupArray b <$> mapM goSetupValue svs
        MS.SetupElem b sv idx -> MS.SetupElem b <$> goSetupValue sv <*> pure idx
        MS.SetupField b sv name -> MS.SetupField b <$> goSetupValue sv <*> pure name
        MS.SetupCast v _ -> case v of {}
        MS.SetupUnion v _ _ -> case v of {}
        MS.SetupGlobal _ _ -> return sv
        MS.SetupGlobalInitializer _ _ -> return sv
        MS.SetupMux b c t f -> MS.SetupMux b <$> goTypedTerm c <*> goSetupValue t <*> goSetupValue f

    goSetupCondition (MS.SetupCond_Equal loc sv1 sv2) =
        MS.SetupCond_Equal loc <$> goSetupValue sv1 <*> goSetupValue sv2
    goSetupCondition (MS.SetupCond_Pred loc tt) =
        MS.SetupCond_Pred loc <$> goTypedTerm tt
    goSetupCondition (MS.SetupCond_Ghost loc gg tt) =
        MS.SetupCond_Ghost loc gg <$> goTypedTerm tt

    goSetupEnum (MirSetupEnumVariant adt variant variantIdx svs) =
      MirSetupEnumVariant adt variant variantIdx <$>
      mapM goSetupValue svs
    goSetupEnum (MirSetupEnumSymbolic adt discr variants) =
      MirSetupEnumSymbolic adt <$>
      goSetupValue discr <*>
      mapM (mapM goSetupValue) variants

    goSetupSlice (MirSetupSliceRaw ref len) =
      MirSetupSliceRaw <$> goSetupValue ref <*> goSetupValue len
    goSetupSlice (MirSetupSlice sliceInfo arr) =
      MirSetupSlice sliceInfo <$> goSetupValue arr
    goSetupSlice (MirSetupSliceRange sliceInfo arr start end) = do
      arr' <- goSetupValue arr
      pure $ MirSetupSliceRange sliceInfo arr' start end

    goTypedTerm tt = do
        term' <- goTerm $ SAW.ttTerm tt
        return $ tt { SAW.ttTerm = term' }

    goTerm term = SAW.scInstantiateExt sc sm term



-- RegValue -> SetupValue conversion

-- | Convert a RegValue into a SetupValue pattern.  Symbolic variables in the
-- RegValue will be converted into fresh variables in the MethodSpec (in either
-- the pre or post state, depending on the pre/post flag `p`), and any
-- MirReferences will be converted into MethodSpec allocations/pointers.
regToSetup :: forall sym bak t st fs tp p rtp args ret.
    (IsSymBackend sym bak, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    bak -> PrePost ->
    (forall tp'. BaseTypeRepr tp' -> W4.Expr t tp' -> IO SAW.TypedTerm) ->
    TypeShape tp -> RegValue sym tp ->
    BuilderT sym t (OverrideSim p sym MIR rtp args ret) (MS.SetupValue MIR)
regToSetup bak p eval shp rv = go shp rv
  where
    sym = backendGetSym bak

    go :: forall tp. TypeShape tp -> RegValue sym tp ->
        BuilderT sym t (OverrideSim p sym MIR rtp args ret) (MS.SetupValue MIR)
    go (UnitShape _) () = return $ MS.SetupTuple () []
    go (PrimShape _ btpr) expr = do
        -- Record all vars used in `expr`
        cache <- use msbVisitCache
        visitExprVars cache expr $ \var -> do
            msbPrePost p . seVars %= Set.insert (Some var)
        liftIO $ MS.SetupTerm <$> eval btpr expr
    go (TupleShape _ _ flds) rvs = MS.SetupTuple () <$> goFields flds rvs
    go (ArrayShape _ elemTy shp) vec = do
        svs <- case vec of
            MirVector_Vector v -> mapM (go shp) (toList v)
            MirVector_PartialVector v -> forM (toList v) $ \p -> do
                rv <- liftIO $ readMaybeType sym "vector element" (shapeType shp) p
                go shp rv
            MirVector_Array _ -> error $ "regToSetup: MirVector_Array NYI"
        return $ MS.SetupArray elemTy svs
    go (StructShape tyAdt _ flds) (AnyValue tpr rvs)
      | Just Refl <- testEquality tpr shpTpr =
        case tyAdt of
          M.TyAdt adtName _ _ -> do
            mbAdt <- use $ msbCollection . M.adts . at adtName
            case mbAdt of
              Just adt -> MS.SetupStruct adt <$> goFields flds rvs
              Nothing -> error $ "regToSetup: Could not find ADT named: "
                              ++ show adtName
          _ -> error $ "regToSetup: Found non-ADT type for struct: "
                    ++ show (PP.pretty tyAdt)
      | otherwise = error $ "regToSetup: type error: expected " ++ show shpTpr ++
        ", but got Any wrapping " ++ show tpr
      where shpTpr = StructRepr $ fmapFC fieldShapeType flds
    go (TransparentShape _ shp) rv = go shp rv
    go (RefShape refTy ty' _ tpr) ref = do
        partIdxLen <- lift $ mirRef_indexAndLenSim ref
        optIdxLen <- liftIO $ readPartExprMaybe sym partIdxLen
        let (optIdx, optLen) =
                (BV.asUnsigned <$> (W4.asBV =<< (fst <$> optIdxLen)),
                    BV.asUnsigned <$> (W4.asBV =<< (snd <$> optIdxLen)))
        idx <- case optIdx of
            Just x -> return $ fromIntegral x
            Nothing -> error $ "unsupported: reference has symbolic offset within allocation " ++
                "(for a ref of type " ++ show refTy ++ ")"
        len <- case optLen of
            Just x -> return $ fromIntegral x
            Nothing -> error $ "unsupported: memory allocation has symbolic size " ++
                "(for a ref of type " ++ show refTy ++ ")"
        -- Offset backward by `idx` to get a pointer to the start of the accessible
        -- allocation.
        offsetSym <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $ fromIntegral $ negate idx
        startRef <- lift $ mirRef_offsetWrapSim tpr ref offsetSym

        -- Casting &T -> &mut T is undefined behavior, so we can safely mark
        -- Immut refs as Immut.  But casting *const T -> *mut T is allowed, so
        -- we conservatively mark *const T as Mut.
        let mutbl = case refTy of
                M.TyRef _ M.Immut -> M.Immut
                _ -> M.Mut
        alloc <- refToAlloc bak p mutbl ty' tpr startRef len
        let offsetSv idx sv = if idx == 0 then sv else MS.SetupElem () sv idx
        return $ offsetSv idx $ MS.SetupVar alloc
    go (SliceShape _ ty mutbl tpr) (Empty :> RV refRV :> RV lenRV) = do
        let (refShp, lenShp) = sliceShapeParts ty mutbl tpr
        refSV <- go refShp refRV
        lenSV <- go lenShp lenRV
        pure $ MS.SetupSlice $ MirSetupSliceRaw refSV lenSV
    go (EnumShape _ _ _ _ _) _ =
      error "Enums not currently supported in overrides"
    go (FnPtrShape _ _ _) _ =
        error "Function pointers not currently supported in overrides"

    goFields :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
        BuilderT sym t (OverrideSim p sym MIR rtp args ret) [MS.SetupValue MIR]
    goFields flds rvs = loop flds rvs []
      where
        loop :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
            [MS.SetupValue MIR] ->
            BuilderT sym t (OverrideSim p sym MIR rtp args ret) [MS.SetupValue MIR]
        loop Empty Empty svs = return svs
        loop (flds :> fld) (rvs :> RV rv) svs = do
            sv <- case fld of
                ReqField shp -> go shp rv
                OptField shp -> liftIO (readMaybeType sym "field" (shapeType shp) rv) >>= go shp
            loop flds rvs (sv : svs)

refToAlloc :: forall sym bak t st fs tp p rtp args ret.
    (IsSymBackend sym bak, sym ~ W4.ExprBuilder t st fs) =>
    bak -> PrePost -> M.Mutability -> M.Ty -> TypeRepr tp -> MirReferenceMux sym tp -> Int ->
    BuilderT sym t (OverrideSim p sym MIR rtp args ret) MS.AllocIndex
refToAlloc bak p mutbl ty tpr ref len = do
    refs <- use $ msbPrePost p . seRefs
    mAlloc <- liftIO $ lookupAlloc ref (toList refs)
    case mAlloc of
        Nothing -> do
            alloc <- use msbNextAlloc
            msbNextAlloc %= MS.nextAllocIndex
            let sym = backendGetSym bak
            loc <- liftIO $ W4.getCurrentProgramLoc sym
            let md = MS.ConditionMetadata
                     { MS.conditionLoc = loc
                     , MS.conditionTags = mempty
                     , MS.conditionType = "reference-to-allocation conversion"
                     , MS.conditionContext = ""
                     }
            let fr = FoundRef alloc (MirAllocSpec md tpr mutbl ty len) ref
            msbPrePost p . seRefs %= (Seq.|> Some fr)
            msbPrePost p . seNewRefs %= (Seq.|> Some fr)
            return alloc
        Just alloc -> return alloc
  where
    -- | Get the MethodSpec `AllocIndex` corresponding to the MirReference
    -- `ref`.  If there is no such allocation yet, then add a new one.
    --
    -- If the presence of `ref` in the list is unknown (symbolic), this is an
    -- error, since it means some allocations might be aliased under some
    -- assignments to the symbolic variables but not under others.
    lookupAlloc ::
        MirReferenceMux sym tp ->
        [Some (FoundRef sym)] ->
        IO (Maybe MS.AllocIndex)
    lookupAlloc _ref [] = return Nothing
    lookupAlloc ref (Some fr : frs) = case testEquality tpr (fr ^. frType) of
        Just Refl -> do
            eq <- mirRef_eqIO bak ref (fr ^. frRef)
            case W4.asConstantPred eq of
                Just True -> return $ Just $ fr ^. frAlloc
                Just False -> lookupAlloc ref frs
                Nothing -> error $ "refToAlloc: ref aliasing depends on symbolic values"
        Nothing -> lookupAlloc ref frs

-- | Run `f` on any newly-added refs/allocations in the MethodSpecBuilder.  If
-- `f` adds more refs, then repeat until there are no more new refs remaining.
forNewRefs ::
    Monad m =>
    PrePost ->
    (forall tp. FoundRef sym tp -> BuilderT sym t m a) ->
    BuilderT sym t m (Seq a)
forNewRefs p f = go
  where
    go = do
        new <- use $ msbPrePost p . seNewRefs
        msbPrePost p . seNewRefs .= Seq.empty
        if Seq.null new then
            return Seq.empty
          else do
            a <- mapM (\(Some fr) -> f fr) new
            b <- go
            return $ a <> b
