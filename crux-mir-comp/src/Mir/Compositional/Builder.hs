{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}

module Mir.Compositional.Builder
where

import Control.Lens
    (makeLenses, (^.), (^?), (%=), (.=), (&), (.~), (%~), use, at, ix, _Wrapped)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Data.Functor.Const
import Data.IORef
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

import qualified What4.Expr.Builder as W4
import What4.FunctionName (functionNameFromText)
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import What4.ProgramLoc

import Lang.Crucible.Backend
import Lang.Crucible.Simulator
import Lang.Crucible.Types

import qualified Verifier.SAW.Prelude as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Simulator.What4.ReturnTrip as SAW
import qualified Verifier.SAW.TypedTerm as SAW

import qualified SAWScript.Crucible.Common.MethodSpec as MS

import Crux.Types (Model)

import Mir.DefId
import Mir.Generator (CollectionState, collection)
import Mir.Intrinsics hiding (MethodSpec, MethodSpecBuilder)
import qualified Mir.Intrinsics as M
import qualified Mir.Mir as M

import Mir.Compositional.Clobber
import Mir.Compositional.Convert
import Mir.Compositional.MethodSpec
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
    }

data StateExtra sym t = StateExtra
    { _seVars :: Set (Some (W4.ExprBoundVar t))
    , _seRefs :: Seq (Pair TypeRepr (MirReferenceMux sym), M.Mutability, M.Ty, MS.AllocIndex)
    , _seNewRefs :: Seq (Pair TypeRepr (MirReferenceMux sym), M.Mutability, M.Ty, MS.AllocIndex)
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
    }

initStateExtra :: StateExtra sym t
initStateExtra = StateExtra
    { _seVars = Set.empty
    , _seRefs = Seq.empty
    , _seNewRefs = Seq.empty
    }

makeLenses ''MethodSpecBuilder
makeLenses ''StateExtra

msbCollection :: Functor f =>
    (M.Collection -> f M.Collection) ->
    (MethodSpecBuilder sym t -> f (MethodSpecBuilder sym t))
msbCollection = msbCollectionState . collection


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

builderNew :: forall sym t st fs rtp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    CollectionState ->
    -- | `DefId` of the `builder_new` monomorphization.  Its `Instance` should
    -- have one type argument, which is the `TyFnDef` of the function that the
    -- spec applies to.
    DefId ->
    OverrideSim (Model sym) sym MIR rtp
        EmptyCtx MethodSpecBuilderType (MethodSpecBuilder sym t)
builderNew cs defId = do
    sym <- getSymInterface
    snapFrame <- liftIO $ pushAssumptionFrame sym

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
addArg :: forall sym t st fs rtp args ret tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    TypeRepr tp -> MirReferenceMux sym tp -> MethodSpecBuilder sym t ->
    OverrideSim (Model sym) sym MIR rtp args ret (MethodSpecBuilder sym t)
addArg tpr argRef msb = execBuilderT msb $ do
    sym <- lift $ getSymInterface
    loc <- liftIO $ W4.getCurrentProgramLoc sym

    let idx = Map.size $ msb ^. msbSpec . MS.csArgBindings
    let ty = case msb ^? msbSpec . MS.csArgs . ix idx of
            Just x -> x
            Nothing -> error $ "arg index out of range: " ++ show idx
    let shp = tyToShapeEq col ty tpr

    rv <- lift $ readMirRefSim tpr argRef
    sv <- regToSetup sym Pre (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv

    void $ forNewRefs Pre $ \tpr ref mutbl ty alloc -> do
        -- Record a points-to entry
        rv <- lift $ readMirRefSim tpr ref
        let shp = tyToShapeEq col ty tpr
        sv <- regToSetup sym Pre (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv
        msbSpec . MS.csPreState . MS.csPointsTos %= (MirPointsTo alloc sv :)

        -- Clobber the current value
        rv' <- case mutbl of
            M.Mut -> lift $ clobberSymbolic sym loc "clobberArg" shp rv
            M.Immut -> lift $ clobberImmutSymbolic sym loc "clobberArg" shp rv
        lift $ writeMirRefSim tpr ref rv'
        -- Gather fresh vars created by the clobber operation
        sv' <- regToSetup sym Post (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv'
        msbSpec . MS.csPostState . MS.csPointsTos %= (MirPointsTo alloc sv' :)

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
setReturn tpr argRef msb = execBuilderT msb $ do
    sym <- lift $ getSymInterface

    let ty = case msb ^. msbSpec . MS.csRet of
            Just x -> x
            Nothing -> M.TyTuple []
    let shp = tyToShapeEq col ty tpr

    rv <- lift $ readMirRefSim tpr argRef
    sv <- regToSetup sym Post (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv

    void $ forNewRefs Post $ \tpr ref _mutbl ty alloc -> do
        rv <- lift $ readMirRefSim tpr ref
        let shp = tyToShapeEq col ty tpr
        sv <- regToSetup sym Post (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv
        msbSpec . MS.csPostState . MS.csPointsTos %= (MirPointsTo alloc sv :)

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
gatherAssumes msb = do
    sym <- getSymInterface

    -- Find all vars that are mentioned in the arguments.
    let vars = msb ^. msbPre . seVars

    -- Find all assumptions that mention a relevant variable.
    assumes <- liftIO $ collectAssumptions sym
    optAssumes' <- liftIO $ relevantPreds sym vars $
        map (\a -> (a ^. W4.labeledPred, a ^. W4.labeledPredMsg)) $ toList assumes
    let assumes' = case optAssumes' of
            Left (pred, msg, Some v) ->
                error $ "assumption `" ++ show pred ++ "` (" ++ show msg ++
                    ") references variable " ++ show v ++ " (" ++ show (W4.bvarName v) ++ " at " ++
                    show (W4.bvarLoc v) ++ "), which does not appear in the function args"
            Right x -> map fst x

    let loc = msb ^. msbSpec . MS.csLoc
    assumeConds <- liftIO $ forM assumes' $ \pred -> do
        tt <- eval pred >>= SAW.mkTypedTerm sc
        return $ MS.SetupCond_Pred loc tt
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
gatherAsserts msb = do
    sym <- getSymInterface

    -- Find all vars that are mentioned in the arguments or return value.
    let vars = (msb ^. msbPre . seVars) `Set.union` (msb ^. msbPost . seVars)

    -- Find all assertions that mention a relevant variable.
    goals <- liftIO $ proofGoalsToList <$> getProofObligations sym
    let asserts = map proofGoal goals
    optAsserts' <- liftIO $ relevantPreds sym vars $
        map (\a -> (a ^. W4.labeledPred, a ^. W4.labeledPredMsg)) asserts
    let asserts' = case optAsserts' of
            Left (pred, msg, Some v) ->
                error $ "assertion `" ++ show pred ++ "` (" ++ show msg ++
                    ") references variable " ++ show v ++ " (" ++ show (W4.bvarName v) ++ " at " ++
                    show (W4.bvarLoc v) ++ "), which does not appear in the function args"
            Right x -> map fst x

    let loc = msb ^. msbSpec . MS.csLoc
    assertConds <- liftIO $ forM asserts' $ \pred -> do
        tt <- eval pred >>= SAW.mkTypedTerm sc
        return $ MS.SetupCond_Pred loc tt
    newVars <- liftIO $ gatherVars sym [Some (MethodSpecValue BoolRepr pred) | pred <- asserts']

    return $ msb
        & msbSpec . MS.csPostState . MS.csConditions %~ (++ assertConds)
        & msbPost . seVars %~ Set.union newVars
  where
    sc = msb ^. msbSharedContext
    eval :: forall tp. W4.Expr t tp -> IO SAW.Term
    eval = msb ^. msbEval

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
    (IsSymInterface sym, IsBoolSolver sym, sym ~ W4.ExprBuilder t st fs) =>
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
finish msb = do
    sym <- getSymInterface
    let ng = W4.exprCounter sym

    -- TODO: also undo any changes to Crucible global variables / refcells
    -- (correct spec functions shouldn't make such changes, but it would be
    -- nice to warn the user if they accidentally do)
    _ <- liftIO $ popAssumptionFrameAndObligations sym (msb ^. msbSnapshotFrame)

    let preVars = msb ^. msbPre . seVars
    let postVars = msb ^. msbPost . seVars
    let postOnlyVars = postVars `Set.difference` preVars

    preVars' <- liftIO $ mapM (\(Some x) -> evalVar x) $ toList preVars
    postVars' <- liftIO $ mapM (\(Some x) -> evalVar x) $ toList postOnlyVars

    let preAllocs = Map.fromList [(alloc, Some $ MirAllocSpec tpr mutbl ty)
            | (Pair tpr _, mutbl, ty, alloc) <- toList $ msb ^. msbPre . seRefs]
    let postAllocs = Map.fromList [(alloc, Some $ MirAllocSpec tpr mutbl ty)
            | (Pair tpr _, mutbl, ty, alloc) <- toList $ msb ^. msbPost . seRefs]

    let ms = msb ^. msbSpec
            & MS.csPreState . MS.csFreshVars .~ preVars'
            & MS.csPreState . MS.csAllocs .~ preAllocs
            & MS.csPostState . MS.csFreshVars .~ postVars'
            & MS.csPostState . MS.csAllocs .~ postAllocs
    nonce <- liftIO $ freshNonce ng

    let ms' = MethodSpec (msb ^. msbCollectionState) ms
    return $ M.MethodSpec ms' (indexValue nonce)

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


-- RegValue -> SetupValue conversion

-- | Convert a RegValue into a SetupValue pattern.  Symbolic variables in the
-- RegValue will be converted into fresh variables in the MethodSpec (in either
-- the pre or post state, depending on the pre/post flag `p`), and any
-- MirReferences will be converted into MethodSpec allocations/pointers.
regToSetup :: forall sym t st fs tp m.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack, MonadIO m) =>
    sym -> PrePost ->
    (forall tp'. BaseTypeRepr tp' -> W4.Expr t tp' -> IO SAW.TypedTerm) ->
    TypeShape tp -> RegValue sym tp -> BuilderT sym t m (MS.SetupValue MIR)
regToSetup sym p eval shp rv = go shp rv
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp -> BuilderT sym t m (MS.SetupValue MIR)
    go (UnitShape _) () = return $ MS.SetupStruct () False []
    go (PrimShape _ btpr) expr = do
        -- Record all vars used in `expr`
        cache <- use msbVisitCache
        visitExprVars cache expr $ \var -> do
            msbPrePost p . seVars %= Set.insert (Some var)
        liftIO $ MS.SetupTerm <$> eval btpr expr
    go (TupleShape _ _ flds) rvs = MS.SetupStruct () False <$> goFields flds rvs
    go (ArrayShape _ _ shp) vec = do
        svs <- case vec of
            MirVector_Vector v -> mapM (go shp) (toList v)
            MirVector_PartialVector v -> forM (toList v) $ \p -> do
                rv <- liftIO $ readMaybeType sym "vector element" (shapeType shp) p
                go shp rv
            MirVector_Array _ -> error $ "regToSetup: MirVector_Array NYI"
        return $ MS.SetupArray () svs
    go (StructShape _ _ flds) (AnyValue tpr rvs)
      | Just Refl <- testEquality tpr shpTpr =
        MS.SetupStruct () False <$> goFields flds rvs
      | otherwise = error $ "regToSetup: type error: expected " ++ show shpTpr ++
        ", but got Any wrapping " ++ show tpr
      where shpTpr = StructRepr $ fmapFC fieldShapeType flds
    go (RefShape refTy ty' tpr) ref = do
        -- Casting &T -> &mut T is undefined behavior, so we can safely mark
        -- Immut refs as Immut.  But casting *const T -> *mut T is allowed, so
        -- we conservatively mark *const T as Mut.
        let mutbl = case refTy of
                M.TyRef _ M.Immut -> M.Immut
                _ -> M.Mut
        alloc <- refToAlloc sym p mutbl ty' tpr ref
        return $ MS.SetupVar alloc

    goFields :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
        BuilderT sym t m [MS.SetupValue MIR]
    goFields flds rvs = loop flds rvs []
      where
        loop :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
            [MS.SetupValue MIR] -> BuilderT sym t m [MS.SetupValue MIR]
        loop Empty Empty svs = return svs
        loop (flds :> fld) (rvs :> RV rv) svs = do
            sv <- case fld of
                ReqField shp -> go shp rv
                OptField shp -> liftIO (readMaybeType sym "field" (shapeType shp) rv) >>= go shp
            loop flds rvs (sv : svs)

refToAlloc :: forall sym t st fs tp m.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, MonadIO m) =>
    sym -> PrePost -> M.Mutability -> M.Ty -> TypeRepr tp -> MirReferenceMux sym tp ->
    BuilderT sym t m MS.AllocIndex
refToAlloc sym p mutbl ty tpr ref = do
    refs <- use $ msbPrePost p . seRefs
    mAlloc <- liftIO $ lookupAlloc ref (toList refs)
    case mAlloc of
        Nothing -> do
            alloc <- use msbNextAlloc
            msbNextAlloc %= MS.nextAllocIndex
            msbPrePost p . seRefs %= (Seq.|> (Pair tpr ref, mutbl, ty, alloc))
            msbPrePost p . seNewRefs %= (Seq.|> (Pair tpr ref, mutbl, ty, alloc))
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
        [(Pair TypeRepr (MirReferenceMux sym), M.Mutability, M.Ty, MS.AllocIndex)] ->
        IO (Maybe MS.AllocIndex)
    lookupAlloc _ref [] = return Nothing
    lookupAlloc ref ((Pair tpr' ref', _, _, alloc) : rs) = case testEquality tpr tpr' of
        Just Refl -> do
            eq <- mirRef_eqIO sym ref ref'
            case W4.asConstantPred eq of
                Just True -> return $ Just alloc
                Just False -> lookupAlloc ref rs
                Nothing -> error $ "refToAlloc: ref aliasing depends on symbolic values"
        Nothing -> lookupAlloc ref rs

-- | Run `f` on any newly-added refs/allocations in the MethodSpecBuilder.  If
-- `f` adds more refs, then repeat until there are no more new refs remaining.
forNewRefs ::
    Monad m =>
    PrePost ->
    (forall tp. TypeRepr tp -> MirReferenceMux sym tp -> M.Mutability -> M.Ty -> MS.AllocIndex ->
        BuilderT sym t m a) ->
    BuilderT sym t m (Seq a)
forNewRefs p f = go
  where
    go = do
        new <- use $ msbPrePost p . seNewRefs
        msbPrePost p . seNewRefs .= Seq.empty
        if Seq.null new then
            return Seq.empty
          else do
            a <- mapM (\(Pair tpr ref, mutbl, ty, alloc) -> f tpr ref mutbl ty alloc) new
            b <- go
            return $ a <> b
