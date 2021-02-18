{-# Language DataKinds #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language GADTs #-}
{-# Language MultiParamTypeClasses #-}
{-# Language OverloadedStrings #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language TemplateHaskell #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}

module Mir.Compositional.Override
where

import Control.Applicative ((<|>))
import Control.Lens
    (makeLenses, (^.), (^..), (^?), (%=), (.=), (&), (.~), (%~), use, at, ix,
        each, to, folded, _Wrapped)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import Data.Foldable
import Data.Functor.Const
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Parameterized.Context (Ctx(..), pattern Empty, pattern (:>), Assignment)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Pair
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Vector as V
import GHC.Stack (HasCallStack)

import qualified What4.Expr.Builder as W4
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.Partial as W4
import What4.ProgramLoc

import Lang.Crucible.Backend
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Types

import qualified Verifier.SAW.Prelude as SAW
import qualified Verifier.SAW.Recognizer as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Simulator.Value as SAW
import qualified Verifier.SAW.Simulator.What4 as SAW
import qualified Verifier.SAW.Term.Functor as SAW
import qualified Verifier.SAW.TypedTerm as SAW

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Override as MS

import qualified Crux.Model as Crux
import Crux.Types (Model)

import Mir.Generator
import Mir.Intrinsics hiding (MethodSpec)
import qualified Mir.Mir as M

import Mir.Compositional.Convert
import Mir.Compositional.MethodSpec


data MethodSpec = MethodSpec 
    { _msCollectionState :: CollectionState
    , _msSpec :: MIRMethodSpec
    }

makeLenses ''MethodSpec

instance (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) => MethodSpecImpl sym MethodSpec where
    msPrettyPrint = printSpec
    msEnable = enable


-- | Pretty-print a MethodSpec.  This wraps `ppMethodSpec` and returns the
-- result as a Rust string.
printSpec ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    MethodSpec ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym (MirSlice (BVType 8)))
printSpec ms = do
    let str = show $ MS.ppMethodSpec (ms ^. msSpec)
    let bytes = Text.encodeUtf8 $ Text.pack str

    sym <- getSymInterface
    len <- liftIO $ W4.bvLit sym knownRepr (BV.mkBV knownRepr $ fromIntegral $ BS.length bytes)

    byteVals <- forM (BS.unpack bytes) $ \b -> do
        liftIO $ W4.bvLit sym (knownNat @8) (BV.mkBV knownRepr $ fromIntegral b)

    let vec = MirVector_Vector $ V.fromList byteVals
    let vecRef = newConstMirRef sym knownRepr vec
    ptr <- subindexMirRefSim knownRepr vecRef =<<
        liftIO (W4.bvLit sym knownRepr (BV.zero knownRepr))
    return $ Empty :> RV ptr :> RV len

-- | Enable a MethodSpec.  This installs an override, so for the remainder of
-- the current test, calls to the subject function will be replaced with
-- `runSpec`.
enable ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    MethodSpec ->
    OverrideSim (Model sym) sym MIR rtp args ret ()
enable ms = do
    let funcName = ms ^. msSpec . MS.csMethod
    MirHandle _name sig mh <- case cs ^? handleMap . ix funcName of
        Just x -> return x
        Nothing -> error $ "MethodSpec has bad method name " ++
            show (ms ^. msSpec . MS.csMethod) ++ "?"

    -- TODO: handle multiple specs for the same function

    bindFnHandle mh $ UseOverride $ mkOverride' (handleName mh) (handleReturnType mh) $
        runSpec (cs ^. collection) mh (ms ^. msSpec)
  where
    cs = ms ^. msCollectionState

-- | "Run" a MethodSpec: assert its preconditions, create fresh symbolic
-- variables for its outputs, and assert its postconditions.
runSpec :: forall sym t st fs args ret rtp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    M.Collection -> FnHandle args ret -> MIRMethodSpec ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym ret)
runSpec col mh ms = do
    sym <- getSymInterface
    simState <- get
    RegMap argVals <- getOverrideArgs
    let argVals' = Map.fromList $ zip [0..] $ MS.assignmentToList argVals

    sgs <- readGlobals
    loc <- liftIO $ W4.getCurrentProgramLoc sym
    let freeVars = Set.fromList $
            ms ^.. MS.csPreState . MS.csFreshVars . each . to SAW.tecExt . to SAW.ecVarIndex

    sc <- liftIO $ SAW.mkSharedContext
    liftIO $ SAW.scLoadPreludeModule sc
    let ng = W4.exprCounter sym
    --sawSym <- liftIO $ SAW.newSAWCoreBackend W4.FloatUninterpretedRepr sc ng

    -- `eval` converts `W4.Expr`s to `SAW.Term`s.  We take what4 exprs from the
    -- context (e.g., in the actual arguments passed to the override) and
    -- convert them to SAWCore terms for use in the OverrideMatcher macro.
    -- Later, we need to convert some SAWCore terms back to what4, so during
    -- this conversion, we also build up a mapping from SAWCore variables
    -- (`SAW.ExtCns`) to what4 ones (`W4.ExprBoundVar`).
    cache <- W4.newIdxCache
    visitCache <- W4.newIdxCache
    w4VarMapRef <- liftIO $ newIORef Map.empty
    let eval' :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval' x = undefined --SAW.evaluateExpr sawSym sc cache x
        eval :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval x = do
            -- When translating W4 vars to SAW `ExtCns`s, also record the
            -- reverse mapping into `w4VarMapRef` so the reverse translation
            -- can be done later on.
            visitExprVars visitCache x $ \var -> do
                let expr = W4.BoundVarExpr var
                term <- eval' expr
                ec <- case SAW.asExtCns term of
                    Just ec -> return ec
                    Nothing -> error "eval on BoundVarExpr produced non-ExtCns?"
                liftIO $ modifyIORef w4VarMapRef $ Map.insert (SAW.ecVarIndex ec) (Some expr)
            eval' x

    -- Generate fresh variables for use in postconditions and result.  The
    -- result, `postFreshTermSub`, maps MethodSpec `VarIndex`es to `Term`s
    -- (really just `ExtCns`s).  Those `Term`s are produced by `eval`
    -- (conversion from what4 to SAW), just like everything else that we put on
    -- the RHS of the OverrideMatcher's `termSub`.
    --
    -- We could allocate these later (it only needs to happen before we process
    -- post-state PointsTos and conditions) but it's easier to do it up-front
    -- so we don't need to split up our `runOverrideMatcher` call into multiple
    -- blocks.
    let postFresh = ms ^. MS.csPostState . MS.csFreshVars
    postFreshTermSub <- liftM Map.fromList $ forM postFresh $ \tec -> do
        let ec = SAW.tecExt tec
        let nameStr = Text.unpack $ SAW.toShortName $ SAW.ecName ec
        let nameSymbol = W4.safeSymbol nameStr
        Some btpr <- liftIO $ termToType sym sc (SAW.ecType ec)
        expr <- liftIO $ W4.freshConstant sym nameSymbol btpr
        stateContext . cruciblePersonality %= Crux.addVar loc nameStr btpr expr
        term <- liftIO $ eval expr
        return (SAW.ecVarIndex ec, term)

    result <- liftIO $ MS.runOverrideMatcher sym sgs mempty postFreshTermSub freeVars loc $ do
        -- Match the override's inputs against the MethodSpec inputs.  This
        -- sets up the `termSub` (symbolic variable bindings) and
        -- `setupValueSub` (allocation bindings) in the OverrideMatcher state.

        -- Match argument SetupValues against argVals.
        forM_ (Map.toList $ ms ^. MS.csArgBindings) $ \(i, (_, sv)) -> do
            ty <- case ms ^. MS.csArgs ^? ix (fromIntegral i) of
                Nothing -> error $ show ("wrong number of args", ms ^. MS.csMethod, i)
                Just x -> return x
            AnyValue tpr rv <- case argVals' ^? ix i of
                Nothing -> error $ show ("wrong number of args", ms ^. MS.csMethod, i)
                Just x -> return x
            let shp = tyToShapeEq col ty tpr
            matchArg sym eval shp rv sv

        -- Match PointsTo SetupValues against accessible memory.
        --
        -- We assume the PointsTos are stored in reversed top-down order (which
        -- is what `builderAddArg` does), so if we walk over them in reverse,
        -- we'll always see the argument or PointsTo that binds a MirReference
        -- to allocation `alloc` before we see the PointsTo for `alloc` itself.
        -- This ensures we can obtain a MirReference for each PointsTo that we
        -- see.
        forM_ (reverse $ ms ^. MS.csPreState . MS.csPointsTos) $ \(MirPointsTo alloc sv) -> do
            allocSub <- use MS.setupValueSub
            Pair tpr ref <- case Map.lookup alloc allocSub of
                Just x -> return x
                Nothing -> error $
                    "PointsTos are out of order: no ref is available for " ++ show alloc
            ty <- case ms ^? MS.csPreState . MS.csAllocs . ix alloc of
                Just (_, _, ty) -> return ty
                Nothing -> error $
                    "impossible: alloc mentioned in csPointsTo is absent from csAllocs?"
            rv <- liftIO $ readMirRefIO sym simState tpr ref
            let shp = tyToShapeEq col ty tpr
            matchArg sym eval shp rv sv

        -- TODO: check that all pre fresh vars are bound
        -- TODO: check that all pre allocs are bound
        -- TODO: check disjointness of refs
        -- TODO: see if we need any other assertions from LLVM OverrideMatcher

        -- Handle preconditions and postconditions.  

        -- Convert preconditions to `osAsserts`
        forM_ (ms ^. MS.csPreState . MS.csConditions) $ \cond -> do
            term <- condTerm sc cond
            w4VarMap <- liftIO $ readIORef w4VarMapRef
            pred <- liftIO $ termToPred sym sc w4VarMap term
            MS.addAssert pred $
                SimError loc (AssertFailureSimError (show $ W4.printSymExpr pred) "")

        -- Convert postconditions to `osAssumes`
        forM_ (ms ^. MS.csPostState . MS.csConditions) $ \cond -> do
            term <- condTerm sc cond
            w4VarMap <- liftIO $ readIORef w4VarMapRef
            pred <- liftIO $ termToPred sym sc w4VarMap term
            MS.addAssume pred

    ((), os) <- case result of
        Left err -> error $ show err
        Right x -> return x

    forM_ (os ^. MS.osAsserts) $ \lp ->
        liftIO $ addAssertion sym lp

    forM_ (os ^. MS.osAssumes) $ \p ->
        liftIO $ addAssumption sym $ W4.LabeledPred p $
            AssumptionReason loc "methodspec postcondition"

    let preAllocMap = os ^. MS.setupValueSub

    let postAllocDefs = filter (\(k,v) -> not $ Map.member k preAllocMap) $
            Map.toList $ ms ^. MS.csPostState . MS.csAllocs
    postAllocMap <- liftM Map.fromList $ forM postAllocDefs $ \(alloc, (Some tpr, _, _)) -> do
        ref <- newMirRefSim tpr
        return (alloc, Pair tpr ref)
    let allocMap = preAllocMap <> postAllocMap

    -- Handle return value and post-state PointsTos

    -- TODO: clobber all writable memory that's accessible in the pre state
    -- + record mut vs imm for each reference discovered within args
    -- + clobber all mut memory

    let retTy = maybe (M.TyTuple []) id $ ms ^. MS.csRet
    let retTpr = handleReturnType mh
    let retShp = tyToShapeEq col retTy retTpr
    w4VarMap <- liftIO $ readIORef w4VarMapRef
    let termSub = os ^. MS.termSub
    retVal <- case ms ^. MS.csRetValue of
        Just sv -> liftIO $ setupToReg sym sc termSub w4VarMap allocMap retShp sv
        Nothing -> case testEquality retTpr UnitRepr of
            Just Refl -> return ()
            Nothing -> error $ "no return value, but return type is " ++ show retTpr

    -- For every post-state PointsTo, write the RHS value into the LHS pointer.
    --
    -- We assume any memory not mentioned in a post-state PointsTo is left
    -- unchanged by the subject function.  `builderAddArg` is responsible for
    -- figuring out which memory is accessible and mutable and thus needs to be
    -- clobbered, and for adding appropriate fresh variables and `PointsTo`s to
    -- the post state.
    forM_ (ms ^. MS.csPostState . MS.csPointsTos) $ \(MirPointsTo alloc sv) -> do
        Pair tpr ref <- case Map.lookup alloc allocMap of
            Just x -> return x
            Nothing -> error $ "post PointsTos are out of order: no ref for " ++ show alloc
        let optAlloc = (ms ^? MS.csPostState . MS.csAllocs . ix alloc) <|>
                (ms ^? MS.csPreState . MS.csAllocs . ix alloc)
        ty <- case optAlloc of
            Just (_, _, ty) -> return ty
            Nothing -> error $
                "impossible: alloc mentioned in post csPointsTo is absent from csAllocs?"
        let shp = tyToShapeEq col ty tpr
        rv <- liftIO $ setupToReg sym sc termSub w4VarMap allocMap shp sv
        writeMirRefSim tpr ref rv

    return retVal


-- | Match argument RegValue `rv` against SetupValue pattern `sv`.  On success,
-- this may update `termSub` and `setupValueSub` with new bindings for the
-- MethodSpec's symbolic variables and allocations.
matchArg ::
    forall sym t st fs tp rorw.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    (forall tp'. W4.Expr t tp' -> IO SAW.Term) ->
    TypeShape tp -> RegValue sym tp -> MS.SetupValue MIR ->
    MS.OverrideMatcher' sym MIR rorw ()
matchArg sym eval shp rv sv = go shp rv sv
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp -> MS.SetupValue MIR ->
        MS.OverrideMatcher' sym MIR rorw ()
    go (UnitShape _) () (MS.SetupStruct () False []) = return ()
    go (PrimShape _ btpr) expr (MS.SetupTerm tt) = do
        loc <- use MS.osLocation
        exprTerm <- liftIO $ eval expr
        var <- case SAW.asExtCns $ SAW.ttTerm tt of
            Just ec -> return $ SAW.ecVarIndex ec
            Nothing -> do
                MS.failure loc $ MS.BadTermMatch (SAW.ttTerm tt) exprTerm
        sub <- use MS.termSub
        when (Map.member var sub) $
            MS.failure loc MS.NonlinearPatternNotSupported
        MS.termSub %= Map.insert var exprTerm
    go (TupleShape _ _ flds) rvs (MS.SetupStruct () False svs) = goFields flds rvs svs
    go (ArrayShape _ _ shp) vec (MS.SetupArray () svs) = case vec of
        MirVector_Vector v -> zipWithM_ (go shp) (toList v) svs
        MirVector_PartialVector pv -> forM_ (zip (toList pv) svs) $ \(p, sv) -> do
            rv <- liftIO $ readMaybeType sym "vector element" (shapeType shp) p
            go shp rv sv
        MirVector_Array _ -> error $ "matchArg: MirVector_Array NYI"
    go (StructShape _ _ flds) (AnyValue tpr rvs) (MS.SetupStruct () False svs)
      | Just Refl <- testEquality tpr shpTpr = goFields flds rvs svs
      | otherwise = error $ "matchArg: type error: expected " ++ show shpTpr ++
        ", but got Any wrapping " ++ show tpr
      where shpTpr = StructRepr $ fmapFC fieldShapeType flds
    go (RefShape _ _ tpr) ref (MS.SetupVar alloc) = do
        m <- use MS.setupValueSub
        case Map.lookup alloc m of
            Nothing -> return ()
            Just (Pair tpr' ref')
              | Just Refl <- testEquality tpr tpr' -> do
                eq <- liftIO $ mirRef_eqIO sym ref ref'
                let loc = mkProgramLoc "matchArg" InternalPos
                MS.addAssert eq $
                    SimError loc (AssertFailureSimError ("mismatch on " ++ show alloc) "")
              | otherwise -> error $ "mismatched types for " ++ show alloc ++ ": " ++
                    show tpr ++ " does not match " ++ show tpr'
        MS.setupValueSub %= Map.insert alloc (Pair tpr ref)
    go shp _ _ = error $ "matchArg: type error: bad SetupValue for " ++ show (shapeType shp)

    goFields :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
        [MS.SetupValue MIR] -> MS.OverrideMatcher' sym MIR rorw ()
    goFields flds rvs svs = loop flds rvs (reverse svs)
      where
        loop :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
            [MS.SetupValue MIR] -> MS.OverrideMatcher' sym MIR rorw ()
        loop Empty Empty [] = return ()
        loop (flds :> fld) (rvs :> RV rv) (sv : svs) = do
            case fld of
                ReqField shp -> go shp rv sv
                OptField shp -> do
                    rv' <- liftIO $ readMaybeType sym "field" (shapeType shp) rv
                    go shp rv' sv
            loop flds rvs svs
        loop _ rvs svs = error $ "matchArg: type error: got RegValues for " ++
            show (Ctx.sizeInt $ Ctx.size rvs) ++ " fields, but got " ++
            show (length svs) ++ " SetupValues"


-- | Convert a SetupValue to a RegValue.  This is used for MethodSpec outputs,
-- namely the return value and any post-state PointsTos.
setupToReg :: forall sym t st fs tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    -- | `termSub`: maps `VarIndex`es in the MethodSpec's namespace to `Term`s
    -- in the context's namespace.
    Map SAW.VarIndex SAW.Term ->
    -- | `regMap`: maps `VarIndex`es in the context's namespace to the
    -- corresponding W4 variables in the context's namespace.
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    Map MS.AllocIndex (MS.Pointer' MIR sym) ->
    TypeShape tp ->
    MS.SetupValue MIR ->
    IO (RegValue sym tp)
setupToReg sym sc termSub regMap allocMap shp sv = go shp sv
  where
    go :: forall tp. TypeShape tp -> MS.SetupValue MIR -> IO (RegValue sym tp)
    go (UnitShape _) (MS.SetupStruct _ False []) = return ()
    go (PrimShape _ btpr) (MS.SetupTerm tt) = do
        term <- liftIO $ SAW.scInstantiateExt sc termSub $ SAW.ttTerm tt
        Some expr <- termToExpr sym sc regMap term
        Refl <- case testEquality (W4.exprType expr) btpr of
            Just x -> return x
            Nothing -> error $ "setupToReg: expected " ++ show btpr ++ ", but got " ++
                show (W4.exprType expr)
        return expr
    go (TupleShape _ _ flds) (MS.SetupStruct _ False svs) = goFields flds svs
    go (ArrayShape _ _ shp) (MS.SetupArray _ svs) = do
        rvs <- mapM (go shp) svs
        return $ MirVector_Vector $ V.fromList rvs
    go (StructShape _ _ flds) (MS.SetupStruct _ False svs) =
        AnyValue (StructRepr $ fmapFC fieldShapeType flds) <$> goFields flds svs
    go (RefShape _ _ tpr) (MS.SetupVar alloc) = case Map.lookup alloc allocMap of
        Just (Pair tpr' ref) -> case testEquality tpr tpr' of
            Just Refl -> return ref
            Nothing -> error $ "setupToReg: type error: bad reference type for " ++ show alloc ++
                ": got " ++ show tpr' ++ " but expected " ++ show tpr
        Nothing -> error $ "setupToReg: no definition for " ++ show alloc
    go shp sv = error $ "setupToReg: type error: bad SetupValue for " ++ show (shapeType shp) ++
        ": " ++ show (MS.ppSetupValue sv)

    goFields :: forall ctx. Assignment FieldShape ctx -> [MS.SetupValue MIR] ->
        IO (Assignment (RegValue' sym) ctx)
    goFields shps svs = loop shps (reverse svs)
      where
        loop :: forall ctx. Assignment FieldShape ctx -> [MS.SetupValue MIR] ->
            IO (Assignment (RegValue' sym) ctx)
        loop Empty [] = return Empty
        loop (shps :> shp) (sv : svs) = do
            rv <- case shp of
                ReqField shp' -> go shp' sv
                OptField shp' -> W4.justPartExpr sym <$> go shp' sv
            rvs <- loop shps svs
            return $ rvs :> RV rv


-- | Convert a `SetupCondition` from the MethodSpec into a boolean `SAW.Term`
-- referencing variables from the override's context.  This uses the current
-- `termSub` to perform the necessary substitution.
condTerm ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    SAW.SharedContext ->
    MS.SetupCondition MIR ->
    MS.OverrideMatcher' sym MIR rorw SAW.Term
condTerm sc (MS.SetupCond_Equal loc sv1 sv2) = do
    error $ "learnCond SetupCond_Equal NYI" -- TODO
condTerm sc (MS.SetupCond_Pred loc tt) = do
    sub <- use MS.termSub
    t' <- liftIO $ SAW.scInstantiateExt sc sub $ SAW.ttTerm tt
    return t'

-- | Convert a `SAW.Term` into a `W4.Expr`.
termToExpr :: forall sym t st fs.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    SAW.Term ->
    IO (Some (W4.SymExpr sym))
termToExpr sym sc varMap term = do
    let convert (Some expr) = case SAW.symExprToValue (W4.exprType expr) expr of
            Just x -> return x
            Nothing -> error $ "termToExpr: failed to convert var  of what4 type " ++
                show (W4.exprType expr)
    ecMap <- mapM convert varMap
    ref <- newIORef mempty
    sv <- SAW.w4SolveBasic sym sc mempty ecMap ref mempty term
    case SAW.valueToSymExpr sv of
        Just x -> return x
        Nothing -> error $ "termToExpr: failed to convert SValue"

-- | Convert a `SAW.Term` to a `W4.Pred`.  If the term doesn't have boolean
-- type, this will raise an error.
termToPred :: forall sym t st fs.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    SAW.Term ->
    IO (W4.Pred sym)
termToPred sym sc varMap term = do
    Some expr <- termToExpr sym sc varMap term
    case W4.exprType expr of
        BaseBoolRepr -> return expr
        btpr -> error $ "termToPred: got result of type " ++ show btpr ++ ", not BaseBoolRepr"

-- | Convert a `SAW.Term` representing a type to a `W4.BaseTypeRepr`.
termToType :: forall sym t st fs.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    SAW.Term ->
    IO (Some W4.BaseTypeRepr)
termToType sym sc term = do
    ref <- newIORef mempty
    sv <- SAW.w4SolveBasic sym sc mempty mempty ref mempty term
    tv <- case sv of
        SAW.TValue tv -> return tv
        _ -> error $ "termToType: bad SValue"
    case tv of
        SAW.VBoolType -> return $ Some BaseBoolRepr
        SAW.VVecType w SAW.VBoolType -> do
            Some w <- return $ mkNatRepr w
            LeqProof <- case testLeq (knownNat @1) w of
                Just x -> return x
                Nothing -> error "termToPred: zero-width bitvector"
            return $ Some $ BaseBVRepr w
        _ -> error $ "termToType: bad SValue"


-- | Run `f` on each `SymExpr` in `v`.
visitRegValueExprs ::
    forall sym tp m.
    Monad m =>
    sym ->
    TypeRepr tp ->
    RegValue sym tp ->
    (forall btp. W4.SymExpr sym btp -> m ()) ->
    m ()
visitRegValueExprs _sym tpr_ v_ f = go tpr_ v_
  where
    go :: forall tp'. TypeRepr tp' -> RegValue sym tp' -> m ()
    go tpr v | AsBaseType btpr <- asBaseType tpr = f v
    go AnyRepr (AnyValue tpr' v') = go tpr' v'
    go UnitRepr () = return ()
    go (MaybeRepr tpr') W4.Unassigned = return ()
    go (MaybeRepr tpr') (W4.PE p v') = f p >> go tpr' v'
    go (VectorRepr tpr') vec = mapM_ (go tpr') vec
    go (StructRepr ctxr) fields = forMWithRepr_ ctxr fields $ \tpr' (RV v') -> go tpr' v'
    go (VariantRepr ctxr) variants = forMWithRepr_ ctxr variants $ \tpr' (VB pe) -> case pe of
        W4.Unassigned -> return ()
        W4.PE p v' -> f p >> go tpr' v'
    go (MirVectorRepr tpr') vec = case vec of
        MirVector_Vector v -> mapM_ (go tpr') v
        MirVector_PartialVector pv -> mapM_ (go (MaybeRepr tpr')) pv
        MirVector_Array _ -> error $ "visitRegValueExprs: unsupported: MirVector_Array"
    -- For now, we require that all references within a MethodSpec be
    -- nonoverlapping, and ignore the `SymExpr`s inside.  If we ever want to
    -- write a spec for e.g. `f(arr, &arr[i], i)`, where the second reference
    -- is offset from the first by a symbolic integer value, then we'd need to
    -- visit exprs from some suffix of each MirReference.
    go (MirReferenceRepr _) _ = return ()
    go tpr _ = error $ "visitRegValueExprs: unsupported: " ++ show tpr

    forMWithRepr_ :: forall ctx m f. Monad m =>
        CtxRepr ctx -> Ctx.Assignment f ctx -> (forall tp. TypeRepr tp -> f tp -> m ()) -> m ()
    forMWithRepr_ ctxr assn f = void $
        Ctx.zipWithM (\x y -> f x y >> return (Const ())) ctxr assn
