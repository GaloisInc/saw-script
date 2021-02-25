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
import Control.Lens (makeLenses, (^.), (^..), (^?), (%=), use, ix, each, to)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import Data.Foldable
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Parameterized.Context (pattern Empty, pattern (:>), Assignment)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import qualified Data.Set as Set
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
import Lang.Crucible.Types

import qualified Verifier.SAW.Prelude as SAW
import qualified Verifier.SAW.Recognizer as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Simulator.Value as SAW
import qualified Verifier.SAW.Simulator.What4 as SAW
import qualified Verifier.SAW.Simulator.What4.ReturnTrip as SAW
import qualified Verifier.SAW.Term.Functor as SAW
import qualified Verifier.SAW.TypedTerm as SAW

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Override as MS

import qualified Crux.Model as Crux
import Crux.Types (Model)

import Mir.Generator
import Mir.Intrinsics hiding (MethodSpec)
import qualified Mir.Mir as M

import Mir.Compositional.Clobber
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
    MirHandle _name _sig mh <- case cs ^? handleMap . ix funcName of
        Just x -> return x
        Nothing -> error $ "MethodSpec has bad method name " ++
            show (ms ^. msSpec . MS.csMethod) ++ "?"

    -- TODO: handle multiple specs for the same function

    bindFnHandle mh $ UseOverride $ mkOverride' (handleName mh) (handleReturnType mh) $
        runSpec cs mh (ms ^. msSpec)
  where
    cs = ms ^. msCollectionState

-- | "Run" a MethodSpec: assert its preconditions, create fresh symbolic
-- variables for its outputs, and assert its postconditions.
runSpec :: forall sym t st fs args ret rtp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    CollectionState -> FnHandle args ret -> MIRMethodSpec ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym ret)
runSpec cs mh ms = do
    let col = cs ^. collection
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
    scs <- liftIO $ SAW.newSAWCoreState sc

    -- `eval` converts `W4.Expr`s to `SAW.Term`s.  We take what4 exprs from the
    -- context (e.g., in the actual arguments passed to the override) and
    -- convert them to SAWCore terms for use in the OverrideMatcher macro.
    -- Later, we need to convert some SAWCore terms back to what4, so during
    -- this conversion, we also build up a mapping from SAWCore variables
    -- (`SAW.ExtCns`) to what4 ones (`W4.ExprBoundVar`).
    visitCache <- W4.newIdxCache
    w4VarMapRef <- liftIO $ newIORef Map.empty
    let eval' :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval' x = SAW.toSC sym scs x
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
                Nothing -> error $ "wrong number of args for " ++ show (ms ^. MS.csMethod) ++
                    ": no arg at index " ++ show i
                Just x -> return x
            AnyValue tpr rv <- case argVals' ^? ix i of
                Nothing -> error $ "wrong number of args for " ++ show (ms ^. MS.csMethod) ++
                    ": no arg at index " ++ show i
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
            Some ptr <- case Map.lookup alloc allocSub of
                Just x -> return x
                Nothing -> error $
                    "PointsTos are out of order: no ref is available for " ++ show alloc
            ty <- case ms ^? MS.csPreState . MS.csAllocs . ix alloc of
                Just (Some allocSpec) -> return $ allocSpec ^. maMirType
                Nothing -> error $
                    "impossible: alloc mentioned in csPointsTo is absent from csAllocs?"
            rv <- liftIO $ readMirRefIO sym simState (ptr ^. mpType) (ptr ^. mpRef)
            let shp = tyToShapeEq col ty (ptr ^. mpType)
            matchArg sym eval shp rv sv


        -- Validity checks

        -- All pre-state and post-state fresh vars must be bound.
        termSub <- use MS.termSub
        let allFresh = ms ^. MS.csPreState . MS.csFreshVars ++
                ms ^. MS.csPostState . MS.csFreshVars
        forM_ allFresh $ \tec -> do
            let var = SAW.ecVarIndex $ SAW.tecExt tec
            when (not $ Map.member var termSub) $ do
                error $ "argument matching failed to produce a binding for " ++
                    show (MS.ppTypedExtCns tec)

        -- All pre-state allocs must be bound.
        allocSub <- use MS.setupValueSub
        forM_ (Map.toList $ ms ^. MS.csPreState . MS.csAllocs) $ \(alloc, info) -> do
            when (not $ Map.member alloc allocSub) $ do
                error $ "argument matching failed to produce a binding for " ++
                    show alloc ++ " (info: " ++ show info ++ ")"

        -- All references in `allocSub` must point to disjoint memory regions.
        liftIO $ checkDisjoint sym (Map.toList allocSub)

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

    let postAllocDefs = filter (\(k,_v) -> not $ Map.member k preAllocMap) $
            Map.toList $ ms ^. MS.csPostState . MS.csAllocs
    postAllocMap <- liftM Map.fromList $ forM postAllocDefs $ \(alloc, Some allocSpec) -> do
        ref <- newMirRefSim (allocSpec ^. maType)
        return (alloc, Some $ MirPointer (allocSpec ^. maType) ref)
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
        Some ptr <- case Map.lookup alloc allocMap of
            Just x -> return x
            Nothing -> error $ "post PointsTos are out of order: no ref for " ++ show alloc
        let optAlloc = (ms ^? MS.csPostState . MS.csAllocs . ix alloc) <|>
                (ms ^? MS.csPreState . MS.csAllocs . ix alloc)
        ty <- case optAlloc of
            Just (Some allocSpec) -> return $ allocSpec ^. maMirType
            Nothing -> error $
                "impossible: alloc mentioned in post csPointsTo is absent from csAllocs?"
        let shp = tyToShapeEq col ty (ptr ^. mpType)
        rv <- liftIO $ setupToReg sym sc termSub w4VarMap allocMap shp sv
        writeMirRefSim (ptr ^. mpType) (ptr ^. mpRef) rv

    -- Clobber all globals.  We don't yet support mentioning globals in specs.
    -- However, we also don't prevent the subject function from modifying
    -- globals.  Since we have no idea what the subject function might do to
    -- globals during a normal call, we conservatively clobber all globals as
    -- part of the spec override.
    clobberGlobals sym loc "run_spec_clobber_globals" cs

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
    go (PrimShape _ _btpr) expr (MS.SetupTerm tt) = do
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
            Just (Some ptr)
              | Just Refl <- testEquality tpr (ptr ^. mpType) -> do
                eq <- liftIO $ mirRef_eqIO sym ref (ptr ^. mpRef)
                let loc = mkProgramLoc "matchArg" InternalPos
                MS.addAssert eq $
                    SimError loc (AssertFailureSimError ("mismatch on " ++ show alloc) "")
              | otherwise -> error $ "mismatched types for " ++ show alloc ++ ": " ++
                    show tpr ++ " does not match " ++ show (ptr ^. mpType)
        MS.setupValueSub %= Map.insert alloc (Some $ MirPointer tpr ref)
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
    Map MS.AllocIndex (Some (MirPointer sym)) ->
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
        Just (Some ptr) -> case testEquality tpr (ptr ^. mpType) of
            Just Refl -> return $ ptr ^. mpRef
            Nothing -> error $ "setupToReg: type error: bad reference type for " ++ show alloc ++
                ": got " ++ show (ptr ^. mpType) ++ " but expected " ++ show tpr
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
        loop shps svs = error $ "setupToReg: type error: got TypeShapes for " ++
            show (Ctx.sizeInt $ Ctx.size shps) ++ " fields, but got " ++
            show (length svs) ++ " SetupValues"


-- | Convert a `SetupCondition` from the MethodSpec into a boolean `SAW.Term`
-- referencing variables from the override's context.  This uses the current
-- `termSub` to perform the necessary substitution.
condTerm ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    SAW.SharedContext ->
    MS.SetupCondition MIR ->
    MS.OverrideMatcher' sym MIR rorw SAW.Term
condTerm _sc (MS.SetupCond_Equal _loc _sv1 _sv2) = do
    error $ "learnCond: SetupCond_Equal NYI" -- TODO
condTerm sc (MS.SetupCond_Pred _loc tt) = do
    sub <- use MS.termSub
    t' <- liftIO $ SAW.scInstantiateExt sc sub $ SAW.ttTerm tt
    return t'
condTerm _ (MS.SetupCond_Ghost _ _ _ _) = do
    error $ "learnCond: SetupCond_Ghost is not supported"

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


checkDisjoint ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    [(MS.AllocIndex, Some (MirPointer sym))] ->
    IO ()
checkDisjoint sym refs = go refs
  where
    go [] = return ()
    go ((alloc, Some ptr) : rest) = do
        forM_ rest $ \(alloc', Some ptr') -> do
            disjoint <- W4.notPred sym =<< mirRef_overlapsIO sym (ptr ^. mpRef) (ptr' ^. mpRef)
            assert sym disjoint $ GenericSimError $
                "references " ++ show alloc ++ " and " ++ show alloc' ++ " must not overlap"
        go rest
