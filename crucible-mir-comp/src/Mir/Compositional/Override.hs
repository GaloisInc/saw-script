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
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Parameterized.Context (pattern Empty, pattern (:>), Assignment)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Vector as V
import GHC.Stack (HasCallStack)

import qualified What4.Expr.Builder as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4
import What4.ProgramLoc

import Lang.Crucible.Backend
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import Lang.Crucible.Types

import qualified SAWCore.Prelude as SAW
import qualified SAWCore.Recognizer as SAW
import qualified SAWCore.SharedTerm as SAW
import qualified SAWCore.Term.Functor as SAW
import qualified CryptolSAWCore.TypedTerm as SAW

import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import qualified SAWCentral.Crucible.Common.Override as MS
import SAWCentral.Crucible.MIR.MethodSpecIR
import SAWCentral.Crucible.MIR.TypeShape

import Mir.Generator
import Mir.Intrinsics hiding (MethodSpec)
import qualified Mir.Mir as M

import Mir.Compositional.Clobber
import Mir.Compositional.Convert


type MirOverrideMatcher sym a = forall p rorw rtp args ret.
    MS.OverrideMatcher' sym MIR rorw (OverrideSim (p sym) sym MIR rtp args ret) a

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
    OverrideSim (p sym) sym MIR rtp args ret (RegValue sym MirSlice)
printSpec ms = do
    let str = show $ MS.ppMethodSpec (ms ^. msSpec)
    let bytes = Text.encodeUtf8 $ Text.pack str

    sym <- getSymInterface
    len <- liftIO $ W4.bvLit sym knownRepr (BV.mkBV knownRepr $ fromIntegral $ BS.length bytes)

    let w8 = knownNat @8
    byteVals <- forM (BS.unpack bytes) $ \b -> do
        liftIO $ W4.bvLit sym w8 (BV.mkBV w8 $ fromIntegral b)

    let vec = MirVector_Vector $ V.fromList byteVals
    let vecRef = newConstMirRef sym (MirVectorRepr (BVRepr w8)) vec
    ptr <- subindexMirRefSim MirReferenceRepr vecRef =<<
        liftIO (W4.bvLit sym knownRepr (BV.zero knownRepr))
    return $ Empty :> RV ptr :> RV len

-- | Enable a MethodSpec.  This installs an override, so for the remainder of
-- the current test, calls to the subject function will be replaced with
-- `runSpec`.
enable ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    MethodSpec ->
    OverrideSim (p sym) sym MIR rtp args ret ()
enable ms = do
    let funcName = ms ^. msSpec . MS.csMethod
    MirHandle _name _sig mh <- case myCS ^? handleMap . ix funcName of
        Just x -> return x
        Nothing -> error $ "MethodSpec has bad method name " ++
            show (ms ^. msSpec . MS.csMethod) ++ "?"

    -- TODO: handle multiple specs for the same function

    bindFnHandle mh $ UseOverride $ mkOverride' (handleName mh) (handleReturnType mh) $
        runSpec myCS mh (ms ^. msSpec)
  where
    myCS = ms ^. msCollectionState

-- | "Run" a MethodSpec: assert its preconditions, create fresh symbolic
-- variables for its outputs, and assert its postconditions.
runSpec :: forall sym p t st fs args ret rtp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    CollectionState -> FnHandle args ret -> MIRMethodSpec ->
    OverrideSim (p sym) sym MIR rtp args ret (RegValue sym ret)
runSpec myCS mh ms = ovrWithBackend $ \bak ->
 do let col = myCS ^. collection
    sym <- getSymInterface
    RegMap argVals <- getOverrideArgs
    let argVals' = Map.fromList $ zip [0..] $ MS.assignmentToList argVals

    loc <- liftIO $ W4.getCurrentProgramLoc sym
    let freeVars = Set.fromList $
            ms ^.. MS.csPreState . MS.csFreshVars . each . to SAW.tecExt . to SAW.ecVarIndex

    sc <- liftIO $ SAW.mkSharedContext
    liftIO $ SAW.scLoadPreludeModule sc

    -- `eval` converts `W4.Expr`s to `SAW.Term`s.  We take what4 exprs from the
    -- context (e.g., in the actual arguments passed to the override) and
    -- convert them to SAWCore terms for use in the OverrideMatcher macro.
    -- Later, we need to convert some SAWCore terms back to what4, so during
    -- this conversion, we also build up a mapping from SAWCore variables
    -- (`SAW.ExtCns`) to what4 ones (`W4.ExprBoundVar`).
    w4VarMapRef <- liftIO $ newIORef Map.empty
    let eval :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval x = exprToTerm sym sc w4VarMapRef x

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
    postFreshTermSub <- liftM IntMap.fromList $ forM postFresh $ \tec -> do
        let ec = SAW.tecExt tec
        let nameStr = Text.unpack $ SAW.toShortName $ SAW.ecName ec
        let nameSymbol = W4.safeSymbol nameStr
        Some btpr <- liftIO $ termToType sym sc (SAW.ecType ec)
        expr <- liftIO $ W4.freshConstant sym nameSymbol btpr
        let ev = CreateVariableEvent loc nameStr btpr expr
        liftIO $ addAssumptions bak (singleEvent ev)
        term <- liftIO $ eval expr
        return (SAW.ecVarIndex ec, term)

    -- Accesses to globals should go through the underlying OverrideSim monad,
    -- rather than using OverrideMatcher's `readGlobal`/`writeGlobal` methods.
    let sgs = error "tried to access SimGlobalState through OverrideMatcher"
    result <- MS.runOverrideMatcher sym sgs mempty postFreshTermSub freeVars loc $ do
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
            let md = MS.ConditionMetadata
                     { MS.conditionLoc = loc
                     , MS.conditionTags = mempty
                     , MS.conditionType = "formal argument matching"
                     , MS.conditionContext = ""
                     }
            matchArg sym sc eval (ms ^. MS.csPreState . MS.csAllocs) md shp rv sv

        -- Match PointsTo SetupValues against accessible memory.
        --
        -- We assume the PointsTos are stored in reversed top-down order (which
        -- is what `builderAddArg` does), so if we walk over them in reverse,
        -- we'll always see the argument or PointsTo that binds a MirReference
        -- to allocation `alloc` before we see the PointsTo for `alloc` itself.
        -- This ensures we can obtain a MirReference for each PointsTo that we
        -- see.
        forM_ (reverse $ ms ^. MS.csPreState . MS.csPointsTos) $ \(MirPointsTo md ref svs) -> do
            alloc <- setupVarAllocIndex ref
            allocSub <- use MS.setupValueSub
            Some ptr <- case Map.lookup alloc allocSub of
                Just x -> return x
                Nothing -> error $
                    "PointsTos are out of order: no ref is available for " ++ show alloc
            (ty, len) <- case ms ^? MS.csPreState . MS.csAllocs . ix alloc of
                Just (Some allocSpec) -> return $ (allocSpec ^. maMirType, allocSpec ^. maLen)
                Nothing -> error $
                    "impossible: alloc mentioned in csPointsTo is absent from csAllocs?"
            forM_ (zip svs [0 .. len - 1]) $ \(sv, i) -> do
                iSym <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $ fromIntegral i
                ref' <- lift $ mirRef_offsetSim (ptr ^. mpRef) iSym
                rv <- lift $ readMirRefSim (ptr ^. mpType) ref'
                let shp = tyToShapeEq col ty (ptr ^. mpType)
                matchArg sym sc eval (ms ^. MS.csPreState . MS.csAllocs) md shp rv sv

        -- Validity checks

        -- All pre-state and post-state fresh vars must be bound.
        termSub <- use MS.termSub
        let allFresh = ms ^. MS.csPreState . MS.csFreshVars ++
                ms ^. MS.csPostState . MS.csFreshVars
        forM_ allFresh $ \tec -> do
            let var = SAW.ecVarIndex $ SAW.tecExt tec
            when (not $ IntMap.member var termSub) $ do
                error $ "argument matching failed to produce a binding for " ++
                    show (SAW.ppTypedExtCns tec)

        -- All pre-state allocs must be bound.
        allocSub <- use MS.setupValueSub
        forM_ (Map.toList $ ms ^. MS.csPreState . MS.csAllocs) $ \(alloc, info) -> do
            when (not $ Map.member alloc allocSub) $ do
                error $ "argument matching failed to produce a binding for " ++
                    show alloc ++ " (info: " ++ show info ++ ")"

        -- All references in `allocSub` must point to disjoint memory regions.
        liftIO $ checkDisjoint bak (Map.toList allocSub)

        -- TODO: see if we need any other assertions from LLVM OverrideMatcher


        -- Handle preconditions and postconditions.

        -- Convert preconditions to `osAsserts`
        forM_ (ms ^. MS.csPreState . MS.csConditions) $ \cond -> do
            (md, term) <- condTerm sc cond
            w4VarMap <- liftIO $ readIORef w4VarMapRef
            pred_ <- liftIO $ termToPred sym sc w4VarMap term
            MS.addAssert pred_ md $
                SimError loc (AssertFailureSimError (show $ W4.printSymExpr pred_) "")

        -- Convert postconditions to `osAssumes`
        forM_ (ms ^. MS.csPostState . MS.csConditions) $ \cond -> do
            (md, term) <- condTerm sc cond
            w4VarMap <- liftIO $ readIORef w4VarMapRef
            pred_ <- liftIO $ termToPred sym sc w4VarMap term
            MS.addAssume pred_ md

    ((), os) <- case result of
        Left err -> error $ show err
        Right x -> return x

    forM_ (os ^. MS.osAsserts) $ \(_md, lp) ->
      -- TODO, track metadata
      liftIO $ addAssertion bak lp
    forM_ (os ^. MS.osAssumes) $ \(_md, p) ->
      liftIO $ addAssumption bak (GenericAssumption loc "methodspec postcondition" p)

    let preAllocMap = os ^. MS.setupValueSub

    let postAllocDefs = filter (\(k,_v) -> not $ Map.member k preAllocMap) $
            Map.toList $ ms ^. MS.csPostState . MS.csAllocs
    postAllocMap <- liftM Map.fromList $ forM postAllocDefs $ \(alloc, Some allocSpec) -> do
        ref <- newMirRefSim (allocSpec ^. maType)
        return ( alloc
               , Some $ MirPointer (allocSpec ^. maType)
                                   (allocSpec ^. maPtrKind)
                                   (allocSpec ^. maMutbl)
                                   (allocSpec ^. maMirType)
                                   ref
               )
    let allocMap = preAllocMap <> postAllocMap

    -- Handle return value and post-state PointsTos

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
    forM_ (ms ^. MS.csPostState . MS.csPointsTos) $ \(MirPointsTo _md ref svs) -> do
        alloc <- setupVarAllocIndex ref
        Some ptr <- case Map.lookup alloc allocMap of
            Just x -> return x
            Nothing -> error $ "post PointsTos are out of order: no ref for " ++ show alloc
        let optAlloc = (ms ^? MS.csPostState . MS.csAllocs . ix alloc) <|>
                (ms ^? MS.csPreState . MS.csAllocs . ix alloc)
        (ty, len) <- case optAlloc of
            Just (Some allocSpec) -> return $ (allocSpec ^. maMirType, allocSpec ^. maLen)
            Nothing -> error $
                "impossible: alloc mentioned in post csPointsTo is absent from csAllocs?"
        let shp = tyToShapeEq col ty (ptr ^. mpType)

        forM_ (zip svs [0 .. len - 1]) $ \(sv, i) -> do
            iSym <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $ fromIntegral i
            ref' <- mirRef_offsetSim (ptr ^. mpRef) iSym
            rv <- liftIO $ setupToReg sym sc termSub w4VarMap allocMap shp sv
            writeMirRefSim (ptr ^. mpType) ref' rv

    -- Clobber all globals.  We don't yet support mentioning globals in specs.
    -- However, we also don't prevent the subject function from modifying
    -- globals.  Since we have no idea what the subject function might do to
    -- globals during a normal call, we conservatively clobber all globals as
    -- part of the spec override.
    clobberGlobals sym loc "run_spec_clobber_globals" myCS

    return retVal


-- | Match argument RegValue `rv` against SetupValue pattern `sv`.  On success,
-- this may update `termSub` and `setupValueSub` with new bindings for the
-- MethodSpec's symbolic variables and allocations.
matchArg ::
    forall sym t st fs tp0.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    (forall tp'. W4.Expr t tp' -> IO SAW.Term) ->
    Map MS.AllocIndex (Some MirAllocSpec) ->
    MS.ConditionMetadata ->
    TypeShape tp0 -> RegValue sym tp0 -> MS.SetupValue MIR ->
    MirOverrideMatcher sym ()
matchArg sym sc eval allocSpecs md shp0 rv0 sv0 = go shp0 rv0 sv0
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp -> MS.SetupValue MIR ->
        MirOverrideMatcher sym ()
    go (UnitShape _) () (MS.SetupTuple () []) = return ()
    go (PrimShape _ _btpr) expr (MS.SetupTerm tt) = do
        loc <- use MS.osLocation
        exprTerm <- liftIO $ eval expr
        case SAW.asExtCns $ SAW.ttTerm tt of
            Just ec -> do
                let var = SAW.ecVarIndex ec
                sub <- use MS.termSub
                when (IntMap.member var sub) $
                    MS.failure loc MS.NonlinearPatternNotSupported
                MS.termSub %= IntMap.insert var exprTerm
            Nothing -> do
                -- If the `TypedTerm` is a constant, we want to assert that the
                -- argument `expr` matches the constant.
                --
                -- For now, this is the case that fires for the length fields
                -- of slices.  This means the slice length must exactly match
                -- the length used in the MethodSpec, or else the spec must
                -- specifically handle symbolic lengths in some range.  It
                -- would be nice to allow any longer slice length, but it's not
                -- clear how to do that soundly (the function might branch on
                -- the length of the slice, for instance).
                Some val <- liftIO $ termToExpr sym sc mempty (SAW.ttTerm tt)
                Refl <- case testEquality (W4.exprType expr) (W4.exprType val) of
                    Just x -> return x
                    Nothing -> error $ "type mismatch: concrete argument type " ++
                        show (W4.exprType expr) ++ " doesn't match SetupValue type " ++
                        show (W4.exprType val)
                eq <- liftIO $ W4.isEq sym expr val
                MS.addAssert eq md $ SimError loc $
                    AssertFailureSimError
                        ("mismatch on " ++ show (W4.exprType expr) ++ ": expected " ++
                            show (W4.printSymExpr val))
                        ""
    go (TupleShape _ _ flds) rvs (MS.SetupTuple () svs) = goFields flds rvs svs
    go (ArrayShape _ _ shp) vec (MS.SetupArray _ svs) = case vec of
        MirVector_Vector v -> zipWithM_ (\x y -> go shp x y) (toList v) svs
        MirVector_PartialVector pv -> forM_ (zip (toList pv) svs) $ \(p, sv) -> do
            rv <- liftIO $ readMaybeType sym "vector element" (shapeType shp) p
            go shp rv sv
        MirVector_Array _ -> error $ "matchArg: MirVector_Array NYI"
    go (StructShape _ _ flds) rvs (MS.SetupStruct _ svs) = goFields flds rvs svs
    go (TransparentShape _ shp) rv sv = go shp rv sv
    go (RefShape refTy pointeeTy mutbl tpr) ref (MS.SetupVar alloc) =
        goRef refTy pointeeTy mutbl tpr ref alloc 0
    go (RefShape refTy pointeeTy mutbl tpr) ref (MS.SetupElem () (MS.SetupVar alloc) idx) =
        goRef refTy pointeeTy mutbl tpr ref alloc idx
    go (SliceShape _ ty mutbl tpr) (Ctx.Empty Ctx.:> RV ref Ctx.:> RV len)
                                   (MS.SetupSlice (MirSetupSliceRaw refSV lenSV)) = do
        let (refShp, lenShp) = sliceShapeParts ty mutbl tpr
        go refShp ref refSV
        go lenShp len lenSV
    go (FnPtrShape _ _ _) _ _ =
        error "Function pointers not currently supported in overrides"
    go shp _ sv = error $ "matchArg: type error: bad SetupValue " ++
        show (MS.ppSetupValue sv) ++ " for " ++ show (shapeType shp)

    goFields :: forall ctx0. Assignment FieldShape ctx0 -> Assignment (RegValue' sym) ctx0 ->
        [MS.SetupValue MIR] -> MirOverrideMatcher sym ()
    goFields flds0 rvs0 svs0 = loop flds0 rvs0 (reverse svs0)
      where
        loop :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
            [MS.SetupValue MIR] -> MirOverrideMatcher sym ()
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

    goRef :: forall tp'.
        M.Ty ->
        M.Ty ->
        M.Mutability ->
        TypeRepr tp' ->
        MirReferenceMux sym ->
        MS.AllocIndex ->
        -- | The expected offset of `ref` past the start of the allocation.
        Int ->
        MirOverrideMatcher sym ()
    goRef refTy pointeeTy mutbl tpr ref alloc refOffset = do
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
        --offsetSym <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $ fromIntegral $ negate idx
        --startRef <- lift $ mirRef_offsetWrapSim tpr ref offsetSym
        when (idx < refOffset) $ error $
            "matchArg: expected at least " ++ show refOffset ++ " accessible elements " ++
                "before reference, but only got " ++ show idx

        Some allocSpec <- return $ case Map.lookup alloc allocSpecs of
            Just x -> x
            Nothing -> error $ "no such alloc " ++ show alloc
        let numAfter = allocSpec ^. maLen - refOffset
        when (len - idx < numAfter) $ error $
            "matchArg: expected at least " ++ show numAfter ++ " accessible elements " ++
                "after reference, but only got " ++ show (len - idx)

        -- Offset backward by `idx` to get a pointer to the start of the accessible
        -- allocation.
        offsetSym <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $
            fromIntegral $ negate refOffset
        ref' <- lift $ mirRef_offsetWrapSim ref offsetSym

        m <- use MS.setupValueSub
        case Map.lookup alloc m of
            Nothing -> return ()
            Just (Some ptr)
              | Just Refl <- testEquality tpr (ptr ^. mpType) -> do
                eq <- lift $ ovrWithBackend $ \bak ->
                        liftIO $ mirRef_eqIO bak ref' (ptr ^. mpRef)
                let loc = mkProgramLoc "matchArg" InternalPos
                MS.addAssert eq md $
                    SimError loc (AssertFailureSimError ("mismatch on " ++ show alloc) "")
              | otherwise -> error $ "mismatched types for " ++ show alloc ++ ": " ++
                    show tpr ++ " does not match " ++ show (ptr ^. mpType)
        MS.setupValueSub %= Map.insert alloc
            (Some $ MirPointer tpr (tyToPtrKind refTy) mutbl pointeeTy ref')


-- | Convert a SetupValue to a RegValue.  This is used for MethodSpec outputs,
-- namely the return value and any post-state PointsTos.
setupToReg :: forall sym t st fs tp0.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    -- | `termSub`: maps `VarIndex`es in the MethodSpec's namespace to `Term`s
    -- in the context's namespace.
    IntMap SAW.Term ->
    -- | `myRegMap`: maps `VarIndex`es in the context's namespace to the
    -- corresponding W4 variables in the context's namespace.
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    Map MS.AllocIndex (Some (MirPointer sym)) ->
    TypeShape tp0 ->
    MS.SetupValue MIR ->
    IO (RegValue sym tp0)
setupToReg sym sc termSub myRegMap allocMap shp0 sv0 = go shp0 sv0
  where
    go :: forall tp. TypeShape tp -> MS.SetupValue MIR -> IO (RegValue sym tp)
    go (UnitShape _) (MS.SetupTuple _ []) = return ()
    go (PrimShape _ btpr) (MS.SetupTerm tt) = do
        term <- liftIO $ SAW.scInstantiateExt sc termSub $ SAW.ttTerm tt
        Some expr <- termToExpr sym sc myRegMap term
        Refl <- case testEquality (W4.exprType expr) btpr of
            Just x -> return x
            Nothing -> error $ "setupToReg: expected " ++ show btpr ++ ", but got " ++
                show (W4.exprType expr)
        return expr
    go (TupleShape _ _ flds) (MS.SetupTuple _ svs) = goFields flds svs
    go (ArrayShape _ _ shp) (MS.SetupArray _ svs) = do
        rvs <- mapM (go shp) svs
        return $ MirVector_Vector $ V.fromList rvs
    go (StructShape _ _ flds) (MS.SetupStruct _ svs) =
        goFields flds svs
    go (TransparentShape _ shp) sv = go shp sv
    go (RefShape _ _ _ tpr) (MS.SetupVar alloc) = case Map.lookup alloc allocMap of
        Just (Some ptr) -> case testEquality tpr (ptr ^. mpType) of
            Just Refl -> return $ ptr ^. mpRef
            Nothing -> error $ "setupToReg: type error: bad reference type for " ++ show alloc ++
                ": got " ++ show (ptr ^. mpType) ++ " but expected " ++ show tpr
        Nothing -> error $ "setupToReg: no definition for " ++ show alloc
    go (SliceShape _ ty mutbl tpr) (MS.SetupSlice (MirSetupSliceRaw refSV lenSV)) = do
        let (refShp, lenShp) = sliceShapeParts ty mutbl tpr
        refRV <- go refShp refSV
        lenRV <- go lenShp lenSV
        pure $ Ctx.Empty Ctx.:> RV refRV Ctx.:> RV lenRV
    go (EnumShape _ _ _ _ _) _ =
      error "Enums not currently supported in overrides"
    go (FnPtrShape _ _ _) _ =
        error "Function pointers not currently supported in overrides"
    go shp sv = error $ "setupToReg: type error: bad SetupValue for " ++ show (shapeType shp) ++
        ": " ++ show (MS.ppSetupValue sv)

    goFields :: forall ctx0. Assignment FieldShape ctx0 -> [MS.SetupValue MIR] ->
        IO (Assignment (RegValue' sym) ctx0)
    goFields shps0 svs0 = loop shps0 (reverse svs0)
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
    MirOverrideMatcher sym (MS.ConditionMetadata, SAW.Term)
condTerm _sc (MS.SetupCond_Equal _loc _sv1 _sv2) = do
    error $ "learnCond: SetupCond_Equal NYI" -- TODO
condTerm sc (MS.SetupCond_Pred md tt) = do
    sub <- use MS.termSub
    t' <- liftIO $ SAW.scInstantiateExt sc sub $ SAW.ttTerm tt
    return (md, t')
condTerm _ (MS.SetupCond_Ghost _ _ _) = do
    error $ "learnCond: SetupCond_Ghost is not supported"


checkDisjoint ::
    (sym ~ W4.ExprBuilder t st fs, IsSymBackend sym bak) =>
    bak ->
    [(MS.AllocIndex, Some (MirPointer sym))] ->
    IO ()
checkDisjoint bak refs = go refs
  where
    sym = backendGetSym bak

    go [] = return ()
    go ((alloc, Some ptr) : rest) = do
        forM_ rest $ \(alloc', Some ptr') -> do
            disjoint <- W4.notPred sym =<< mirRef_overlapsIO bak (ptr ^. mpRef) (ptr' ^. mpRef)
            assert bak disjoint $ GenericSimError $
                "references " ++ show alloc ++ " and " ++ show alloc' ++ " must not overlap"
        go rest

-- | Take a 'MS.SetupValue' that is assumed to be a bare 'MS.SetupVar' and
-- extract the underlying 'MS.AllocIndex'. If this assumption does not hold,
-- this function will raise an error.
--
-- This is used in conjunction with 'MirPointsTo' values. With the way that
-- @crucible-mir-comp@ is currently set up, the only sort of 'MS.SetupValue'
-- that will be put into a 'MirPointsTo' value's left-hand side is a
-- 'MS.SetupVar', so we can safely use this function on such 'MS.SetupValue's.
-- Other parts of SAW can break this assumption (e.g., if you wrote something
-- like @mir_points_to (mir_static "X") ...@ in a SAW specification), but these
-- parts of SAW are not used in @crucible-mir-comp@.
setupVarAllocIndex :: Applicative m => MS.SetupValue MIR -> m MS.AllocIndex
setupVarAllocIndex (MS.SetupVar idx) = pure idx
setupVarAllocIndex val =
  error $ "setupVarAllocIndex: Expected SetupVar, received: "
       ++ show (MS.ppSetupValue val)
