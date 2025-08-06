{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Mir.Compositional.Clobber
where

import Control.Lens ((^.), (^?), ix)
import Control.Monad (forM_)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Vector as V
import GHC.Stack (HasCallStack)

import qualified What4.Expr.Builder as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4
import What4.ProgramLoc

import Lang.Crucible.Backend
import Lang.Crucible.Simulator

import SAWCentral.Crucible.MIR.TypeShape

import Mir.Generator (CollectionState, collection, staticMap, StaticVar(..))
import Mir.Intrinsics hiding (MethodSpec, MethodSpecBuilder)
import qualified Mir.Mir as M
import Mir.TransTy (pattern CTyUnsafeCell)

import Mir.Compositional.Convert



-- Helper functions for generating clobbering PointsTos

-- | Apply `f` to all of the `RegValue`s within a `RegValue`.  This calls `f`
-- only on the immediate descendants of `rv`; it does not perform a recursive
-- traversal.
traverseTypeShape :: forall sym p t st fs tp0 rtp args ret.
  (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
  sym -> String ->
  (forall tp.
    TypeShape tp ->
    RegValue sym tp ->
    OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp)) ->
  TypeShape tp0 -> RegValue sym tp0 ->
  OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp0)
traverseTypeShape sym nameStr f shp0 rv0 = go shp0 rv0
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp ->
        OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp)
    go (UnitShape _) () = return ()
    go (PrimShape _ _) _ = die "PrimShape unimplemented"
    go (ArrayShape _ _ shp) mirVec = case mirVec of
        MirVector_Vector v -> MirVector_Vector <$> mapM (f shp) v
        MirVector_PartialVector pv ->
            MirVector_PartialVector <$> mapM (mapM (f shp)) pv
        MirVector_Array _ -> die "MirVector_Array is unsupported"
    go (TupleShape _ _ flds) rvs =
        Ctx.zipWithM (traverseFieldShape sym f) flds rvs
    go (StructShape _ _ flds) rvs =
        Ctx.zipWithM (traverseFieldShape sym f) flds rvs
    go (TransparentShape _ shp) rv = f shp rv
    go (EnumShape _ _ _ _ _) _rv = die "EnumShape unimplemented"
    go (FnPtrShape _ _ _) _rv = die "FnPtrShape unimplemented"
    go (RefShape _ _ _ _) _rv = die "RefShape unimplemented"
    go (SliceShape _ ty mutbl tpr) (Ctx.Empty Ctx.:> RV ref Ctx.:> RV len) = do
        let (refShp, lenShp) = sliceShapeParts ty mutbl tpr
        ref' <- f refShp ref
        len' <- f lenShp len
        pure $ Ctx.Empty Ctx.:> RV ref' Ctx.:> RV len'

    die :: String -> a
    die msg = error $ "traverseTypeShape: " ++ msg ++ ", for " ++ nameStr

-- | Apply `f` to all of the `RegValue`s within a `RegValue'`.
--
-- When the `FieldShape` is `OptField`, this requires the `MaybeRepr` to be
-- initialized; it will raise an `error` otherwise.
traverseFieldShape :: forall sym p t st fs tp0 rtp args ret.
  (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
  sym ->
  (forall tp.
    TypeShape tp ->
    RegValue sym tp ->
    OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp)) ->
  FieldShape tp0 -> RegValue' sym tp0 ->
  OverrideSim (p sym) sym MIR rtp args ret (RegValue' sym tp0)
traverseFieldShape sym f shp0 rv0 = goField shp0 rv0
  where
    goField :: forall tp. FieldShape tp -> RegValue' sym tp ->
        OverrideSim (p sym) sym MIR rtp args ret (RegValue' sym tp)
    goField (ReqField shp) (RV rv) = RV <$> f shp rv
    goField (OptField shp) (RV rv) = do
        rv' <- liftIO $ readMaybeType sym "field" (shapeType shp) rv
        rv'' <- f shp rv'
        return $ RV $ W4.justPartExpr sym rv''

-- | Replace each primitive value within `rv` with a fresh symbolic variable.
clobberSymbolic :: forall sym p t st fs tp0 rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym -> ProgramLoc -> String -> TypeShape tp0 -> RegValue sym tp0 ->
    OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp0)
clobberSymbolic sym loc nameStr shp0 rv0 = go shp0 rv0
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp ->
        OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp)
    go shp@(PrimShape _ _btpr) _rv = freshSymbolic sym loc nameStr shp
    go shp rv = traverseTypeShape sym nameStr go shp rv

-- | Like `clobberSymbolic`, but for values in "immutable" memory.  Values
-- inside an `UnsafeCell<T>` wrapper can still be modified even with only
-- immutable (`&`) access.  So this function modifies only the portions of `rv`
-- that lie within an `UnsafeCell` and leaves the rest unchanged.
clobberImmutSymbolic :: forall sym p t st fs tp0 rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym -> ProgramLoc -> String -> TypeShape tp0 -> RegValue sym tp0 ->
    OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp0)
clobberImmutSymbolic sym loc nameStr shp0 rv0 = go shp0 rv0
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp ->
        OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp)
    go shp@(StructShape (CTyUnsafeCell _) _ _) rv =
        clobberSymbolic sym loc nameStr shp rv
    go shp@(TransparentShape (CTyUnsafeCell _) _) rv =
        clobberSymbolic sym loc nameStr shp rv
    -- If we reached a leaf value without entering an `UnsafeCell`, then
    -- there's nothing to change.
    go (PrimShape _ _) rv = return rv
    -- Since this ref is in immutable memory, whatever behavior we're
    -- approximating with this clobber can't possibly modify it.
    go (RefShape _ _ _ _tpr) rv = return rv
    go shp rv = traverseTypeShape sym nameStr go shp rv

-- | Construct a fresh symbolic `RegValue` of type `tp0`.
freshSymbolic :: forall sym p t st fs tp0 rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym -> ProgramLoc -> String -> TypeShape tp0 ->
    OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp0)
freshSymbolic sym loc nameStr shp0 = go shp0
  where
    go :: forall tp. TypeShape tp ->
        OverrideSim (p sym) sym MIR rtp args ret (RegValue sym tp)
    go (UnitShape _) = return ()
    go (PrimShape _ btpr) = do
        let nameSymbol = W4.safeSymbol nameStr
        expr <- liftIO $ W4.freshConstant sym nameSymbol btpr
        let ev = CreateVariableEvent loc nameStr btpr expr
        ovrWithBackend $ \bak ->
          liftIO $ addAssumptions bak (singleEvent ev)
        return expr
    go (ArrayShape (M.TyArray _ len) _ shp) =
        MirVector_Vector <$> V.replicateM len (go shp)
    go (FnPtrShape _ _ _) = die "Function pointers not currently supported in overrides"
    go shp = die $ show (shapeType shp) ++ " NYI"

    die :: String -> a
    die msg = error $ "freshSymbolic: " ++ msg ++ ", for " ++ nameStr


-- Note on clobbering refs inside `static`s: The current behavior is to leave
-- refs inside immutable memory unchanged, and to error on encountering a ref
-- inside mutable memory.  We don't explicitly traverse refs inside
-- `clobberGlobals`; however, since immutable statics always contain a constant
-- value (and can't be mutated after the program starts), refs inside them can
-- only ever point to other statics.  So if immutable static `A` contains a
-- reference to a non-`Freeze` (i.e. `UnsafeCell`-containing) allocation `x`,
-- it's okay that we don't traverse the ref from `A` to `x`, because `x` is
-- guaranteed to be another static, and will get clobbered that way.
--
-- If we ever add a `RefShape` case to the non-`Immut` `clobberSymbolic`, that
-- case will need to traverse through refs and clobber their contents.  We
-- can't rely on the target of the ref being another static, since the program
-- might have stored the result of e.g. `Box::leak` (of type `&'static mut T`)
-- into the mutable static.  And overwriting the ref itself with a symbolic or
-- invalid ref value is not enough, since the function we're approximating
-- might write through the old ref before replacing it with a new one.

clobberGlobals :: forall sym p t st fs rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym -> ProgramLoc -> String -> CollectionState ->
    OverrideSim (p sym) sym MIR rtp args ret ()
clobberGlobals sym loc nameStr cs = do
    forM_ (Map.toList $ cs ^. staticMap) $ \(defId, StaticVar gv) -> do
        let static = case cs ^? collection . M.statics . ix defId of
                Just x -> x
                Nothing -> error $ "couldn't find static def for " ++ show defId
        let tpr = globalType gv
        let shp = tyToShapeEq (cs ^. collection) (static ^. M.sTy) tpr
        let nameStr' = nameStr ++ " (" ++ show defId ++ ")"
        let clobber = case static ^. M.sMutable of
                False -> clobberImmutSymbolic sym loc nameStr'
                True -> clobberSymbolic sym loc nameStr'
        rv <- readGlobal gv
        rv' <- clobber shp rv
        writeGlobal gv rv'

clobberGlobalsOverride :: forall sym p t st fs rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    CollectionState ->
    OverrideSim (p sym) sym MIR rtp args ret ()
clobberGlobalsOverride cs = do
    sym <- getSymInterface
    loc <- liftIO $ W4.getCurrentProgramLoc sym
    clobberGlobals sym loc "clobber_globals" cs
