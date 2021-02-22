{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Mir.Compositional.Clobber
where

import Control.Lens ((%=))
import Control.Monad.Except
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import qualified Data.Vector as V
import GHC.Stack (HasCallStack)

import qualified What4.Expr.Builder as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4
import What4.ProgramLoc

import Lang.Crucible.Backend
import Lang.Crucible.Simulator
import Lang.Crucible.Types

import qualified Crux.Model as Crux
import Crux.Types (Model)

import Mir.Intrinsics hiding (MethodSpec, MethodSpecBuilder)
import qualified Mir.Mir as M
import Mir.TransTy (pattern CTyUnsafeCell)

import Mir.Compositional.Convert



-- Helper functions for generating clobbering PointsTos

-- | Replace each primitive value within `rv` with a fresh symbolic variable.
clobberSymbolic :: forall sym t st fs tp rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym -> ProgramLoc -> String -> TypeShape tp -> RegValue sym tp ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym tp)
clobberSymbolic sym loc nameStr shp rv = go shp rv
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp ->
        OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym tp)
    go (UnitShape _) () = return ()
    go shp@(PrimShape _ btpr) _rv = freshSymbolic sym loc nameStr shp
    go (ArrayShape _ _ shp) mirVec = case mirVec of
        MirVector_Vector v -> MirVector_Vector <$> mapM (go shp) v
        MirVector_PartialVector pv ->
            MirVector_PartialVector <$> mapM (mapM (go shp)) pv
        MirVector_Array _ -> error $ "clobberSymbolic: MirVector_Array is unsupported"
    go (TupleShape _ _ flds) rvs =
        Ctx.zipWithM goField flds rvs
    go (StructShape _ _ flds) (AnyValue tpr rvs)
      | Just Refl <- testEquality tpr shpTpr = AnyValue tpr <$> Ctx.zipWithM goField flds rvs
      | otherwise = error $ "clobberSymbolic: type error: expected " ++ show shpTpr ++
        ", but got Any wrapping " ++ show tpr
      where shpTpr = StructRepr $ fmapFC fieldShapeType flds
    go shp _rv = error $ "clobberSymbolic: " ++ show (shapeType shp) ++ " NYI"

    goField :: forall tp. FieldShape tp -> RegValue' sym tp ->
        OverrideSim (Model sym) sym MIR rtp args ret (RegValue' sym tp)
    goField (ReqField shp) (RV rv) = RV <$> go shp rv
    goField (OptField shp) (RV rv) = do
        rv' <- liftIO $ readMaybeType sym "field" (shapeType shp) rv
        rv'' <- go shp rv'
        return $ RV $ W4.justPartExpr sym rv''

-- | Like `clobberSymbolic`, but for values in "immutable" memory.  Values
-- inside an `UnsafeCell<T>` wrapper can still be modified even with only
-- immutable (`&`) access.  So this function modifies only the portions of `rv`
-- that lie within an `UnsafeCell` and leaves the rest unchanged.
clobberImmutSymbolic :: forall sym t st fs tp rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym -> ProgramLoc -> String -> TypeShape tp -> RegValue sym tp ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym tp)
clobberImmutSymbolic sym loc nameStr shp rv = go shp rv
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp ->
        OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym tp)
    go (UnitShape _) () = return ()
    -- If we reached a leaf value without entering an `UnsafeCell`, then
    -- there's nothing to change.
    go (PrimShape _ _) rv = return rv
    go (ArrayShape _ _ shp) mirVec = case mirVec of
        MirVector_Vector v -> MirVector_Vector <$> mapM (go shp) v
        MirVector_PartialVector pv ->
            MirVector_PartialVector <$> mapM (mapM (go shp)) pv
        MirVector_Array _ -> error $ "clobberSymbolic: MirVector_Array is unsupported"
    go shp@(StructShape (CTyUnsafeCell _) _ _) rv =
        clobberSymbolic sym loc nameStr shp rv
    go (TupleShape _ _ flds) rvs =
        Ctx.zipWithM goField flds rvs
    go (StructShape _ _ flds) (AnyValue tpr rvs)
      | Just Refl <- testEquality tpr shpTpr = AnyValue tpr <$> Ctx.zipWithM goField flds rvs
      | otherwise = error $ "clobberSymbolic: type error: expected " ++ show shpTpr ++
        ", but got Any wrapping " ++ show tpr
      where shpTpr = StructRepr $ fmapFC fieldShapeType flds
    go shp _rv = error $ "clobberSymbolic: " ++ show (shapeType shp) ++ " NYI"

    goField :: forall tp. FieldShape tp -> RegValue' sym tp ->
        OverrideSim (Model sym) sym MIR rtp args ret (RegValue' sym tp)
    goField (ReqField shp) (RV rv) = RV <$> go shp rv
    goField (OptField shp) (RV rv) = do
        rv' <- liftIO $ readMaybeType sym "field" (shapeType shp) rv
        rv'' <- go shp rv'
        return $ RV $ W4.justPartExpr sym rv''

-- | Construct a fresh symbolic `RegValue` of type `tp`.
freshSymbolic :: forall sym t st fs tp rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym -> ProgramLoc -> String -> TypeShape tp ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym tp)
freshSymbolic sym loc nameStr shp = go shp
  where
    go :: forall tp. TypeShape tp ->
        OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym tp)
    go (UnitShape _) = return ()
    go (PrimShape _ btpr) = do
        let nameSymbol = W4.safeSymbol nameStr
        expr <- liftIO $ W4.freshConstant sym nameSymbol btpr
        stateContext . cruciblePersonality %= Crux.addVar loc nameStr btpr expr
        return expr
    go (ArrayShape (M.TyArray _ len) _ shp) =
        MirVector_Vector <$> V.replicateM len (go shp)
    go shp = error $ "freshSymbolic: " ++ show (shapeType shp) ++ " NYI"
