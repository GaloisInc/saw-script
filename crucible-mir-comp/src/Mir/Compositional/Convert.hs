{-# LANGUAGE DataKinds #-}
{-# Language FlexibleContexts #-}
{-# Language GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Conversions between Crucible `RegValue`s and SAW `Term`s.
module Mir.Compositional.Convert
where

import Control.Monad
import Control.Monad.IO.Class
import Data.Foldable
import Data.Functor.Const
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Parameterized.Context (pattern Empty, pattern (:>), Assignment)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Stack (HasCallStack)

import Lang.Crucible.Backend
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Types

import qualified What4.Expr.Builder as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4
import qualified What4.SWord as W4 (SWord(..))

import qualified SAWCore.SharedTerm as SAW
import qualified SAWCore.Simulator.MonadLazy as SAW
import qualified SAWCore.Simulator.Value as SAW
import SAWCoreWhat4.What4 (SValue)
import qualified SAWCoreWhat4.What4 as SAW
import qualified SAWCoreWhat4.ReturnTrip as SAW (baseSCType)

import SAWCentral.Crucible.MIR.TypeShape

import Mir.Intrinsics
import qualified Mir.Mir as M


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
    go tpr v | AsBaseType _btpr <- asBaseType tpr = f v
    go AnyRepr (AnyValue tpr' v') = go tpr' v'
    go UnitRepr () = return ()
    go (MaybeRepr _tpr) W4.Unassigned = return ()
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
        CtxRepr ctx -> Assignment f ctx -> (forall tp. TypeRepr tp -> f tp -> m ()) -> m ()
    forMWithRepr_ ctxr assn f = void $
        Ctx.zipWithM (\x y -> f x y >> return (Const ())) ctxr assn

-- | Run `f` on each free symbolic variable in `e`.
visitExprVars ::
    forall t tp m.
    MonadIO m =>
    W4.IdxCache t (Const ()) ->
    W4.Expr t tp ->
    (forall tp'. W4.ExprBoundVar t tp' -> m ()) ->
    m ()
visitExprVars cache e f = go Set.empty e
  where
    go :: Set (Some (W4.ExprBoundVar t)) -> W4.Expr t tp' -> m ()
    go bound e = void $ W4.idxCacheEval cache e (go' bound e >> return (Const ()))

    go' :: Set (Some (W4.ExprBoundVar t)) -> W4.Expr t tp' -> m ()
    go' bound e = case e of
        W4.BoundVarExpr v
          | not $ Set.member (Some v) bound -> f v
          | otherwise -> return ()
        W4.NonceAppExpr nae -> case W4.nonceExprApp nae of
            W4.Forall v e' -> go (Set.insert (Some v) bound) e'
            W4.Exists v e' -> go (Set.insert (Some v) bound) e'
            W4.Annotation _ _ e' -> go bound e'
            W4.ArrayFromFn _ -> error "unexpected ArrayFromFn"
            W4.MapOverArrays _ _ _ -> error "unexpected MapOverArrays"
            W4.ArrayTrueOnEntries _ _ -> error "unexpected ArrayTrueOnEntries"
            W4.FnApp _ _ -> error "unexpected FnApp"
        W4.AppExpr ae ->
            void $ W4.traverseApp (\e' -> go bound e' >> return e') $ W4.appExprApp ae
        W4.FloatExpr _ _ _ -> return ()
        W4.StringExpr _ _ -> return ()
        W4.BoolExpr _ _ -> return ()
        W4.SemiRingLiteral _ _ _ -> return ()


readMaybeType :: forall tp sym. IsSymInterface sym =>
    sym -> String -> TypeRepr tp -> RegValue sym (MaybeType tp) ->
    IO (RegValue sym tp)
readMaybeType sym desc tpr rv = readPartExprMaybe sym rv >>= \x -> case x of
    Just x -> return x
    Nothing -> error $ "regToSetup: accessed possibly-uninitialized " ++ desc ++
        " of type " ++ show tpr

readPartExprMaybe :: IsSymInterface sym => sym -> W4.PartExpr (W4.Pred sym) a -> IO (Maybe a)
readPartExprMaybe _sym W4.Unassigned = return Nothing
readPartExprMaybe _sym (W4.PE p v)
  | Just True <- W4.asConstantPred p = return $ Just v
  | otherwise = return Nothing


-- | Convert a `SAW.Term` into a `W4.Expr`.
termToExpr :: forall sym t st fs.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    SAW.Term ->
    IO (Some (W4.SymExpr sym))
termToExpr sym sc varMap term = do
    sv <- termToSValue sym sc varMap term
    case SAW.valueToSymExpr sv of
        Just x -> return x
        Nothing -> error $ "termToExpr: failed to convert SValue"

-- | Convert a `SAW.Term` into a Crucible `RegValue`.  Requires a `TypeShape`
-- giving the expected MIR/Crucible type in order to distinguish cases like
-- `(A, (B, C))` vs `(A, B, C)` (these are the same type in saw-core).
termToReg :: forall sym t st fs tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    SAW.Term ->
    TypeShape tp ->
    IO (RegValue sym tp)
termToReg sym sc varMap term shp = do
    sv <- termToSValue sym sc varMap term
    go shp sv
  where
    go :: forall tp'. TypeShape tp' -> SValue sym -> IO (RegValue sym tp')
    go shp sv = case (shp, sv) of
        (UnitShape _, SAW.VUnit) -> return ()
        (PrimShape _ BaseBoolRepr, SAW.VBool b) -> return b
        (PrimShape _ (BaseBVRepr w), SAW.VWord (W4.DBV e))
          | Just Refl <- testEquality (W4.exprType e) (BaseBVRepr w) -> return e
        (PrimShape _ (BaseBVRepr w), SAW.VVector v)
          | intValue w == fromIntegral (V.length v) -> do
            bits <- forM v $ SAW.force >=> \x -> case x of
                SAW.VBool b -> return b
                _ -> fail $ "termToReg: type error: need to produce " ++ show (shapeType shp) ++
                    ", but simulator returned a vector containing " ++ show x
            buildBitVector w bits
        (TupleShape _ _ flds, _) -> do
            svs <- tupleToListRev (Ctx.sizeInt $ Ctx.size flds) [] sv
            goTuple flds svs
        (ArrayShape (M.TyArray _ n) _ shp, SAW.VVector thunks) -> do
            svs <- mapM SAW.force $ toList thunks
            when (length svs /= n) $ fail $
                "termToReg: type error: expected an array of length " ++ show n ++
                    ", but simulator returned " ++ show (length svs) ++ " elements"
            v <- V.fromList <$> mapM (go shp) svs
            return $ MirVector_Vector v
        -- Special case: saw-core/cryptol doesn't distinguish bitvectors from
        -- vectors of booleans, so it may return `VWord` (bitvector) where an
        -- array of `bool` is expected.
        (ArrayShape (M.TyArray _ n) _ (PrimShape _ BaseBoolRepr), SAW.VWord (W4.DBV e))
          | Just (Some w) <- someNat n,
            Just LeqProof <- testLeq (knownNat @1) w,
            Just Refl <- testEquality (W4.exprType e) (BaseBVRepr w) -> do
            v <- V.generateM n $ \i -> do
                -- Cryptol bitvectors are MSB-first, but What4 uses LSB-first.
                liftIO $ W4.testBitBV sym (fromIntegral $ n - i - 1) e
            return $ MirVector_Vector v
        _ -> error $ "termToReg: type error: need to produce " ++ show (shapeType shp) ++
            ", but simulator returned " ++ show sv

    -- | Convert an `SValue` tuple (built from nested `VPair`s) into a list of
    -- the inner `SValue`s, in reverse order.
    tupleToListRev :: Int -> [SValue sym] -> SValue sym -> IO [SValue sym]
    tupleToListRev 2 acc (SAW.VPair x y) = do
        x' <- SAW.force x
        y' <- SAW.force y
        return $ y' : x' : acc
    tupleToListRev n acc (SAW.VPair x xs) | n > 2 = do
        x' <- SAW.force x
        xs' <- SAW.force xs
        tupleToListRev (n - 1) (x' : acc) xs'
    tupleToListRev n _ _ | n < 2 = error $ "bad tuple size " ++ show n
    tupleToListRev n _ v = error $ "termToReg: expected tuple of " ++ show n ++
        " elements, but got " ++ show v

    goTuple :: forall ctx.
        Assignment FieldShape ctx ->
        [SValue sym] ->
        IO (RegValue sym (StructType ctx))
    goTuple Empty [] = return Empty
    goTuple (flds :> fld) (sv : svs) = do
        rv <- goField fld sv
        rvs <- goTuple flds svs
        return (rvs :> RV rv)
    goTuple _ _ = fail "termToReg: mismatched tuple size"

    goField :: forall tp'. FieldShape tp' -> SValue sym -> IO (RegValue sym tp')
    goField (ReqField shp) sv = go shp sv
    goField (OptField shp) sv = W4.justPartExpr sym <$> go shp sv

    -- | Build a bitvector from a vector of bits.  The length of the vector is
    -- required to match `w`.
    buildBitVector :: forall w. (1 <= w) =>
        NatRepr w -> Vector (W4.Pred sym) -> IO (W4.SymExpr sym (BaseBVType w))
    buildBitVector w v = do
        bvs <- mapM (\b -> W4.bvFill sym (knownNat @1) b) $ toList v
        case bvs of
            [] -> error $ "buildBitVector: expected " ++ show w ++ " bits, but got 0"
            (bv : bvs') -> do
                Some bv' <- go (knownNat @1) bv bvs'
                Refl <- case testEquality (W4.exprType bv') (BaseBVRepr w) of
                    Just x -> return x
                    Nothing -> error $ "buildBitVector: expected " ++ show (BaseBVRepr w) ++
                        ", but got " ++ show (W4.exprType bv')
                return bv'
      where
        go :: forall w. (1 <= w) =>
            NatRepr w ->
            W4.SymExpr sym (BaseBVType w) ->
            [W4.SymExpr sym (BaseBVType 1)] ->
            IO (Some (W4.SymExpr sym))
        go _ bv [] = return $ Some bv
        go w bv (b : bs)
          | LeqProof <- addPrefixIsLeq w (knownNat @1) = do
            bv' <- W4.bvConcat sym bv b
            go (addNat w (knownNat @1)) bv' bs

-- | Common code for termToExpr and termToReg
termToSValue :: forall sym t st fs.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    SAW.Term ->
    IO (SAW.SValue sym)
termToSValue sym sc varMap term = do
    let convert (Some expr) = case SAW.symExprToValue (W4.exprType expr) expr of
            Just x -> return x
            Nothing -> error $ "termToExpr: failed to convert var  of what4 type " ++
                show (W4.exprType expr)
    ecMap <- mapM convert varMap
    ref <- newIORef mempty
    SAW.w4SolveBasic sym sc mempty ecMap ref mempty term

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


exprToTerm :: forall sym t st fs tp m.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, MonadIO m, MonadFail m) =>
    sym ->
    SAW.SharedContext ->
    IORef (Map SAW.VarIndex (Some (W4.Expr t))) ->
    W4.Expr t tp ->
    m SAW.Term
exprToTerm sym sc w4VarMapRef val = liftIO $ do
    ty <- SAW.baseSCType sym sc (W4.exprType val)
    ec <- SAW.scFreshEC sc "w4expr" ty
    modifyIORef w4VarMapRef $ Map.insert (SAW.ecVarIndex ec) (Some val)
    term <- SAW.scExtCns sc ec
    return term

regToTerm :: forall sym t st fs tp m.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, MonadIO m, MonadFail m) =>
    sym ->
    SAW.SharedContext ->
    String ->
    IORef (Map SAW.VarIndex (Some (W4.Expr t))) ->
    TypeShape tp ->
    RegValue sym tp ->
    m SAW.Term
regToTerm sym sc name w4VarMapRef shp rv = go shp rv
  where
    go :: forall tp.
        TypeShape tp ->
        RegValue sym tp ->
        m SAW.Term
    go shp rv = case (shp, rv) of
        (UnitShape _, ()) -> liftIO $ SAW.scUnitValue sc
        (PrimShape _ _, expr) -> exprToTerm sym sc w4VarMapRef expr
        (TupleShape _ _ flds, rvs) -> do
            terms <- Ctx.zipWithM (\fld (RV rv) -> Const <$> goField fld rv) flds rvs
            liftIO $ SAW.scTuple sc (toListFC getConst terms)
        (ArrayShape _ _ shp, vec) -> do
            terms <- goVector shp vec
            tyTerm <- shapeToTerm sc shp
            liftIO $ SAW.scVector sc tyTerm terms
        _ -> fail $
            "type error: " ++ name ++ " got argument of unsupported type " ++ show (shapeType shp)

    goField :: forall tp.
        FieldShape tp ->
        RegValue sym tp ->
        m SAW.Term
    goField (OptField shp) rv = do
        rv' <- liftIO $ readMaybeType sym "field" (shapeType shp) rv
        go shp rv'
    goField (ReqField shp) rv = go shp rv

    goVector :: forall tp.
        TypeShape tp ->
        MirVector sym tp ->
        m [SAW.Term]
    goVector shp (MirVector_Vector v) = mapM (go shp) $ toList v
    goVector shp (MirVector_PartialVector pv) = do
        forM (toList pv) $ \rv -> do
            rv' <- liftIO $ readMaybeType sym "field" (shapeType shp) rv
            go shp rv'
    goVector _shp (MirVector_Array _) = fail $
        "regToTerm: MirVector_Array not supported"
