{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language ViewPatterns #-}

module Mir.Cryptol
where

import Control.Lens (use, (^.), (^?), _Wrapped, ix)
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import Data.Foldable
import Data.Functor.Const
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text

import Data.Parameterized.Context (pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr
import Data.Parameterized.TraversableFC

import qualified What4.Expr.Builder as W4

import Lang.Crucible.Backend
import Lang.Crucible.CFG.Core
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator

import Crux
import Crux.Types

import Mir.DefId
import Mir.Generator (CollectionState, collection)
import Mir.Intrinsics
import qualified Mir.Mir as M
import Mir.Overrides (getString)

import qualified Verifier.SAW.Cryptol.Prelude as SAW
import qualified Verifier.SAW.CryptolEnv as SAW
import qualified Verifier.SAW.Recognizer as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Simulator.What4.ReturnTrip as SAW
import qualified Verifier.SAW.TypedTerm as SAW

import Mir.Compositional.Convert

import Debug.Trace


cryptolOverrides ::
    forall sym p t st fs args ret blocks rtp a r .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    Maybe (SomeOnlineSolver sym) ->
    CollectionState ->
    Text ->
    CFG MIR blocks args ret ->
    Maybe (OverrideSim (p sym) sym MIR rtp a r ())
cryptolOverrides _symOnline cs name cfg

  | (normDefId "crucible::cryptol::load" <> "::_inst") `Text.isPrefixOf` name
  , Empty
      :> MirSliceRepr (BVRepr (testEquality (knownNat @8) -> Just Refl))
      :> MirSliceRepr (BVRepr (testEquality (knownNat @8) -> Just Refl))
      <- cfgArgTypes cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "cryptol_load" (cfgReturnType cfg) $ do
        let tyArg = cs ^? collection . M.intrinsics . ix (textId name) .
                M.intrInst . M.inSubsts . _Wrapped . ix 0
        sig <- case tyArg of
            Just (M.TyFnPtr sig) -> return sig
            _ -> error $ "expected TyFnPtr argument, but got " ++ show tyArg

        RegMap (Empty :> RegEntry _tpr modulePathStr :> RegEntry _tpr' nameStr) <- getOverrideArgs
        cryptolLoad (cs ^. collection) sig (cfgReturnType cfg) modulePathStr nameStr

  | otherwise = Nothing


cryptolLoad ::
    forall sym p t st fs rtp a r tp .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    M.Collection ->
    M.FnSig ->
    TypeRepr tp ->
    RegValue sym (MirSlice (BVType 8)) ->
    RegValue sym (MirSlice (BVType 8)) ->
    OverrideSim (p sym) sym MIR rtp a r (RegValue sym tp)
cryptolLoad col sig (FunctionHandleRepr argsCtx retTpr) modulePathStr nameStr = do
    modulePath <- getString modulePathStr >>= \x -> case x of
        Just s -> return $ Text.unpack s
        Nothing -> fail "cryptol::load module path must not be symbolic"
    name <- getString nameStr >>= \x -> case x of
        Just s -> return $ Text.unpack s
        Nothing -> fail "cryptol::load function name must not be symbolic"

    let argShps = map (tyToShape col) (sig ^. M.fsarg_tys)
    let retShp = tyToShapeEq col (sig ^. M.fsreturn_ty) retTpr

    -- TODO share a single SharedContext across all calls
    sc <- liftIO $ SAW.mkSharedContext
    liftIO $ SAW.scLoadPreludeModule sc
    liftIO $ SAW.scLoadCryptolModule sc
    let ?fileReader = BS.readFile
    ce <- liftIO $ SAW.initCryptolEnv sc
    (m, ce') <- liftIO $ SAW.loadCryptolModule sc ce modulePath
    tt <- liftIO $ SAW.lookupCryptolModule m name

    scs <- liftIO $ SAW.newSAWCoreState sc

    halloc <- simHandleAllocator <$> use stateContext
    let fnName = "cryptol_" ++ modulePath ++ "_" ++ name
    fh <- liftIO $ mkHandle' halloc (fromString fnName) argsCtx retTpr
    bindFnHandle fh $ UseOverride $ mkOverride' (handleName fh) (handleReturnType fh) $
        cryptolRun sc scs fnName argShps retShp (SAW.ttTerm tt)

    return $ HandleFnVal fh

cryptolLoad _ _ tpr _ _ = fail $ "cryptol::load: bad function type " ++ show tpr


cryptolRun ::
    forall sym p t st fs rtp a r tp .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    SAW.SharedContext ->
    SAW.SAWCoreState t ->
    String ->
    [Some TypeShape] ->
    TypeShape tp ->
    SAW.Term ->
    OverrideSim (p sym) sym MIR rtp a r (RegValue sym tp)
cryptolRun sc scs name argShps retShp funcTerm = do
    sym <- getSymInterface

    visitCache <- liftIO $ (W4.newIdxCache :: IO (W4.IdxCache t (Const ())))
    w4VarMapRef <- liftIO $ newIORef (Map.empty :: Map SAW.VarIndex (Some (W4.Expr t)))

    RegMap argsCtx <- getOverrideArgs
    args <- forM (zip argShps (toListFC (\re -> Some re) argsCtx)) $
        \(Some argShp, Some (RegEntry tpr val)) -> do
            Refl <- case testEquality (shapeType argShp) tpr of
                Just x -> return x
                Nothing -> fail $
                    "type error: " ++ name ++ " expected argument of type " ++
                        show (shapeType argShp) ++ ", but got " ++ show tpr
            regToTerm sym sc scs name visitCache w4VarMapRef argShp val
    appTerm <- liftIO $ SAW.scApplyAll sc funcTerm args 

    w4VarMap <- liftIO $ readIORef w4VarMapRef
    rv <- liftIO $ termToReg sym sc w4VarMap appTerm retShp
    return rv

  where

exprToTerm :: forall sym p t st fs tp rtp a r.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    sym ->
    SAW.SharedContext ->
    SAW.SAWCoreState t ->
    W4.IdxCache t (Const ()) ->
    IORef (Map SAW.VarIndex (Some (W4.Expr t))) ->
    W4.Expr t tp ->
    OverrideSim (p sym) sym MIR rtp a r SAW.Term
exprToTerm sym sc scs visitCache w4VarMapRef val = do
    visitExprVars visitCache val $ \var -> do
        let expr = W4.BoundVarExpr var
        term <- liftIO $ SAW.toSC sym scs expr
        ec <- case SAW.asExtCns term of
            Just ec -> return ec
            Nothing -> error "eval on BoundVarExpr produced non-ExtCns?"
        liftIO $ modifyIORef w4VarMapRef $ Map.insert (SAW.ecVarIndex ec) (Some expr)
    liftIO $ SAW.toSC sym scs val

regToTerm :: forall sym p t st fs tp rtp a r.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    sym ->
    SAW.SharedContext ->
    SAW.SAWCoreState t ->
    String ->
    W4.IdxCache t (Const ()) ->
    IORef (Map SAW.VarIndex (Some (W4.Expr t))) ->
    TypeShape tp ->
    RegValue sym tp ->
    OverrideSim (p sym) sym MIR rtp a r SAW.Term
regToTerm sym sc scs name visitCache w4VarMapRef shp rv = go shp rv
  where
    go :: forall tp.
        TypeShape tp ->
        RegValue sym tp ->
        OverrideSim (p sym) sym MIR rtp a r SAW.Term
    go shp rv = case (shp, rv) of
        (UnitShape _, ()) -> liftIO $ SAW.scUnitValue sc
        (PrimShape _ _, expr) -> exprToTerm sym sc scs visitCache w4VarMapRef expr
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
        OverrideSim (p sym) sym MIR rtp a r SAW.Term
    goField (OptField shp) rv = do
        rv' <- liftIO $ readMaybeType sym "field" (shapeType shp) rv
        go shp rv'
    goField (ReqField shp) rv = go shp rv

    goVector :: forall tp.
        TypeShape tp ->
        MirVector sym tp ->
        OverrideSim (p sym) sym MIR rtp a r [SAW.Term]
    goVector shp (MirVector_Vector v) = mapM (go shp) $ toList v
    goVector shp (MirVector_PartialVector pv) = do
        forM (toList pv) $ \rv -> do
            rv' <- liftIO $ readMaybeType sym "field" (shapeType shp) rv
            go shp rv'
    goVector shp (MirVector_Array _) = fail $
        "regToTerm: MirVector_Array not supported"

shapeToTerm :: forall tp m.
    (MonadIO m, MonadFail m) =>
    SAW.SharedContext ->
    TypeShape tp ->
    m SAW.Term
shapeToTerm sc shp = go shp
  where
    go :: forall tp. TypeShape tp -> m SAW.Term
    go (UnitShape _) = liftIO $ SAW.scUnitType sc
    go (PrimShape _ BaseBoolRepr) = liftIO $ SAW.scBoolType sc
    go (PrimShape _ (BaseBVRepr w)) = liftIO $ SAW.scBitvector sc (natValue w) 
    go (TupleShape _ _ flds) = do
        tys <- toListFC getConst <$> traverseFC (\x -> Const <$> goField x) flds
        liftIO $ SAW.scTupleType sc tys
    go (ArrayShape (M.TyArray _ n) _ shp) = do
        ty <- go shp
        n <- liftIO $ SAW.scNat sc (fromIntegral n)
        liftIO $ SAW.scVecType sc n ty
    go shp = fail $ "shapeToTerm: unsupported type " ++ show (shapeType shp)

    goField :: forall tp. FieldShape tp -> m SAW.Term
    goField (OptField shp) = go shp
    goField (ReqField shp) = go shp

