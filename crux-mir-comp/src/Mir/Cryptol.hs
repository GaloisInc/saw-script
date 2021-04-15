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

import Control.Lens (use)
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import Data.Functor.Const
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text

import Data.Parameterized.Context (pattern Empty, pattern (:>))
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
import Mir.Generator (CollectionState)
import Mir.Intrinsics
import Mir.Overrides (getString)

import qualified Verifier.SAW.Cryptol.Prelude as SAW
import qualified Verifier.SAW.CryptolEnv as SAW
import qualified Verifier.SAW.Prelude as SAW
import qualified Verifier.SAW.Recognizer as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Simulator.What4.ReturnTrip as SAW
import qualified Verifier.SAW.TypedTerm as SAW

import Mir.Compositional.Convert (visitExprVars)
import Mir.Compositional.Override (termToExpr)

import Debug.Trace


cryptolOverrides ::
    forall sym p t st fs args ret blocks rtp a r .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    Maybe (SomeOnlineSolver sym) ->
    CollectionState ->
    Text ->
    CFG MIR blocks args ret ->
    Maybe (OverrideSim (p sym) sym MIR rtp a r ())
cryptolOverrides _symOnline _cs name cfg

  | (normDefId "crucible::cryptol::load" <> "::_inst") `Text.isPrefixOf` name
  , Empty
      :> MirSliceRepr (BVRepr (testEquality (knownNat @8) -> Just Refl))
      :> MirSliceRepr (BVRepr (testEquality (knownNat @8) -> Just Refl))
      <- cfgArgTypes cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "cryptol_load" (cfgReturnType cfg) $ do
        RegMap (Empty :> RegEntry _tpr modulePathStr :> RegEntry _tpr' nameStr) <- getOverrideArgs
        cryptolLoad (cfgReturnType cfg) modulePathStr nameStr

  | otherwise = Nothing


cryptolLoad ::
    forall sym p t st fs rtp a r tp .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    TypeRepr tp ->
    RegValue sym (MirSlice (BVType 8)) ->
    RegValue sym (MirSlice (BVType 8)) ->
    OverrideSim (p sym) sym MIR rtp a r (RegValue sym tp)
cryptolLoad (FunctionHandleRepr argsCtx retTpr) modulePathStr nameStr = do
    modulePath <- getString modulePathStr >>= \x -> case x of
        Just s -> return $ Text.unpack s
        Nothing -> fail "cryptol::load module path must not be symbolic"
    name <- getString nameStr >>= \x -> case x of
        Just s -> return $ Text.unpack s
        Nothing -> fail "cryptol::load function name must not be symbolic"

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
        cryptolRun sc scs fnName retTpr (SAW.ttTerm tt)

    return $ HandleFnVal fh

cryptolLoad tpr _ _ = fail $ "cryptol::load: bad function type " ++ show tpr


cryptolRun ::
    forall sym p t st fs rtp a r tp .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    SAW.SharedContext ->
    SAW.SAWCoreState t ->
    String ->
    TypeRepr tp ->
    SAW.Term ->
    OverrideSim (p sym) sym MIR rtp a r (RegValue sym tp)
cryptolRun sc scs name retTpr funcTerm = do
    sym <- getSymInterface

    visitCache <- liftIO $ (W4.newIdxCache :: IO (W4.IdxCache t (Const ())))
    w4VarMapRef <- liftIO $ newIORef (Map.empty :: Map SAW.VarIndex (Some (W4.Expr t)))

    RegMap argsCtx <- getOverrideArgs
    args <- forM (toListFC (\re -> Some re) argsCtx) $ \(Some (RegEntry tpr val)) -> do
        case asBaseType tpr of
            AsBaseType btpr -> do
                visitExprVars visitCache val $ \var -> do
                    let expr = W4.BoundVarExpr var
                    term <- liftIO $ SAW.toSC sym scs expr
                    ec <- case SAW.asExtCns term of
                        Just ec -> return ec
                        Nothing -> error "eval on BoundVarExpr produced non-ExtCns?"
                    liftIO $ modifyIORef w4VarMapRef $ Map.insert (SAW.ecVarIndex ec) (Some expr)
                liftIO $ SAW.toSC sym scs val
            NotBaseType -> fail $
                "type error: " ++ name ++ " got argument of non-base type " ++ show tpr
    appTerm <- liftIO $ SAW.scApplyAll sc funcTerm args 

    w4VarMap <- liftIO $ readIORef w4VarMapRef
    Some expr <- liftIO $ termToExpr sym sc w4VarMap appTerm
    Refl <- case testEquality (baseToType $ W4.exprType expr) retTpr of
        Just x -> return x
        Nothing -> fail $
            "type error: expected " ++ name ++ " to return " ++ show retTpr ++
                ", but it returned " ++ show (W4.exprType expr) ++ " instead"
    return expr
