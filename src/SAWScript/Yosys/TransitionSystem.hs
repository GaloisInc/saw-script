{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language TupleSections #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language GADTs #-}

module SAWScript.Yosys.TransitionSystem where

import Control.Lens.TH (makeLenses)

import Control.Lens ((^.), view, at)
import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import Data.Functor.Const (Const(..))
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import qualified Data.Text as Text
import qualified Data.ByteString as BS
import qualified Data.IORef as IORef

import Numeric.Natural (Natural)

import Data.Parameterized.Some
import Data.Parameterized.NatRepr
import Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TraversableFC

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedTerm as SC

import qualified Verifier.SAW.Simulator.Value as Sim
import qualified Verifier.SAW.Simulator.What4 as SimW4
import qualified Verifier.SAW.Simulator.What4.ReturnTrip as SimW4

import qualified What4.Interface as W4
import qualified What4.Symbol as W4
import qualified What4.SWord as W4
import qualified What4.Expr.Builder as W4.B
import qualified What4.TransitionSystem as W4

import qualified Language.Sally as Sally
import qualified Language.Sally.TransitionSystem as Sally

import SAWScript.Yosys.Utils
import SAWScript.Yosys.State

data SequentialField tp = SequentialField
  { _sequentialFieldName :: Text
  , _sequentialFieldTypeRepr :: W4.BaseTypeRepr tp
  }
makeLenses ''SequentialField

data SequentialFields ctx = SequentialFields
  { _sequentialFields :: Ctx.Assignment SequentialField ctx
  , _sequentialFieldsIndex :: Map Text (Some (Ctx.Index ctx))
  }
makeLenses ''SequentialFields

sequentialReprs ::
  forall m.
  MonadIO m =>
  Map Text Natural ->
  m (Some SequentialFields)
sequentialReprs fs = do
  let assocs = Map.assocs fs
  Some fields <- go assocs
  idxs <- Ctx.traverseAndCollect (\idx _ -> pure [Some idx]) fields
  let index = zipWith (\(nm, _) idx -> (nm, idx)) assocs $ reverse idxs
  pure $ Some SequentialFields
    { _sequentialFields = fields
    , _sequentialFieldsIndex = Map.fromList index
    }
  where
    go :: [(Text, Natural)] -> m (Some (Ctx.Assignment SequentialField))
    go [] = pure $ Some Ctx.empty
    go ((nm, n):ns) = case someNat n of
      Just (Some nr) | Just LeqProof <- testLeq (knownNat @1) nr -> do
        let field = SequentialField
              { _sequentialFieldName = nm
              , _sequentialFieldTypeRepr = W4.BaseBVRepr nr
              }
        Some rest <- go ns
        pure $ Some $ Ctx.extend rest field
      _ -> throw . YosysError $ "Invalid width for state field: " <> nm

ecBindingsOfFields ::
  MonadIO m =>
  W4.B.ExprBuilder n st fs ->
  SC.SharedContext ->
  Text ->
  Map Text SC.Term ->
  SequentialFields ctx ->
  W4.SymStruct (W4.B.ExprBuilder n st fs) ctx ->
  m (Map Text (SC.ExtCns SC.Term, SimW4.SValue (W4.B.ExprBuilder n st fs)))
ecBindingsOfFields sym sc pfx fs s inp = fmap Map.fromList . forM (Map.assocs fs) $ \(baseName, ty) -> do
  let nm = pfx <> baseName
  ec <- liftIO $ SC.scFreshEC sc nm ty
  val <- case s ^. sequentialFieldsIndex . at nm of
    Just (Some idx)
      | sf <- s ^. sequentialFields . ixF' idx
      , W4.BaseBVRepr _nr <- sf ^. sequentialFieldTypeRepr
        -> do
          inpExpr <- liftIO $ W4.structField sym inp idx
          pure . Sim.VWord $ W4.DBV inpExpr
    _ -> throw . YosysError $ "Invalid field binding: " <> nm
  pure (baseName, (ec, val))

queryModelChecker ::
  MonadIO m =>
  W4.B.ExprBuilder n st fs ->
  SimW4.SAWCoreState n ->
  SC.SharedContext ->
  YosysSequential ->
  FilePath ->
  SC.TypedTerm ->
  Set.Set Text ->
  m ()
queryModelChecker sym _scs sc sequential path query fixedInputs = do
  let (fixedInputWidths, variableInputWidths) = Map.partitionWithKey (\nm _ -> Set.member nm fixedInputs) $ sequential ^. yosysSequentialInputWidths
  let (fixedInputFields, variableInputFields) = Map.partitionWithKey (\nm _ -> Set.member nm fixedInputs) $ sequential ^. yosysSequentialInputFields
  let internalWidths = Map.singleton "cycle" 8
  internalFields <- forM internalWidths $ \w -> liftIO $ SC.scBitvector sc w

  Some inputFields <- sequentialReprs variableInputWidths
  let inputReprs = TraversableFC.fmapFC (view sequentialFieldTypeRepr) $ inputFields ^. sequentialFields
  let inputNames = TraversableFC.fmapFC (Const . W4.safeSymbol . Text.unpack . view sequentialFieldName) $ inputFields ^. sequentialFields

  let combinedWidths = Map.unions
        [ sequential ^. yosysSequentialStateWidths
        , Map.mapKeys ("stateinput_"<>) fixedInputWidths
        , Map.mapKeys ("stateoutput_"<>) $ sequential ^. yosysSequentialOutputWidths
        , Map.mapKeys ("internal_"<>) internalWidths
        ]
  Some stateFields <- sequentialReprs combinedWidths
  let stateReprs = TraversableFC.fmapFC (view sequentialFieldTypeRepr) $ stateFields ^. sequentialFields
  let stateNames = TraversableFC.fmapFC (Const . W4.safeSymbol . Text.unpack . view sequentialFieldName) $ stateFields ^. sequentialFields
  let ts = W4.TransitionSystem
        { W4.inputReprs = inputReprs
        , W4.inputNames = inputNames
        , W4.stateReprs = stateReprs
        , W4.stateNames = stateNames
        , W4.initialStatePredicate = \cur -> do
            curInternalBindings <- ecBindingsOfFields sym sc "internal_" internalFields stateFields cur
            cycleVal <- case Map.lookup "cycle" curInternalBindings of
              Just (ec, _) -> SC.scExtCns sc ec
              Nothing -> throw $ YosysError "Invalid current cycle field"
            zero <- SC.scBvConst sc 8 0
            wnat <- SC.scNat sc 8
            cyclePred <- SC.scBvEq sc wnat cycleVal zero
            ref <- IORef.newIORef Map.empty
            let args = Map.unions $ fmap (Map.fromList . fmap (\(ec, x) -> (SC.ecVarIndex ec, x)) . Map.elems)
                  [ curInternalBindings
                  ]
            sval <- SimW4.w4SolveBasic sym sc Map.empty args ref Set.empty cyclePred
            case sval of
              Sim.VBool b -> pure b
              _ -> throw . YosysError $ "Invalid type when converting predicate to What4: " <> Text.pack (show sval)
        , W4.stateTransitions = \input cur next -> do
            inputBindings <- ecBindingsOfFields sym sc "" (fst <$> variableInputFields) inputFields input
            curBindings <- ecBindingsOfFields sym sc "" (fst <$> (sequential ^. yosysSequentialStateFields)) stateFields cur
            curFixedInputBindings <- ecBindingsOfFields sym sc "stateinput_" (fst <$> fixedInputFields) stateFields cur
            curInternalBindings <- ecBindingsOfFields sym sc "internal_" internalFields stateFields cur
            nextBindings <- ecBindingsOfFields sym sc "" (fst <$> (sequential ^. yosysSequentialStateFields)) stateFields next
            nextFixedInputBindings <- ecBindingsOfFields sym sc "stateinput_" (fst <$> fixedInputFields) stateFields next
            nextOutputBindings <- ecBindingsOfFields sym sc "stateoutput_" (fst <$> (sequential ^. yosysSequentialOutputFields)) stateFields next
            nextInternalBindings <- ecBindingsOfFields sym sc "internal_" internalFields stateFields next
            inps <- fmap Map.fromList . forM (Map.assocs $ sequential ^. yosysSequentialInputWidths) $ \(nm, _) ->
              let bindings = if Set.member nm fixedInputs then curFixedInputBindings else inputBindings
              in case Map.lookup nm bindings of
                Just (ec, _) -> (nm,) <$> SC.scExtCns sc ec
                Nothing -> throw . YosysError $ "Invalid input field: " <> nm
            states <- forM curBindings $ \(ec, _) -> SC.scExtCns sc ec
            inpst <- cryptolRecord sc states
            domainRec <- cryptolRecord sc $ Map.insert "__state__" inpst inps
            codomainRec <- liftIO $ SC.scApply sc (sequential ^. yosysSequentialTerm . SC.ttTermLens) domainRec
            codomainFields <- insertStateField sc (sequential ^. yosysSequentialStateFields) $ sequential ^. yosysSequentialOutputFields
            outst <- cryptolRecordSelect sc codomainFields codomainRec "__state__"
            stPreds <- forM (Map.assocs $ sequential ^. yosysSequentialStateWidths) $ \(nm, w) -> do
              val <- cryptolRecordSelect sc (sequential ^. yosysSequentialStateFields) outst nm
              wnat <- SC.scNat sc w
              new <- case Map.lookup nm nextBindings of
                Just (ec, _) -> SC.scExtCns sc ec
                Nothing -> throw . YosysError $ "Invalid state update field: " <> nm
              liftIO $ SC.scBvEq sc wnat new val
            outputPreds <- forM (Map.assocs $ sequential ^. yosysSequentialOutputWidths) $ \(nm, w) -> do
              val <- cryptolRecordSelect sc codomainFields codomainRec nm
              wnat <- SC.scNat sc w
              new <- case Map.lookup nm nextOutputBindings of
                Just (ec, _) -> SC.scExtCns sc ec
                Nothing -> throw . YosysError $ "Invalid output update field: " <> nm
              liftIO $ SC.scBvEq sc wnat new val
            fixedInputPreds <- forM (Map.assocs fixedInputWidths) $ \(nm, w) -> do
              wnat <- SC.scNat sc w
              val <- case Map.lookup nm curFixedInputBindings of
                Just (ec, _) -> SC.scExtCns sc ec
                Nothing -> throw . YosysError $ "Invalid current fixed input field: " <> nm
              new <- case Map.lookup nm nextFixedInputBindings of
                Just (ec, _) -> SC.scExtCns sc ec
                Nothing -> throw . YosysError $ "Invalid next fixed input field: " <> nm
              liftIO $ SC.scBvEq sc wnat new val
            cycleIncrement <- do
              wnat <- SC.scNat sc 8
              val <- case Map.lookup "cycle" curInternalBindings of
                Just (ec, _) -> SC.scExtCns sc ec
                Nothing -> throw $ YosysError "Invalid current cycle field"
              one <- SC.scBvConst sc 8 1
              incremented <- SC.scBvAdd sc wnat val one
              new <- case Map.lookup "cycle" nextInternalBindings of
                Just (ec, _) -> SC.scExtCns sc ec
                Nothing -> throw $ YosysError "Invalid next cycle field"
              liftIO $ SC.scBvEq sc wnat new incremented
            identity <- SC.scBool sc True
            conj <- foldM (SC.scAnd sc) identity $ stPreds <> outputPreds <> fixedInputPreds <> [cycleIncrement]
            ref <- IORef.newIORef Map.empty
            let args = Map.unions $ fmap (Map.fromList . fmap (\(ec, x) -> (SC.ecVarIndex ec, x)) . Map.elems)
                  [ inputBindings
                  , curBindings
                  , curFixedInputBindings
                  , curInternalBindings
                  , nextBindings
                  , nextOutputBindings
                  , nextFixedInputBindings
                  , nextInternalBindings
                  ]
            sval <- SimW4.w4SolveBasic sym sc Map.empty args ref Set.empty conj
            w4Conj <- case sval of
              Sim.VBool b -> pure b
              _ -> throw . YosysError $ "Invalid type when converting predicate to What4: " <> Text.pack (show sval)
            pure
              [ (W4.systemSymbol "default!", w4Conj)
              ]
        , W4.queries = \cur -> do
            curFixedInputBindings <- ecBindingsOfFields sym sc "stateinput_" (fst <$> fixedInputFields) stateFields cur
            curOutputBindings <- ecBindingsOfFields sym sc "stateoutput_" (fst <$> (sequential ^. yosysSequentialOutputFields)) stateFields cur
            curInternalBindings <- ecBindingsOfFields sym sc "internal_" internalFields stateFields cur
            fixedInps <- fmap Map.fromList . forM (Map.assocs fixedInputWidths) $ \(nm, _) ->
              case Map.lookup nm curFixedInputBindings of
                Nothing -> throw . YosysError $ "Invalid fixed input field: " <> nm
                Just (ec, _) -> (nm,) <$> SC.scExtCns sc ec
            outputs <- fmap Map.fromList . forM (Map.assocs $ sequential ^. yosysSequentialOutputWidths) $ \(nm, _) ->
              case Map.lookup nm curOutputBindings of
                Nothing -> throw . YosysError $ "Invalid output field: " <> nm
                Just (ec, _) -> (nm,) <$> SC.scExtCns sc ec
            cycleVal <- case Map.lookup "cycle" curInternalBindings of
              Just (ec, _) -> SC.scExtCns sc ec
              Nothing -> throw $ YosysError "Invalid current cycle field"
            fixedInputRec <- cryptolRecord sc fixedInps
            outputRec <- cryptolRecord sc outputs
            result <- liftIO $ SC.scApplyAll sc (query ^. SC.ttTermLens) [cycleVal, fixedInputRec, outputRec]
            ref <- IORef.newIORef Map.empty
            let args = Map.unions $ fmap (Map.fromList . fmap (\(ec, x) -> (SC.ecVarIndex ec, x)) . Map.elems)
                  [ curOutputBindings
                  , curFixedInputBindings
                  , curInternalBindings
                  ]
            sval <- SimW4.w4SolveBasic sym sc Map.empty args ref Set.empty result
            w4Pred <- case sval of
              Sim.VBool b -> pure b
              _ -> throw . YosysError $ "Invalid type when converting predicate to What4: " <> Text.pack (show sval)
            pure [w4Pred]
        }
  sts <- liftIO $ Sally.exportTransitionSystem sym Sally.mySallyNames ts
  sexp <- liftIO $ Sally.sexpOfSally sym sts
  liftIO . BS.writeFile path . encodeUtf8 . Text.pack . show $ Sally.sexpToDoc sexp
  pure ()
