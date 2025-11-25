{- |
Module      : SAWCentral.Yosys.TransitionSystem
Description : Exporting stateful HDL circuits to model checkers
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language TupleSections #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language GADTs #-}

module SAWCentral.Yosys.TransitionSystem where

import Control.Lens.TH (makeLenses)

import Control.Lens ((^.), view, at)
import Control.Monad (forM, foldM)
import Control.Exception (throw)

import Data.Functor.Const (Const(..))
import qualified Data.Set as Set
import Data.Set (Set)
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

import qualified SAWCore.Name as SC
import qualified SAWCore.SharedTerm as SC
import qualified CryptolSAWCore.TypedTerm as SC

import qualified SAWCore.Simulator.Value as Sim
import qualified SAWCoreWhat4.What4 as SimW4

import qualified What4.Interface as W4
import qualified What4.Symbol as W4
import qualified What4.SWord as W4
import qualified What4.Expr.Builder as W4.B
import qualified What4.TransitionSystem as W4

import qualified Language.Sally as Sally
import qualified Language.Sally.TransitionSystem as Sally

import SAWCentral.Yosys.Utils
import SAWCentral.Yosys.State

-- | A named field with the given What4 base type.
data SequentialField tp = SequentialField
  { _sequentialFieldName :: Text
  , _sequentialFieldTypeRepr :: W4.BaseTypeRepr tp
  }
makeLenses ''SequentialField

-- | A typed record associating field names with What4 base types.
data SequentialFields ctx = SequentialFields
  { _sequentialFields :: Ctx.Assignment SequentialField ctx
  , _sequentialFieldsIndex :: Map Text (Some (Ctx.Index ctx))
  }
makeLenses ''SequentialFields

-- | Convert a mapping from names to widths into a typed mapping from
-- those names to What4 bitvectors of those widths.
sequentialReprs ::
  Map Text Natural ->
  IO (Some SequentialFields)
sequentialReprs fs =
  do let assocs = Map.assocs fs
     Some fields <- go assocs
     idxs <- Ctx.traverseAndCollect (\idx _ -> pure [Some idx]) fields
     let index = zipWith (\(nm, _) idx -> (nm, idx)) assocs $ reverse idxs
     pure $ Some SequentialFields
       { _sequentialFields = fields
       , _sequentialFieldsIndex = Map.fromList index
       }
  where
    go :: [(Text, Natural)] -> IO (Some (Ctx.Assignment SequentialField))
    go [] = pure $ Some Ctx.empty
    go ((nm, n):ns) =
      case someNat n of
        Just (Some nr)
          | Just LeqProof <- testLeq (knownNat @1) nr ->
              do let field = SequentialField
                       { _sequentialFieldName = nm
                       , _sequentialFieldTypeRepr = W4.BaseBVRepr nr
                       }
                 Some rest <- go ns
                 pure $ Some $ Ctx.extend rest field
        _ -> throw $ YosysErrorInvalidStateFieldWidth nm

-- | Given information about field names and types alongside an
-- appropriately-typed What4 struct value, explode that struct into a
-- mapping from field names to fresh typed SAWCore constants and
-- SAWCore What4 simulator values. (This is used to unpack a What4
-- struct into a representation that is more convenient to manipulate
-- in SAWCore.)
ecBindingsOfFields ::
  W4.B.ExprBuilder n st fs ->
  SC.SharedContext ->
  Text {- ^ Prefix to prepend to all field names -} ->
  Map Text SC.Term {- ^ Mapping from field names to SAWCore types -} ->
  SequentialFields ctx {- ^ Mapping from field names to What4 base types -} ->
  W4.SymStruct (W4.B.ExprBuilder n st fs) ctx {- ^ What4 record to deconstruct -} ->
  IO (Map Text (SC.VarName, SC.Term, SimW4.SValue (W4.B.ExprBuilder n st fs)))
ecBindingsOfFields sym sc pfx fs s inp =
  fmap Map.fromList . forM (Map.assocs fs) $ \(baseName, ty) ->
  do let nm = pfx <> baseName
     vn <- SC.scFreshVarName sc nm
     val <-
       case s ^. sequentialFieldsIndex . at nm of
         Just (Some idx)
           | sf <- s ^. sequentialFields . ixF' idx
           , W4.BaseBVRepr _nr <- sf ^. sequentialFieldTypeRepr ->
               do inpExpr <- W4.structField sym inp idx
                  pure . Sim.VWord $ W4.DBV inpExpr
         _ -> throw $ YosysErrorTransitionSystemMissingField nm
     pure (baseName, (vn, ty, val))

-- | Given a sequential circuit and a query, construct and write to
-- disk a Sally transition system encoding that query.
queryModelChecker ::
  W4.B.ExprBuilder n st fs ->
  SC.SharedContext ->
  YosysSequential ->
  FilePath {- ^ Path to write the resulting Sally input -} ->
  SC.TypedTerm {- ^ A boolean function of three parameters: an 8-bit cycle counter, a record of "fixed" inputs, and a record of circuit outputs -} ->
  Set Text {- ^ Names of circuit inputs that are fixed -}->
  IO ()
queryModelChecker sym sc sequential path query fixedInputs =
  do -- there are 5 classes of field:
     --  - fixed inputs (inputs from the circuit named in the fixed set, assumed to be constant across cycles
     --  - variable inputs (all other inputs from the circuit)
     --  - outputs (all outputs from the circuit)
     --  - state (all circuit flip-flop states)
     --  - internal (right now, just a cycle counter)
     let (fixedInputWidths, variableInputWidths) = Map.partitionWithKey (\nm _ -> Set.member nm fixedInputs) $ sequential ^. yosysSequentialInputWidths
     let (fixedInputFields, variableInputFields) = Map.partitionWithKey (\nm _ -> Set.member nm fixedInputs) $ sequential ^. yosysSequentialInputFields
     let internalWidths = Map.singleton "cycle" 8
     internalFields <- forM internalWidths $ \w -> SC.scBitvector sc w

     -- the "inputs" for our transition system are exclusively the circuit's variable inputs
     Some inputFields <- sequentialReprs variableInputWidths
     let inputReprs = TraversableFC.fmapFC (view sequentialFieldTypeRepr) $ inputFields ^. sequentialFields
     let inputNames = TraversableFC.fmapFC (Const . W4.safeSymbol . Text.unpack . view sequentialFieldName) $ inputFields ^. sequentialFields

     -- while the transition system "states" are everything else: flip-flop states, fixed inputs, all outputs, and the cycle counter
     let combinedWidths = Map.unions
           [ sequential ^. yosysSequentialStateWidths
           , Map.mapKeys ("stateinput_"<>) fixedInputWidths
           , Map.mapKeys ("stateoutput_"<>) $ sequential ^. yosysSequentialOutputWidths
           , Map.mapKeys ("internal_"<>) internalWidths
           ]
     Some stateFields <- sequentialReprs combinedWidths
     let stateReprs = TraversableFC.fmapFC (view sequentialFieldTypeRepr) $ stateFields ^. sequentialFields
     let stateNames = TraversableFC.fmapFC (Const . W4.safeSymbol . Text.unpack . view sequentialFieldName) $ stateFields ^. sequentialFields
     let lookupBinding nm bindings =
           case Map.lookup nm bindings of
             Just (vn, tp, _) -> SC.scVariable sc vn tp
             Nothing -> throw $ YosysErrorTransitionSystemMissingField nm
     let ts = W4.TransitionSystem
           { W4.inputReprs = inputReprs
           , W4.inputNames = inputNames
           , W4.stateReprs = stateReprs
           , W4.stateNames = stateNames
           , W4.initialStatePredicate = \cur ->
               do -- initially , we assert that cycle = 0
                  curInternalBindings <- ecBindingsOfFields sym sc "internal_" internalFields stateFields cur
                  cycleVal <- lookupBinding "cycle" curInternalBindings
                  zero <- SC.scBvConst sc 8 0
                  wnat <- SC.scNat sc 8
                  cyclePred <- SC.scBvEq sc wnat cycleVal zero
                  ref <- IORef.newIORef Map.empty
                  let args = Map.unions $ fmap (Map.fromList . fmap (\(vn, _ty, x) -> (SC.vnIndex vn, x)) . Map.elems)
                        [ curInternalBindings
                        ]
                  sval <- SimW4.w4SolveBasic sym sc Map.empty args ref Set.empty cyclePred
                  case sval of
                    Sim.VBool b -> pure b
                    _ -> throw YosysErrorTransitionSystemBadType
           , W4.stateTransitions = \input cur next ->
               do -- there is exactly one state transition, defined by the SAWCore function f representing the circuit
                  -- here, we assert that:
                  --  - the new value of each state field is equal to the same field in f(<previous state + all inputs>)
                  --  - the new value of each output is equal to the same output in f(<previous state + all inputs>)
                  --  - the new value of each fixed input is equal to the old value of that fixed input
                  --  - the new cycle counter is equal to the old cycle counter plus one
                  inputBindings <- ecBindingsOfFields sym sc "" (fst <$> variableInputFields) inputFields input
                  curBindings <- ecBindingsOfFields sym sc "" (fst <$> (sequential ^. yosysSequentialStateFields)) stateFields cur
                  curFixedInputBindings <- ecBindingsOfFields sym sc "stateinput_" (fst <$> fixedInputFields) stateFields cur
                  curInternalBindings <- ecBindingsOfFields sym sc "internal_" internalFields stateFields cur
                  nextBindings <- ecBindingsOfFields sym sc "" (fst <$> (sequential ^. yosysSequentialStateFields)) stateFields next
                  nextFixedInputBindings <- ecBindingsOfFields sym sc "stateinput_" (fst <$> fixedInputFields) stateFields next
                  nextOutputBindings <- ecBindingsOfFields sym sc "stateoutput_" (fst <$> (sequential ^. yosysSequentialOutputFields)) stateFields next
                  nextInternalBindings <- ecBindingsOfFields sym sc "internal_" internalFields stateFields next
                  inps <-
                    fmap Map.fromList . forM (Map.assocs $ sequential ^. yosysSequentialInputWidths) $ \(nm, _) ->
                    let bindings = if Set.member nm fixedInputs then curFixedInputBindings else inputBindings
                    in (nm,) <$> lookupBinding nm bindings
                  states <- forM curBindings $ \(vn, tp, _) -> SC.scVariable sc vn tp
                  inpst <- cryptolRecord sc states
                  domainRec <- cryptolRecord sc $ Map.insert "__state__" inpst inps
                  codomainRec <- SC.scApply sc (sequential ^. yosysSequentialTerm . SC.ttTermLens) domainRec
                  codomainFields <- insertStateField sc (sequential ^. yosysSequentialStateFields) $ sequential ^. yosysSequentialOutputFields
                  outst <- cryptolRecordSelect sc codomainFields codomainRec "__state__"
                  stPreds <-
                    forM (Map.assocs $ sequential ^. yosysSequentialStateWidths) $ \(nm, w) ->
                    do val <- cryptolRecordSelect sc (sequential ^. yosysSequentialStateFields) outst nm
                       wnat <- SC.scNat sc w
                       new <- lookupBinding nm nextBindings
                       SC.scBvEq sc wnat new val
                  outputPreds <-
                    forM (Map.assocs $ sequential ^. yosysSequentialOutputWidths) $ \(nm, w) ->
                    do val <- cryptolRecordSelect sc codomainFields codomainRec nm
                       wnat <- SC.scNat sc w
                       new <- lookupBinding nm nextOutputBindings
                       SC.scBvEq sc wnat new val
                  fixedInputPreds <-
                    forM (Map.assocs fixedInputWidths) $ \(nm, w) ->
                    do wnat <- SC.scNat sc w
                       val <- lookupBinding nm curFixedInputBindings
                       new <- lookupBinding nm nextFixedInputBindings
                       SC.scBvEq sc wnat new val
                  cycleIncrement <-
                    do wnat <- SC.scNat sc 8
                       val <- lookupBinding "cycle" curInternalBindings
                       one <- SC.scBvConst sc 8 1
                       incremented <- SC.scBvAdd sc wnat val one
                       new <- lookupBinding "cycle" nextInternalBindings
                       SC.scBvEq sc wnat new incremented
                  identity <- SC.scBool sc True
                  conj <- foldM (SC.scAnd sc) identity $ stPreds <> outputPreds <> fixedInputPreds <> [cycleIncrement]
                  ref <- IORef.newIORef Map.empty
                  let args =
                        Map.unions $ fmap (Map.fromList . fmap (\(vn, _tp, x) -> (SC.vnIndex vn, x)) . Map.elems)
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
                  w4Conj <-
                    case sval of
                      Sim.VBool b -> pure b
                      _ -> throw YosysErrorTransitionSystemBadType
                  pure
                    [ (W4.systemSymbol "default!", w4Conj)
                    ]
           , W4.queries = \cur ->
               do -- here we generate a single query, corresponding to the provided query term q
                  -- this is q applied to:
                  --  - the cycle counter (an 8-bit bitvector)
                  --  - a record of the fixed inputs (as usual really a SAWCore tuple, ordered per the Cryptol record type)
                  --  - a record of the outputs
                  curFixedInputBindings <- ecBindingsOfFields sym sc "stateinput_" (fst <$> fixedInputFields) stateFields cur
                  curOutputBindings <- ecBindingsOfFields sym sc "stateoutput_" (fst <$> (sequential ^. yosysSequentialOutputFields)) stateFields cur
                  curInternalBindings <- ecBindingsOfFields sym sc "internal_" internalFields stateFields cur
                  fixedInps <-
                    fmap Map.fromList . forM (Map.assocs fixedInputWidths) $ \(nm, _) ->
                    (nm,) <$> lookupBinding nm curFixedInputBindings
                  outputs <-
                    fmap Map.fromList . forM (Map.assocs $ sequential ^. yosysSequentialOutputWidths) $ \(nm, _) ->
                    (nm,) <$> lookupBinding nm curOutputBindings
                  cycleVal <- lookupBinding "cycle" curInternalBindings
                  fixedInputRec <- cryptolRecord sc fixedInps
                  outputRec <- cryptolRecord sc outputs
                  result <- SC.scApplyAll sc (query ^. SC.ttTermLens) [cycleVal, fixedInputRec, outputRec]
                  ref <- IORef.newIORef Map.empty
                  let args =
                        Map.unions $ fmap (Map.fromList . fmap (\(vn, _ty, x) -> (SC.vnIndex vn, x)) . Map.elems)
                        [ curOutputBindings
                        , curFixedInputBindings
                        , curInternalBindings
                        ]
                  sval <- SimW4.w4SolveBasic sym sc Map.empty args ref Set.empty result
                  w4Pred <-
                    case sval of
                      Sim.VBool b -> pure b
                      _ -> throw . YosysError $ "Invalid type when converting predicate to What4: " <> Text.pack (show sval)
                  pure [w4Pred]
           }
     sts <- Sally.exportTransitionSystem sym Sally.mySallyNames ts
     sexp <- Sally.sexpOfSally sym sts
     BS.writeFile path . encodeUtf8 . Text.pack . show $ Sally.sexpToDoc sexp
     pure ()
