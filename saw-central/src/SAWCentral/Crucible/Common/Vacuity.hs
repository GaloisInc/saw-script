{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module SAWCentral.Crucible.Common.Vacuity (
  GenericCrucibleContext(..),
  checkAssumptionsForContradictions
) where

import Prelude hiding (fail)
import           Control.Lens
import           Control.Monad (forM_)
import           Control.Monad.Extra (findM, whenM)
import           Data.Function
import           Data.List
import qualified What4.ProgramLoc as W4
import qualified What4.Interface as W4
import qualified Lang.Crucible.Backend as Crucible
import SAWCore.SharedTerm
import SAWCoreWhat4.ReturnTrip
import SAWCentral.Proof
import SAWCentral.TopLevel
import SAWCentral.Value
import SAWCentral.Options
import qualified SAWCentral.Crucible.Common as Common
import           SAWCentral.Crucible.Common.MethodSpec (CrucibleMethodSpecIR)
import qualified SAWCentral.Crucible.Common.MethodSpec as MS

type AssumptionReason = (MS.ConditionMetadata, String)

-- | Minimal backend-independent context
data GenericCrucibleContext sym = GenericCrucibleContext
  { gccSym :: sym  -- What4 symbolic backend
  }

-- | Top-level check and minimal core reporter
checkAssumptionsForContradictions ::
  GenericCrucibleContext Common.Sym ->
  CrucibleMethodSpecIR ext ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  TopLevel ()
checkAssumptionsForContradictions gcc methodSpec tactic assumptions =
  whenM
    (assumptionsContainContradiction gcc methodSpec tactic assumptions)
    (computeMinimalContradictingCore gcc methodSpec tactic assumptions)

-- | Check if the assumptions are contradictory
assumptionsContainContradiction ::
  GenericCrucibleContext Common.Sym ->
  CrucibleMethodSpecIR ext ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  TopLevel Bool
assumptionsContainContradiction gcc methodSpec tactic assumptions = do
  let sym = gccSym gcc
  st <- io $ Common.sawCoreState sym
  let sc = saw_ctx st
  let ploc = methodSpec ^. MS.csLoc

  (goal', pgl) <- io $
   do
    -- conjunction of all assumptions
    assume <- scAndList sc (toListOf (folded . Crucible.labeledPred) assumptions)
    -- implies falsehood
    goal   <- scImplies sc assume =<< toSC sym st (W4.falsePred sym)
    goal'  <- boolToProp sc [] goal
    return (goal',
            ProofGoal
              { goalNum     = 0
              , goalType    = "vacuousness check"
              , goalName    = "vacuousness_check"
              , goalLoc     = show (W4.plSourceLoc ploc) ++ " in " ++ show (W4.plFunction ploc)
              , goalDesc    = "vacuousness check"
              , goalSequent = propToSequent goal'
              , goalTags    = mempty
              })

  res <- runProofScript tactic goal' pgl Nothing
           "vacuousness check" False False
  case res of
    ValidProof _ _     -> return True
    InvalidProof _ _ _ -> return False
    UnfinishedProof _  ->
      -- TODO? is this the right behavior?
      do printOutLnTop Warn "Could not determine if preconditions are vacuous"
         return True

-- | Try to find the smallest contradictory subset
computeMinimalContradictingCore ::
  GenericCrucibleContext Common.Sym ->
  CrucibleMethodSpecIR ext ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  TopLevel ()
computeMinimalContradictingCore gcc methodSpec tactic assumes = do
  printOutLnTop Warn "Contradiction detected! Computing minimal core of contradictory assumptions:"
  let cores = sortBy (compare `on` length) (subsequences assumes)
  findM (assumptionsContainContradiction gcc methodSpec tactic) cores >>= \case
    Nothing ->
      printOutLnTop Warn "No minimal core: the assumptions did not contain a contradiction."
    Just core -> do
      forM_ core $ \assume ->
        case assume ^. Crucible.labeledPredMsg of
          (loc, reason) ->
            printOutLnTop Warn (show loc ++ ": " ++ reason)
      printOutLnTop Warn "Because of the contradiction, the following proofs may be vacuous."
