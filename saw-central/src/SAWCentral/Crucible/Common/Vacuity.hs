{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module SAWCentral.Crucible.Common.Vacuity (
  checkAssumptionsForContradictions
) where

import Prelude hiding (fail)

import           Control.Lens
import           Control.Monad.Extra (findM, whenM)
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State (gets)
import           Data.Function
import           Data.List (sortBy, subsequences)
import qualified Prettyprinter as PP
import           Prettyprinter ((<+>))

import qualified What4.ProgramLoc as W4
import qualified What4.Interface as W4
import qualified Lang.Crucible.Backend as Crucible
import SAWSupport.Console
import qualified SAWSupport.Pretty as PPS
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

-- | Checks whether the given list of assumptions contains a contradiction, and
-- if so, computes and displays a minimal set of contradictory assumptions.
checkAssumptionsForContradictions ::
  Show (MS.MethodId ext) =>
  Common.Sym ->
  CrucibleMethodSpecIR ext ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  TopLevel ()
checkAssumptionsForContradictions sym methodSpec tactic assumptions =
  whenM
    (assumptionsContainContradiction sym methodSpec tactic assumptions)
    (computeMinimalContradictingCore sym methodSpec tactic assumptions)

-- | Checks for contradictions within the given list of assumptions, by asking
-- the solver about whether their conjunction entails falsehood.
assumptionsContainContradiction ::
  Show (MS.MethodId ext) =>
  Common.Sym ->
  CrucibleMethodSpecIR ext ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  TopLevel Bool
assumptionsContainContradiction sym methodSpec tactic assumptions = 
  do
     st <- io $ Common.sawCoreState sym
     let sc  = saw_sc st
     let ploc = methodSpec^.MS.csLoc
     (goal',pgl) <- io $
      do
         -- conjunction of all assumptions
         assume <- scAndList sc (toListOf (folded . Crucible.labeledPred) assumptions)
         -- implies falsehood
         goal  <- scImplies sc assume =<< toSC sym st (W4.falsePred sym)
         goal' <- boolToProp sc [] goal
         return $ (goal',
                  ProofGoal
                  { goalNum  = 0
                  , goalType = "vacuousness check"
                  , goalName = show (methodSpec^.MS.csMethod)
                  , goalLoc  = show (W4.plSourceLoc ploc) ++ " in " ++ show (W4.plFunction ploc)
                  , goalDesc = "vacuousness check"
                  , goalSequent = propToSequent goal'
                  , goalTags = mempty
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

-- | Given a list of assumptions, computes and displays a smallest subset of
-- them that are contradictory among each themselves.  This is **not**
-- implemented efficiently.
computeMinimalContradictingCore ::
  Show (MS.MethodId ext) =>
  Common.Sym ->
  CrucibleMethodSpecIR ext ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  TopLevel ()
computeMinimalContradictingCore sym methodSpec tactic assumes =
  do
     liftIO $ warnN "Contradiction detected!"
     -- test subsets of assumptions of increasing sizes until we find a
     -- contradictory one
     let cores = sortBy (compare `on` length) (subsequences assumes)
     result <- findM (assumptionsContainContradiction sym methodSpec tactic) cores
     let result' = case result of
           Nothing ->
             "No minimal core: the assumptions did not contains a contradiction."
           Just core ->
             let once assume =
                   let (cmeta, reason) = assume ^. Crucible.labeledPredMsg
                       cmeta' = MS.prettyConditionMetadata cmeta
                       reason' = PP.pretty reason
                   in
                   PP.indent 3 $ PP.braces cmeta' <+> reason'
             in
             PP.vsep $
               "Computing minimal core of contradictory assumptions:" :
               map once core

     opts <- gets rwPPOpts
     liftIO $ warnN $ PPS.renderText opts result'
     liftIO $ warnN "Because of the contradiction, the following proofs may be vacuous."
