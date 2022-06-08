module SAWScript.Prover.SBV
  ( proveUnintSBV
  , proveUnintSBVIO
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.yices, SBV.mathSAT, SBV.boolector
  , prepNegatedSBV
  ) where

import System.Directory

import           Data.Maybe
import           Data.Set ( Set )
import           Control.Monad

import qualified Data.SBV.Dynamic as SBV
import qualified Data.SBV.Internals as SBV

import qualified Verifier.SAW.Simulator.SBV as SBVSim

import Verifier.SAW.SharedTerm

import SAWScript.Proof(Sequent, sequentSize, sequentToSATQuery, CEX)
import SAWScript.Prover.SolverStats
import SAWScript.Value

-- | Bit-blast a proposition and check its validity using SBV.
-- Constants with names in @unints@ are kept as uninterpreted
-- functions.
proveUnintSBV ::
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Set VarIndex  {- ^ Uninterpreted functions -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  Sequent       {- ^ A proposition to be proved -} ->
  TopLevel (Maybe CEX, SolverStats)
    -- ^ (example/counter-example, solver statistics)
proveUnintSBV conf unintSet timeout goal =
  do sc <- getSharedContext
     io $ proveUnintSBVIO sc conf unintSet timeout goal

proveUnintSBVIO ::
  SharedContext ->
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Set VarIndex  {- ^ Uninterpreted functions -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  Sequent       {- ^ A proposition to be proved -} ->
  IO (Maybe CEX, SolverStats)
    -- ^ (example/counter-example, solver statistics)
proveUnintSBVIO sc conf unintSet timeout goal =
  do p <- findExecutable . SBV.executable $ SBV.solver conf
     unless (isJust p) . fail $ mconcat
       [ "Unable to locate the executable \""
       , SBV.executable $ SBV.solver conf
       , "\" needed to run the solver "
       , show . SBV.name $ SBV.solver conf
       ]

     (labels, argNames, lit) <- prepNegatedSBV sc unintSet goal

     let script = maybe (return ()) SBV.setTimeOut timeout >> lit

     SBV.SatResult r <- SBV.satWith conf script

     let stats = solverStats ("SBV->" ++ show (SBV.name (SBV.solver conf)))
                             (sequentSize goal)
     case r of
       SBV.Unsatisfiable {} -> return (Nothing, stats)

       SBV.Satisfiable {} ->
         do let dict = SBV.getModelDictionary r
                r'   = SBVSim.getLabels labels dict argNames
            return (r', stats)

       SBV.DeltaSat{} -> fail "Prover returned an unexpected DeltaSat result"

       SBV.SatExtField {} -> fail "Prover returned model in extension field"

       SBV.Unknown {} -> fail "Prover returned Unknown"

       SBV.ProofError _ ls _ -> fail . unlines $ "Prover returned error: " : ls


-- | Convert a saw-core proposition to a logically-negated SBV
-- symbolic boolean formula with existentially quantified variables.
-- The returned formula is suitable for checking satisfiability. The
-- specified function names are left uninterpreted.

prepNegatedSBV ::
  SharedContext ->
  Set VarIndex {- ^ Uninterpreted function names -} ->
  Sequent      {- ^ Proposition to prove -} ->
  IO ([SBVSim.Labeler], [ExtCns Term], SBV.Symbolic SBV.SVal)
prepNegatedSBV sc unintSet goal =
  do satq <- sequentToSATQuery sc unintSet goal
     SBVSim.sbvSATQuery sc mempty satq
