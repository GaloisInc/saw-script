module SAWScript.Prover.SBV
  ( proveUnintSBV
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.yices, SBV.mathSAT, SBV.boolector
  , prepNegatedSBV
  ) where

import System.Directory

import           Data.Maybe
import           Data.Set ( Set )
import qualified Data.Text as Text
import           Control.Monad

import qualified Data.SBV.Dynamic as SBV
import qualified Data.SBV.Internals as SBV

import qualified Verifier.SAW.Simulator.SBV as SBVSim

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue

import SAWScript.Proof(Prop, propSize, propToSATQuery)
import SAWScript.Prover.SolverStats

-- | Bit-blast a proposition and check its validity using SBV.
-- Constants with names in @unints@ are kept as uninterpreted
-- functions.
proveUnintSBV ::
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Set VarIndex  {- ^ Uninterpreted functions -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  SharedContext {- ^ Context for working with terms -} ->
  Prop          {- ^ A proposition to be proved -} ->
  IO (Maybe [(String, FirstOrderValue)], SolverStats)
    -- ^ (example/counter-example, solver statistics)
proveUnintSBV conf unintSet timeout sc goal =
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
                             (propSize goal)
     case r of
       SBV.Unsatisfiable {} -> return (Nothing, stats)

       SBV.Satisfiable {} ->
         do let dict = SBV.getModelDictionary r
                r'   = SBVSim.getLabels labels dict (map Text.unpack argNames)
            return (r', stats)

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
  Prop     {- ^ Proposition to prove -} ->
  IO ([SBVSim.Labeler], [Text.Text], SBV.Symbolic SBV.SVal)
prepNegatedSBV sc unintSet goal =
  do satq <- propToSATQuery sc unintSet goal
     SBVSim.sbvSATQuery sc mempty satq
