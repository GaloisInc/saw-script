{-# LANGUAGE OverloadedStrings #-}
module SAWCentral.Prover.SBV
  ( proveUnintSBV
  , proveUnintSBVIO
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.cvc5, SBV.yices, SBV.mathSAT, SBV.boolector, SBV.bitwuzla
  ) where

import           Control.Monad

import           Data.Maybe
import           Data.Text (Text)
import qualified Data.Text as Text

import System.Directory

import qualified Data.SBV.Dynamic as SBV
import qualified Data.SBV.Internals as SBV

import qualified SAWCoreSBV.SBV as SBVSim

import SAWCore.SharedTerm
import SAWCore.SATQuery (SATQuery(..))

import SAWCentral.Proof (CEX)
import SAWCentral.Value

-- | Bit-blast a proposition and check its validity using SBV.
-- Constants with names in @unints@ are kept as uninterpreted
-- functions.
proveUnintSBV ::
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  SATQuery      {- ^ A query to be proved -} ->
  TopLevel (Maybe CEX, Text)
    -- ^ (example/counter-example, solver statistics)
proveUnintSBV conf timeout satq =
  do sc <- getSharedContext
     io $ proveUnintSBVIO sc conf timeout satq

proveUnintSBVIO ::
  SharedContext ->
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  SATQuery      {- ^ A query to be proved -} ->
  IO (Maybe CEX, Text)
    -- ^ (example/counter-example, solver statistics)
proveUnintSBVIO sc conf timeout satq =
  do p <- findExecutable . SBV.executable $ SBV.solver conf
     unless (isJust p) . fail $ mconcat
       [ "Unable to locate the executable \""
       , SBV.executable $ SBV.solver conf
       , "\" needed to run the solver "
       , show . SBV.name $ SBV.solver conf
       ]

     (labels, argNames, lit) <- SBVSim.sbvSATQuery sc mempty satq

     let script = maybe (return ()) SBV.setTimeOut timeout >> lit

     SBV.SatResult r <- SBV.satWith conf script

     let solver_name = "SBV->" <> Text.pack (show (SBV.name (SBV.solver conf)))

     case r of
       SBV.Unsatisfiable {} -> return (Nothing, solver_name)

       SBV.Satisfiable {} ->
         do let dict = SBV.getModelDictionary r
                r'   = SBVSim.getLabels labels dict argNames
            return (r', solver_name)

       SBV.DeltaSat{} -> fail "Prover returned an unexpected DeltaSat result"

       SBV.SatExtField {} -> fail "Prover returned model in extension field"

       SBV.Unknown {} -> fail "Prover returned Unknown"

       SBV.ProofError _ ls _ -> fail . unlines $ "Prover returned error: " : ls
