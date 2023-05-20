{- |
Module      : SAWScript.SolverVersions
Description : Determining SMT solver backend versions
License     : BSD3
Maintainer  : m-yac
Stability   : provisional
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWScript.SolverVersions
  ( Solver(..)
  , SolverBackend(..)
  , W4BackendExtra(..)
  , getSolverBackendVersions
  ) where

import Control.Exception
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Data.List (group)

import qualified Data.SBV.Dynamic as SBV
import Data.SBV.Dynamic (Solver(..))

import qualified GitRev as GitRev
import GitRev (aigHash, w4Hash, sbvVer)

-- | A datatype representing one of the solver backends available in SAW
data SolverBackend = SBV SBV.SMTConfig
                   | W4 W4BackendExtra Solver
                   | AIG
                   | RME

-- | A datatype representing one of the ways the what4 backend can be used in
-- SAW - i.e. directly ('W4_Base'), with a tactic ('W4_Tactic'), by converting
-- to SMTLib2 then calling ABC ('W4_SMTLib2'), by converting to Verilog then
-- calling ABC ('W4_Verilog'), or by converting to AIGER then calling ABC
-- ('W4_AIGER')
data W4BackendExtra = W4_Base
                    | W4_Tactic String
                    | W4_SMTLib2
                    | W4_Verilog
                    | W4_AIGER

-- | Given an 'SBV.SMTConfig' from @SBV@, query the solver for its version and
-- return the result as a string.
-- Adapted from @what4/test/ProbeSolvers.hs@
getSolverVersion :: SBV.SMTConfig -> IO String
getSolverVersion c =
  let cmd = SBV.executable (SBV.solver c)
      args = case SBV.name (SBV.solver c) of
               -- n.b. abc will return a non-zero exit code if asked
               -- for command usage.
               SBV.ABC -> ["s", "-q", "version;quit"]
               _ -> ["--version"]
  in try (readProcessWithExitCode cmd args "") >>= \case
    Right (ExitSuccess,o,_) | [l] <- lines o -> return l
    Right _                   -> return "unknown"
    Left (_ :: SomeException) -> return "unknown"

-- | Given a solver backend, return a list of all relevant version information.
-- For example, @SBV SBV.z3@ returns @["SBV ?.?", "Z3 version ?.?.? - ? bit"]@
getSolverBackendVersions :: SolverBackend -> IO [String]
getSolverBackendVersions backend = map (unwords . map head . group) <$>
  case backend of
    SBV c  -> do solver_ver <- getSolverVersion c
                 return [ ["SBV", sbvVer]
                        , (show $ SBV.name $ SBV.solver c) : words solver_ver ]
    W4 x s -> do solver_ver <- getSolverVersion (SBV.defaultSolverConfig s)
                 let (ex1, ex2) = w4Extra x
                 return $ [ ["what4", w4Hash] ++ ex1 ] ++ ex2 ++
                          [ show s : words solver_ver ]
    AIG    -> do return [["AIG", aigHash]]
    RME    -> do return [["RME", GitRev.hash]]
  where w4Extra W4_Base       = ([], [])
        w4Extra (W4_Tactic t) = (["using", t], [])
        w4Extra W4_SMTLib2    = (["to", "SMTLib2"], [])
        w4Extra W4_Verilog    = (["to", "Verilog"], [])
        w4Extra W4_AIGER      = (["to", "AIGER"], [["AIG", aigHash]])
