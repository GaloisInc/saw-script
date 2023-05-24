{- |
Module      : SAWScript.SolverVersions
Description : Determining SMT solver backend versions
License     : BSD3
Maintainer  : m-yac
Stability   : provisional
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWScript.SolverVersions where

import Control.Exception
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.SBV.Dynamic as SBV

import SAWScript.SolverCache
import qualified GitRev as GitRev
import GitRev (aigHash, w4Hash, sbvVer)

-- | Given an 'SBV.Solver' from @SBV@, attempt to query the solver for its
-- version and return the result as a string.
-- Adapted from @what4/test/ProbeSolvers.hs@
getSolverVersion :: SBV.Solver -> IO (Maybe String)
getSolverVersion s =
  let s' = SBV.solver $ SBV.defaultSolverConfig s
      args = case SBV.name s' of
               -- n.b. abc will return a non-zero exit code if asked
               -- for command usage.
               SBV.ABC -> ["s", "-q", "version;quit"]
               _ -> ["--version"]
  in try (readProcessWithExitCode (SBV.executable s') args "") >>= \case
    Right (ExitSuccess,o,_) | [l] <- lines o -> return $ Just l
    Right _                   -> return Nothing
    Left (_ :: SomeException) -> return Nothing

-- | Get the 'SolverBackendVersion' of a 'SolverBackend'
getSolverBackendVersion :: SolverBackend -> IO SolverBackendVersion
getSolverBackendVersion backend = SolverBackendVersion backend <$>
  case backend of
    Solver s -> getSolverVersion s
    W4 _     -> return w4Hash
    SBV      -> return sbvVer
    AIG      -> return aigHash
    RME      -> return (Just GitRev.hash)

-- | Get the 'Set' of 'SolverBackendVersion's of a list of 'SolverBackend's
getSolverBackendVersions :: [SolverBackend] -> IO (Set SolverBackendVersion)
getSolverBackendVersions = fmap Set.fromList . mapM getSolverBackendVersion
