{- |
Module      : SAWScript.SolverVersions
Description : Determining SMT solver backend versions
License     : BSD3
Maintainer  : m-yac
Stability   : provisional
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.SolverVersions where

import Control.Exception
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))

import qualified Data.Map as Map

import qualified Data.SBV.Dynamic as SBV

import SAWScript.SolverCache
import GitRev

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
getSolverBackendVersion :: SolverBackend -> IO (Maybe String)
getSolverBackendVersion backend = case backend of
  What4     -> return what4Hash
  SBV       -> return sbvVersion
  AIG       -> return aigHash
  RME       -> return (Just hash)
  -- We use individual cases for the remaining constructors to ensure that if
  -- a new backend is added, a warning is generated for this pattern match
  ABC       -> getSolverVersion SBV.ABC
  Boolector -> getSolverVersion SBV.Boolector
  Bitwuzla  -> getSolverVersion SBV.Bitwuzla
  CVC4      -> getSolverVersion SBV.CVC4
  CVC5      -> getSolverVersion SBV.CVC5
  DReal     -> getSolverVersion SBV.DReal
  MathSAT   -> getSolverVersion SBV.MathSAT
  Yices     -> getSolverVersion SBV.Yices
  Z3        -> getSolverVersion SBV.Z3

-- | Get the set of 'SolverBackendVersions' of a list of 'SolverBackend's
getSolverBackendVersions :: [SolverBackend] -> IO SolverBackendVersions
getSolverBackendVersions backends = Map.fromList <$>
  mapM (\backend -> (backend,) <$> getSolverBackendVersion backend) backends
