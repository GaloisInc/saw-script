{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Main
Copyright   : Galois, Inc. 2019
License     : BSD3
Maintainer  : val@galois.com
Stability   : experimental
Portability : portable
-}

module Main (main) where

import Control.Monad ( unless, foldM )
import Control.Monad.Reader ( liftIO )
import Data.List ( intercalate )
import Data.Maybe ( fromMaybe )
import System.Directory ( getCurrentDirectory, findExecutable
                        , doesDirectoryExist )
import System.Environment ( lookupEnv )
import System.Exit ( ExitCode (ExitSuccess), exitFailure )
import System.FilePath ( (</>), pathSeparator, searchPathSeparator
                       , takeDirectory, takeFileName, isAbsolute )
import System.IO ( hPutStrLn, stderr )
import System.Process ( readCreateProcessWithExitCode
                      , shell, CreateProcess (..) )
import Test.Tasty ( defaultMain, localOption, mkTimeout, TestTree )
import Test.Tasty.HUnit ( testCase, (@=?) )

data EnvVarSpec = EV String String
                  -- ^ single string value
                | EVp String Char [String]
                  -- ^ accumulative path with separator

updEnvVars :: String -> String -> [EnvVarSpec] -> [EnvVarSpec]
updEnvVars n v [] = [EV n v | v /= ""]
updEnvVars n v (EV  n'   v' : evs) | n == n' = EV  n (if v == "" then v' else v) : evs
updEnvVars n v (EVp n' s v' : evs) | n == n' = EVp n s (v' <> [v]) : evs
updEnvVars n v (ev : evs) = ev : updEnvVars n v evs

envVarAssocList :: [EnvVarSpec] -> [(String, String)]
envVarAssocList = map envVarAssoc
  where
    envVarAssoc (EV  n v)    = (n, v)
    envVarAssoc (EVp n s vs) = (n, intercalate [s] vs)

-- | Returns the environment variable assocList to use for running
-- each individual test.
testParams :: FilePath -> (String -> IO ()) -> IO [(String, String)]
testParams base verbose = do
  here <- getCurrentDirectory
  let absTestBase = if isAbsolute base then base
                    else here </> base

  -- try to determine where the saw binary is in case there are other
  -- executables there (e.g. z3, etc.)
  sawExe <- findExecutable "saw" >>= pure . \case
              Just e -> e
              _      -> "" -- may be supplied via env var

  verbose $ "Found saw: " <> sawExe
  let eVars0 = [ EV  "HOME"     absTestBase
               , EVp "PATH"     searchPathSeparator [takeDirectory sawExe]
               , EV  "TESTBASE" absTestBase
               , EV  "DIRSEP"   [pathSeparator]
               , EV  "CPSEP"    [searchPathSeparator]

               -- The eval is used to protect the evaluation of the
               -- single-quoted arguments supplied below when run in a
               -- bash test.sh script.
               , EVp "SAW"      ' ' ["eval", "saw"]
               ]
      addEnvVar evs e = do v <- lookupEnv e
                           pure $ updEnvVars e (fromMaybe "" v) evs
  -- override eVars0 with any environment variables set in this process
  e1 <- foldM addEnvVar eVars0 [ "SAW", "PATH", "SAW_SOLVER_CACHE_PATH"]

  pure $ envVarAssocList e1

-- | Tests SAWCore to Coq translation by turning the `./test.sh` script into a
--   Tasty test. TODO: this is mostly duplicated from `intTests/IntegrationTests.hs`.
main :: IO ()
main = do
  -- Run tests with VERBOSE=y environment variable for extra output.
  verbose <- lookupEnv "VERBOSE" >>= pure . \case
    Just "y" -> putStrLn
    _        -> const $ pure ()
  found <- doesDirectoryExist base

  unless found $ do
    curwd <- getCurrentDirectory
    hPutStrLn stderr $ "FAILURE: cannot find test directory " <> base <> " from " <> curwd
    exitFailure

  envVars <- testParams base verbose
  verbose $ "ENV: " <> show envVars
  defaultMain $
    localOption (mkTimeout $ 500 * 1000 * 1000) $  -- 500 second timeout in usecs
    mkTest envVars
  where
    base :: FilePath
    base = "otherTests" </> "saw-core-coq"

    mkTest :: [(String,String)] -> TestTree
    mkTest envVars = testCase (takeFileName base) $ do
      let cmd = (shell "bash test.sh") { cwd = Just base, env = Just envVars }
      (r, o, e) <- liftIO $ readCreateProcessWithExitCode cmd ""
      unless (r == ExitSuccess) $ putStrLn o >> hPutStrLn stderr e
      ExitSuccess @=? r

