{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Main
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Tasty wrapper that invokes @bash test.sh@ in this directory and
checks the exit code. The shell script handles all the per-test
work (running saw, diffing stdout against @*.log.good@, diffing
emitted @.lean@ against @*.lean.good@, optionally elaborating each
@.lean@ via @lake env lean@).

Direct port of @otherTests/saw-core-rocq/Test.hs@.
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
                | EVp String Char [String]

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

testParams :: FilePath -> (String -> IO ()) -> IO [(String, String)]
testParams base verbose = do
  here <- getCurrentDirectory
  let absTestBase = if isAbsolute base then base else here </> base
  sawExe <- findExecutable "saw" >>= pure . \case
              Just e -> e
              _      -> ""
  verbose $ "Found saw: " <> sawExe
  let eVars0 = [ EV  "HOME"     absTestBase
               , EVp "PATH"     searchPathSeparator [takeDirectory sawExe]
               , EV  "TESTBASE" absTestBase
               , EV  "DIRSEP"   [pathSeparator]
               , EV  "CPSEP"    [searchPathSeparator]
               , EVp "SAW"      ' ' ["eval", "saw"]
               ]
      addEnvVar evs e = do v <- lookupEnv e
                           pure $ updEnvVars e (fromMaybe "" v) evs
  e1 <- foldM addEnvVar eVars0 [ "SAW", "PATH", "SAW_SOLVER_CACHE_PATH"]
  pure $ envVarAssocList e1

main :: IO ()
main = do
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
    localOption (mkTimeout $ 500 * 1000 * 1000) $
    mkTest envVars
  where
    base :: FilePath
    base = "otherTests" </> "saw-core-lean"

    mkTest :: [(String,String)] -> TestTree
    mkTest envVars = testCase (takeFileName base) $ do
      let cmd = (shell "bash test.sh") { cwd = Just base, env = Just envVars }
      (r, o, e) <- liftIO $ readCreateProcessWithExitCode cmd ""
      unless (r == ExitSuccess) $ putStrLn o >> hPutStrLn stderr e
      ExitSuccess @=? r
