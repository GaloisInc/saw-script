{-# LANGUAGE NamedFieldPuns #-}

module Main where

import System.FilePath ((</>))

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.HUnit.ScriptExit

import Paths_saw_remote_api
import Argo.PythonBindings

main :: IO ()
main =
  do reqs <- getArgoPythonFile "requirements.txt"
     withPython3venv (Just reqs) $ \pip python ->
       do pySrc <- getArgoPythonFile "."
          testScriptsDir <- getDataFileName "test-scripts/"
          pip ["install", pySrc]

          scriptTests <- makeScriptTests testScriptsDir [python]

          defaultMain $
            testGroup "Tests for saw-remote-api" scriptTests
