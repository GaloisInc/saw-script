{-# LANGUAGE DoAndIfThenElse #-}
module Main where

import System.Exit

import Tests.Common
import Tests.SharedTerm

main = do
  let allTests = sharedTermTests
  r <- runTestCases allTests
  if r then
    putStrLn "All tests successful." >> exitWith ExitSuccess
  else
    putStrLn "One or more tests failed." >> exitWith (ExitFailure 1)
