{-# LANGUAGE DoAndIfThenElse #-}
module Main where

import System.Exit

import Tests.Common


import Tests.BitBlast
import Tests.Parser
import Tests.SharedTerm
import Tests.Rewriter

main = do
  let allTests = [ ("SharedTerm", sharedTermTests)
                 , ("Parser", parserTests)
                 , ("BitBlast", bitblastTests)
                 , ("Rewriter", rewriter_tests)
                 ]
  r <- runTestCases allTests
  if r then
    putStrLn "All tests successful." >> exitWith ExitSuccess
  else
    putStrLn "One or more tests failed." >> exitWith (ExitFailure 1)
