module Main (main) where

import Test.FList qualified
import Test.SAWT.Interpret qualified
import Test.Stack qualified
import Test.Tasty (TestTree, defaultMain, testGroup)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "main"
    [ Test.Stack.tests,
      Test.SAWT.Interpret.tests,
      Test.FList.tests
    ]
