module Main (main) where

import Test.SAWT.Interpret qualified
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Util.FList qualified
import Test.Util.Stack qualified

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "main"
    [ Test.SAWT.Interpret.tests,
      Test.Util.FList.tests,
      Test.Util.Stack.tests
    ]
