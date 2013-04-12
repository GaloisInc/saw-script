module Tests.SharedTerm where

import Test.QuickCheck.Monadic

import Tests.Common

import Verifier.SAW.SharedTerm
import Verifier.SAW.Prelude

sharedTermTests :: [TestCase]
sharedTermTests =
  [ mkTestCase "preludeBool" $ monadicIO $ run $ do
      sc <- mkSharedContext preludeModule
      _ <- scPreludeBool sc
      return ()
  ]