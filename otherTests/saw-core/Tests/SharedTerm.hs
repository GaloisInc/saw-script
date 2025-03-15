{-
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Tests.SharedTerm
  ( sharedTermTests
  ) where

import Control.Monad
import Test.Tasty
import Test.Tasty.HUnit
import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm


sharedTermTests :: [TestTree]
sharedTermTests =
  [ preludeSharedSmokeTest
  ]

-- | Tests that a shared context for the prelude can be created,
-- along with a single term.
preludeSharedSmokeTest :: TestTree
preludeSharedSmokeTest =
  testCase "preludeSharedSmokeTest" $ do
    sc <- mkSharedContext
    scLoadPreludeModule sc
    void $ scApplyPrelude_Bool sc
    return ()
