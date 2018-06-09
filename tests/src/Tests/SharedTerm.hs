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
import Data.Hashable
import qualified Data.Map as Map

import Data.Time.Clock

import Test.Tasty
import Test.Tasty.HUnit

import Verifier.SAW.SharedTerm
import Verifier.SAW.Prelude


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
