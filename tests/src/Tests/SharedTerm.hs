{- |
Copyright   : Galois, Inc. 2012-2014
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
import Tests.Common

import Verifier.SAW.SharedTerm
import Verifier.SAW.Prelude


sharedTermTests :: [TestCase]
sharedTermTests =
  [ preludeSharedSmokeTest
  ]

-- | Tests that a shared context for the prelude can be created,
-- along with a single term.
preludeSharedSmokeTest :: TestCase
preludeSharedSmokeTest =
  mkTestCase "preludeSharedSmokeTest" $ monadicIO $ run $ do
    sc <- mkSharedContext preludeModule
    void $ scPreludeBool sc
    return ()
