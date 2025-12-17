{-# LANGUAGE OverloadedStrings #-}

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
import qualified Data.IORef as IORef

import Test.Tasty
import Test.Tasty.HUnit

import qualified SAWSupport.Pretty as PPS
import SAWCore.Prelude
import SAWCore.SharedTerm


sharedTermTests :: [TestTree]
sharedTermTests =
  [ preludeSharedSmokeTest
  ]

-- | Tests that a shared context for the prelude can be created,
-- along with a single term.
preludeSharedSmokeTest :: TestTree
preludeSharedSmokeTest =
  testCase "preludeSharedSmokeTest" $ do
    ppopts <- IORef.newIORef PPS.defaultOpts
    sc <- mkSharedContext ppopts
    scLoadPreludeModule sc
    void $ scGlobalDef sc "Prelude.Bool"
    return ()
