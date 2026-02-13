{-# LANGUAGE OverloadedStrings #-}

{- |
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Tests.Rewriter
  ( rewriter_tests
  ) where

import Control.Monad (when)
import qualified Data.Text as Text

import qualified SAWSupport.Pretty as PPS

import SAWCore.OpenTerm (OpenTerm)
import qualified SAWCore.OpenTerm as OT
import SAWCore.Prelude
import SAWCore.Rewriter
import SAWCore.SharedTerm

import Test.Tasty
import Test.Tasty.HUnit

scMkTerm :: SharedContext -> OpenTerm -> IO Term
scMkTerm sc t = OT.complete sc t

rewriter_tests :: [TestTree]
rewriter_tests =
  [ prelude_bveq_sameL_test ]

prelude_bveq_sameL_test :: TestTree
prelude_bveq_sameL_test =
  testCase "prelude_bveq_sameL_test" $ do
    sc <- mkSharedContext
    scLoadPreludeModule sc
    let eqs = [ "Prelude.bveq_sameL" ]
    ss <- scSimpset sc [] eqs [] :: IO (Simpset ())
    natType <- scNatType sc
    n <- scFreshVariable sc "n" natType
    boolType <- scBoolType sc
    bvType <- scVecType sc n boolType
    x <- scFreshVariable sc "x" bvType
    z <- scFreshVariable sc "z" bvType
    let lhs =
          OT.applyGlobal "Prelude.bvEq"
          [ OT.term n
          , OT.term x
          , OT.applyGlobal "Prelude.bvAdd" [OT.term n, OT.term x, OT.term z]
          ]
    let rhs =
          OT.applyGlobal "Prelude.bvEq"
          [ OT.term n
          , OT.applyGlobal "Prelude.bvNat" [OT.term n, OT.nat 0]
          , OT.term z
          ]
    (_, lhs_term) <- rewriteSharedTerm sc ss =<< scMkTerm sc lhs
    (_, rhs_term) <- rewriteSharedTerm sc ss =<< scMkTerm sc rhs
    when (lhs_term /= rhs_term) $ do
        lhs_term' <- ppTerm sc PPS.defaultOpts lhs_term
        rhs_term' <- ppTerm sc PPS.defaultOpts rhs_term
        assertFailure $ Text.unpack $ Text.unlines [
            "Incorrect conversion:",
            "   " <> Text.pack lhs_term',
            "   " <> Text.pack rhs_term'
         ]
