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


import SAWCore.Conversion
import SAWCore.Prelude
import SAWCore.Rewriter
import SAWCore.SharedTerm

import Test.Tasty
import Test.Tasty.HUnit

scMkTerm :: SharedContext -> TermBuilder Term -> IO Term
scMkTerm sc t = runTermBuilder t (scGlobalDef sc) (scTermF sc)

rewriter_tests :: [TestTree]
rewriter_tests =
  [ prelude_bveq_sameL_test ]

prelude_bveq_sameL_test :: TestTree
prelude_bveq_sameL_test =
  testCase "prelude_bveq_sameL_test" $ do
    sc0 <- mkSharedContext
    scLoadPreludeModule sc0
    let eqs = [ "Prelude.bveq_sameL" ]
    ss <- scSimpset sc0 [] eqs []
    let sc = rewritingSharedContext sc0 ss
    natType <- scNatType sc0
    n <- scFreshVariable sc "n" natType
    boolType <- scBoolType sc0
    bvType <- scVecType sc0 n boolType
    x <- scFreshVariable sc "x" bvType
    z <- scFreshVariable sc "z" bvType
    let lhs =
          mkGlobalDef "Prelude.bvEq"
            `pureApp` n
            `pureApp` x
            `mkApp` (mkGlobalDef "Prelude.bvAdd" `pureApp` n `pureApp` x `pureApp` z)
    let rhs =
          mkGlobalDef "Prelude.bvEq"
            `pureApp` n
            `mkApp` (mkGlobalDef "Prelude.bvNat" `pureApp` n `mkApp` mkNatLit 0)
            `pureApp` z
    lhs_term <- scMkTerm sc lhs
    rhs_term <- scMkTerm sc rhs
    assertEqual "Incorrect conversion\n" lhs_term rhs_term
