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
          mkGlobalDef "Prelude.bvEq"
            `pureApp` n
            `pureApp` x
            `mkApp` (mkGlobalDef "Prelude.bvAdd" `pureApp` n `pureApp` x `pureApp` z)
    let rhs =
          mkGlobalDef "Prelude.bvEq"
            `pureApp` n
            `mkApp` (mkGlobalDef "Prelude.bvNat" `pureApp` n `mkApp` mkNatLit 0)
            `pureApp` z
    (_, lhs_term) <- rewriteSharedTermConvertibility sc ss =<< scMkTerm sc lhs
    (_, rhs_term) <- rewriteSharedTermConvertibility sc ss =<< scMkTerm sc rhs
    assertEqual "Incorrect conversion\n" lhs_term rhs_term
