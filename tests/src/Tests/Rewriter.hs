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


import Verifier.SAW.Conversion
import Verifier.SAW.Prelude
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm

import Test.Tasty
import Test.Tasty.HUnit

scMkTerm :: SharedContext -> TermBuilder Term -> IO Term
scMkTerm sc t = runTermBuilder t (scTermF sc)

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
    natType <- scMkTerm sc (mkDataType "Prelude.Nat" [] [])
    n <- scFreshGlobal sc "n" natType
    bvType <- scMkTerm sc (mkGlobalDef "Prelude.bitvector" `mkApp` return n)
    x <- scFreshGlobal sc "x" bvType
    z <- scFreshGlobal sc "z" bvType
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
