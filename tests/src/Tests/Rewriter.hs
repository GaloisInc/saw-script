{-# LANGUAGE OverloadedStrings #-}
module Tests.Rewriter
  ( rewriter_tests
  ) where

import Control.Monad

import Verifier.SAW.Conversion
import Verifier.SAW.Prelude
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm

import Tests.Common

scMkTerm :: SharedContext s -> TermBuilder (SharedTerm s) (SharedTerm s) -> IO (SharedTerm s)
scMkTerm sc t = runTermBuilder t (scTermF sc)

rewriter_tests :: [TestCase]
rewriter_tests =
  [ prelude_bveq_sameL_test ]

prelude_bveq_sameL_test :: TestCase
prelude_bveq_sameL_test = 
  mkTestCase "prelude_bveq_sameL_test" $ monadicIO $ run $ do
    sc0 <- mkSharedContext preludeModule
    let eqs = [ "Prelude.bveq_sameL" ]
    ss <- scSimpset sc0 [] eqs []
    let sc = rewritingSharedContext sc0 ss
    natType <- scMkTerm sc (mkDataType "Prelude.Nat" [])
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
    unless (lhs_term == rhs_term) $ do
      fail $ "Incorrect conversion\n"
          ++ "Result:   " ++ show lhs_term ++ "\n"
          ++ "Expected: " ++ show rhs_term