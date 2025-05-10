{-# LANGUAGE OverloadedStrings #-}
{-
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : myac@galois.com
Stability   : experimental
Portability : portable
-}

module Tests.Simulator
  ( simulatorTests
  )
where

import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import GHC.Natural

import SAWCore.Term.Pretty (ppTerm, defaultPPOpts)
import SAWCore.Prelude
import SAWCore.SharedTerm
import SAWCore.Simulator.TermModel

import Test.Tasty
import Test.Tasty.HUnit

bindM2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bindM2 k m1 m2 = join $ k <$> m1 <*> m2

bindM3 :: Monad m => (a -> b -> c -> m d) -> m a -> m b -> m c -> m d
bindM3 k m1 m2 m3 = join $ k <$> m1 <*> m2 <*> m3

-- Copied from Prims.hs and TermModel.hs
bvPad :: SharedContext -> Natural -> Natural -> Term -> IO Term
bvPad sc w xsize x = do pad <- bpBvLit (fromIntegral $ w - xsize) 0
                        bpBvJoin pad x
  where bpBvLit = scBvConst sc
        bpBvJoin xtm ytm = let (xn, yn) = (w - xsize, xsize) in snd <$>
          do xn' <- scNat sc xn
             yn' <- scNat sc yn
             a   <- scBoolType sc
             tm  <- scAppend sc xn' yn' a xtm ytm
             return (xn+yn, tm)


simulatorTests :: [TestTree]
simulatorTests = testNormalizeSharedTerm <$> normalizeSharedTermTests

normalizeSharedTermTests :: [NormalizeSharedTermTest]
normalizeSharedTermTests = [

  -- Succ 2 ~> 3
  ("Succ_nat",
   \sc -> scCtorApp sc "Prelude.Succ" . (:[]) =<< scNat sc 2,
   \sc -> scNat sc 3),
  -- Succ (bvToNat 8 2) ~> bvToNat 9 (bvNat 9 3) 
  ("Succ_bvToNat",
   \sc -> scCtorApp sc "Prelude.Succ" . (:[]) =<<
            scBvToNat sc 8 =<< scBvLit sc 8 2,
   \sc -> scBvToNat sc 9 =<< scBvConst sc 9 3),

  -- 1+2 ~> 3
  ("add_nats",
   \sc -> bindM2 (scAddNat sc) (scNat sc 1) (scNat sc 2),
   \sc -> scNat sc 3),
  -- (bvToNat 4 1)+(bvToNat 6 2) ~> bvToNat 7 (bvNat 7 3)
  ("add_bvToNat",
   \sc -> bindM2 (scAddNat sc) (scBvToNat sc 4 =<< scBvLit sc 4 1)
                               (scBvToNat sc 6 =<< scBvLit sc 6 2),
   \sc -> scBvToNat sc 7 =<< scBvConst sc 7 3),

  -- 5-4 ~> 1
  ("sub_nats",
   \sc -> bindM2 (scSubNat sc) (scNat sc 5) (scNat sc 4),
   \sc -> scNat sc 1),
  -- (bvToNat 8 5)-4 ~> bvToNat 8 (bvNat 8 1)
  ("sub_bvToNat",
   \sc -> bindM2 (scSubNat sc) (scBvToNat sc 8 =<< scBvLit sc 8 5)
                               (scNat sc 4),
   \sc -> scBvToNat sc 8 =<< scBvConst sc 8 1),

  -- 3*5 ~> 15
  ("mul_nats",
   \sc -> bindM2 (scMulNat sc) (scNat sc 3) (scNat sc 5),
   \sc -> scNat sc 15),
  -- 3*(bvToNat 8 x) ~> bvToNat 10 (bvMul 10 3 (0b00 # x))
  ("mul_bvToNat",
   \sc -> bindM2 (scLambda sc "x") (scBitvector sc 8) $
          bindM2 (scMulNat sc) (scNat sc 3)
                               (scBvToNat sc 8 =<< scLocalVar sc 0),
   \sc -> bindM2 (scLambda sc "x") (scBitvector sc 8) $
          scBvToNat sc 10 =<< bindM3 (scBvMul sc) (scNat sc 10)
                                     (scBvConst sc 10 3)
                                     (bvPad sc 10 8 =<< scLocalVar sc 0)),

  -- max 2 7 ~> 7
  ("max_nats",
   \sc -> bindM2 (scMaxNat sc) (scNat sc 2) (scNat sc 7),
   \sc -> scNat sc 7),
  -- max 2 (bvToNat 8 7) ~> bvToNat 8 (bvNat 8 7)
  ("max_bvToNat",
   \sc -> bindM2 (scMaxNat sc) (scNat sc 2)
                               (scBvToNat sc 8 =<< scBvLit sc 8 7),
   \sc -> scBvToNat sc 8 =<< scBvConst sc 8 7),

  -- min 2 7 ~> 2
  ("min_nats",
   \sc -> bindM2 (scMinNat sc) (scNat sc 2) (scNat sc 7),
   \sc -> scNat sc 2),
  -- min (bvToNat 8 2) 7 ~> bvToNat 8 (bvNat 8 2)
  ("min_bvToNat",
   \sc -> bindM2 (scMinNat sc) (scBvToNat sc 8 =<< scBvLit sc 8 2)
                               (scNat sc 7),
   \sc -> scBvToNat sc 8 =<< scBvConst sc 8 2),

  -- divMod 22 7 ~> (3, 1)
  ("divMod_nats",
   \sc -> bindM2 (scDivModNat sc) (scNat sc 22) (scNat sc 7),
   \sc -> bindM2 (scPairValue sc) (scNat sc 3) (scNat sc 1)),
  -- divMod 22 (bvToNat 8 7) ~> (bvToNat 8 (bvNat 8 3), bvToNat 8 (bvNat 8 1))
  ("divMod_bvToNat",
   \sc -> bindM2 (scDivModNat sc) (scNat sc 22)
                                  (scBvToNat sc 8 =<< scBvLit sc 8 7),
   \sc -> bindM2 (scPairValue sc) (scBvToNat sc 8 =<< scBvConst sc 8 3)
                                  (scBvToNat sc 8 =<< scBvConst sc 8 1)),

  -- widthNat 5 ~> 3
  ("widthNat_nat",
   \sc -> scGlobalApply sc "Prelude.widthNat" . (:[]) =<< scNat sc 5,
   \sc -> scNat sc 3),
  -- widthNat (bvToNat 8 5) ~> 8
  ("widthNat_bvToNat",
   \sc -> scGlobalApply sc "Prelude.widthNat" . (:[]) =<<
            scBvToNat sc 8 =<< scBvLit sc 8 5,
   \sc -> scNat sc 8),

  -- equalNat (3*5) (5*3) ~> True
  ("equalNat_nats",
   \sc -> bindM2 (scEqualNat sc)
                 (bindM2 (scMulNat sc) (scNat sc 3) (scNat sc 5))
                 (bindM2 (scMulNat sc) (scNat sc 5) (scNat sc 3)),
   \sc -> scBool sc True),
  -- equalNat (3*(bvToNat 8 x)) (bvToNat 8 (bvMul 8 x 3)) ~>
  -- bvEq 10 (bvMul 10 3 (0b00 # x)) (0b00 # bvMul 8 x 3))
  ("equalNat_bvToNat",
   \sc -> bindM2 (scLambda sc "x") (scBitvector sc 8) $
          bindM2 (scEqualNat sc)
                 (bindM2 (scMulNat sc) (scNat sc 3)
                                       (scBvToNat sc 8 =<< scLocalVar sc 0))
                 (scBvToNat sc 8 =<< bindM3 (scBvMul sc) (scNat sc 8)
                                            (scLocalVar sc 0)
                                            (scBvConst sc 8 3)),
   \sc -> bindM2 (scLambda sc "x") (scBitvector sc 8) $
          bindM3 (scBvEq sc) (scNat sc 10)
                 (bindM3 (scBvMul sc) (scNat sc 10)
                                      (scBvConst sc 10 3)
                                      (bvPad sc 10 8 =<< scLocalVar sc 0))
                 (bvPad sc 10 8 =<< bindM3 (scBvMul sc) (scNat sc 8)
                                           (scLocalVar sc 0)
                                           (scBvConst sc 8 3))),
    
  -- ltNat 4 9 ~> True
  ("ltNat_nats",
   \sc -> bindM2 (scLtNat sc) (scNat sc 4) (scNat sc 9),
   \sc -> scBool sc True),
  -- ltNat (bvToNat 8 4) 9 ~> True
  ("ltNat_bvToNat",
   \sc -> bindM2 (scLtNat sc) (scBvToNat sc 8 =<< scBvLit sc 8 4) (scNat sc 9),
   \sc -> scBool sc True)

  ]


newtype PrettyTerm = PrettyTerm Term deriving (Eq)

instance Show PrettyTerm where
  show (PrettyTerm t) = show (ppTerm defaultPPOpts t)

type NormalizeSharedTermTest = (String, (SharedContext -> IO Term),
                                        (SharedContext -> IO Term))
  
testNormalizeSharedTerm :: NormalizeSharedTermTest -> TestTree
testNormalizeSharedTerm (nm, m1, m2) =
  testCase nm $ do
    sc <- mkSharedContext
    scLoadPreludeModule sc
    t1 <- m1 sc
    t2 <- m2 sc
    modmap <- scGetModuleMap sc
    t1' <- normalizeSharedTerm sc modmap Map.empty Map.empty Set.empty t1
    assertEqual "Incorrect normalization" (PrettyTerm t2) (PrettyTerm t1')
