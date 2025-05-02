{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Tests.Functor (functorTests) where

import Control.Monad (when)
import Data.Hashable

import Test.Tasty
import Test.Tasty.HUnit

import SAWCore.Term.Functor


-- There are three properties of Term/TermF/FlatTermF that the
-- Eq, Ord, and Hashable instances are supposed to respect:
--    1. Comparison is up to alpha equivalence.
--    2. The STApp (shared) and Unshared cases of Term are not
--       distinguished.
--
-- And of course Eq, Ord, and Hashable need to be mutually consistent:
--    t1 == t2 <-> compare t1 t2 == Eq
--    t1 == t2 <-> hash t1 == hash t2
--
-- Note that we don't need the terms we test on to be well typed, so
-- we can produce nonsense like "1" of type "1" without anything bad
-- happens. This makes it quite a bit easier.
--
-- Similarly, because the things we're testing are pure, we don't need
-- the sharing to actually work or be connected to a SharedContext,
-- just consistent with expectations.
--
-- To wit:
--    - stAppIndex should only be the same for equal terms
--    - stAppHash t = hash (stAppTermF t)
--    - and stAppFreeVars can always be empty.


-- | Construct a shared Term according to expectations
--   Note: I am playing fast and loose with the indexes
shared :: TermIndex -> TermF Term -> Term
shared ix t = STApp {
    stAppIndex = ix,
    stAppHash = hash t,
    stAppFreeVars = emptyBitSet,
    stAppTermF = t
 }

-- | Some LocalNames (LocalName is just Text)
lnFoo, lnBar :: LocalName
lnFoo = "foo"
lnBar = "bar"

-- | An external constant
ecFoo :: ExtCns Term
ecFoo = EC {
    ecVarIndex = 0,
    ecName = ModuleIdentifier "Foo.Module",
    ecType = Unshared $ FTermF UnitType
 }
 
-- | Test in the Either monad so we can use do-notation. (It might be
--   better to accumulate a list of all the terms that fail, if they
--   do, rather than detecting one at a time.  However, that requires
--   a good deal more glue as neither Either nor Maybe can be used
--   that way.
type Failure = (String, String, String)
type Result = Either Failure ()

-- | Check a result. 
check :: Failure -> Bool -> Result
check _ True = Right ()
check f False = Left f

-- | Check that two values are equal.
--   Hopefully the compiler doesn't eliminate any of the checks...
checkEq :: (Show t, Eq t, Ord t, Hashable t) => t -> t -> Result
checkEq a b = do
  let f c = (show a, show b, c)
  check (f "Eq") $ a == b
  check (f "Ord") $ compare a b == EQ
  check (f "Hashable") $ hash a == hash b

-- | Check that a comparison is as expected.
--   Hopefully the compiler doesn't eliminate any of the checks...
checkComparison :: (Show t, Eq t, Ord t, Hashable t) => Ordering -> t -> t -> Result
checkComparison comp a b = do
  let f c = (show a, show b, c)
  -- check the Eq instance
  let eqr = case comp of
        EQ -> a == b
        _ -> a /= b
  check (f "Eq") eqr
  -- check the Ord instance
  check (f "Ord") $ compare a b == comp
  -- check the Hashable instance
  case comp of
      EQ -> check (f "Hashable") $ hash a == hash b
      _ -> pure ()

-- | Typeclass-polymorphic test function.
--   Recurses consing more complex terms; the first argument is a
--   depth limit.
class (Show t, Eq t, Ord t, Hashable t) => TestIt t where
  -- | Test a single term
  testOne :: Int -> t -> Result
  -- | Test two terms with a known comparison.
  testTwo :: Int -> Ordering -> t -> t -> Result
  -- | We never autogenerate two nonequal terms, so make an entry point for some
  seedTwo :: t -> t -> Result
  seedTwo a b = do
      -- get the base comparison
      let comp = compare a b
      -- now run it
      testTwo 0 comp a b

-- | Test in FlatTermF
instance TestIt (FlatTermF Term) where
  testOne depth ff = do
      -- reflexivity
      checkEq ff ff
      -- continue at the TermF level
      let f = FTermF ff
      testOne depth f

  testTwo depth comp ff1 ff2 = do
      -- check that they compare as expected
      checkComparison comp ff1 ff2
      -- continue at the TermF level
      let f1 = FTermF ff1
          f2 = FTermF ff2
      testTwo depth comp f1 f2

-- | Test in TermF
instance TestIt (TermF Term) where
  testOne depth f = do
      -- reflexivity
      checkEq f f
      -- continue at the Term level
      let s = shared 0 f
          u = Unshared f
      testOne depth s
      testOne depth u
      -- shared and unshared compare equal
      testTwo depth EQ s u

  testTwo depth comp f1 f2 = do
      -- check that they compare as expected
      checkComparison comp f1 f2
      -- continue at the Term level
      let s1 = shared 1 f1
          s2 = shared 2 f2
          u1 = Unshared f1
          u2 = Unshared f2
      testTwo depth comp s1 s2
      testTwo depth comp u1 u2
      -- shared and unshared compare the same
      testTwo depth comp s1 u2
      testTwo depth comp u1 s2

instance TestIt Term where
  testOne depth t = do
      -- reflexivity
      checkEq t t
      -- build and test more stuff
      when (depth < 2) $ do
        let depth' = depth + 1
            unit = Unshared $ FTermF $ UnitValue
            zero = Unshared $ FTermF $ NatLit 0
            localvar = Unshared $ LocalVar 0
        testOne depth' $ PairValue t t
        testOne depth' $ PairValue t zero
        testOne depth' $ PairValue unit t
        testOne depth' $ App t t
        testOne depth' $ App t zero
        testOne depth' $ App unit t
        testOne depth' $ Lambda lnFoo t t
        testOne depth' $ Lambda lnBar t localvar
        testOne depth' $ Pi lnFoo t t
        testOne depth' $ Pi lnBar t localvar
        testTwo depth' EQ (Lambda lnFoo t t) (Lambda lnBar t t)
        testTwo depth' EQ (Pi lnFoo t t) (Pi lnBar t t)
        testTwo depth' GT (Constant ecFoo (Just t)) (Constant ecFoo Nothing)

  testTwo depth comp t1 t2 = do
      -- check that they compare as expected
      checkComparison comp t1 t2
      -- build and test more stuff
      when (depth < 2 && comp /= EQ) $ do
        let depth' = depth + 1
        -- check that the variable name doesn't affect the comparison
        testTwo depth' comp (Lambda lnFoo t1 t1) (Lambda lnFoo t2 t2)
        testTwo depth' comp (Lambda lnFoo t1 t1) (Lambda lnBar t2 t2)
        testTwo depth' comp (Lambda lnBar t1 t1) (Lambda lnFoo t2 t2)
        testTwo depth' comp (Pi lnFoo t1 t1) (Pi lnFoo t2 t2)
        testTwo depth' comp (Pi lnFoo t1 t1) (Pi lnBar t2 t2)
        testTwo depth' comp (Pi lnBar t1 t1) (Pi lnFoo t2 t2)
        pure ()

-- | Run some tests
tests :: Result
tests = do
  let unit, zero, one :: FlatTermF Term
      unit = UnitValue
      zero = NatLit 0
      one = NatLit 1
  testOne 0 unit
  testOne 0 one
  seedTwo zero one
  seedTwo one zero
  seedTwo one unit

-- | Wrap the tests in Tasty.
runTests :: TestTree
runTests =
  testCase "functorTests" $ do
    case tests of
      Right () -> pure ()
      Left (t1, t2, class_) -> do
          let msg = "Failed: " ++ class_ ++ " on " ++ t1 ++ " and " ++ t2
          assertFailure msg

functorTests :: [TestTree]
functorTests = [runTests]
