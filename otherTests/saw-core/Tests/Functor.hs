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
import Data.Text (Text)
import qualified Data.Text as Text

import Test.Tasty
import Test.Tasty.HUnit

import qualified SAWSupport.Pretty as PPS

import SAWCore.Name
import SAWCore.Term.Functor
import SAWCore.Term.Raw
import SAWCore.Term.Pretty (ppTermPure)


-- The Eq, Ord, and Hashable instances for Term/TermF/FlatTermF are
-- supposed to perform comparisons up to structural equality.
-- Terms that differ in their stAppIndex fields but are otherwise
-- structurally equal should compare as equal.
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
    stAppVarTypes = mempty,
    stAppTermF = t,
    stAppType = Left PropSort
 }

-- | Some variable names
vnFoo, vnBar :: VarName
vnFoo = VarName 2 "foo"
vnBar = VarName 3 "bar"

-- | An external constant
nmFoo :: Name
nmFoo = Name {
    nameIndex = 0,
    nameInfo = ModuleIdentifier "Foo.Module"
 }

-- | Test in the Either monad so we can use do-notation. (It might be
--   better to accumulate a list of all the terms that fail, if they
--   do, rather than detecting one at a time.  However, that requires
--   a good deal more glue as neither Either nor Maybe can be used
--   that way.
type Failure = (String, String, Text)
type Result = Either Failure ()

-- | Check a result.
check :: Failure -> Bool -> Result
check _ True = Right ()
check f False = Left f

-- | Typeclass-polymorphic test function.
--   Recurses consing more complex terms; the first argument is a
--   depth limit.
class (Eq t, Ord t, Hashable t) => TestIt t where
  -- | Promote back to Term for printing
  rewrap :: t -> Term

  -- | Check that two values are equal.
  --   Hopefully the compiler doesn't eliminate any of the checks...
  checkEq :: t -> t -> Result
  checkEq a b = do
    let a' = ppTermPure PPS.defaultOpts $ rewrap a
        b' = ppTermPure PPS.defaultOpts $ rewrap b
        f c = (a', b', c)
    check (f "Eq") $ a == b
    check (f "Ord") $ compare a b == EQ
    check (f "Hashable") $ hash a == hash b

  -- | Check that a comparison is as expected.
  --   Hopefully the compiler doesn't eliminate any of the checks...
  checkComparison :: Ordering -> t -> t -> Result
  checkComparison comp a b = do
    let a' = ppTermPure PPS.defaultOpts $ rewrap a
        b' = ppTermPure PPS.defaultOpts $ rewrap b
        f c = (a', b', c)
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
  rewrap t = shared 200 $ FTermF t

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
  rewrap t = shared 201 t

  testOne depth f = do
      -- reflexivity
      checkEq f f
      -- continue at the Term level
      let s = shared 0 f
          u = shared 100 f
      testOne depth s
      testOne depth u
      -- different term IDs compare equal
      testTwo depth EQ s u

  testTwo depth comp f1 f2 = do
      -- check that they compare as expected
      checkComparison comp f1 f2
      -- continue at the Term level
      let s1 = shared 1 f1
          s2 = shared 2 f2
          u1 = shared 101 f1
          u2 = shared 102 f2
      testTwo depth comp s1 s2
      testTwo depth comp u1 u2
      -- different term IDs compare as equal
      testTwo depth comp s1 u2
      testTwo depth comp u1 s2

instance TestIt Term where
  rewrap t = t

  testOne depth t = do
      -- reflexivity
      checkEq t t
      -- build and test more stuff
      when (depth < 2) $ do
        let depth' = depth + 1
            unit = shared 103 $ FTermF $ StringLit "()"
            zero = shared 104 $ FTermF $ StringLit "0"
            localvar = shared 105 $ Variable vnBar t
        testOne depth' $ App t t
        testOne depth' $ App t zero
        testOne depth' $ App unit t
        testOne depth' $ Lambda vnFoo t t
        testOne depth' $ Lambda vnBar t localvar
        testOne depth' $ Pi vnFoo t t
        testOne depth' $ Pi vnBar t localvar
        testTwo depth' LT (Lambda vnFoo t t) (Lambda vnBar t t)
        testTwo depth' LT (Pi vnFoo t t) (Pi vnBar t t)
        testTwo depth' EQ (Constant nmFoo :: TermF Term) (Constant nmFoo :: TermF Term)

  testTwo depth comp t1 t2 = do
      -- check that they compare as expected
      checkComparison comp t1 t2
      -- build and test more stuff
      when (depth < 2 && comp /= EQ) $ do
        let depth' = depth + 1
        -- check that the variable name affects the comparison
        testTwo depth' comp (Lambda vnFoo t1 t1) (Lambda vnFoo t2 t2)
        testTwo depth' LT (Lambda vnFoo t1 t1) (Lambda vnBar t2 t2)
        testTwo depth' GT (Lambda vnBar t1 t1) (Lambda vnFoo t2 t2)
        testTwo depth' comp (Pi vnFoo t1 t1) (Pi vnFoo t2 t2)
        testTwo depth' LT (Pi vnFoo t1 t1) (Pi vnBar t2 t2)
        testTwo depth' GT (Pi vnBar t1 t1) (Pi vnFoo t2 t2)
        pure ()

-- | Run some tests
tests :: Result
tests = do
  let unit, zero, one :: FlatTermF Term
      unit = StringLit "()"
      zero = StringLit "0"
      one = StringLit "1"
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
          let msg = "Failed: " ++ Text.unpack class_ ++ " on " ++ t1 ++ " and " ++ t2
          assertFailure msg

functorTests :: [TestTree]
functorTests = [runTests]
