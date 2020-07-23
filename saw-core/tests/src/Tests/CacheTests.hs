{-
Copyright   : Galois, Inc. 2019
License     : BSD3
Maintainer  : kquick@galois.com
Stability   : experimental
Portability : portable
-}

module Tests.CacheTests
  ( cacheTests
  )
where

import Control.Monad
import Control.Monad.ST
import Data.Ref ( C )
import Test.Tasty
import Test.Tasty.HUnit
import Verifier.SAW.Cache


cacheTests :: [TestTree]
cacheTests =
  [ cacheMapTestIO
  , cacheMapTestST
  , intMapTestIO
  , intMapTestST
  ]

-- | Tests that a normal cache map can be used that will memoize
-- values in the IO monad.
cacheMapTestIO :: TestTree
cacheMapTestIO =
  testGroup "normal map IO tests"
  [
    testCase "String->Bool small test" $
      cTestA newCacheMap [ ("hello", True), ("world", False) ]
  , testCase "String->String test" $
      cTestA newCacheMap [ ("hello", "world"), ("world", "fair"), ("Goodbye", "!") ]
  , testCase "Int->Char test" $
      cTestA newCacheMap [ (9 :: Int, 'n'), (3, 't'), (-427, 'f'), (0, 'z') ]
  ]

cacheMapTestST :: TestTree
cacheMapTestST =
  testGroup "normal map ST tests"
  [
    testCase "String->Bool small test" $
      stToIO $ cTestA newCacheMap [ ("hello", True), ("world", False) ]
  , testCase "String->String test" $
      stToIO $ cTestA newCacheMap [ ("hello", "world"), ("world", "fair"), ("Goodbye", "!") ]
  , testCase "Int->Char test" $
      stToIO $ cTestA newCacheMap [ (9 :: Int, 'n'), (3, 't'), (-427, 'f'), (0, 'z') ]
  ]

-- | Tests that a normal cache map can be used that will memoize
-- values in the IO monad.
intMapTestIO :: TestTree
intMapTestIO =
  testGroup "int map IO tests"
  [
    testCase "intmap Bool small test" $
      cTestA newCacheIntMap [ (11, True), (0, False) ]
  , testCase "intmap Int test" $
      cTestA newCacheIntMap [ (1, 0 :: Int), (0, -5), (-5, 39) ]
  , testCase "intmap String test" $
      cTestA newCacheIntMap [ (1, "True"), (0, "not yet"), (-5, "negative"), (3248902, "big") ]
  ]


-- | Tests that a normal cache map can be used that will memoize
-- values in the IO monad.
intMapTestST :: TestTree
intMapTestST =
  testGroup "int map IO tests"
  [
    testCase "intmap Bool small test" $
      stToIO $ cTestA newCacheIntMap [ (11, True), (0, False) ]
  , testCase "intmap Int test" $
      stToIO $ cTestA newCacheIntMap [ (1, 0 :: Int), (0, -5), (-5, 39) ]
  , testCase "intmap String test" $
      stToIO $ cTestA newCacheIntMap [ (1, "True"), (0, "not yet"), (-5, "negative"), (3248902, "big") ]
  ]


-- Always pass at least 2 entries in the keyval array, keys and values should be independently unique
cTestA :: (C m, Eq k, Eq v, Show k, Show v) =>
          m (Cache m k v) -> [(k,v)] -> m ()
cTestA mkCache keyvals = do
  c1 <- mkCache  -- will cache the keyvals
  c2 <- mkCache  -- will separately cache all keys equal to the same val (the first)
  let (k0, v0) = head keyvals
  let (kOmega, vOmega) = last keyvals

  -- Verify a value can be added, and once it is added, it does not
  -- need to be recomputed (i.e. it is memoized)
  v0' <- useCache c1 k0 (return v0)
  v0'' <- useCache c1 k0 (error "should not be called")
  unless (v0 == v0') $ error "initial cache store failed"
  unless (v0 == v0'') $ error "cached value retrieval failed"

  vOmega' <- useCache c2 k0 (return vOmega)
  vOmega'' <- useCache c2 k0 (return v0)
  unless (vOmega == vOmega') $ error "second cache initial store failed"
  unless (v0'    /= vOmega') $ error "caches are not independent"
  unless (vOmega == vOmega'') $ error "initial cache value is not persistent"

  -- Verify all the other values can similarly be cached once, and
  -- that they are distinct from the initial value.
  forM_ (tail keyvals) $ \(k,v) -> do
    vx <- useCache c1 k (return v)
    unless (v == vx) $ error "incorrect value stored"
    vy <- useCache c1 k (error "must not be called for vy")
    unless (v == vy) $ error "incorrect value cached"
    vo <- useCache c1 k0 (error "must not be called for vo")
    when (vy == vo) $ error "value collision"
    vz <- useCache c1 k (error "must not be called for vz")
    unless (v == vz) $ error "correct value not still cached"
    v2 <- useCache c2 k (return vOmega)
    unless (vOmega == v2) $ error "incorrect  stored in second cache"
    if k == kOmega
      then unless (v2 == vz) $ error "caches can share values"
      else unless (v2 /= vz) $ error "caches are independent for all keys"
