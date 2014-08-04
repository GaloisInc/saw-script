{-# LANGUAGE ExistentialQuantification #-}

{- |
Module      : Verifier.SAW.Cache
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Cache
  ( Cache
  , newCache
  , newCacheMap
  , newCacheMap'
  , newCacheIntMap
  , newCacheIntMap'
  , useCache
  ) where


import Control.Monad (liftM)
import Control.Monad.Ref
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Prelude hiding (lookup)

data Cache r k a = forall t. Cache (r t) (k -> t -> Maybe a) (k -> a -> t -> t)

useCache :: MonadRef r m => Cache r k a -> k -> m a -> m a
useCache (Cache ref lookup update) k action = do
  result <- liftM (lookup k) (readRef ref)
  case result of
    Just x -> return x
    Nothing -> do
      x <- action
      modifyRef ref (update k x)
      return x

newCache :: (MonadRef r m, Ord k) => m (Cache r k a)
newCache = newCacheMap

newCacheMap :: (MonadRef r m, Ord k) => m (Cache r k a)
newCacheMap = newCacheMap' Map.empty

newCacheMap' :: (MonadRef r m, Ord k) => Map.Map k a -> m (Cache r k a)
newCacheMap' initialMap = do
  ref <- newRef initialMap
  return (Cache ref Map.lookup Map.insert)

newCacheIntMap :: (MonadRef r m) => m (Cache r Int a)
newCacheIntMap = newCacheIntMap' IntMap.empty

newCacheIntMap' :: (MonadRef r m) => IntMap.IntMap a -> m (Cache r Int a)
newCacheIntMap' initialMap = do
  ref <- newRef initialMap
  return (Cache ref IntMap.lookup IntMap.insert)
