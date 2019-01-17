{-# LANGUAGE ExistentialQuantification #-}

{- |
Module      : Verifier.SAW.Cache
Copyright   : Galois, Inc. 2012-2015
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
  )
where

import           Control.Monad (liftM)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import           Data.Ref
import           Prelude hiding (lookup)

data Cache m k a = forall t. Cache (T m t) (k -> t -> Maybe a) (k -> a -> t -> t)

useCache :: C m => Cache m k a -> k -> m a -> m a
useCache (Cache ref lookup update) k action = do
  result <- liftM (lookup k) (Data.Ref.read ref)
  case result of
    Just x -> return x
    Nothing -> do
      x <- action
      modify ref (update k x)
      return x

newCache :: (C m, Ord k) => m (Cache m k a)
newCache = newCacheMap

newCacheMap :: (C m, Ord k) => m (Cache m k a)
newCacheMap = newCacheMap' Map.empty

newCacheMap' :: (C m, Ord k) => Map.Map k a -> m (Cache m k a)
newCacheMap' initialMap = do
  ref <- new initialMap
  return (Cache ref Map.lookup Map.insert)

newCacheIntMap :: (C m) => m (Cache m Int a)
newCacheIntMap = newCacheIntMap' IntMap.empty

newCacheIntMap' :: (C m) => IntMap.IntMap a -> m (Cache m Int a)
newCacheIntMap' initialMap = do
  ref <- new initialMap
  return (Cache ref IntMap.lookup IntMap.insert)
