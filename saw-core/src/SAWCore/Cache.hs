{-# LANGUAGE ExistentialQuantification #-}

{- |
Module      : SAWCore.Cache
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Cache
  ( MapCache
  , newMapCache
  , useMapCache
  , IntCache
  , newIntCache
  , useIntCache
  )
where

import qualified Data.IntMap as IntMap
import           Data.IntMap (IntMap)
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Ref

newtype MapCache m k a = MapCache (T m (Map k a))

newMapCache :: (C m, Ord k) => m (MapCache m k a)
newMapCache = MapCache <$> new Map.empty

useMapCache :: (C m, Ord k) => MapCache m k a -> k -> m a -> m a
useMapCache (MapCache ref) k action =
  do m <- Data.Ref.read ref
     case Map.lookup k m of
       Just x -> pure x
       Nothing ->
         do x <- action
            modify ref (Map.insert k x)
            pure x

newtype IntCache m a = IntCache (T m (IntMap a))

newIntCache :: (C m) => m (IntCache m a)
newIntCache = IntCache <$> new IntMap.empty

useIntCache :: C m => IntCache m a -> Int -> m a -> m a
useIntCache (IntCache ref) k action =
  do m <- Data.Ref.read ref
     case IntMap.lookup k m of
       Just x -> pure x
       Nothing ->
         do x <- action
            modify ref (IntMap.insert k x)
            pure x
