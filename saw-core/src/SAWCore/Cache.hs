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

-- | A @MapCache m k a@ is a mutable reference to a 'Map' with keys of
-- type @k@ and values of type @a@, for use in monad @m@.
newtype MapCache m k a = MapCache (T m (Map k a))

-- | Create a new empty 'MapCache'.
newMapCache :: (C m, Ord k) => m (MapCache m k a)
newMapCache = MapCache <$> new Map.empty

-- | Memoize a computation of type @k -> m a@ using a 'MapCache'.
-- If the cache already contains an entry for the given key, return
-- the value immediately without running the given monadic action.
-- Otherwise run the monadic action, store the result in the cache,
-- and also return the newly-computed value.
useMapCache :: (C m, Ord k) => MapCache m k a -> k -> m a -> m a
useMapCache (MapCache ref) k action =
  do m <- Data.Ref.read ref
     case Map.lookup k m of
       Just x -> pure x
       Nothing ->
         do x <- action
            modify ref (Map.insert k x)
            pure x

-- | An @IntCache m k a@ is a mutable reference to an 'IntMap' with
-- keys of type 'Int' and values of type @a@, for use in monad @m@.
-- @IntCache m a@ is a more efficient alternative to @MapCache m Int
-- a@.
newtype IntCache m a = IntCache (T m (IntMap a))

-- | Create a new empty 'IntCache'.
newIntCache :: (C m) => m (IntCache m a)
newIntCache = IntCache <$> new IntMap.empty

-- | Memoize a computation of type @Int -> m a@ using an 'IntCache'.
-- If the cache already contains an entry for the given key, return
-- the value immediately without running the given monadic action.
-- Otherwise run the monadic action, store the result in the cache,
-- and also return the newly-computed value.
useIntCache :: C m => IntCache m a -> Int -> m a -> m a
useIntCache (IntCache ref) k action =
  do m <- Data.Ref.read ref
     case IntMap.lookup k m of
       Just x -> pure x
       Nothing ->
         do x <- action
            modify ref (IntMap.insert k x)
            pure x
