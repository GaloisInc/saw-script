module Verifier.SAW.Cache
  ( Cache
  , newCache
  , newCacheIORefMap
  , newCacheIORefMap'
  , newCacheMVarMap
  , newCacheIORefIntMap
  , newCacheSTRefMap
  , useCache
  ) where

import Control.Applicative ((<$>))
import Control.Concurrent.MVar
import Control.Monad (liftM)
import Control.Monad.IO.Class
import Control.Monad.ST
import Data.IORef
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.STRef

data Cache m k a = Cache (k -> m (Maybe a)) (k -> a -> m ())

useCache :: Monad m => Cache m k a -> k -> m a -> m a
useCache (Cache lookup update) k action =
    do result <- lookup k
       case result of
         Just x -> return x
         Nothing ->
             do x <- action
                update k x
                return x

newCache :: (MonadIO m, Ord k) => m (Cache m k a)
newCache = newCacheIORefMap

newCacheIORefMap :: (MonadIO m, Ord k) => m (Cache m k a)
newCacheIORefMap =
    do ref <- liftIO $ newIORef Map.empty
       let lookup k = liftIO $ Map.lookup k <$> readIORef ref
       let update k x = liftIO $ modifyIORef ref (Map.insert k x)
       return (Cache lookup update)

newCacheIORefMap' :: (MonadIO m, Ord k) => Map.Map k a -> m (Cache m k a)
newCacheIORefMap' initialMap =
    do ref <- liftIO $ newIORef initialMap
       let lookup k = liftIO $ Map.lookup k <$> readIORef ref
       let update k x = liftIO $ modifyIORef ref (Map.insert k x)
       return (Cache lookup update)

newCacheMVarMap :: (MonadIO m, Ord k) => m (Cache m k a)
newCacheMVarMap =
    do mvar <- liftIO $ newMVar Map.empty
       let lookup k = liftIO $ Map.lookup k <$> readMVar mvar
       let update k x = liftIO $ modifyMVar_ mvar (return . Map.insert k x)
       return (Cache lookup update)

newCacheIORefIntMap :: MonadIO m => m (Cache m Int a)
newCacheIORefIntMap =
    do ref <- liftIO $ newIORef IntMap.empty
       let lookup k = liftIO $ IntMap.lookup k <$> readIORef ref
       let update k x = liftIO $ modifyIORef ref (IntMap.insert k x)
       return (Cache lookup update)

newCacheSTRefMap :: Ord k => ST s (Cache (ST s) k a)
newCacheSTRefMap =
    do ref <- newSTRef Map.empty
       let lookup k = Map.lookup k <$> readSTRef ref
       let update k x = modifySTRef ref (Map.insert k x)
       return (Cache lookup update)
