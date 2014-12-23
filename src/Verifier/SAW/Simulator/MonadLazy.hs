module Verifier.SAW.Simulator.MonadLazy where

import Control.Monad.Identity
import Control.Monad.IO.Class
import Data.IORef

class Monad m => MonadLazy m where
  delay :: m a -> m (m a)

force :: m a -> m a
force = id

ready :: Monad m => a -> m a
ready = return

instance MonadLazy Identity where
  delay = return

instance MonadLazy IO where
  delay = delayIO

delayIO :: MonadIO m => m a -> m (m a)
delayIO m = liftM pull (liftIO (newIORef Nothing))
  where
    pull ref = do
      r <- liftIO (readIORef ref)
      case r of
        Nothing -> do
          x <- m
          liftIO (writeIORef ref (Just x))
          return x
        Just x -> return x
