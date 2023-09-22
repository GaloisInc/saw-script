module Logging where

import Control.Monad.IO.Class
import System.Log (Priority (..))
import System.Log.Handler.Simple (fileHandler)
import System.Log.Logger (addHandler, debugM, infoM, setLevel, updateGlobalLogger, warningM)

initializeLogging :: String -> FilePath -> IO ()
initializeLogging logName logFile =
  do
    updateGlobalLogger logName (setLevel logLevel)
    h <- fileHandler logFile logLevel
    updateGlobalLogger logName (addHandler h)
  where
    logLevel = DEBUG

info :: MonadIO m => String -> String -> m ()
info logName msg = liftIO (infoM logName msg)

debug :: MonadIO m => String -> String -> m ()
debug logName msg = liftIO (debugM logName msg)

warning :: MonadIO m => String -> String -> m ()
warning logName msg = liftIO (warningM logName msg)
