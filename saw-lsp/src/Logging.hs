module Logging where

import Control.Monad.IO.Class (MonadIO, liftIO)
import System.Log (Priority (..))
import System.Log.Formatter (simpleLogFormatter)
import System.Log.Handler (LogHandler (setFormatter))
import System.Log.Handler.Simple (fileHandler)
import System.Log.Logger (addHandler, debugM, infoM, setLevel, updateGlobalLogger, warningM)

initializeLogging :: String -> FilePath -> IO ()
initializeLogging logName logFile =
  do
    updateGlobalLogger logName (setLevel logLevel)
    h <- formatted <$> fileHandler logFile logLevel
    updateGlobalLogger logName (addHandler h)
  where
    logLevel = DEBUG
    formatted h = setFormatter h (simpleLogFormatter "[$time : $prio] $msg")

info :: MonadIO m => String -> String -> m ()
info logName msg = liftIO (infoM logName msg)

debug :: MonadIO m => String -> String -> m ()
debug logName msg = liftIO (debugM logName msg)

warning :: MonadIO m => String -> String -> m ()
warning logName msg = liftIO (warningM logName msg)
