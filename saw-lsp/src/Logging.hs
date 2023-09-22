module Logging where

import Control.Monad.IO.Class (MonadIO, liftIO)
import System.IO
import System.Log (Priority (..))
import System.Log.Formatter (simpleLogFormatter)
import System.Log.Handler (LogHandler (setFormatter))
import System.Log.Handler.Simple (GenericHandler (closeFunc), streamHandler)
import System.Log.Logger (addHandler, debugM, infoM, setLevel, updateGlobalLogger, warningM)

-- | A file handler that opens its files in write mode
--
-- Largely courtesy of `System.Log.Handler.Simple`'s source
writeFileHandler :: FilePath -> Priority -> IO (GenericHandler Handle)
writeFileHandler fp priority =
  do
    h <- openFile fp WriteMode
    sh <- streamHandler h priority
    return (sh {closeFunc = hClose})

initializeLogging :: String -> FilePath -> IO ()
initializeLogging logName logFile =
  do
    updateGlobalLogger logName (setLevel logLevel)
    h <- formatted <$> writeFileHandler logFile logLevel
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
