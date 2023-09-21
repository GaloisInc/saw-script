module Responder where

import Control.Concurrent (ThreadId, forkIO)
import Control.Concurrent.STM (TChan, atomically, readTChan)
import Control.Monad
import Language.LSP.Server (LanguageContextEnv, runLspT)
import Responder.Result
import Server.Config (Config)
import Server.Monad

launchResponder :: LanguageContextEnv Config -> TChan Result -> IO ()
launchResponder cfg channel = void (forkIO (forever (responder cfg channel)))

responder :: LanguageContextEnv Config -> TChan Result -> IO ()
responder cfg channel =
  do
    result <- atomically (readTChan channel)
    case result of
      Pending tid -> informClient "success"
      Success -> pure ()
      Failure err -> pure ()
  where
    informClient msg = runLspT cfg (inform msg)

-- foo = inform
