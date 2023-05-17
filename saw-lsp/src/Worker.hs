module Worker (worker, WorkerInput (..)) where

import Control.Concurrent.STM
import Control.Monad (forever)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Language.LSP.Types (Uri)

data WorkerInput = SemanticTokens Uri | InterpretToPoint | PrintGoal

act :: TChan WorkerInput -> IO ()
act channel =
  do
    req <- liftIO $ atomically $ readTChan channel
    case req of
      InterpretToPoint -> pure ()
      PrintGoal -> pure ()
      SemanticTokens _ -> pure ()

worker :: TChan WorkerInput -> IO ()
worker channel = forever $ act channel
