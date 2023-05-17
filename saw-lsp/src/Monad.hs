{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Monad where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM
import Control.Monad.Catch (Exception, MonadThrow (throwM))
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader
import Control.Monad.State.Class (MonadState (..))
import Data.Aeson
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Generics (Generic)
import Language.LSP.Server
import Language.LSP.Types (MessageType (..), ResponseError, SMethod (SWindowShowMessage), ShowMessageParams (..))
import REPL (Process, saw)
import Reactor (ReactorInput, reactor)
import SAWScript.Value qualified as SAW
import Text.Printf (printf)
import TopLevel (TopLevelT, runTopLevelT)
import Worker (WorkerInput, worker)

newtype Config = Config ()
  deriving (FromJSON)

emptyConfig :: Config
emptyConfig = Config ()

data ServerState = ServerState
  { ssConfig :: !(LanguageContextEnv Config),
    ssWorkerChannel :: !(TChan WorkerInput),
    ssReactorChannel :: !(TChan ReactorInput),
    ssSaw :: !Process,
    ssLogFile :: !FilePath
  }

serverState :: LanguageContextEnv Config -> IO ServerState
serverState env =
  do
    rChannel <- atomically newTChan
    wChannel <- atomically newTChan

    void $ forkIO (reactor rChannel)
    -- void $ forkIO (worker wChannel)

    sawProc <- saw

    pure
      ServerState
        { ssConfig = env,
          ssWorkerChannel = wChannel,
          ssReactorChannel = rChannel,
          ssSaw = sawProc,
          ssLogFile = defaultLogFile
        }

newtype ServerM a = ServerM
  { getServerM :: ReaderT ServerState (LspM Config) a
  }
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadReader ServerState,
      MonadIO,
      MonadThrow,
      MonadUnliftIO,
      MonadLsp Config
    )

instance MonadState Config ServerM where
  get = getConfig
  put = setConfig

runServerM :: ServerState -> ServerM a -> IO a
runServerM sst (ServerM a) = runLspT (ssConfig sst) (runReaderT a sst)

-- liftEither :: (MonadThrow m, Exception e) => Either e a -> m a
liftEither :: Either ResponseError a -> ServerM a
liftEither e =
  case e of
    Left l ->
      do
        sendNotification SWindowShowMessage (ShowMessageParams MtError (Text.pack (show l)))
        throwM l
    Right r -> pure r

-- liftMaybe :: (MonadThrow m, Exception e) => e -> Maybe a -> m a
liftMaybe :: ResponseError -> Maybe a -> ServerM a
liftMaybe e m =
  case m of
    Nothing ->
      do
        sendNotification SWindowShowMessage (ShowMessageParams MtError (Text.pack (show e)))
        throwM e
    Just a -> pure a

defaultLogFile :: FilePath
defaultLogFile = "/Users/sam/Desktop/projects/do1/saw-lsp/log.txt"

instance Exception ResponseError

debug :: Text -> ServerM ()
debug = debug' . Text.unpack

debug' :: String -> ServerM ()
debug' s =
  do
    lf <- asks ssLogFile
    liftIO $ appendFile lf msg
  where
    msg = printf "[debug] %s\n" s
