{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Server.Monad where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM (TChan, atomically, newTChan)
import Control.Monad (void)
import Control.Monad.Catch (Exception, MonadCatch, MonadThrow (throwM))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (MonadReader, ReaderT (..), asks)
import Data.Text (Text)
import Data.Text qualified as Text
import Language.LSP.Server
import Language.LSP.Types (MessageType (..), ResponseError, SMethod (..), ShowMessageParams (..))
import Server.Config
import Server.Reactor (ReactorInput, reactor)
import Text.Printf (printf)

-------------------------------------------------------------------------------

data ServerEnv = ServerEnv
  { serverConfig :: !(LanguageContextEnv Config),
    -- serverWorkerChannel :: !(TChan WorkerInput),
    serverReactorChannel :: !(TChan ReactorInput),
    serverLogFile :: !FilePath
  }

newServerEnv :: LanguageContextEnv Config -> IO ServerEnv
newServerEnv env =
  do
    rChannel <- atomically newTChan
    wChannel <- atomically newTChan

    void $ forkIO (reactor rChannel)
    -- void $ forkIO (worker wChannel)

    pure
      ServerEnv
        { serverConfig = env,
          -- serverWorkerChannel = wChannel,
          serverReactorChannel = rChannel,
          serverLogFile = defaultLogFile
        }

-------------------------------------------------------------------------------

newtype ServerM a = ServerM
  { getServerM :: ReaderT ServerEnv (LspM Config) a
  }
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadReader ServerEnv,
      MonadIO,
      MonadThrow,
      MonadCatch,
      MonadUnliftIO
    )

instance MonadLsp Config ServerM where
  getLspEnv = asks serverConfig

runServerM :: ServerM a -> ServerEnv -> IO a
runServerM (ServerM r) serverEnv =
  do
    let lspAction = runReaderT r serverEnv
    runLspT (serverConfig serverEnv) lspAction

liftEither :: Either ResponseError a -> ServerM a
liftEither e =
  case e of
    Left l ->
      do
        sendNotification SWindowShowMessage (ShowMessageParams MtError (Text.pack (show l)))
        throwM l
    Right r -> pure r

liftMaybe :: ResponseError -> Maybe a -> ServerM a
liftMaybe e m =
  case m of
    Nothing ->
      do
        sendNotification SWindowShowMessage (ShowMessageParams MtError (Text.pack (show e)))
        throwM e
    Just a -> pure a

-------------------------------------------------------------------------------

instance Exception ResponseError

defaultLogFile :: FilePath
defaultLogFile = "/Users/sam/projects/do1/saw-script/saw-lsp/log.txt"

debug :: Text -> ServerM ()
debug = debug' . Text.unpack

debug' :: String -> ServerM ()
debug' s =
  do
    logFile <- asks serverLogFile
    liftIO $ appendFile logFile $ printf "[debug] %s\n" s

inform :: Text -> ServerM ()
inform msg = sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)

inform' :: String -> ServerM ()
inform' = inform . Text.pack

warn :: Text -> ServerM ()
warn msg = sendNotification SWindowShowMessage (ShowMessageParams MtWarning msg)

warn' :: String -> ServerM ()
warn' = warn . Text.pack
