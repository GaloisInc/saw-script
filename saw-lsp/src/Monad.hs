{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Monad where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM (TChan, atomically, newTChan, readTChan)
import Control.Monad (forever, void)
import Control.Monad.Catch (Exception, MonadCatch, MonadThrow (throwM))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (MonadReader, ReaderT (..), asks)
import Control.Monad.Trans (MonadTrans (..))
import Data.Aeson (FromJSON)
import Data.Text (Text)
import Data.Text qualified as Text
import Language.LSP.Server
import Language.LSP.Types (MessageType (..), ResponseError, SMethod (..), ShowMessageParams (..))
import Reactor (ReactorInput, reactor)
import SAWT
import System.IO (hPutStrLn, stderr)
import Text.Printf (printf)
import Worker (WorkerInput)

newtype Config = Config ()
  deriving (FromJSON)

emptyConfig :: Config
emptyConfig = Config ()

-------------------------------------------------------------------------------

data ServerEnv = ServerEnv
  { serverConfig :: !(LanguageContextEnv Config),
    serverWorkerChannel :: !(TChan WorkerInput),
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
          serverWorkerChannel = wChannel,
          serverReactorChannel = rChannel,
          serverLogFile = defaultLogFile
        }

-------------------------------------------------------------------------------

newtype ServerM a = ServerM
  { getServerM :: ReaderT ServerEnv (SAWT (LspM Config)) a
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

runServerM :: ServerM a -> ServerEnv -> SAWEnv -> IO a
runServerM (ServerM r) serverEnv sawEnv =
  do
    let sawAction = runReaderT r serverEnv
        lspAction = runSAWT sawAction sawEnv
    runLspT (serverConfig serverEnv) lspAction

liftSAW :: SAWT (LspM Config) a -> ServerM a
liftSAW action = ServerM (lift action)

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
    liftIO $ appendFile logFile msg
  where
    msg = printf "[debug] %s\n" s