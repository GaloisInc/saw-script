{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Server.Monad where

import Control.Concurrent.STM (TChan, atomically, newTChan)
import Control.Monad.Catch (Exception, MonadCatch, MonadThrow (throwM))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (MonadReader, ReaderT (..), asks)
import Data.Text (Text)
import Data.Text qualified as Text
import Language.LSP.Server
import Language.LSP.Types (ErrorCode (..), MessageType (..), ResponseError (..), SMethod (..), ShowMessageParams (..))
import Logging qualified as L
import Message
import Server.Config
import Server.Reactor (ReactorInput)

-------------------------------------------------------------------------------

data ServerEnv = ServerEnv
  { seConfig :: !(LanguageContextEnv Config),
    seReactorChannel :: !(TChan ReactorInput),
    seWorkerGovernorChannel :: !(TChan Action),
    seResponderChannel :: !(TChan Result)
  }

newServerEnv :: LanguageContextEnv Config -> IO ServerEnv
newServerEnv cfg =
  do
    rChannel <- atomically newTChan
    wgChannel <- atomically newTChan
    respChannel <- atomically newTChan
    pure
      ServerEnv
        { seConfig = cfg,
          seReactorChannel = rChannel,
          seWorkerGovernorChannel = wgChannel,
          seResponderChannel = respChannel
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
  getLspEnv = asks seConfig

runServerM :: ServerM a -> ServerEnv -> IO a
runServerM (ServerM r) serverEnv =
  do
    let lspAction = runReaderT r serverEnv
    runLspT (seConfig serverEnv) lspAction

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

internalError :: Text -> ResponseError
internalError s = ResponseError InternalError s Nothing

logName :: String
logName = "Server"

info :: String -> ServerM ()
info = L.info logName

debug :: String -> ServerM ()
debug = L.debug logName

warning :: String -> ServerM ()
warning = L.warning logName

--------------------------------------------------------------------------------

informText :: MonadLsp config f => Text -> f ()
informText msg = sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)

inform :: MonadLsp config f => String -> f ()
inform = informText . Text.pack

warnText :: MonadLsp config f => Text -> f ()
warnText msg = sendNotification SWindowShowMessage (ShowMessageParams MtWarning msg)

warn :: MonadLsp config f => String -> f ()
warn = warnText . Text.pack
