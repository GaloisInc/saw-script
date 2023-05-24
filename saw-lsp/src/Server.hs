{-# LANGUAGE TypeOperators #-}

module Server where

import Control.Exception (SomeException, catch)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Aeson qualified as Aeson
import Data.Text (Text)
import Data.Text qualified as Text
import Handlers (handlers)
import Language.LSP.Server
import Language.LSP.Types
import Monad
import SAWT (SAWEnv, defaultSAWEnv)
import System.IO (hPrint, hPutStrLn, stderr)
import Control.Concurrent (threadDelay)

run :: IO Int
run = runServer server -- `catch` handler
  where
    handler :: SomeException -> IO Int
    handler exn =
      do
        hPutStrLn stderr "server failed"
        hPrint stderr exn
        pure 56

server :: ServerDefinition Config
server =
  ServerDefinition
    { defaultConfig = emptyConfig,
      onConfigurationChange = onConfigurationChange',
      doInitialize = doInitialize',
      staticHandlers = handlers,
      interpretHandler = interpretHandler',
      options = options'
    }

onConfigurationChange' :: Config -> Aeson.Value -> Either Text Config
onConfigurationChange' _old v =
  do
    case Aeson.fromJSON v of
      Aeson.Error e -> Left (Text.pack e)
      Aeson.Success cfg -> Right cfg

doInitialize' ::
  LanguageContextEnv Config ->
  RequestMessage 'Initialize ->
  IO (Either ResponseError (ServerEnv, SAWEnv))
doInitialize' env initMsg =
  do
    serverEnv <- newServerEnv env
    sawEnv <- defaultSAWEnv
    -- let sawEnv = undefined
    -- threadDelay 10000000 -- microseconds
    pure (Right (serverEnv, sawEnv))

interpretHandler' :: (ServerEnv, SAWEnv) -> (ServerM <~> IO)
interpretHandler' (serverEnv, sawEnv) = Iso serverToIO ioToServer
  where
    serverToIO :: ServerM a -> IO a
    serverToIO action = runServerM action serverEnv sawEnv

    ioToServer :: IO a -> ServerM a
    ioToServer = liftIO

options' :: Options
options' = defaultOptions {textDocumentSync = Just tds}
  where
    tds =
      TextDocumentSyncOptions
        { _openClose = Just True,
          _change = Just TdSyncFull,
          _willSave = Just False,
          _willSaveWaitUntil = Just False,
          _save = Just (InR (SaveOptions {_includeText = Just True}))
        }
