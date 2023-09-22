{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Responder where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM (TChan, atomically, readTChan, writeTChan)
import Control.Monad
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, StateT, evalStateT, gets)
import Data.Aeson qualified as Aeson
import Language.LSP.Server (LanguageContextEnv, LspT, runLspT, sendRequest)
import Language.LSP.Types
  ( MessageActionItem (..),
    MessageType (..),
    SMethod (..),
    ShowDocumentParams (..),
    ShowMessageRequestParams (..),
    filePathToUri,
  )
import Logging qualified as L
import Message (Action (..), Result (..), ThreadHandle)
import Server.Config (Config)
import Server.Monad (inform, warn)
import System.IO.Temp (writeSystemTempFile)

launchResponder :: LanguageContextEnv Config -> TChan Action -> TChan Result -> IO ()
launchResponder cfg actionChannel resultChannel =
  do
    L.initializeLogging logName "responder.log"
    let st = mkResponderState cfg resultChannel actionChannel
    void (forkIO (runResponder (forever responder) st))

newtype Responder a = Responder {unResponder :: StateT ResponderState IO a}
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadIO,
      MonadState ResponderState
    )

runResponder :: Responder a -> ResponderState -> IO a
runResponder (Responder action) = evalStateT action

data ResponderState = ResponderState
  { rsCfg :: LanguageContextEnv Config,
    rsResultChannel :: TChan Result,
    rsActionChannel :: TChan Action
  }

mkResponderState :: LanguageContextEnv Config -> TChan Result -> TChan Action -> ResponderState
mkResponderState cfg resultChannel actionChannel =
  ResponderState {rsCfg = cfg, rsResultChannel = resultChannel, rsActionChannel = actionChannel}

readResult :: Responder Result
readResult =
  do
    chan <- gets rsResultChannel
    liftIO (atomically (readTChan chan))

writeAction :: Action -> Responder ()
writeAction action =
  do
    chan <- gets rsActionChannel
    liftIO (atomically (writeTChan chan action))

responder :: Responder ()
responder =
  do
    debug "about to read result"
    result <- readResult
    debug ("read result: " <> show result)
    case result of
      Pending tHandle -> pending tHandle
      DisplayGoal goal -> displayGoal goal
      Success str -> informClient ("success: " <> str)
      Failure err -> warnClient ("failure: " <> err)
  where
    informClient msg = lsp (inform msg)
    warnClient msg = lsp (warn msg)

lsp :: LspT Config IO a -> Responder a
lsp action =
  do
    cfg <- gets rsCfg
    liftIO (runLspT cfg action)

pending :: ThreadHandle -> Responder ()
pending tHandle =
  do
    chan <- gets rsActionChannel
    lsp $
      do
        let params =
              ShowMessageRequestParams
                MtInfo
                "Started a thread"
                (Just [MessageActionItem "kill it"])
        _ <- sendRequest
          SWindowShowMessageRequest
          params
          \case
            Right (Just (MessageActionItem "kill it")) ->
              do
                debug "ur killing it sis!!!!!!"
                liftIO (atomically (writeTChan chan (Kill tHandle)))
                pure ()
            _ -> pure ()
        pure ()

displayGoal :: String -> Responder ()
displayGoal goal =
  lsp $
    do
      goalFilePath <- liftIO $ writeSystemTempFile "lsp" goal
      let goalUri = filePathToUri goalFilePath
          externalApplication = Just False
          takeFocus = Just False
          highlight = Nothing -- Just (LSP.Range (LSP.Position 0 5) (LSP.Position 1 3))
          showDocParams = ShowDocumentParams goalUri externalApplication takeFocus highlight
      _ <- sendRequest (SCustomMethod "$/displayGoal") (Aeson.toJSON showDocParams) \case
        Left err -> debug (show err)
        Right _ -> debug "success"
      pure ()

--------------------------------------------------------------------------------

logName :: String
logName = "Responder"

debug :: MonadIO m => String -> m ()
debug = L.debug logName
