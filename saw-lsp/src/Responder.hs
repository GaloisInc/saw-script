{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Responder where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM (TChan, atomically, readTChan, writeTChan)
import Control.Monad
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, StateT, evalStateT, gets)
import Language.LSP.Server (LanguageContextEnv, LspT, runLspT, sendRequest)
import Language.LSP.Types
  ( MessageActionItem (..),
    MessageType (..),
    SMethod (..),
    ShowMessageRequestParams (..),
  )
import Message (Action (..), Result (..), ThreadHandle)
import Server.Config (Config)
import Server.Monad (inform)
import System.Log.Logger (warningM)

launchResponder :: LanguageContextEnv Config -> TChan Action -> TChan Result -> IO ()
launchResponder cfg actionChannel resultChannel =
  let st = mkResponderState cfg resultChannel actionChannel
   in void (forkIO (runResponder (forever responder) st))

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
    result <- readResult
    case result of
      Pending tHandle -> pending tHandle
      Success str -> informClient ("success: " <> str)
      Failure err -> informClient ("failure: " <> err)
  where
    informClient msg = lsp (inform msg)

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
                liftIO (warningM "pending" "ur killing it sis!!!!!!")
                liftIO (atomically (writeTChan chan (Kill tHandle)))
                pure ()
            _ -> pure ()
        pure ()
