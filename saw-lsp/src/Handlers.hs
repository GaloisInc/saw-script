{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant lambda" #-}

module Handlers where

import Control.Concurrent.STM
import Control.Monad.IO.Class
import Control.Monad.Reader (ask)
import Handlers.Custom.InterpretToPoint (handleInterpretToPoint)
import Handlers.Initialized (handleInitialized)
import Handlers.TextDocument.DidChange (handleTextDocumentDidChange)
import Handlers.TextDocument.DidOpen (handleTextDocumentDidOpen)
import Handlers.TextDocument.DidSave (handleTextDocumentDidSave)
import Handlers.TextDocument.SemanticTokensFull (handleTextDocumentSemanticTokensFull)
import Language.LSP.Server
import Language.LSP.Types
import Monad (ServerM, ServerState (ssReactorChannel), runServerM)
import Reactor (ReactorInput (..))

handlers :: Handlers ServerM
handlers = mapHandlers dispatchRequest dispatchNotification hs
  where
    hs =
      mconcat
        [ handleInitialized,
          handleInterpretToPoint,
          handleTextDocumentDidChange,
          handleTextDocumentDidOpen,
          handleTextDocumentDidSave,
          handleTextDocumentSemanticTokensFull
        ]

    dispatchRequest ::
      forall (a :: Method 'FromClient 'Request).
      Handler ServerM a ->
      Handler ServerM a
    dispatchRequest handler = \msg request ->
      do
        sst <- ask
        let chan = ssReactorChannel sst
        liftIO $ atomically $ writeTChan chan (ReactorAction (runServerM sst (handler msg request)))

    dispatchNotification ::
      forall (a :: Method 'FromClient 'Notification).
      Handler ServerM a ->
      Handler ServerM a
    dispatchNotification handler = \notif ->
      do
        sst <- ask
        let chan = ssReactorChannel sst
        liftIO $ atomically $ writeTChan chan (ReactorAction (runServerM sst (handler notif)))