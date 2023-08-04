{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant lambda" #-}

module Handlers where

import Control.Concurrent.STM (atomically, writeTChan)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ask)
import Handlers.Custom.InterpretToPoint (handleInterpretToPoint)
import Handlers.Initialized (handleInitialized)
import Handlers.TextDocument.DidChange (handleTextDocumentDidChange)
import Handlers.TextDocument.DidOpen (handleTextDocumentDidOpen)
import Handlers.TextDocument.DidSave (handleTextDocumentDidSave)
import Handlers.TextDocument.SemanticTokensFull (handleTextDocumentSemanticTokensFull)
import Language.LSP.Server (Handler, Handlers, mapHandlers)
import Language.LSP.Types (From (..), Method, MethodType (..))
import SAWT (getRef)
import Server.Monad (ServerEnv (serverReactorChannel), ServerM, liftSAW, runServerM')
import Server.Reactor (ReactorInput (..))

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
    serverEnv <- ask
    sawStateRef <- liftSAW getRef
    let rChannel = serverReactorChannel serverEnv
    liftIO $
      atomically $
        writeTChan rChannel $
          ReactorAction $
            runServerM' (handler msg request) serverEnv sawStateRef

dispatchNotification ::
  forall (a :: Method 'FromClient 'Notification).
  Handler ServerM a ->
  Handler ServerM a
dispatchNotification handler = \notif ->
  do
    serverEnv <- ask
    sawStateRef <- liftSAW getRef
    let rChannel = serverReactorChannel serverEnv
    liftIO $
      atomically $
        writeTChan rChannel $
          ReactorAction $
            runServerM' (handler notif) serverEnv sawStateRef
