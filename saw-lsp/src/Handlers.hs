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
import Language.LSP.Server (Handlers)
import Monad (ServerEnv (serverReactorChannel), ServerM, runServerM)
import Reactor (ReactorInput (..))

handlers :: Handlers ServerM
handlers = hs -- mapHandlers dispatchRequest dispatchNotification hs
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

-- dispatchRequest ::
--   forall (a :: Method 'FromClient 'Request).
--   Handler ServerM a ->
--   Handler ServerM a
-- dispatchRequest handler = \msg request ->
--   do
--     sEnv <- ask
--     let chan = serverReactorChannel sEnv
--     liftIO $
--       atomically $
--         writeTChan chan $
--           ReactorAction $
--             runServerM (handler msg request) sEnv

-- dispatchNotification ::
--   forall (a :: Method 'FromClient 'Notification).
--   Handler ServerM a ->
--   Handler ServerM a
-- dispatchNotification handler = \notif ->
--   do
--     sEnv <- ask
--     let chan = serverReactorChannel sEnv
--     liftIO $
--       atomically $
--         writeTChan chan $
--           ReactorAction $
--             runServerM (handler notif) sEnv
