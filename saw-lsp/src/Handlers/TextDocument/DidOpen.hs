module Handlers.TextDocument.DidOpen where

import Control.Lens ((^.))
import Language.LSP.Server (Handlers, notificationHandler)
import Language.LSP.Types (Method (TextDocumentDidOpen), NotificationMessage, SMethod (STextDocumentDidOpen))
import Language.LSP.Types.Lens qualified as LSP
import Server.Monad

handleTextDocumentDidOpen :: Handlers ServerM
handleTextDocumentDidOpen = notificationHandler STextDocumentDidOpen doOpen

doOpen :: NotificationMessage 'TextDocumentDidOpen -> ServerM ()
doOpen notif =
  do
    debug "doOpen"
  where
    -- let res = mkResponse uri
    -- sendNotification
    -- openVFS logVFS notif
    -- pure ()

    -- sendRequest method params responder
    -- logVFS = cmap (fmap (Text.pack . show)) logToLogMessage
    uri = notif ^. LSP.params . LSP.textDocument . LSP.uri

-- DidOpenTextDocumentParams (TextDocumentItem uri _ _ text) = notif ^. LSP.params
