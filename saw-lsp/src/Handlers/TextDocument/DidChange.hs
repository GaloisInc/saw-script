module Handlers.TextDocument.DidChange where

import Language.LSP.Server (Handlers, notificationHandler)
import Language.LSP.Types (Method (TextDocumentDidChange), NotificationMessage, SMethod (STextDocumentDidChange))
import Server.Monad (ServerM, debug)

handleTextDocumentDidChange :: Handlers ServerM
handleTextDocumentDidChange = notificationHandler STextDocumentDidChange doChange

doChange :: NotificationMessage 'TextDocumentDidChange -> ServerM ()
doChange notif =
  do
    debug "doChange" "doChange"
