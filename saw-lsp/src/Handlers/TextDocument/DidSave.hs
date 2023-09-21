module Handlers.TextDocument.DidSave where

import Control.Lens ((^.))
import Language.LSP.Server (Handlers, notificationHandler)
import Language.LSP.Types (Method (TextDocumentDidSave), NotificationMessage, SMethod (STextDocumentDidSave))
import Language.LSP.Types.Lens qualified as LSP
import Server.Monad

handleTextDocumentDidSave :: Handlers ServerM
handleTextDocumentDidSave = notificationHandler STextDocumentDidSave doSave

doSave :: NotificationMessage 'TextDocumentDidSave -> ServerM ()
doSave notif =
  do
    debug "doSave" "doSave"
  where
    tdi = notif ^. LSP.params . LSP.textDocument
