module Handlers.Initialized where

import Language.LSP.Server (Handlers, notificationHandler)
import Language.LSP.Types (Method (..), NotificationMessage, SMethod (..))
import Server.Monad (ServerM, debug)

handleInitialized :: Handlers ServerM
handleInitialized = notificationHandler SInitialized doInitialized

doInitialized ::
  NotificationMessage 'Initialized ->
  ServerM ()
doInitialized notif =
  do
    debug "doInitialized" "doInitialized"
