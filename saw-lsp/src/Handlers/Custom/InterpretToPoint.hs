{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}

module Handlers.Custom.InterpretToPoint where

import Monad
import SAW (InterpretParams (..), interpretToPoint)
import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Reader (asks)
import Data.Aeson as Aeson
import Data.Aeson.Types (parseEither)
import Data.List (intercalate)
import Data.Text qualified as Text
import Language.LSP.Server
import Language.LSP.Types hiding (Position)
import Language.LSP.Types.Lens qualified as LSP
import Language.LSP.VFS (virtualFileText)
import REPL (command)

handleInterpretToPoint :: Handlers ServerM
handleInterpretToPoint = requestHandler (SCustomMethod "$/interpretToPoint") doInterp

doInterp ::
  RequestMessage 'CustomMethod ->
  (Either ResponseError Aeson.Value -> ServerM ()) ->
  ServerM ()
doInterp request responder =
  do
    debug "doInterp"
    InterpretParams {..} <- liftEither (fromParams ps)
    debug' (show posn)
    vfM <- getVirtualFile (toNormalizedUri uri)
    vf <- liftMaybe (ResponseError InternalError "" Nothing) vfM
    let text = virtualFileText vf
    saw <- asks ssSaw
    goal <- liftIO $ interpretToPoint saw text posn
    -- result <- liftIO $ command saw "eval_int {{ 3: [2] }}"
    -- sendRequest SWindowShowDocument (ShowDocumentParams )
    responder (Right (Aeson.String goal))
  where
    ps = request ^. LSP.params

{-
Verify that the user has clicked just past a semicolon
- But merely trust that they did so inside a proof script

- Parse the entire module
  - *Assume we're in a `do` block
- Slot a `Bind`/`Expr` (`LExpr`?) dispatching to proof_subshell in the
  appropriate slot in the block list
- *Print the whole thing
- Send it to the repl wholesale (`include` via tempfile? line by line?)

-}

mkShowDocumentParams ::
  -- | the document to show
  Uri ->
  -- | whether to show it in an external program
  Maybe Bool ->
  -- | whether to take focus
  Maybe Bool ->
  -- | what to select, if anything
  Maybe Range ->
  ShowDocumentParams
mkShowDocumentParams = ShowDocumentParams

mkDocRequest :: InterpretParams -> Either ResponseError ShowDocumentParams
mkDocRequest = undefined

fromParams :: Aeson.Value -> Either ResponseError InterpretParams
fromParams v =
  case parseEither parseJSON v of
    Left e -> Left (ResponseError InternalError (Text.pack e) Nothing)
    Right p -> Right p
