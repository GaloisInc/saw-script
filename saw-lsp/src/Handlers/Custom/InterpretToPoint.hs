{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}

module Handlers.Custom.InterpretToPoint where

import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Reader (asks)
import Data.Aeson as Aeson
import Data.Aeson.Types (parseEither)
import Data.Bifunctor (Bifunctor (first), second)
import Data.List (intercalate)
import Data.Text (Text)
import Data.Text qualified as Text
import Error (internalError)
import Language.LSP.Server
import Language.LSP.Types hiding (Position)
import Language.LSP.Types.Lens qualified as LSP
import Language.LSP.VFS (VirtualFile, virtualFileText)
import Monad
import REPL (command)
import SAW (InterpretParams (..), Position, interpretToPoint)
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser (parseModule)
import SAWScript.AST (Stmt)

handleInterpretToPoint :: Handlers ServerM
handleInterpretToPoint = requestHandler (SCustomMethod "$/interpretToPoint") doInterp

doInterp ::
  RequestMessage 'CustomMethod ->
  (Either ResponseError Aeson.Value -> ServerM ()) ->
  ServerM ()
doInterp request responder =
  do
    sendNotification SWindowShowMessage (ShowMessageParams MtError "where did I go so wrong?")
    responder (Left (internalError "nah brah"))
    -- InterpretParams {..} <- liftEither (fromParams ps)
    -- vf <- getVF (toNormalizedUri uri)
    -- let text = virtualFileText vf
    -- undefined
  where
    ps = request ^. LSP.params

getVF :: NormalizedUri -> ServerM VirtualFile
getVF uri =
  do
    vfM <- getVirtualFile uri
    liftMaybe (internalError "file not found") vfM

interp :: Text -> Position -> ServerM String
interp text posn =
  do
    stmts <- liftEither parsed
    undefined
  where
    lexed = lexSAW "" (Text.unpack text)
    parsed = first (\e -> internalError ("parse error: " <> Text.pack (show e))) $ parseModule lexed

  

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
