{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}

module Handlers.Custom.InterpretToPoint where

import Control.Lens ((^.))
import Control.Monad.Cont (MonadIO (liftIO))
import Data.Aeson ((.:))
import Data.Aeson qualified as Aeson
import Data.Aeson.Types qualified as Aeson
import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.UUID.V4 qualified as UUID
import Handlers.Custom.InterpretToPoint.Truncate
import Language.LSP.Server
import Language.LSP.Types
  ( Method (..),
    RequestMessage,
    ResponseError,
    SMethod (..),
    Uri,
    toNormalizedUri,
    uriToFilePath,
  )
import Language.LSP.Types.Lens qualified as LSP
import Language.LSP.VFS (virtualFileText)
import Message (Action (..))
import SAWScript.AST (Stmt (..))
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser (parseModule)
import Server.Monad
import Text.Printf (printf)

handleInterpretToPoint :: Handlers ServerM
handleInterpretToPoint = requestHandler (SCustomMethod "$/interpretToPoint") doInterp

doInterp ::
  RequestMessage 'CustomMethod ->
  (Either ResponseError Aeson.Value -> ServerM ()) ->
  ServerM ()
doInterp request responder =
  do
    debug "Interpreting script"

    interpParams <- liftEither (fromParams (request ^. LSP.params))
    fileStmts <- resolve (uri interpParams)
    truncatedStmts <- truncateStmts (posn interpParams) fileStmts

    tellWorkerGovernor (Interpret truncatedStmts)

resolve :: Uri -> ServerM [Stmt]
resolve uri =
  do
    vfM <- getVirtualFile (toNormalizedUri uri)
    vf <- liftMaybe (internalError "file not found") vfM
    let fileText = virtualFileText vf
        filePath = fromMaybe "<no path>" (uriToFilePath uri)
    liftEither (first (internalError . Text.pack) (parseSAWFile filePath fileText))

truncateStmts :: Position -> [Stmt] -> ServerM [Stmt]
truncateStmts position fileStmts =
  do
    uuid <- liftIO UUID.nextRandom
    let truncatedStmts = truncateScript position (show uuid) fileStmts
    inform $
      printf
        "Truncating %i statements to %i statements"
        (length fileStmts)
        (length truncatedStmts)
    pure truncatedStmts

parseSAWFile :: FilePath -> Text -> Either String [Stmt]
parseSAWFile path text =
  do
    let lexed = lexSAW path (Text.unpack text)
    first show (parseModule lexed)

-------------------------------------------------------------------------------

data InterpretParams = InterpretParams
  { posn :: Position,
    offset :: Int,
    uri :: Uri
  }
  deriving (Show)

instance Aeson.FromJSON InterpretParams where
  parseJSON = Aeson.withObject "InterpretParams" \v ->
    InterpretParams <$> v .: "posn" <*> v .: "offset" <*> v .: "uri"

fromParams :: Aeson.Value -> Either ResponseError InterpretParams
fromParams v = first (internalError . Text.pack) (Aeson.parseEither Aeson.parseJSON v)
