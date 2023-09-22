{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}

module Handlers.Custom.InterpretToPoint where

import Control.Lens ((^.))
import Control.Monad.Catch (throwM)
import Control.Monad.Cont (MonadIO (liftIO))
import Data.Aeson ((.:))
import Data.Aeson qualified as Aeson
import Data.Aeson.Types qualified as Aeson
import Data.Bifunctor (first)
import Data.List.NonEmpty (NonEmpty ((:|)))
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
    ShowDocumentParams (ShowDocumentParams),
    Uri,
    filePathToUri,
    toNormalizedUri,
    uriToFilePath,
  )
import Language.LSP.Types.Lens qualified as LSP
import Language.LSP.VFS (virtualFileText)
import SAWScript.AST (Stmt (..))
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser (parseModule)
import SAWT.Interpret (interpretSAWScript)
import Server.Error (internalError)
import Server.Monad
import System.IO.Temp (writeSystemTempFile)
import Text.Printf (printf)
import Message (Action (..))

handleInterpretToPoint :: Handlers ServerM
handleInterpretToPoint = requestHandler (SCustomMethod "$/interpretToPoint") doInterp

doInterp ::
  RequestMessage 'CustomMethod ->
  (Either ResponseError Aeson.Value -> ServerM ()) ->
  ServerM ()
doInterp request responder =
  do
    info "doInterp" "Interpreting script"
    interpParams <- liftEither (fromParams (request ^. LSP.params))

    fileStmts <- resolve (uri interpParams)
    truncatedStmts <- truncateStmts (posn interpParams) fileStmts

    (matchedPrefix, _val, outM) <- undefined -- liftSAW (interpretSAWScript True truncatedStmts)
    -- inform' $ printf "Reusing prior execution of %i statements" matchedPrefix

    let goal = fromMaybe "<no goal>" outM
    displayGoal goal

resolve :: Uri -> ServerM [Stmt]
resolve uri =
  do
    vfM <- getVirtualFile (toNormalizedUri uri)
    vf <- liftMaybe (internalError "file not found") vfM
    let fileText = virtualFileText vf
        filePath = fromMaybe "<no path>" (uriToFilePath uri)
    liftEither (first (internalError . Text.pack) (parseSAWFile filePath fileText))

truncateStmts :: Position -> [Stmt] -> ServerM (NonEmpty Stmt)
truncateStmts position fileStmts =
  do
    uuid <- liftIO UUID.nextRandom
    let truncatedStmts = truncateScript position (show uuid) fileStmts
    inform' $
      printf
        "Truncating %i statements to %i statements"
        (length fileStmts)
        (length truncatedStmts)
    case truncatedStmts of
      [] ->
        let msg = "Cannot interpret empty script"
         in warn msg >> throwM (internalError msg)
      (stmt : stmts) ->
        pure (stmt :| stmts)

displayGoal :: String -> ServerM ()
displayGoal goal =
  do
    goalFilePath <- liftIO $ writeSystemTempFile "lsp" goal
    let goalUri = filePathToUri goalFilePath
        externalApplication = Just False
        takeFocus = Just False
        highlight = Nothing -- Just (LSP.Range (LSP.Position 0 5) (LSP.Position 1 3))
        showDocParams = ShowDocumentParams goalUri externalApplication takeFocus highlight
    _ <- sendRequest (SCustomMethod "$/displayGoal") (Aeson.toJSON showDocParams) \case
      Left err -> debug "displayGoal" (show err)
      Right _ -> debug "displayGoal" "success"
    pure ()

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
