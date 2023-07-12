{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}

module Handlers.Custom.InterpretToPoint where

import Control.Lens ((^.))
import Control.Monad.Cont (MonadIO (liftIO))
import Data.Aeson ((.:))
import Data.Aeson qualified as Aeson
import Data.Aeson.Types qualified as Aeson
import Data.Bifunctor (first)
import Data.Text (Text)
import Data.Text qualified as Text
import Error (internalError)
import Handlers.Custom.InterpretToPoint.Truncate
import Language.LSP.Server
import Language.LSP.Types
  ( MessageType (..),
    Method (..),
    NormalizedUri,
    RequestMessage,
    ResponseError,
    SMethod (..),
    ShowDocumentParams (ShowDocumentParams),
    ShowMessageParams (ShowMessageParams),
    Uri,
    filePathToUri,
    toNormalizedUri,
  )
import Language.LSP.Types.Lens qualified as LSP
import Language.LSP.VFS (VirtualFile, virtualFileText)
import Monad
import SAWScript.AST (Stmt (..), prettyWholeModule)
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser (parseModule)
import SAWT (drainSAWEnv, flushOutput, runStmt, runStmtCheckpoint)
import System.IO.Temp (writeSystemTempFile)

data InterpretParams = InterpretParams
  { posn :: Position,
    offset :: Int,
    uri :: Uri
  }
  deriving (Show)

instance Aeson.FromJSON InterpretParams where
  parseJSON = Aeson.withObject "InterpretParams" \v ->
    InterpretParams <$> v .: "posn" <*> v .: "offset" <*> v .: "uri"

handleInterpretToPoint :: Handlers ServerM
handleInterpretToPoint = requestHandler (SCustomMethod "$/interpretToPoint") doInterp

doInterp ::
  RequestMessage 'CustomMethod ->
  (Either ResponseError Aeson.Value -> ServerM ()) ->
  ServerM ()
doInterp request responder =
  do
    -- debug "doInterp"
    interpParams <- liftEither (fromParams ps)
    -- debug' (show interpParams)
    fileText <- virtualFileText <$> resolveUri (toNormalizedUri (uri interpParams))
    fileStmts <- liftEither (first (internalError . Text.pack) (parseFile fileText))
    let fileStmts' = truncateScript (posn interpParams) fileStmts
    case fileStmts' of
      [] ->
        let msg = Text.pack $ "would truncate all " <> show (length fileStmts) <> " statements"
         in sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)
      stmts ->
        do
          let orig = show (length fileStmts)
              new = show (length stmts)
              msg = Text.pack $ "would truncate " <> orig <> " statements to " <> new <> " statements"
          debug' (show (prettyWholeModule stmts))
          sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)
    liftSAW drainSAWEnv
    hits <- mapM (liftSAW . runStmtCheckpoint) fileStmts'
    debug' (show hits)
    -- liftSAW (mapM_ runStmt fileStmts')
    ss <- liftSAW flushOutput
    let goal = ss !! 1
    goalFile <- liftIO $ writeSystemTempFile "lsp" goal
    let goalUri = filePathToUri goalFile
        externalApplication = Just False
        takeFocus = Just False
        highlight = Nothing -- Just (LSP.Range (LSP.Position 0 5) (LSP.Position 1 3))
        showDocParams = ShowDocumentParams goalUri externalApplication takeFocus highlight
    _ <- sendRequest (SCustomMethod "$/displayGoal") (Aeson.toJSON showDocParams) \case
      Left err -> debug' (show err)
      Right _ -> debug "success"
    pure ()
  where
    ps = request ^. LSP.params

resolveUri :: NormalizedUri -> ServerM VirtualFile
resolveUri uri =
  do
    vfM <- getVirtualFile uri
    liftMaybe (internalError "file not found") vfM

parseFile :: Text -> Either String [Stmt]
parseFile text =
  do
    let lexed = lexSAW "TODO" (Text.unpack text)
    first show (parseModule lexed)

fromParams :: Aeson.Value -> Either ResponseError InterpretParams
fromParams v = first (internalError . Text.pack) (Aeson.parseEither Aeson.parseJSON v)

{-
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
-}
