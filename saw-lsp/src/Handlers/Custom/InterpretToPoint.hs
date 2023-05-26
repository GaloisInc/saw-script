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
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Error (internalError)
import Language.LSP.Server
import Language.LSP.Types
  ( MessageType (..),
    Method (..),
    NormalizedUri,
    RequestMessage,
    ResponseError,
    SMethod (..),
    ShowDocumentParams (ShowDocumentParams),
    ShowDocumentResult (ShowDocumentResult),
    ShowMessageParams (ShowMessageParams),
    Uri,
    filePathToUri,
    toNormalizedUri,
  )
import Language.LSP.Types.Lens qualified as LSP
import Language.LSP.VFS (VirtualFile, virtualFileText)
import Monad
import SAWScript.AST (Expr (..), Located (..), Pattern (..), Stmt (..), prettyWholeModule)
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser (parseModule)
import SAWScript.Position (Pos (..), getPos)
import SAWT (emptySAWEnv, flushOutput, runSAWStmt)
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

-- Include absolute offset?
data Position = Position
  { line :: Int,
    character :: Int
  }
  deriving (Show)

instance Aeson.FromJSON Position where
  parseJSON = Aeson.withObject "Position" \v ->
    Position <$> v .: "line" <*> v .: "character"

handleInterpretToPoint :: Handlers ServerM
handleInterpretToPoint = requestHandler (SCustomMethod "$/interpretToPoint") doInterp

doInterp ::
  RequestMessage 'CustomMethod ->
  (Either ResponseError Aeson.Value -> ServerM ()) ->
  ServerM ()
doInterp request responder =
  do
    debug "doInterp"
    interpParams <- liftEither (fromParams ps)
    debug' (show interpParams)
    fileText <- virtualFileText <$> resolveUri (toNormalizedUri (uri interpParams))
    fileStmts <- liftEither (first (internalError . Text.pack) (parseFile fileText))
    let Position l c = posn interpParams
        mark = Position (l + 1) (c + 1)
        var v = Var (Located v "" Unknown)
        printGoal = StmtBind Unknown (PWild Nothing) Nothing (var "print_goal")
        admit = StmtBind Unknown (PWild Nothing) Nothing (Application (var "admit") (String "TODO"))
        fileStmts' = truncateAfterPointWith [printGoal, admit] mark fileStmts
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
    liftSAW emptySAWEnv
    liftSAW (mapM_ runSAWStmt fileStmts')
    ss <- liftSAW flushOutput
    let goal = ss !! 1
    goalFile <- liftIO $ writeSystemTempFile "lsp" goal
    let goalUri = filePathToUri goalFile
        externalApplication = Just False
        takeFocus = Just False
        highlight = Nothing -- Just (LSP.Range (LSP.Position 0 5) (LSP.Position 1 3))
        showDocParams = ShowDocumentParams goalUri externalApplication takeFocus highlight
    _ <- sendRequest SWindowShowDocument showDocParams \case
      Left err -> debug' (show err)
      Right (ShowDocumentResult r) -> if r then pure () else debug "client failed"
    _ <- sendRequest (SCustomMethod "$/displayGoal") (Aeson.toJSON showDocParams) \case
      Left err -> debug "error"
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

truncateAfterPointWith :: [Stmt] -> Position -> [Stmt] -> [Stmt]
truncateAfterPointWith additions mark = mapMaybe (truncateStmtWith additions mark)

truncateStmtWith :: [Stmt] -> Position -> Stmt -> Maybe Stmt
truncateStmtWith additions mark stmt
  | pos `endsBefore` mark = Just stmt
  | pos `startsAfter` mark = Nothing
  | otherwise =
      case stmt of
        StmtBind posn pat ty e -> StmtBind posn pat ty <$> truncateLExprWith additions mark e
        _ -> undefined
  where
    pos = getPos stmt

truncateLExprWith :: [Stmt] -> Position -> Expr -> Maybe Expr
truncateLExprWith additions mark expr =
  case expr of
    LExpr pos e
      | pos `endsBefore` mark -> Just expr
      | pos `startsAfter` mark -> Nothing
      | otherwise -> LExpr pos <$> truncateOverlappingExprWith additions mark e
    _ -> Nothing

truncateOverlappingExprWith :: [Stmt] -> Position -> Expr -> Maybe Expr
truncateOverlappingExprWith additions mark expr =
  case expr of
    Bool _ -> Just expr
    String _ -> Just expr
    Int _ -> Just expr
    Code _ -> Just expr
    CType _ -> Just expr
    Array es -> Just (Array (mapMaybe goExpr es)) -- TODO
    Block ss -> Just (Block (mapMaybe goStmt ss <> additions))
    Tuple es -> Just expr -- TODO
    Record binds -> Just expr
    Index a i -> Just expr
    Lookup e n -> Just expr
    TLookup e i -> Just expr
    Var _ -> Just expr
    Function pat e -> Just expr
    Application e1 e2 -> Application <$> goExpr e1 <*> goExpr e2
    Let d e -> Just expr
    TSig e ty -> Just expr
    IfThenElse c t f -> Just expr
    LExpr p e -> truncateLExprWith additions mark expr
  where
    goExpr = truncateOverlappingExprWith additions mark
    goStmt = truncateStmtWith additions mark

startsAfter :: Pos -> Position -> Bool
startsAfter reference Position {..} =
  case reference of
    Range _ refStartLine refStartCol _ _ ->
      case refStartLine `compare` line of
        LT -> False
        EQ -> refStartCol >= character
        GT -> True
    _ -> False

endsBefore :: Pos -> Position -> Bool
endsBefore pos Position {..} =
  case pos of
    Range _ _ _ refEndLine refEndCol ->
      case refEndLine `compare` line of
        LT -> True
        EQ -> refEndCol <= character
        GT -> False
    _ -> False

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