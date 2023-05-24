{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}

module Handlers.Custom.InterpretToPoint where

import Control.Applicative ((<|>))
import Control.Lens ((^.))
import Data.Aeson qualified as Aeson
import Data.Aeson.Types (parseEither)
import Data.Bifunctor (first)
import Data.Maybe (fromJust, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Error (internalError)
import Language.LSP.Server
import Language.LSP.Types
  ( MessageType (MtError),
    Method (CustomMethod),
    NormalizedUri,
    RequestMessage,
    ResponseError,
    SMethod (SCustomMethod, SWindowShowMessage),
    ShowMessageParams (ShowMessageParams),
    toNormalizedUri,
  )
import Language.LSP.Types.Lens qualified as LSP
import Language.LSP.VFS (VirtualFile, virtualFileText)
import Monad
import SAW (InterpretParams (..), Position (..))
import SAWScript.AST (Expr (..), Located (..), Pattern (..), Stmt (..), prettyWholeModule)
import SAWScript.Interpreter (interpretStmt)
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser (parseModule)
import SAWScript.Position (Pos (..), getPos)
import SAWScript.Value (TopLevel)
import SAWT (flushOutput, liftTopLevel, runSAWStmt, emptySAWEnv)

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
         in sendNotification SWindowShowMessage (ShowMessageParams MtError msg)
      stmts ->
        do
          let orig = show (length fileStmts)
              new = show (length stmts)
              msg = Text.pack $ "would truncate " <> orig <> " statements to " <> new <> " statements"
          debug' (show (prettyWholeModule stmts))
          sendNotification SWindowShowMessage (ShowMessageParams MtError msg)
    liftSAW emptySAWEnv
    liftSAW (mapM_ runSAWStmt fileStmts')
    ss <- liftSAW flushOutput
    let goal = last ss
    debug' goal
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
    Block ss -> Just $
      Block $
        case length (mapMaybe goStmt ss) of
          0 -> additions
          n
            | n == length ss -> ss
            | otherwise -> ss <> additions
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
fromParams v = first (internalError . Text.pack) (parseEither Aeson.parseJSON v)

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