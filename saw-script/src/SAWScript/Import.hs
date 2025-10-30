{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.Import
Description : Loading and parsing SAW-Script files.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

module SAWScript.Import (
    readSchema,
    readSchemaPattern,
    readStmtSemi,
    readExpression,
    findAndLoadFile
  ) where

import qualified Data.Text.IO as TextIO (readFile)
import qualified Data.Text as Text
import Data.Text (Text)
import System.Directory
import System.FilePath (normalise)

import SAWCentral.Position (Pos)
import SAWCentral.AST
import SAWCentral.Options

import SAWScript.Panic (panic)
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser
import SAWScript.Token (Token)

lexSAW' :: FilePath -> Text.Text -> IO [Token Pos]
lexSAW' fileName str = do
  -- XXX wrap printing of positions in the message-printing infrastructure
  case lexSAW fileName str of
    Left (_, pos, msg) ->
         fail $ show pos ++ ": " ++ Text.unpack msg
    Right (tokens', Nothing) -> pure tokens'
    Right (_, Just (SAWCentral.Options.Error, pos, msg)) ->
         fail $ show pos ++ ": " ++ Text.unpack msg
    Right (tokens', Just _) -> pure tokens'

-- | Read a type schema from a string. This is used to digest the type
-- signatures for builtins, and the expansions for builtin typedefs.
--
-- The first argument (fakeFileName) is a string to pass as the
-- filename for the lexer, which (complete with line and column
-- numbering of dubious value) will go into the positions of the
-- elements of the resulting type.
--
-- FUTURE: we should figure out how to generate more meaningful
-- positions (like "third argument of concat") but this at least
-- allows telling the user which builtin the type came from.
--
readSchema :: FilePath -> Text -> Schema
readSchema fakeFileName str =
  let croak what msg =
        error (what ++ " error in builtin " ++ Text.unpack str ++ ": " ++ msg)
      tokens =
        -- XXX clean this up when we clean out the message printing infrastructure
        case lexSAW fakeFileName str of
          Left (_, _, msg) -> croak "Lexer" $ Text.unpack msg
          Right (tokens', Nothing) -> tokens'
          Right (_      , Just (Error, _pos, msg)) -> croak "Lexer" $ Text.unpack msg
          Right (tokens', Just (_, _pos, _msg)) -> tokens'
  in
  case parseSchema tokens of
    Left err -> croak "Parse" $ show err
    Right schema -> schema

-- | Read a schema pattern from a string. This is used by the
--   :search REPL command.
--
readSchemaPattern :: FilePath -> Text -> IO (Either [Text] SchemaPattern)
readSchemaPattern fakeFileName str = do
  tokens <- lexSAW' fakeFileName str
  let result = case parseSchemaPattern tokens of
        Left err -> Left [Text.pack $ show err]
        Right pat -> Right pat
  pure result

-- | Read an expression from a string. This is used by the
--   :type REPL command.
readExpression :: FilePath -> Text -> IO (Either [Text] Expr)
readExpression fakeFileName str = do
  tokens <- lexSAW' fakeFileName str
  let result = case parseExpression tokens of
        Left err -> Left [Text.pack $ show err]
        Right e -> Right e
  pure result

-- | Read a statement from a string. This is used by the REPL evaluator.
readStmtSemi :: FilePath -> Text -> IO (Either [Text] Stmt)
readStmtSemi fakeFileName str = do
  tokens <- lexSAW' fakeFileName str
  let result = case parseStmtSemi tokens of
        Left err -> Left [Text.pack $ show err]
        Right s -> Right s
  pure result

parseFile :: [Token Pos] -> Either ParseError [Stmt]
parseFile tokens = do
  case parseModule tokens of
    Left err -> Left err
    Right stmts -> Right stmts

-- | Load the 'Stmt's in a @.saw@ file.
loadFile :: Options -> FilePath -> IO (Either [Text] [Stmt])
loadFile opts fname = do
  printOutLn opts Info $ "Loading file " ++ show fname
  ftext <- TextIO.readFile fname
  -- XXX: the print functions should take care of printing the position
  -- (clean this up when we clean out the printing infrastructure)
  -- XXX: the print functions should also take care of exiting on an
  -- error (immediately or later). For now, print warnings right away
  -- and return errors in Either.
  case lexSAW fname ftext of
    Left (_, pos, txt) -> do
      let txt' = Text.pack (show pos) <> ": " <> txt
      return $ Left [txt']
    Right (tokens, optmsg) -> do
      case optmsg of
        Nothing -> return ()
        -- The types make it possible to get an error back in the
        -- optmsg field. Panic if we do, because the lexer isn't
        -- supposed to do that, and currently does not.
        Just (Error, _, _) ->
          panic "loadFile" ["Lexer returned an error in the warning slot"]
        Just (vrb, pos, txt) -> do
          let txt' = show pos ++ ": " ++ Text.unpack txt
          printOutLn opts vrb txt'
      case parseFile tokens of
        Left err -> return $ Left [Text.pack $ show err]
        Right result -> return $ Right result

-- | Find a file, potentially looking in a list of multiple search paths (as
-- specified via the @SAW_IMPORT_PATH@ environment variable or
-- @-i@/@--import-path@ command-line options). If the file was successfully
-- found, load it. If not, raise an error.
findAndLoadFile :: Options -> FilePath -> IO (Either [Text] [Stmt])
findAndLoadFile opts fp = do
  let paths = importPath opts
  mfname <- findFile paths fp
  case mfname of
    Nothing -> do
        let msgs = [
                "Couldn't find file: " <> Text.pack fp,
                "  Searched in directories:"
             ] ++ map (\p -> "    " <> Text.pack p) paths
        return $ Left msgs
    Just fname ->
      -- NB: Normalise the path name. The default SAW_IMPORT_PATH contains ".",
      -- and the behavior of filepath's 'normalise' function is to prepend a
      -- search path to the front of the file path that is found, which can
      -- cause paths like "./foo.saw" to be returned. This looks ugly in error
      -- messages, where we would rather display "foo.saw" instead.
      loadFile opts (normalise fname)
