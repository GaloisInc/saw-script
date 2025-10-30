{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.Import
Description : Loading and parsing SAW-Script files.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

module SAWScript.Import (
    readSchemaPure,
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
import qualified SAWCentral.Options as Options

import SAWScript.Panic (panic)
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser
import SAWScript.Token (Token)


-- | Type shorthand for an operation that can return warnings and/or
--   errors. On error it returns Left and a list of messages, at least
--   one of which is an error and therefore fatal. On success, it
--   returns a (possibly empty) list of messages, which are all
--   warnings and not fatal, and a result of type a.
type WithMsgs a = Either [Text] ([Text], a)

-- | Read some SAWScript text, using the selected parser entry point.
--
--   Returns only in Either; caller is responsible for handling the
--   resulting warnings and errors.
--
--   The FilePath argument is the name of the file the text comes
--   from. If the text didn't come from a file, it should have a
--   suitable placeholder string; that's what ends up in the source
--   positions in the results.
--
readAny :: FilePath -> Text.Text -> ([Token Pos] -> Either ParseError a) -> WithMsgs a
readAny fileName str parser =
    -- XXX printing of positions properly belongs to the
    -- message-printing infrastructure.
    let positionMsg pos msg =
          Text.pack (show pos) <> ": " <> msg
    in
    case lexSAW fileName str of
        Left (_verbosity, pos, msg) ->
            Left [positionMsg pos msg]
        Right (tokens, optmsg) ->
            let msgs = case optmsg of
                  Nothing -> []
                  Just (Options.Error, _, _) ->
                      panic "readAny" ["Lexer returned an error in the warning slot"]
                  Just (_verbosity, pos, msg) ->
                      [positionMsg pos msg]
            in
            case parser tokens of
                Left err ->
                    let err' = Text.pack (show err) in
                    Left (msgs ++ [err'])
                Right tree ->
                    -- Note: there's no such things as warnings in a
                    -- Happy parser, so there are no more messages to
                    -- add in this branch.
                    Right (msgs, tree)

-- | Use the readAny result to panic if any messages were generated.
panicOnMsgs :: Text -> WithMsgs a -> a
panicOnMsgs whoAmI result = case result of
   Left errs ->
       panic whoAmI ("Unexpected errors:" : errs)
   Right ([], tree) ->
       tree
   Right (warns, _) ->
       panic whoAmI ("Unexpected warnings:" : warns)

-- | Handle the readAny result in IO.
--
--   Also return in Either, to be consistent with the current interface
--   into this file. Prints any warnings, and return just errors or a
--   result.
--
dispatchMsgs :: Options.Options -> WithMsgs a -> IO (Either [Text] a)
dispatchMsgs opts result =
    let printMsg vrb msg =
          Options.printOutLn opts vrb (Text.unpack msg)
    in
    case result of
        Left errs ->
            pure $ Left errs
        Right (msgs, tree) -> do
            mapM_ (printMsg Options.Warn) msgs
            pure $ Right tree

-- | Read a type schema from a string. This is used to digest the type
--   signatures for builtins, and the expansions for builtin typedefs.
--
-- Pure function that panics on any error or warning. This is
-- appropriate since we use it only to handle the builtins; any
-- glitches there are properly panics.
--
-- The first argument (fileName) is a string to pass as the
-- filename for the lexer, which (complete with line and column
-- numbering of dubious value) will go into the positions of the
-- elements of the resulting type.
--
-- The fake file name names the builtin object involved, so we'll also
-- use it as the panic location string if we need to panic.
--
-- FUTURE: we should figure out how to generate more meaningful
-- positions (like "third argument of concat") but this at least
-- allows telling the user which builtin the type came from.
--
readSchemaPure :: FilePath -> Text -> Schema
readSchemaPure fakeFileName str =
    panicOnMsgs (Text.pack fakeFileName) $ readAny fakeFileName str parseSchema

-- | Read a schema pattern from a string. This is used by the
--   :search REPL command.
--
readSchemaPattern :: FilePath -> Text -> IO (Either [Text] SchemaPattern)
readSchemaPattern fileName str = do
  -- XXX: this preserves the original behavior of ignoring the
  -- verbosity setting. We could expect the caller to pass in the
  -- options value to get the verbosity setting, and that's really
  -- the right thing to do; except that current plans are to get
  -- rid of that verbosity setting in the near future anyway.
  let opts = Options.defaultOptions

  let result = readAny fileName str parseSchemaPattern
  dispatchMsgs opts result

-- | Read an expression from a string. This is used by the
--   :type REPL command.
readExpression :: FilePath -> Text -> IO (Either [Text] Expr)
readExpression fileName str = do
  -- XXX as above
  let opts = Options.defaultOptions

  let result = readAny fileName str parseExpression
  dispatchMsgs opts result

-- | Read a statement from a string. This is used by the REPL evaluator.
readStmtSemi :: FilePath -> Text -> IO (Either [Text] Stmt)
readStmtSemi fileName str = do
  -- XXX as above
  let opts = Options.defaultOptions

  let result = readAny fileName str parseStmtSemi
  dispatchMsgs opts result

-- | Load the 'Stmt's in a @.saw@ file.
loadFile :: Options.Options -> FilePath -> IO (Either [Text] [Stmt])
loadFile opts fname = do
  Options.printOutLn opts Options.Info $ "Loading file " ++ show fname
  ftext <- TextIO.readFile fname

  let result = readAny fname ftext parseModule
  dispatchMsgs opts result

-- | Find a file, potentially looking in a list of multiple search paths (as
-- specified via the @SAW_IMPORT_PATH@ environment variable or
-- @-i@/@--import-path@ command-line options). If the file was successfully
-- found, load it. If not, raise an error.
findAndLoadFile :: Options.Options -> FilePath -> IO (Either [Text] [Stmt])
findAndLoadFile opts fp = do
  let paths = Options.importPath opts
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
