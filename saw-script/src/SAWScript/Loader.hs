{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.Loader
Description : Loading and parsing SAW-Script files.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

module SAWScript.Loader (
    readSchemaPure,
    readSchemaPattern,
    readExpression,
    readREPLTextUnchecked,
    findAndLoadFileUnchecked
  ) where

import qualified Data.Text.IO as TextIO (readFile)
import qualified Data.Text as Text
import Data.Text (Text)
--import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import System.Directory
import System.FilePath (normalise, takeDirectory)

import qualified SAWSupport.ScopedMap as ScopedMap
--import SAWSupport.ScopedMap (ScopedMap)

import SAWCentral.Position (Pos(..), getPos)
import qualified SAWCentral.Options as Options
import SAWCentral.Options (Options)
import SAWCentral.AST
import SAWCentral.Value (Environ(..), RebindableEnv)

import SAWScript.Panic (panic)
import SAWScript.Token (Token)
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser
import SAWScript.Include as Inc
import SAWScript.Typechecker (checkDecl, checkSchema, checkSchemaPattern)


-- | Type shorthand for an operation that can return warnings and/or
--   errors. On error it returns Left and a list of messages, at least
--   one of which is an error and therefore fatal. On success, it
--   returns a (possibly empty) list of messages, which are all
--   warnings and not fatal, and a result of type a.
type WithMsgs a = Either [Text] ([Text], a)

-- | The messages produced by the typechecker are pairs of position and
--   String. Convert to Text. XXX: the error infrastructure is supposed
--   to be what knows how to print source positions.
convertTypeMsg :: (Pos, String) -> Text
convertTypeMsg (pos, msg) =
    let pos' = Text.pack (show pos)
        msg' = Text.pack msg
    in
    pos' <> ": " <> msg'

-- | Type shorthand for an include path.
--
--   The LHS is the directory the current file was included from
--   (starts as ".") and the RHS is the user's search path.
type IncludePath = (FilePath, [FilePath])

-- | Wrap statements in a pushd/popd pair.
--
--   See the notes in the interpreter for why we do this.
--
--   FUTURE: if we keep this thing, it would be nice to attach the
--   source position of the include to the push and pop statements.
--
wrapDir :: FilePath -> WithMsgs [Stmt] -> WithMsgs [Stmt]
wrapDir dir result =
    case result of
        Left errs -> Left errs
        Right (msgs, stmts) ->
            let stmts' = 
                  let pos = PosInternal "pushd/popd derived from include" in
                  [StmtPushdir pos dir] ++ stmts ++ [StmtPopdir pos]
            in
            Right (msgs, stmts')

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
dispatchMsgs :: Options -> WithMsgs a -> IO (Either [Text] a)
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

-- | Run the readAny result through the `Include` module to resolve
--   @include@ statements.
--
--   If we fail after collecting warnings, print the warnings before
--   returning the failure.
--
resolveIncludes ::
    Int -> IncludePath -> Options -> Inc.Processor a -> WithMsgs a ->
    IO (WithMsgs a)
resolveIncludes depth incpath opts process result =
    let printMsg vrb msg =
          Options.printOutLn opts vrb (Text.unpack msg)
    in
    case result of
        Left errs ->
            pure $ Left errs
        Right (msgs, tree) -> do
            result' <- process (includeFile depth incpath opts) tree
            case result' of
                Left errs -> do
                    mapM_ (printMsg Options.Warn) msgs
                    pure $ Left errs
                Right tree' ->
                    pure $ Right (msgs, tree')

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
-- Note: there is no way to reach @include@ statements from type
-- schemas, so no need to process includes in what we read.
--
readSchemaPure ::
    FilePath ->
    PrimitiveLifecycle ->
    Map Name (PrimitiveLifecycle, NamedType) ->
    Text ->
    Schema
readSchemaPure fakeFileName lc tyenv str = do
    let result = readAny fakeFileName str parseSchema
    let result' = case result of
          Left errs -> Left errs
          Right (msgs, schema) ->
              let (errs_or_results, warns) = checkSchema lc tyenv schema
                  warns' = map convertTypeMsg warns
              in
              case errs_or_results of
                  Left errs -> Left (msgs ++ warns' ++ map convertTypeMsg errs)
                  Right () -> Right (msgs ++ warns', schema)
    panicOnMsgs (Text.pack fakeFileName) result'

-- | Read a schema pattern from a string. This is used by the
--   :search REPL command.
--
--   Also runs the typechecker to check the pattern.
--
-- Note: there is no way to reach @include@ statements from schema
-- patterns, so no need to process includes in what we read.
--
readSchemaPattern ::
    Options ->
    FilePath -> Environ -> RebindableEnv -> Set PrimitiveLifecycle -> Text ->
    IO (Either [Text] SchemaPattern)
readSchemaPattern opts fileName environ rbenv avail str = do
  let result = readAny fileName str parseSchemaPattern
  let result' = case result of
        Left errs -> Left errs
        Right (msgs, pat) ->
          let Environ varenv tyenv _cryenv = environ in

          -- XXX it should not be necessary to do this munging
          let squash (pos, lc, ty, _val, _doc) = (pos, lc, ReadOnlyVar, ty)
              varenv' = Map.map squash $ ScopedMap.flatten varenv
              tyenv' = ScopedMap.flatten tyenv
              rbsquash (pos, ty, _val) = (pos, Current, RebindableVar, ty)
              rbenv' = Map.map rbsquash rbenv
              varenv'' = Map.union varenv' rbenv'
          in
          let (errs_or_results, warns) = checkSchemaPattern avail varenv'' tyenv' pat
              warns' = map convertTypeMsg warns
          in
          case errs_or_results of
              Left errs -> Left (msgs ++ warns' ++ map convertTypeMsg errs)
              Right results -> Right (msgs ++ warns', results)
  dispatchMsgs opts result'

-- | Read an expression from a string. This is used by the
--   :type REPL command.
--
-- It is possible for someone to provide an expression that includes
-- an @include@ in a do-block, so just in case call into `Include`
-- to resolve any that appear.
--
readExpression ::
    Options ->
    FilePath -> Environ -> RebindableEnv -> Set PrimitiveLifecycle -> Text ->
    IO (Either [Text] (Schema, Expr))
readExpression opts fileName environ rbenv avail str = do
  let incpath = (".", Options.importPath opts)

  let result = readAny fileName str parseExpression
  result' <- resolveIncludes 0{-depth-} incpath opts Inc.processExpr result
  let result'' = case result' of
        Left errs -> Left errs
        Right (msgs, expr) ->
           let Environ varenv tyenv _cryenvs = environ in

           -- XXX it should not be necessary to do this munging
           let squash (defpos, lc, ty, _val, _doc) = (defpos, lc, ReadOnlyVar, ty)
               varenv' = Map.map squash $ ScopedMap.flatten varenv
               tyenv' = ScopedMap.flatten tyenv
               rbsquash (defpos, ty, _val) = (defpos, Current, RebindableVar, ty)
               rbenv' = Map.map rbsquash rbenv
               varenv'' = Map.union varenv' rbenv'
           in
           -- XXX: also it shouldn't be necessary to do this wrappery
           let pos = getPos expr
               decl = Decl pos (PWild pos Nothing) Nothing expr
           in
           let (errs_or_results, warns) = checkDecl avail varenv'' tyenv' decl
               warns' = map convertTypeMsg warns
           in
           case errs_or_results of
               Left errs -> Left (msgs ++ warns' ++ map convertTypeMsg errs)
               Right decl' ->
                   let expr' = dDef decl'
                       schema = case dType decl' of
                         Just sch -> sch
                         Nothing ->
                             -- If the typechecker didn't insert a type, it's bust,
                             -- so panic. Not much point in printing the expression
                             -- or position in panic, since it's what the user just
                             -- typed.
                             panic "readExpressionChecked" [
                                 "Typechecker failed to produce a type"
                             ]
                   in
                   Right (msgs ++ warns', (schema, expr'))
  dispatchMsgs opts result''

-- | Read a statement from a string. This is used by the REPL evaluator.
--   Doesn't run the typechecker (yet).
--
--   May produce more than one statement if the statement given is an
--   @include@.
readREPLTextUnchecked :: Options -> FilePath -> Text -> IO (Either [Text] [Stmt])
readREPLTextUnchecked opts fileName str = do
  let incpath = (".", Options.importPath opts)

  let result = readAny fileName str parseREPLText
  result' <- resolveIncludes 0{-depth-} incpath opts Inc.processStmts result
  dispatchMsgs opts result'

-- | Find a file, potentially looking in a list of multiple search paths (as
-- specified via the @SAW_IMPORT_PATH@ environment variable or
-- @-i@/@--import-path@ command-line options). If the file was successfully
-- found, return the full path. If not, fail by returning `Left`.
--
locateFile :: IncludePath -> FilePath -> IO (Either [Text] FilePath)
locateFile (current, rawdirs) file = do
  -- Replace "." in the search path with the directory the current
  -- file came from, which might or might not be ".".
  let dirs = map adjust rawdirs
      adjust "." = current
      adjust dir = dir

  mfname <- findFile dirs file
  case mfname of
    Nothing -> do
        let msgs = [
                "Couldn't find file: " <> Text.pack file,
                "  Searched in directories:"
             ] ++ map (\p -> "    " <> Text.pack p) dirs
        return $ Left msgs
    Just fname ->
      -- NB: Normalise the path name. The default SAW_IMPORT_PATH contains ".",
      -- and the behavior of filepath's 'normalise' function is to prepend a
      -- search path to the front of the file path that is found, which can
      -- cause paths like "./foo.saw" to be returned. This looks ugly in error
      -- messages, where we would rather display "foo.saw" instead.
      return $ Right (normalise fname)

-- | Load the 'Stmt's in a @.saw@ file.
--   Doesn't run the typechecker (yet).
includeFile :: Int -> IncludePath -> Options -> FilePath ->
    IO (Either [Text] [Stmt])
includeFile depth incpath opts fname = do
  result <- locateFile incpath fname
  case result of
    Left errs -> return $ Left errs
    Right fname' ->
      if depth > 128 then
          pure $ Left ["Maximum include depth exceeded"]
      else do
          let (_current, dirs) = incpath
              current' = takeDirectory fname'
              incpath' = (current', dirs)

          Options.printOutLn opts Options.Info $ "Loading file " ++ show fname'
          ftext <- TextIO.readFile fname'

          let result' = wrapDir current' $ readAny fname ftext parseModule
          result'' <- resolveIncludes (depth + 1) incpath' opts Inc.processStmts result'
          dispatchMsgs opts result''

-- | Find a file, potentially looking in a list of multiple search paths (as
-- specified via the @SAW_IMPORT_PATH@ environment variable or
-- @-i@/@--import-path@ command-line options). If the file was successfully
-- found, load it. If not, fail by returning `Left`.
--
-- Doesn't run the typechecker (yet).
findAndLoadFileUnchecked :: Options -> FilePath -> IO (Either [Text] [Stmt])
findAndLoadFileUnchecked opts fp =
  let incpath = (".", Options.importPath opts) in
  includeFile 0{-depth-} incpath opts fp
