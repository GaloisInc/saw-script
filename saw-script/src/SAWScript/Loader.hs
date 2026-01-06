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
import qualified Data.IORef as IORef
import Data.IORef (IORef)
import Data.List (uncons)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
--import Data.Map (Map)
import System.Directory
import System.FilePath (normalise, takeDirectory)

import qualified Prettyprinter as PP

import qualified SAWSupport.ScopedMap as ScopedMap
import SAWSupport.ScopedMap (ScopedMap)
import qualified SAWSupport.Pretty as PPS
import qualified SAWSupport.Position as PosSupport
import qualified SAWSupport.Console as Cons

import qualified SAWCentral.Position as Pos
import SAWCentral.Position (Pos(..))
import qualified SAWCentral.Options as Options
import SAWCentral.Options (Options)
import SAWCentral.AST
import SAWCentral.Value (Environ(..), RebindableEnv)

import SAWScript.Panic (HasCallStack, panic)
import SAWScript.Token (Token, tokPos)
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser
import SAWScript.Include as Inc
import SAWScript.Typechecker (checkDecl, checkSchema, checkSchemaPattern)


-- | Type shorthand for an operation that can return warnings and/or
--   errors. On error it returns Left and a list of messages, at least
--   one of which is an error and therefore fatal. On success, it
--   returns a (possibly empty) list of messages, which are all
--   warnings and not fatal, and a result of type a.
--
--   The position is a Maybe because errors from the parser come back
--   with a position already stuffed into the message text, and we would
--   like to not print another vacuous one along with it.
--
--   The text is a Doc because we've improved the parser so it sometimes
--   prints tabular messages.
--
type WithMsgs a = Either [(Pos, PPS.Doc)] ([(Pos, PPS.Doc)], a)

-- | Type shorthand for an include path.
--
--   The LHS is the directory the current file was included from
--   (starts as ".") and the RHS is the user's search path.
type IncludePath = (FilePath, [FilePath])

-- | Type shorthand for the set of includes already seen.
--
--   We pass it around as an IORef because it needs to accumulate
--   as we go.
type SeenSet = IORef (Set FilePath)

-- | Construct an empty SeenSet.
emptySeenSet :: IO SeenSet
emptySeenSet = IORef.newIORef Set.empty

-- | Check for membership in a SeenSet.
seenSetMember :: FilePath -> SeenSet -> IO Bool
seenSetMember x ref = do
    set <- IORef.readIORef ref
    pure $ Set.member x set

-- | Insert into a SeenSet.
seenSetInsert :: FilePath -> SeenSet -> IO ()
seenSetInsert x ref = do
    set <- IORef.readIORef ref
    IORef.writeIORef ref (Set.insert x set)
    pure ()

-- | Wrap statements in a pushd/popd pair.
--
--   See the notes in the interpreter for why we do this.
--
--   FUTURE: if we keep this thing, it would be nice to attach the
--   source position of the include to the push and pop statements.
--
wrapDir :: FilePath -> IO [Stmt] -> IO [Stmt]
wrapDir dir m = do
    stmts <- m
    let pos = PosInternal "pushd/popd derived from include"
    pure $ [StmtPushdir pos dir] ++ stmts ++ [StmtPopdir pos]

-- | Read some SAWScript text, using the selected parser entry point.
--
--   Returns only in Either; caller is responsible for handling the
--   resulting warnings and errors. We need it to be this way because
--   processing the builtin table at startup has to be pure.
--
--   The FilePath argument is the name of the file the text comes
--   from. If the text didn't come from a file, it should have a
--   suitable placeholder string; that's what ends up in the source
--   positions in the results.
--
--   The second text argument (which goes with the parser function) is
--   the EOF token name passed to `prettyParseError`, which should
--   generally be either "end of line" or "end of file".
--
readAny :: FilePath -> Text -> Text -> ([Token Pos] -> Either ParseError a) -> WithMsgs a
readAny fileName str eofName parser =
    case lexSAW fileName str of
        Left (_verbosity, pos, msg) ->
            Left [(pos, PP.pretty msg)]
        Right (tokens, optmsg) ->
            let msgs = case optmsg of
                  Nothing -> []
                  Just (Options.Error, _, _) ->
                      panic "readAny" ["Lexer returned an error in the warning slot"]
                  Just (_verbosity, pos, msg) ->
                      [(pos, PP.pretty msg)]
            in
            case parser tokens of
                Left err ->
                    let (optpos, err') = prettyParseError eofName err
                        pos = case optpos of
                            Nothing ->
                                -- Happy is unable to provide the
                                -- position of an error at EOF. Here
                                -- we have the input token list, so we
                                -- can pick up after it. Use the
                                -- trailing edge of the last token.
                                case uncons (reverse tokens) of
                                    Nothing ->
                                        Range fileName 1 1 1 1
                                    Just (t, _) ->
                                        Pos.trailingPos $ tokPos t
                            Just p ->
                                p
                    in
                    Left (msgs ++ [(pos, err')])
                Right tree ->
                    -- Note: there's no such things as warnings in a
                    -- Happy parser, so there are no more messages to
                    -- add in this branch.
                    Right (msgs, tree)

-- | Use the readAny result to panic if any messages were generated.
panicOnMsgs :: Text -> WithMsgs a -> a
panicOnMsgs whoAmI result =
  -- Properly, printing the positions with the errors should be done
  -- by the error infrastructure. However, the error infrastructure
  -- necessarily needs to run in `IO`, and we need to _not_ run in
  -- `IO` here because we're part of initializing the builtins table.
  -- Do it by hand instead. I don't think it's worth adding extra
  -- stuff to SAWConsole just to avoid needing this code.
  let pp (pos, msg) =
        let msg' = PP.pretty (PosSupport.ppPosition pos) <> ":" PP.<+> msg in
        PPS.renderText PPS.defaultOpts msg'
  in
  case result of
   Left errs ->
       panic whoAmI ("Unexpected errors:" : map pp errs)
   Right ([], tree) ->
       tree
   Right (warns, _) ->
       panic whoAmI ("Unexpected warnings:" : map pp warns)

-- | Like `panicOnMsgs` but for typechecker results. XXX: the
--   typechecker should issue its own messages; if not, it at least
--   shouldn't be arbitrarily different.
panicOnMsgs' :: Text -> (Either [(Pos, String)] a, [(Pos, String)]) -> a
panicOnMsgs' whoAmI (errs_or_results, warns) =
    let pp (pos, msg) =
          PosSupport.ppPosition pos <> ": " <> Text.pack msg
    in
    case warns of
        [] -> case errs_or_results of
            Left errs -> panic whoAmI ("Unexpected errors: " : map pp errs)
            Right result -> result
        _ -> panic whoAmI ("Unexpected warnings: " : map pp warns)

-- | Handle the readAny result in IO.
--
--   Add HasCallStack because if the panic happens we'll want to know
--   where we came from. XXX: figure out how to get rid of the panic
--   and remove HasCallStack again.
dispatchMsgs :: HasCallStack => WithMsgs a -> IO a
dispatchMsgs result =
    case result of
        Left errs -> do
            let pp (pos, msg) = Cons.errDP' pos msg
            mapM_ pp errs
            Cons.checkFail
            panic "dispatchMsgs" ["checkFail didn't fail"]
        Right (msgs, tree) -> do
            let pp (pos, msg) = Cons.warnP' pos msg
            mapM_ pp msgs
            pure tree

-- | Handle a typechecker result in IO.
--
--   Add HasCallStack because if the panic happens we'll want to know
--   where we came from. XXX: figure out how to get rid of the panic
--   and remove HasCallStack again.
dispatchMsgs' :: HasCallStack => (Either [(Pos, String)] a, [(Pos, String)]) -> IO a
dispatchMsgs' (errs_or_result, warns) = do
    mapM_ (\(pos, msg) -> Cons.warnP pos $ Text.pack msg) warns
    case errs_or_result of
        Left errs -> do
            mapM_ (\(pos, msg) -> Cons.errDP pos $ Text.pack msg) errs
            Cons.checkFail
            panic "dispatchMsgs'" ["checkFail didn't fail"]
        Right tree ->
            pure tree

-- | Call `readAny` then `panicOnMsgs`.
readAnyPure :: FilePath -> Text -> Text -> ([Token Pos] -> Either ParseError a) -> Text -> a
readAnyPure fileName str eofName parser whoAmI =
    panicOnMsgs whoAmI $ readAny fileName str eofName parser

-- | Call `readAny` then `dispatchMsgs`.
readAnyIO :: FilePath -> Text -> Text -> ([Token Pos] -> Either ParseError a) -> IO a
readAnyIO fileName str eofName parser =
    dispatchMsgs $ readAny fileName str eofName parser

-- | Run the readAny result through the `Include` module to resolve
--   @include@ statements.
--
--   If we fail after collecting warnings, print the warnings before
--   returning the failure.
--
resolveIncludes ::
    Int -> SeenSet -> IncludePath -> Options -> Inc.Processor a -> a -> IO a
resolveIncludes depth seen incpath opts process tree =
    process (includeFile depth seen incpath opts) tree

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
    ScopedMap Name (PrimitiveLifecycle, NamedType) ->
    Text ->
    Schema
readSchemaPure fakeFileName lc tyenv str =
    let schema = readAnyPure fakeFileName str "end of input" parseSchema (Text.pack fakeFileName) in
    panicOnMsgs' (Text.pack fakeFileName) $ checkSchema lc tyenv schema

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
    IO SchemaPattern
readSchemaPattern _opts fileName environ rbenv avail str = do
  pat <- readAnyIO fileName str "end of line" parseSchemaPattern
  let Environ varenv tyenv _cryenv = environ

  -- XXX it should not be necessary to do this munging
  --
  -- Note that we need to flatten the scopes we have here
  -- (outside the typechecker) in order to have the union with
  -- the rebindable env to work right.
  let squash (pos, lc, ty, _val, _doc) = (pos, lc, ReadOnlyVar, ty)
      varenv' = Map.map squash $ ScopedMap.flatten varenv
      rbsquash (pos, ty, _val) = (pos, Current, RebindableVar, ty)
      rbenv' = Map.map rbsquash rbenv
      varenv'' = Map.union varenv' rbenv'
      varenv''' = ScopedMap.seed varenv''

  dispatchMsgs' $ checkSchemaPattern avail varenv''' tyenv pat

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
    IO (Schema, Expr)
readExpression opts fileName environ rbenv avail str = do
  seen <- emptySeenSet
  let incpath = (".", Options.importPath opts)

  expr0 <- readAnyIO fileName str "end of line" parseExpression
  expr <- resolveIncludes 0{-depth-} seen incpath opts Inc.processExpr expr0
  let Environ varenv tyenv _cryenvs = environ

  -- XXX it should not be necessary to do this munging
  let squash (defpos, lc, ty, _val, _doc) = (defpos, lc, ReadOnlyVar, ty)
      varenv' = Map.map squash $ ScopedMap.flatten varenv
      rbsquash (defpos, ty, _val) = (defpos, Current, RebindableVar, ty)
      rbenv' = Map.map rbsquash rbenv
      varenv'' = Map.union varenv' rbenv'
      varenv''' = ScopedMap.seed varenv''

  -- XXX: also it shouldn't be necessary to do this wrappery
  let pos = Pos.getPos expr
      decl = Decl pos (PWild pos Nothing) Nothing expr

  decl' <- dispatchMsgs' $ checkDecl avail varenv''' tyenv decl

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

  pure (schema, expr')

-- | Read statements from a string. This is used by the REPL evaluator.
--   Doesn't run the typechecker (yet).
--
--   May produce more than one statement if the statement given is an
--   @include@.
readREPLTextUnchecked :: Options -> FilePath -> Text -> IO [Stmt]
readREPLTextUnchecked opts fileName str = do
  seen <- emptySeenSet
  let incpath = (".", Options.importPath opts)

  stmts <- readAnyIO fileName str "end of line" parseREPLText
  resolveIncludes 0{-depth-} seen incpath opts Inc.processStmts stmts

-- | Find a file, potentially looking in a list of multiple search paths (as
-- specified via the @SAW_IMPORT_PATH@ environment variable or
-- @-i@/@--import-path@ command-line options). If the file was successfully
-- found, return the full path. If not, fail by returning `Left`.
--
locateFile :: IncludePath -> FilePath -> IO FilePath
locateFile (current, rawdirs) file = do
  -- Replace "." in the search path with the directory the current
  -- file came from, which might or might not be ".".
  let dirs = map adjust rawdirs
      adjust "." = current
      adjust dir = dir

  mfname <- findFile dirs file
  case mfname of
    Nothing -> do
        -- XXX make this a pp-doc instead
        let msg = Text.unlines ([
                      "Couldn't find file: " <> Text.pack file,
                      "  Searched in directories:"
                  ] ++ map (\p -> "    " <> Text.pack p) dirs)
        -- XXX pass in the include position
        Cons.errN msg
    Just fname ->
      -- NB: Normalise the path name. The default SAW_IMPORT_PATH contains ".",
      -- and the behavior of filepath's 'normalise' function is to prepend a
      -- search path to the front of the file path that is found, which can
      -- cause paths like "./foo.saw" to be returned. This looks ugly in error
      -- messages, where we would rather display "foo.saw" instead.
      return $ normalise fname

-- | Load the 'Stmt's in a @.saw@ file.
--   Doesn't run the typechecker (yet).
includeFile ::
    Int -> SeenSet -> IncludePath -> Options -> FilePath -> Bool -> IO [Stmt]
includeFile depth seen incpath opts fname once = do
  fname' <- locateFile incpath fname
  alreadySeen <- seenSetMember fname' seen 
  if depth > 128 then
      -- XXX pass in the include position as well
      Cons.errX $ "Maximum include depth exceeded"
  else if once && alreadySeen then do
      -- include_once and we've already seen this file
      Cons.noteN $ "Skipping already-included file \"" <>
                   Text.pack fname' <> "\""
      pure []
  else do
      seenSetInsert fname' seen
      let (_current, dirs) = incpath
          current' = takeDirectory fname'
          incpath' = (current', dirs)

      Cons.noteN $ "Loading file \"" <> Text.pack fname' <> "\""
      ftext <- TextIO.readFile fname'

      stmts <- wrapDir current' $ readAnyIO fname ftext "end of file" parseModule
      resolveIncludes (depth + 1) seen incpath' opts Inc.processStmts stmts

-- | Find a file, potentially looking in a list of multiple search paths (as
-- specified via the @SAW_IMPORT_PATH@ environment variable or
-- @-i@/@--import-path@ command-line options). If the file was successfully
-- found, load it. If not, fail by returning `Left`.
--
-- Doesn't run the typechecker (yet).
findAndLoadFileUnchecked :: Options -> FilePath -> IO [Stmt]
findAndLoadFileUnchecked opts fp = do
  let depth = 0
  seen <- emptySeenSet
  let incpath = (".", Options.importPath opts)
      once = False
  includeFile depth seen incpath opts fp once
