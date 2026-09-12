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
import Prettyprinter ((<+>))

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
import qualified SAWScript.Typechecker as Ty (Message(..))


------------------------------------------------------------
-- Support logic

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


------------------------------------------------------------
-- Messages and results

-- | Type shorthand for the results produced by the parser: either a
--   parse error, or a value. The parser never produces warnings, and
--   (for now at least) it can only produce one error before giving
--   up.
type ParseResult a = Either ParseError a

-- | Type shorthand for a parser function: list of tokens to a result.
type Parser a = [Token Pos] -> ParseResult a

-- | Type shorthand for a typechecker result. The typechecker returns
--   a list of messages (using, for now at least, its own type to
--   encode errors vs. warnings vs. notices) and a value.
--
--   On error the message list includes at least one error, and the
--   result value exists but is not meaningful and can/should be
--   discarded.
--
--   On success the message list contains only warnings or notices
--   (or is empty) and the result is valid.
--
type TyResult a = ([Ty.Message], a)

-- | Type shorthand for the result of `readAny`, which differs from
--   the typechecker result by not separating errors from warnings
--   and therefore preserving message order.
--
--   On error it returns Left and a list of messages, at least
--   one of which is an error and therefore fatal.
--
--   On success, it returns a (possibly empty) list of messages, which
--   are all warnings and not fatal, and a result of type a.
--
--   The text is a Doc because we've improved the parser so it sometimes
--   prints structured messages. The typechecker often does as well.
--
type GenericResult a = Either [(Pos, PPS.Doc)] ([(Pos, PPS.Doc)], a)


------------------------------------------------------------
-- Common load logic

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
readAny :: PPS.Opts -> FilePath -> Text -> Text -> Parser a -> GenericResult a
readAny ppopts fileName str eofName parser =
    case lexSAW fileName eofName str of
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
                    let (optpos, err') = prettyParseError ppopts eofName err
                        pos = case optpos of
                            Nothing ->
                                -- Happy is unable to provide the
                                -- position of an error at EOF. Here
                                -- we have the input token list, so we
                                -- can pick up after it. Use the
                                -- trailing edge of the last token.
                                case uncons (reverse tokens) of
                                    Nothing ->
                                        -- empty file
                                        Range fileName 1 1 1 1 ""
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
--   (Including warnings. This is used when processing the builtins
--   table during startup, and it should not produce warnings.)
panicOnGenericMsgs :: PPS.Opts -> Text -> GenericResult a -> a
panicOnGenericMsgs ppopts whoAmI result =
  -- Properly, printing the positions with the errors should be done
  -- by the error infrastructure. However, the error infrastructure
  -- necessarily needs to run in `IO`, and we need to _not_ run in
  -- `IO` here because we're part of initializing the builtins table.
  -- Do it by hand instead. I don't think it's worth adding extra
  -- stuff to SAWConsole just to avoid needing this code.
  let pp (pos, msg) =
        let msg' = PP.pretty (PosSupport.ppPosition pos) <> ":" PP.<+> msg in
        PPS.renderText ppopts msg'
  in
  case result of
   Left errs ->
       panic whoAmI ("Unexpected errors:" : map pp errs)
   Right ([], tree) ->
       tree
   Right (warns, _) ->
       panic whoAmI ("Unexpected warnings:" : map pp warns)

-- | Like `panicOnGeneric Msgs` but for typechecker results. XXX: the
--   typechecker should issue its own messages; if not, at least the
--   format shouldn't be arbitrarily different.
panicOnTyMsgs :: Text -> TyResult a -> a
panicOnTyMsgs whoAmI (msgs, result) =
    let pp msg =
          let (pos, desc, msg') = case msg of
                Ty.Error p doc -> (p, "Error: ", doc)
                Ty.Warning p doc -> (p, "Warning: ", doc)
                Ty.Notice p doc -> (p, "Note: ", doc)
                Ty.Comment p doc -> (p, "", doc)
          in
          let msg'' = PosSupport.prettyPosition pos <> ":" <+> desc <> msg' in
          PPS.renderText PPS.defaultOpts msg''  -- startup time, use default opts
    in
    case msgs of
        [] -> result
        _ -> panic whoAmI ("Unexpected typechecker messages:" : map pp msgs)

-- | Handle the readAny result in IO.
--
--   Add HasCallStack because if the panic happens we'll want to know
--   where we came from. XXX: figure out how to get rid of the panic
--   and remove HasCallStack again.
dispatchGenericMsgs :: HasCallStack => GenericResult a -> IO a
dispatchGenericMsgs result =
    case result of
        Left errs -> do
            let pp (pos, msg) = Cons.errDP' pos msg
            mapM_ pp errs
            Cons.checkFail
            panic "dispatchGenericMsgs" ["checkFail didn't fail"]
        Right (msgs, tree) -> do
            let pp (pos, msg) = Cons.warnP' pos msg
            mapM_ pp msgs
            pure tree

-- | Handle a typechecker result in IO.
dispatchTyMsgs :: TyResult a -> IO a
dispatchTyMsgs (msgs, result) = do
    let dispatch msg = case msg of
          Ty.Error pos msg' -> Cons.errDP' pos msg'
          Ty.Warning pos msg' -> Cons.warnP' pos msg'
          Ty.Notice pos msg' -> Cons.noteP' pos msg'
          Ty.Comment pos msg' -> Cons.commentP' pos msg'
    mapM_ dispatch msgs
    -- This crashes out if the above issued any errors
    Cons.checkFail
    pure result

-- | Call `readAny` and panic if it generates any diagnostics.
readAnyPure :: PPS.Opts -> FilePath -> Text -> Text -> Parser a -> Text -> a
readAnyPure ppopts fileName str eofName parser whoAmI =
    panicOnGenericMsgs ppopts whoAmI $ readAny ppopts fileName str eofName parser

-- | Call `readAny` then `dispatchGenericMsgs`.
readAnyIO :: PPS.Opts -> FilePath -> Text -> Text -> Parser a -> IO a
readAnyIO ppopts fileName str eofName parser =
    dispatchGenericMsgs $ readAny ppopts fileName str eofName parser

-- | Run the readAny result through the `Include` module to resolve
--   @include@ statements.
--
--   If we fail after collecting warnings, print the warnings before
--   returning the failure.
--
resolveIncludes ::
    Int -> SeenSet -> IncludePath -> Options -> PPS.Opts -> Inc.Processor a -> a -> IO a
resolveIncludes depth seen incpath opts ppopts process tree =
    process (includeFile depth seen incpath opts ppopts) tree


------------------------------------------------------------
-- Entry points for loading

-- | Read a type schema from a string. This is used to digest the type
--   signatures for builtins, and the expansions for builtin typedefs.
--
-- Pure function that panics on any error or warning. This is
-- appropriate since we use it only to handle the builtins; any
-- glitches there are properly panics.
--
-- The first argument (@name@) is the name of the builtin we're
-- processing. This is used to concoct a fake
-- filename for the lexer, which (complete with line and column
-- numbering of dubious value) will go into the positions of the
-- elements of the resulting type.
--
-- FUTURE: we should figure out how to generate more meaningful
-- positions (like "third argument of concat") but this at least
-- allows telling the user which builtin the type came from.
--
-- The name is also used as part of the panic location if reading the
-- schema fails, so we know which builtin caused the problem.
--
-- Note: there is no way to reach @include@ statements from type
-- schemas, so no need to process includes in what we read.
--
readSchemaPure ::
    -- | Name of the builtin whose type signature we're reading
    Text ->
    -- | Lifecycle state of the builtin
    PrimitiveLifecycle ->
    -- | Environment for named types
    ScopedMap Name (PrimitiveLifecycle, NamedType) ->
    -- | Text to read from
    Text ->
    -- | Result (a type scheme)
    Schema
readSchemaPure name lc tyenv str =
    -- This is for use during initialization, so we can use the default ppopts
    let ppopts = PPS.defaultOpts in
    let fakeFileName = Text.unpack $ "<definition of " <> name <> ">"
        whoAmI = "readSchemaPure on " <> name
    in
    let schema = readAnyPure ppopts fakeFileName str "end-of-input" parseSchema whoAmI in
    panicOnTyMsgs (Text.pack fakeFileName) $ checkSchema ppopts lc tyenv schema name

-- | Read a schema pattern from a string. This is used by the
--   :search REPL command.
--
--   Also runs the typechecker to check the pattern.
--
-- Note: there is no way to reach @include@ statements from schema
-- patterns, so no need to process includes in what we read.
--
readSchemaPattern ::
    Options -> PPS.Opts ->
    FilePath -> Environ -> RebindableEnv -> Set PrimitiveLifecycle -> Text ->
    IO SchemaPattern
readSchemaPattern _opts ppopts fileName environ rbenv avail str = do
  pat <- readAnyIO ppopts fileName str "end-of-line" parseSchemaPattern
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

  dispatchTyMsgs $ checkSchemaPattern avail varenv''' tyenv pat

-- | Read an expression from a string. This is used by the
--   :type REPL command.
--
-- It is possible for someone to provide an expression that includes
-- an @include@ in a do-block, so just in case call into `Include`
-- to resolve any that appear.
--
readExpression ::
    Options -> PPS.Opts ->
    FilePath -> Environ -> RebindableEnv -> Set PrimitiveLifecycle -> Text ->
    IO (Schema, Expr)
readExpression opts ppopts fileName environ rbenv avail str = do
  seen <- emptySeenSet
  let incpath = (".", Options.importPath opts)

  expr0 <- readAnyIO ppopts fileName str "end-of-line" parseExpression
  expr <- resolveIncludes 0{-depth-} seen incpath opts ppopts Inc.processExpr expr0
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

  decl' <- dispatchTyMsgs $ checkDecl ppopts avail varenv''' tyenv decl

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
readREPLTextUnchecked :: Options -> PPS.Opts -> FilePath -> Text -> IO [Stmt]
readREPLTextUnchecked opts ppopts fileName str = do
  seen <- emptySeenSet
  let incpath = (".", Options.importPath opts)

  stmts <- readAnyIO ppopts fileName str "end-of-line" parseREPLText
  resolveIncludes 0{-depth-} seen incpath opts ppopts Inc.processStmts stmts

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
    Int -> SeenSet -> IncludePath -> Options -> PPS.Opts -> FilePath -> Bool -> IO [Stmt]
includeFile depth seen incpath opts ppopts fname once = do
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

      stmts <- wrapDir current' $ readAnyIO ppopts fname ftext "end-of-file" parseModule
      resolveIncludes (depth + 1) seen incpath' opts ppopts Inc.processStmts stmts

-- | Find a file, potentially looking in a list of multiple search paths (as
-- specified via the @SAW_IMPORT_PATH@ environment variable or
-- @-i@/@--import-path@ command-line options). If the file was successfully
-- found, load it. If not, fail by returning `Left`.
--
-- Doesn't run the typechecker (yet).
findAndLoadFileUnchecked :: Options -> PPS.Opts -> FilePath -> IO [Stmt]
findAndLoadFileUnchecked opts ppopts fp = do
  let depth = 0
  seen <- emptySeenSet
  let incpath = (".", Options.importPath opts)
      once = False
  includeFile depth seen incpath opts ppopts fp once
