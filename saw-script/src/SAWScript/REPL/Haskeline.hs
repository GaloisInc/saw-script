{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWScript.REPL.Haskeline
Description :
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

Haskeline interface layer with main REPL loop and tab completion
support.
-}

module SAWScript.REPL.Haskeline (repl) where

import Control.Monad (when)
import Control.Monad.State (gets)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import qualified Control.Exception as X
import Data.Maybe (mapMaybe)
import Data.Char (isAlphaNum, isSpace)
import qualified Data.Text as Text
import Data.Text (Text)
import System.Directory(getAppUserDataDirectory,createDirectoryIfMissing)
import System.FilePath((</>))

import System.Console.Haskeline

import SAWCentral.Proof (psGoals)
import SAWScript.Panic (panic)
import SAWScript.REPL.Monad
import SAWScript.REPL.Data
import SAWScript.REPL.Command


-- | Construct the prompt for the current environment.
getPrompt :: REPL String
getPrompt =
  do batch <- gets rIsBatch
     if batch then return ""
     else do
       mpst <- gets rProofState
       case mpst of
         Nothing ->
             return "sawscript> "
         Just pst ->
             return ("proof ("++show (length (psGoals pst))++")> ")

-- | Haskeline-specific repl implementation.
repl :: Maybe FilePath -> REPL ()
repl mbBatchFile = do
    let style = case mbBatchFile of
          Nothing   -> defaultBehavior
          Just path -> useFile path
    settings <- liftIO (setHistoryFile replSettings)
    runInputTBehavior style settings $ withInterrupt loop
  where

  loop = do
    prompt <- lift getPrompt
    mb     <- handleInterrupt (return (Just "")) (getInputLines prompt [])
    case mb of
        Nothing ->
            -- EOF
            return ()
        Just txt -> do
            lift $ executeText (Text.pack txt)
            continue <- lift $ gets rContinue
            when continue
                loop

  getInputLines prompt linesSoFar = do
      mbtext <- getInputLine prompt
      case mbtext of
          Nothing ->
              return Nothing
          Just text -> do
              let text' = filter (\c -> c /= '\r') text
              if not (null text') && last text' == '\\' then do
                  -- Get more lines
                  let newPrompt = map (\_ -> ' ') prompt
                  getInputLines newPrompt (init text' : linesSoFar)
              else do
                  -- We accumulated these backwards, so reverse
                  let linesAll = text : linesSoFar
                      linetext = unlines $ reverse linesAll
                  return $ Just linetext

-- | Try to set the history file.
setHistoryFile :: Settings REPL -> IO (Settings REPL)
setHistoryFile ss =
  do dir <- getAppUserDataDirectory "saw"
     createDirectoryIfMissing True dir
     return ss { historyFile = Just (dir </> "history") }
   `X.catch` \(X.SomeException {}) -> return ss

-- | Haskeline settings for the REPL.
replSettings :: Settings REPL
replSettings  = Settings
  { complete       = completeReplText
  , historyFile    = Nothing
  , autoAddHistory = True
  }

------------------------------------------------------------
-- Approximate lexer and parser
-- (for use in completions)

data ALPResult
    = HaveSAWScriptValue Text
    | HaveSAWScriptType Text
    | HaveCryptolValue Text
    | HaveCryptolType Text
    | HaveQuotedString

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''

approxLexerParser :: Text -> ALPResult
approxLexerParser text0 = nowhere text0 text0
  where

    -- State for nowhere in particular
    nowhere start here =
        case Text.uncons here of
            Nothing ->
                HaveSAWScriptValue start
            Just ('{', here') -> case Text.uncons here' of
                Nothing ->
                    -- End of string with a single left-brace.  In an
                    -- ideal world here we might complete from field
                    -- names of known record types, and add in another
                    -- left-brace as an option.  We don't have enough
                    -- infrastructure for that, though, so assume
                    -- we're still nowhere in particular.
                    nowhere here' here'
                Just ('{', here'') ->
                    cryexpr here'' here''
                Just ('|', here'') ->
                    crytype here'' here''
                Just (c, here'') ->
                    nowhere (if isIdentChar c then start else here'') here''
            Just ('"', here') ->
                qstring here'
            Just (':', here') ->
                sawtypeinit here'
            Just (c, here') ->
                nowhere (if isIdentChar c then start else here') here'

    -- State for when we've seen a colon so we probably want a type,
    -- but we haven't seen anything yet. Accept spaces.
    sawtypeinit here =
        case Text.uncons here of
            Nothing ->
                HaveSAWScriptType ""
            Just (' ', here') ->
                sawtypeinit here'
            Just (c, here') ->
                if isIdentChar c then
                    sawtype here here'
                else
                    nowhere here here

    -- State for when we've seen a colon so we probably want a type,
    -- and we're accumulating a word. Stop on spaces.
    sawtype start here =
        case Text.uncons here of
            Nothing ->
                HaveSAWScriptType start
            Just (c, here') ->
                if isIdentChar c then
                    sawtype start here'
                else
                    nowhere here here

    -- State for Cryptol expressions in {{ }}.
    cryexpr start here =
        case Text.uncons here of
            Nothing ->
                HaveCryptolValue start
            Just ('}', here') -> case Text.uncons here' of
                Nothing ->
                    HaveCryptolValue ""
                Just ('}', here'') ->
                    nowhere here'' here''
                Just _ ->
                    cryexpr here' here'
            Just (c, here') ->
                cryexpr (if isIdentChar c then start else here') here'

    -- State for Cryptol types in {| |}.
    crytype start here =
        case Text.uncons here of
            Nothing ->
                HaveCryptolType start
            Just ('|', here') -> case Text.uncons here' of
                Nothing ->
                    HaveCryptolType ""
                Just ('}', here'') ->
                    nowhere here'' here''
                Just _ ->
                    crytype here' here'
            Just (c, here') ->
                crytype (if isIdentChar c then start else here') here'

    -- State for quoted strings.
    qstring here =
        case Text.uncons here of
            Nothing ->
                HaveQuotedString
            Just ('\\', here') -> case Text.uncons here' of
                Nothing ->
                    HaveQuotedString
                Just (_, here'') ->
                    qstring here''
            Just ('"', here') ->
                nowhere here' here'
            Just (_, here') ->
                qstring here'


------------------------------------------------------------
-- Completion

-- | Haskeline's completion cursors are string-zippers in String,
--   pairs where the LHS is a reverse list of characters behind the
--   cursor, and the RHS is a forward list of characters after the
--   cursor.
type Cursor = (String, String)

-- | Extract the LHS from a Haskeline cursor in its raw form.
cursorLeftRaw :: Cursor -> String
cursorLeftRaw (l, _r) = l

-- | Extract the LHS from a Haskeline cursor as Text.
cursorLeftText :: Cursor -> Text
cursorLeftText (l, _r) = sanitize (Text.pack $ reverse l)

-- | Construct a completion that appends the rest of `word`
--   having already seen `prefix`.
appendCompletion :: (Int, Text) -> Completion
appendCompletion (prefixlen, word) =
   Completion {
       replacement = Text.unpack $ Text.drop prefixlen word,
       display = Text.unpack word,
       isFinished = True
   }

-- | Search a list of names by prefix
searchNames :: [Text] -> Text -> [(Int, Text)]
searchNames candidates prefix =
    let len = Text.length prefix
        visit candidate =
          if prefix `Text.isPrefixOf` candidate then
              Just (len, candidate)
          else
              Nothing
    in
    mapMaybe visit candidates

-- | Search a list of names by prefix, where we get the
--   list of names from a REPL action.
searchNames' :: REPL [Text] -> Text -> REPL [(Int, Text)]
searchNames' getCandidates prefix = do
    candidates <- getCandidates
    return $ searchNames candidates prefix

-- | Search for SAWScript types by prefix
searchSAWScriptTypes :: Text -> REPL [(Int, Text)]
searchSAWScriptTypes prefix =
    searchNames' getSAWScriptTypeNames prefix

-- | Search for SAWScript values/variables by prefix
searchSAWScriptValues :: Text -> REPL [(Int, Text)]
searchSAWScriptValues prefix =
    searchNames' getSAWScriptValueNames prefix

-- | Search for Cryptol types by prefix
searchCryptolTypes :: Text -> REPL [(Int, Text)]
searchCryptolTypes prefix =
    searchNames' getCryptolTypeNames prefix

-- | Search for Cryptol values/variables by prefix
searchCryptolValues :: Text -> REPL [(Int, Text)]
searchCryptolValues prefix =
    searchNames' getCryptolExprNames prefix

-- | Search for SAWScript things based on context.
searchSAWScriptText :: Text -> REPL (Maybe [(Int, Text)])
searchSAWScriptText text =
   -- Run the approximate lexer/parser.
   --
   -- Maybe someday alex/happy will give us a completion mode so we
   -- can run the real lexer and parser...
   --
   case approxLexerParser text of
       HaveSAWScriptValue word -> Just <$> searchSAWScriptValues word
       HaveSAWScriptType word -> Just <$> searchSAWScriptTypes word
       HaveCryptolValue word -> Just <$> searchCryptolValues word
       HaveCryptolType word -> Just <$> searchCryptolTypes word
       HaveQuotedString -> return Nothing

-- | Completion for SAWScript types
completeSAWScriptType :: Text -> CompletionFunc REPL
completeSAWScriptType text cursor = do
    candidates <- searchSAWScriptTypes text
    let completions = map appendCompletion candidates 
    return (cursorLeftRaw cursor, completions)

-- | Completion for general SAWScript text / values
completeSAWScriptValue :: Text -> CompletionFunc REPL
completeSAWScriptValue text cursor = do
    mbCandidates <- searchSAWScriptText text
    case mbCandidates of
        Nothing ->
            completeFilename cursor
        Just candidates -> do
            let completions = map appendCompletion candidates
            return (cursorLeftRaw cursor, completions)

-- | Completion for REPL :-commands
completeReplCommand :: Text -> CompletionFunc REPL
completeReplCommand text cursor =
    -- Split into words by spaces
    case Text.split isSpace text of
        [] ->
            -- Impossible: there's a colon in the string
            panic "replComp" ["The colon disappeared!"] 
        [cmdPrefix] -> do
            -- We have one word, which is a partial or full command
            -- name. Search for everything that begins with that
            -- prefix, then construct an append-completion for each.
            --
            -- Because we don't want to replace any of the existing
            -- text on the line, the LHS of the return value should
            -- always be the LHS of the input cursor.

            let completion cmd =
                    appendCompletion (Text.length cmdPrefix, cName cmd)
            let completions = map completion $ searchCommandsByPrefix cmdPrefix
            return (cursorLeftRaw cursor, completions)
        cmdName : args ->
            -- We have at least one partial argument
            case searchExactCommandByPrefix cmdName of
                Nothing ->
                    -- It's not a valid command so there's no completions
                    return (cursorLeftRaw cursor, [])
                Just cmd ->
                    -- Complete from whatever namespace the argument
                    -- type is in. XXX: this assumes that all commands
                    -- take either zero (NoArg) or one or more uniform
                    -- (other cases) of arguments. This isn't actually
                    -- true.  For example, completing for :cd will
                    -- cheerfully add any number of directory names,
                    -- but you can only actually give it one. Should
                    -- strengthen the argument schema.
                    case cBody cmd of
                        ExprArg _       -> completeSAWScriptValue (last args) cursor
                        SymbolNameArg _ -> completeSAWScriptValue (last args) cursor
                        TypeArgs _      -> completeSAWScriptType (last args) cursor
                        FilenameArg _   -> completeFilename cursor
                        NoArg       _   -> return (cursorLeftRaw cursor, [])

-- | Top-level completion for the REPL.
--
completeReplText :: CompletionFunc REPL
completeReplText cursor = do
  let text = cursorLeftText cursor
  if Text.null text then
      completeSAWScriptValue "" cursor
  else if Text.isPrefixOf ":" text then do
      completeReplCommand text cursor
  else
      completeSAWScriptValue text cursor
