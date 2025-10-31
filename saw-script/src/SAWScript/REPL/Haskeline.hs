{- |
Module      : SAWScript.REPL.Haskeline
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module SAWScript.REPL.Haskeline (repl) where

import SAWScript.REPL.Monad
import SAWScript.REPL.Data
import SAWScript.REPL.Command

import Control.Monad (when)
import Control.Monad.State (gets)
import Data.Char (isAlphaNum, isSpace)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.List (isPrefixOf)
import System.Console.Haskeline
import System.Directory(getAppUserDataDirectory,createDirectoryIfMissing)
import System.FilePath((</>))
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import qualified Control.Exception as X

import SAWCentral.Proof (psGoals)

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
repl mbBatchFile =
  do settings <- liftIO (setHistoryFile replSettings)
     runInputTBehavior style settings $ withInterrupt loop
  where

  style = case mbBatchFile of
    Nothing   -> defaultBehavior
    Just path -> useFile path

  loop = do
    prompt <- lift getPrompt
    mb     <- handleInterrupt (return (Just "")) (getInputLines prompt [])
    case mb of
        Nothing ->
            -- EOF
            return ()
        Just line ->
            -- XXX why is findCommand passed to parseCommand...?
            case parseCommand findCommand (Text.pack line) of
                Nothing ->
                    loop
                Just result -> do
                    lift $ runCommand result
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
  { complete       = replComp
  , historyFile    = Nothing
  , autoAddHistory = True
  }


-- Completion ------------------------------------------------------------------

-- | Top-level completion for the REPL.
replComp :: CompletionFunc REPL
replComp cursor@(l,r)
  | ":" `Text.isPrefixOf` l'
  , Just (cmd,rest) <- splitCommand l' = case findCommand cmd of

      [c] | Text.null rest && not (Text.any isSpace l') -> do
            return (l, [cmdComp cmd c])
          | otherwise -> do
            (rest',cs) <- cmdArgument (cBody c) (reverse $ Text.unpack $ sanitize rest, r)
            -- XXX this drops any leading spaces in l', which is ok but untidy
            return (unwords [rest', reverse $ Text.unpack cmd], cs)

      cmds ->
        return (l, [ cmdComp l' c | c <- cmds ])

  | l' == ":" =
      return (l, [ cmdComp l' c | c <- findCommand "" ])
  | otherwise = completeSAWScriptValue cursor
  where
  l' = sanitize (Text.pack $ reverse l)

-- | Generate a completion from a REPL command definition.
cmdComp :: Text -> CommandDescr -> Completion
cmdComp prefix c = Completion
  { replacement = Text.unpack $ Text.drop (Text.length prefix) (cName c)
  , display     = Text.unpack $ cName c
  , isFinished  = True
  }

-- | Dispatch to a completion function based on the kind of completion the
-- command is expecting.
cmdArgument :: CommandBody -> CompletionFunc REPL
cmdArgument ct cursor@(l,_) = case ct of
  ExprArg _     -> completeSAWScriptValue cursor
  TypeArg _     -> completeSAWScriptType cursor
  FilenameArg _ -> completeFilename cursor
  ShellArg _    -> completeFilename cursor
  NoArg       _ -> return (l,[])

data LexerMode = ModeNormal | ModeCryptol | ModeCryType | ModeQuote

lexerMode :: String -> LexerMode
lexerMode = normal
  where
    normal [] = ModeNormal
    normal ('{' : '{' : s) = cryptol s
    normal ('{' : '|' : s) = crytype s
    normal ('\"' : s) = quote s
    normal (_ : s) = normal s

    cryptol [] = ModeCryptol
    cryptol ('}' : '}' : s) = normal s
    cryptol (_ : s) = cryptol s

    crytype [] = ModeCryType
    crytype ('|' : '}' : s) = normal s
    crytype (_ : s) = crytype s

    quote [] = ModeQuote
    quote ('\"' : s) = normal s
    quote (_ : s) = quote s

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''

-- | Complete a name from the SAWScript value environment.
completeSAWScriptValue :: CompletionFunc REPL
completeSAWScriptValue cursor@(l, _) = do
  ns1 <- getSAWScriptValueNames
  ns2 <- getCryptolExprNames
  ns3 <- getCryptolTypeNames
  let n = reverse (takeWhile isIdentChar l)
      nameComps prefix ns = map (nameComp prefix) (filter (prefix `isPrefixOf`) ns)
  case lexerMode (reverse l) of
    ModeNormal  -> return (l, nameComps n ns1)
    ModeCryptol -> return (l, nameComps n ns2)
    ModeCryType -> return (l, nameComps n ns3)
    ModeQuote   -> completeFilename cursor

-- | Complete a name from the SAWScript type environment.
completeSAWScriptType :: CompletionFunc REPL
completeSAWScriptType (l, _) = do
  ns <- getSAWScriptTypeNames
  let prefix = reverse (takeWhile isIdentChar l)
      nameComps = map (nameComp prefix) (filter (prefix `isPrefixOf`) ns)
  return (l, nameComps)

-- | Generate a completion from a prefix and a name.
nameComp :: String -> String -> Completion
nameComp prefix c = Completion
  { replacement = drop (length prefix) c
  , display     = c
  , isFinished  = True
  }
