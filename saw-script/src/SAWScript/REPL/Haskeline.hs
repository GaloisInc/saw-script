{- |
Module      : SAWScript.REPL.Haskeline
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module SAWScript.REPL.Haskeline (repl, replBody) where

import SAWScript.REPL.Command
import SAWScript.REPL.Monad

import Control.Monad (when)
import Control.Monad.State (gets, modify)
import Data.Char (isAlphaNum, isSpace)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.List (isPrefixOf)
import System.Console.Haskeline
import System.Directory(getAppUserDataDirectory,createDirectoryIfMissing)
import System.FilePath((</>))
import qualified Control.Monad.IO.Class as MTL
import qualified Control.Monad.Trans.Class as MTL
import qualified Control.Exception as X

import SAWCentral.TopLevel( TopLevelRO(..) )


-- | Haskeline-specific repl implementation.
--
-- XXX this needs to handle Ctrl-C, which at the moment will just cause
-- haskeline to exit.  See the function 'withInterrupt' for more info on how to
-- handle this.
repl :: Maybe FilePath -> REPL ()
repl mbBatchFile =
  replBody mbBatchFile


replBody :: Maybe FilePath -> REPL ()
replBody mbBatchFile =
  do settings <- MTL.liftIO (setHistoryFile replSettings)
     enableSubshell (runInputTBehavior style settings body)
  where
  body = withInterrupt loop

  style = case mbBatchFile of
    Nothing   -> defaultBehavior
    Just path -> useFile path

  -- not entirely sure why we need a type signature here, but it croaks without
  enableSubshell :: REPL a -> REPL a
  enableSubshell m = do
    ro <- gets rTopLevelRO
    let ro' = ro { roSubshell = subshell (runInputT replSettings (withInterrupt loop)) }
    modify (\refs -> refs { rTopLevelRO = ro' })
    result <- m
    modify (\refs -> refs { rTopLevelRO = ro })
    return result

  loop = do
    prompt <- MTL.lift getPrompt
    mb     <- handleInterrupt (return (Just "")) (getInputLines prompt [])
    case mb of
      Just line
        | Just cmd <- parseCommand findCommand (Text.pack line) -> do
          continue <- MTL.lift $ do
            handleInterrupt handleCtrlC (runCommand cmd)
            shouldContinue
          when continue loop

        | otherwise -> loop

      Nothing -> return ()

  getInputLines prompt ls =
    do mb <- fmap (filter (/= '\r')) <$> getInputLine prompt
       let newPrompt = map (\_ -> ' ') prompt
       case mb of
          Nothing -> return Nothing
          Just l | not (null l) && last l == '\\' ->
                                      getInputLines newPrompt (init l : ls)
                 | otherwise -> return $ Just $ unlines $ reverse $ l : ls



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
