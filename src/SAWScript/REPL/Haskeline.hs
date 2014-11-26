-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module SAWScript.REPL.Haskeline where

import SAWScript.REPL.Command
import SAWScript.REPL.Monad
import SAWScript.REPL.Trie

import Control.Monad (when)
import Data.Char (isAlphaNum, isSpace)
import Data.Function (on)
import Data.List (isPrefixOf,sortBy)
import System.Console.Haskeline
import System.Directory(getAppUserDataDirectory,createDirectoryIfMissing)
import System.FilePath((</>))
import qualified Control.Monad.IO.Class as MTL
import qualified Control.Monad.Trans.Class as MTL
import qualified Control.Exception as X

import SAWScript.Options (Options)


-- | Haskeline-specific repl implementation.
--
-- XXX this needs to handle Ctrl-C, which at the moment will just cause
-- haskeline to exit.  See the function 'withInterrupt' for more info on how to
-- handle this.
repl :: Maybe FilePath -> Options -> REPL () -> IO ()
repl mbBatch opts begin =
  do settings <- setHistoryFile replSettings
     runREPL isBatch opts (runInputTBehavior style settings body)
  where
  body = withInterrupt $ do
    MTL.lift begin
    loop

  (isBatch,style) = case mbBatch of
    Nothing   -> (False,defaultBehavior)
    Just path -> (True,useFile path)

  loop = do
    prompt <- MTL.lift getPrompt
    mb     <- handleInterrupt (return (Just "")) (getInputLines prompt [])
    case mb of

      Just line
        | Just cmd <- parseCommand findCommand line -> do
          continue <- MTL.lift $ do
            handleInterrupt handleCtrlC (runCommand cmd)
            shouldContinue
          when continue loop

        | otherwise -> loop

      Nothing -> return ()

  getInputLines prompt ls =
    do mb <- getInputLine prompt
       let newPropmpt = map (\_ -> ' ') prompt
       case mb of
          Nothing -> return Nothing
          Just l | not (null l) && last l == '\\' ->
                                      getInputLines newPropmpt (init l : ls)
                 | otherwise -> return $ Just $ unlines $ reverse $ l : ls



-- | Try to set the history file.
setHistoryFile :: Settings REPL -> IO (Settings REPL)
setHistoryFile ss =
  do dir <- getAppUserDataDirectory "saw"
     createDirectoryIfMissing True dir
     return ss { historyFile = Just (dir </> "history") }
   `X.catch` \(SomeException {}) -> return ss

-- | Haskeline settings for the REPL.
replSettings :: Settings REPL
replSettings  = Settings
  { complete       = cryptolCommand
  , historyFile    = Nothing
  , autoAddHistory = True
  }


-- Utilities -------------------------------------------------------------------

instance MTL.MonadIO REPL where
  liftIO = io

instance MonadException REPL where
  controlIO branchIO = REPL $ \ ref -> do
    runBody <- branchIO $ RunIO $ \ m -> do
      a <- unREPL m ref
      return (return a)
    unREPL runBody ref


-- Completion ------------------------------------------------------------------

-- | Completion for cryptol commands.
cryptolCommand :: CompletionFunc REPL
cryptolCommand cursor@(l,r)
  | ":" `isPrefixOf` l'
  , Just (cmd,rest) <- splitCommand l' = case findCommand cmd of

      [c] | null rest && not (any isSpace l') -> do
            return (l, [cmdComp cmd c])
          | otherwise -> do
            (rest',cs) <- cmdArgument (cBody c) (reverse (sanitize rest),r)
            return (unwords [rest', reverse cmd],cs)

      cmds ->
        return (l, [ cmdComp l' c | c <- cmds ])

  | otherwise = completeSAWScript cursor
  where
  l' = sanitize (reverse l)

-- | Generate a completion from a REPL command definition.
cmdComp :: String -> CommandDescr -> Completion
cmdComp prefix c = Completion
  { replacement = drop (length prefix) (cName c)
  , display     = cName c
  , isFinished  = True
  }

-- | Dispatch to a completion function based on the kind of completion the
-- command is expecting.
cmdArgument :: CommandBody -> CompletionFunc REPL
cmdArgument ct cursor@(l,_) = case ct of
  ExprArg     _ -> completeExpr cursor
  ExprTypeArg _ -> (completeExpr +++ completeType) cursor
  FilenameArg _ -> completeFilename cursor
  ShellArg _    -> completeFilename cursor
  OptionArg _   -> completeOption cursor
  NoArg       _ -> return (l,[])

-- | Complete a name from the expression environment.
completeExpr :: CompletionFunc REPL
completeExpr (l,_) = do
  ns <- getExprNames
  let n    = reverse l
      vars = filter (n `isPrefixOf`) ns
  return (l,map (nameComp n) vars)

-- | Complete a name from the type synonym environment.
completeType :: CompletionFunc REPL
completeType (l,_) = do
  ns <- getTypeNames
  let n    = reverse l
      vars = filter (n `isPrefixOf`) ns
  return (l,map (nameComp n) vars)

data LexerMode = ModeNormal | ModeCryptol | ModeQuote

lexerMode :: String -> LexerMode
lexerMode = normal
  where
    normal [] = ModeNormal
    normal ('{' : '{' : s) = cryptol s
    normal ('\"' : s) = quote s
    normal (_ : s) = normal s

    cryptol [] = ModeCryptol
    cryptol ('}' : '}' : s) = normal s
    cryptol (_ : s) = cryptol s

    quote [] = ModeQuote
    quote ('\"' : s) = normal s
    quote (_ : s) = quote s

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c `elem` "_\'"

-- | Complete a name from the sawscript environment.
completeSAWScript :: CompletionFunc REPL
completeSAWScript cursor@(l, _) = do
  ns1 <- getSAWScriptNames
  ns2 <- getExprNames
  let n = reverse (takeWhile isIdentChar l)
      nameComps prefix ns = map (nameComp prefix) (filter (prefix `isPrefixOf`) ns)
  case lexerMode (reverse l) of
    ModeNormal  -> return (l, nameComps n ns1)
    ModeCryptol -> return (l, nameComps n ns2)
    ModeQuote   -> completeFilename cursor

-- | Generate a completion from a prefix and a name.
nameComp :: String -> String -> Completion
nameComp prefix c = Completion
  { replacement = drop (length prefix) c
  , display     = c
  , isFinished  = True
  }


-- | Join two completion functions together, merging and sorting their results.
(+++) :: CompletionFunc REPL -> CompletionFunc REPL -> CompletionFunc REPL
(as +++ bs) cursor = do
  (_,acs) <- as cursor
  (_,bcs) <- bs cursor
  return (fst cursor, sortBy (compare `on` replacement) (acs ++ bcs))


-- | Complete an option from the options environment.
--
-- XXX this can do better, as it has access to the expected form of the value
completeOption :: CompletionFunc REPL
completeOption cursor@(l,_) = return (fst cursor, map comp opts)
  where
  n        = reverse l
  opts     = lookupTrie n userOptions
  comp opt = Completion
    { replacement = drop (length n) (optName opt)
    , display     = optName opt
    , isFinished  = False
    }
