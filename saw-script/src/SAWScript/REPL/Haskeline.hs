{- |
Module      : SAWScript.REPL.Haskeline
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module SAWScript.REPL.Haskeline (repl, replBody) where

import SAWScript.REPL.Command
import SAWScript.REPL.Monad

import Control.Monad (when)
#if MIN_VERSION_haskeline(0,8,0)
import qualified Control.Monad.Catch as E
#endif
import Data.Char (isAlphaNum, isSpace)
import Data.List (isPrefixOf)
import Data.Maybe (isJust)
import System.Console.Haskeline
import System.Directory(getAppUserDataDirectory,createDirectoryIfMissing)
import System.FilePath((</>))
import qualified Control.Monad.IO.Class as MTL
import qualified Control.Monad.Trans.Class as MTL
import qualified Control.Exception as X

import SAWCentral.Options (Options)
import SAWCentral.TopLevel( TopLevelRO(..) )


-- | Haskeline-specific repl implementation.
--
-- XXX this needs to handle Ctrl-C, which at the moment will just cause
-- haskeline to exit.  See the function 'withInterrupt' for more info on how to
-- handle this.
repl :: Maybe FilePath -> Options -> REPL () -> IO ()
repl mbBatch opts begin =
  runREPL (isJust mbBatch) opts (replBody mbBatch begin)


replBody :: Maybe FilePath -> REPL () -> REPL ()
replBody mbBatch begin =
  do settings <- MTL.liftIO (setHistoryFile replSettings)
     enableSubshell (runInputTBehavior style settings body)
  where
  body = withInterrupt $ do
    MTL.lift begin
    loop

  style = case mbBatch of
    Nothing   -> defaultBehavior
    Just path -> useFile path

  enableSubshell m =
    REPL $ \refs ->
      do let ro' = (rTopLevelRO refs){ roSubshell = subshell (runInputT replSettings (withInterrupt loop)) }
         unREPL m refs{ rTopLevelRO = ro' }

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


-- Utilities -------------------------------------------------------------------

instance MTL.MonadIO REPL where
  liftIO = io

#if !MIN_VERSION_haskeline(0,8,0)
-- older haskeline provides a MonadException class internally

instance MonadException REPL where
  controlIO branchIO = REPL $ \ ref -> do
    runBody <- branchIO $ RunIO $ \ m -> do
      a <- unREPL m ref
      return (return a)
    unREPL runBody ref

#else

-- haskeline requires instances of MonadMask

instance E.MonadThrow REPL where
  throwM e = REPL $ \_ -> X.throwIO e

instance E.MonadCatch REPL where
  catch repl_op handler = REPL $ \ioref ->
    E.catch (unREPL repl_op ioref) (\e -> unREPL (handler e) ioref)

instance E.MonadMask REPL where
  mask repl_op = REPL $ \ioref ->
    E.mask (\runIO -> unREPL (repl_op (\f -> REPL (\ioref' -> runIO (unREPL f ioref')))) ioref)
  uninterruptibleMask repl_op = REPL $ \ioref ->
    E.uninterruptibleMask (\runIO -> unREPL (repl_op (\f -> REPL (\ioref' -> runIO (unREPL f ioref')))) ioref)
  generalBracket acquire release repl_op = REPL $ \ioref ->
    E.generalBracket
    (unREPL acquire ioref)
    (\rsrc exitCase -> unREPL (release rsrc exitCase) ioref)
    (\rsrc -> unREPL (repl_op rsrc) ioref)
#endif


-- Completion ------------------------------------------------------------------

-- | Top-level completion for the REPL.
replComp :: CompletionFunc REPL
replComp cursor@(l,r)
  | ":" `isPrefixOf` l'
  , Just (cmd,rest) <- splitCommand l' = case findCommand cmd of

      [c] | null rest && not (any isSpace l') -> do
            return (l, [cmdComp cmd c])
          | otherwise -> do
            (rest',cs) <- cmdArgument (cBody c) (reverse (sanitize rest),r)
            return (unwords [rest', reverse cmd],cs)

      cmds ->
        return (l, [ cmdComp l' c | c <- cmds ])

  | l' == ":" =
      return (l, [ cmdComp l' c | c <- findCommand "" ])
  | otherwise = completeSAWScriptValue cursor
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
isIdentChar c = isAlphaNum c || c `elem` "_\'"

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
