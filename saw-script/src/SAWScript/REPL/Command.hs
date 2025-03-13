{- |
Module      : SAWScript.REPL.Command
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP, PatternGuards, FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
-- TODO RGS: Do better (or at least comment why we do this)
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module SAWScript.REPL.Command (
    -- * Commands
    Command(..), CommandDescr(..), CommandBody(..)
  , parseCommand
  , runCommand
  , splitCommand
  , findCommand
  , findNbCommand

    -- Misc utilities
  , handleCtrlC
  , sanitize

    -- To support Notebook interface (might need to refactor)
  , replParse
  --, liftModuleCmd
  --, moduleCmdResult
  ) where

--import Verifier.SAW.SharedTerm (SharedContext)


import SAWScript.REPL.Monad
import SAWScript.REPL.Trie
import SAWCentral.Position (getPos)

import Cryptol.Parser (ParseError())

import Control.Exception (throwIO)
import Control.Monad (guard, void, when)

import Data.Char (isSpace,isPunctuation,isSymbol)
import Data.Function (on)
import Data.List (intercalate, nub)
import qualified Data.Text as Text
import System.FilePath((</>), isPathSeparator)
import System.Directory(getHomeDirectory,getCurrentDirectory,setCurrentDirectory,doesDirectoryExist)
import qualified Data.Map as Map

-- SAWScript imports
import qualified SAWCentral.Options (Verbosity(..))
import qualified SAWCentral.AST as SS
    (pShow,
     Located(..),
     Decl(..),
     Pattern(..))
import SAWCentral.Exceptions
import SAWScript.MGU (checkDecl, checkSchemaPattern)
import SAWScript.Search (compileSearchPattern, matchSearchPattern)
import SAWScript.Interpreter (interpretStmt)
import qualified SAWScript.Lexer (lexSAW)
import qualified SAWScript.Parser (parseStmtSemi, parseExpression, parseSchemaPattern)
import SAWCentral.TopLevel (TopLevelRW(..))


-- Commands --------------------------------------------------------------------

-- | Commands.
data Command
  = Command (REPL ())         -- ^ Successfully parsed command
  | Ambiguous String [String] -- ^ Ambiguous command, list of conflicting
                              --   commands
  | Unknown String            -- ^ The unknown command

-- | Command builder.
data CommandDescr = CommandDescr
  { cName :: String
  , cAliases :: [String]
  , cBody :: CommandBody
  , cHelp :: String
  }

instance Show CommandDescr where
  show = cName

instance Eq CommandDescr where
  (==) = (==) `on` cName

instance Ord CommandDescr where
  compare = compare `on` cName

data CommandBody
  = ExprArg     (String   -> REPL ())
  | FilenameArg (FilePath -> REPL ())
  | ShellArg    (String   -> REPL ())
  | NoArg       (REPL ())


-- | Convert the command list to a Trie, expanding aliases.
makeCommands :: [CommandDescr] -> CommandMap
makeCommands list  = foldl insert emptyTrie (concatMap expandAliases list)
  where
  insert m (name, d) = insertTrie name d m
  expandAliases :: CommandDescr -> [(String, CommandDescr)]
  expandAliases d = (cName d, d) : zip (cAliases d) (repeat d)

-- | REPL command parsing.
commands :: CommandMap
commands = makeCommands commandList

-- | Notebook command parsing.
nbCommands :: CommandMap
nbCommands = makeCommands nbCommandList

-- | A subset of commands safe for Notebook execution
nbCommandList :: [CommandDescr]
nbCommandList  =
  [ CommandDescr ":env"  []      (NoArg envCmd)
    "display the current sawscript environment"
  , CommandDescr ":search" []    (ExprArg searchCmd)
    "search the environment by type"
  , CommandDescr ":tenv" []      (NoArg tenvCmd)
    "display the current sawscript type environment"
  , CommandDescr ":type" [":t"]  (ExprArg typeOfCmd)
    "check the type of an expression"
  , CommandDescr ":?"    []      (ExprArg helpCmd)
    "display a brief description about a built-in operator"
  , CommandDescr ":help" []      (ExprArg helpCmd)
    "display a brief description about a built-in operator"
  ]

commandList :: [CommandDescr]
commandList  =
  nbCommandList ++
  [ CommandDescr ":quit" []   (NoArg quitCmd)
    "exit the REPL"
  , CommandDescr ":cd"   []   (FilenameArg cdCmd)
    "set the current working directory"
  , CommandDescr ":pwd"  []   (NoArg pwdCmd)
    "display the current working directory"
  ]

genHelp :: [CommandDescr] -> [String]
genHelp cs = map cmdHelp cs
  where
  cmdHelp cmd = concat [ "  ", cName cmd, pad (cName cmd), cHelp cmd ]
  padding     = 2 + maximum (map (length . cName) cs)
  pad n       = replicate (max 0 (padding - length n)) ' '


-- Command Evaluation ----------------------------------------------------------

-- | Run a command.
runCommand :: Command -> REPL ()
runCommand c = case c of

  Command cmd -> exceptionProtect cmd

  Unknown cmd -> io (putStrLn ("Unknown command: " ++ cmd))

  Ambiguous cmd cmds -> io $ do
    putStrLn (cmd ++ " is ambiguous, it could mean one of:")
    putStrLn ("\t" ++ intercalate ", " cmds)


typeOfCmd :: String -> REPL ()
typeOfCmd str
  | null str = do io $ putStrLn "[error] :type requires an argument"
  | otherwise =
  do let (tokens, optmsg) = SAWScript.Lexer.lexSAW replFileName (Text.pack str)
     case optmsg of
       Nothing -> return ()
       Just (_vrb, pos, msg) -> do
         -- XXX wrap printing of positions in the message-printing infrastructure
         let msg' = show pos ++ ": " ++ Text.unpack msg
         io $ putStrLn msg'
     expr <- case SAWScript.Parser.parseExpression tokens of
       Left err -> fail (show err)
       Right expr -> return expr
     let pos = getPos expr
         decl = SS.Decl pos (SS.PWild pos Nothing) Nothing expr
     rw <- getValueEnvironment
     decl' <- do
       let (errs_or_results, warns) = checkDecl (rwValueTypes rw) (rwNamedTypes rw) decl
       let issueWarning (msgpos, msg) =
             -- XXX the print functions should be what knows how to show positions...
             putStrLn (show msgpos ++ ": Warning: " ++ msg)
       io $ mapM_ issueWarning warns
       either failTypecheck return errs_or_results
     let ~(SS.Decl _pos _ (Just schema) _expr') = decl'
     io $ putStrLn $ SS.pShow schema

searchCmd :: String -> REPL ()
searchCmd str
  | null str = do io $ putStrLn $ "[error] :search requires at least one argument"
  | otherwise =
  do let (tokens, optmsg) = SAWScript.Lexer.lexSAW replFileName (Text.pack str)
     case optmsg of
       Nothing -> return ()
       Just (vrb, pos, msg) -> do
         -- XXX wrap printing of positions in the message-printing infrastructure
         let msg' = show pos ++ ": " ++ Text.unpack msg
         io $ putStrLn msg'
         -- XXX this prints twice, fix it up when we do the message-printing cleanup
         when (vrb == SAWCentral.Options.Error) $
             io $ throwIO $ userError msg'
     pat <- case SAWScript.Parser.parseSchemaPattern tokens of
       Left err -> fail (show err)
       Right pat -> return pat
     rw <- getValueEnvironment
     let valueTypes = rwValueTypes rw
         namedTypes = rwNamedTypes rw
         (errs_or_results, warns) = checkSchemaPattern valueTypes namedTypes pat
     let issueWarning (msgpos, msg) =
           -- XXX the print functions should be what knows how to show positions...
           putStrLn (show msgpos ++ ": Warning: " ++ msg)
     io $ mapM_ issueWarning warns
     pat' <- either failTypecheck return $ errs_or_results
     let search = compileSearchPattern namedTypes pat'
         matches = Map.assocs $ Map.filter (matchSearchPattern search) valueTypes
         printMatch (lname, ty) = do
           let name = Text.unpack $ SS.getVal lname
               ty' = SS.pShow ty
           putStrLn (name ++ " : " ++ ty')
     io $ mapM_ printMatch matches


quitCmd :: REPL ()
quitCmd  = stop


envCmd :: REPL ()
envCmd = do
  env <- getValueEnvironment
  let showLName = Text.unpack . SS.getVal
  io $ sequence_ [ putStrLn (showLName x ++ " : " ++ SS.pShow v) | (x, v) <- Map.assocs (rwValueTypes env) ]

tenvCmd :: REPL ()
tenvCmd = do
  env <- getValueEnvironment
  io $ sequence_ [ putStrLn (Text.unpack a ++ " : " ++ SS.pShow t) | (a, t) <- Map.assocs (rwNamedTypes env) ]

helpCmd :: String -> REPL ()
helpCmd cmd
  | null cmd = io (mapM_ putStrLn (genHelp commandList))
  | otherwise =
    do env <- getEnvironment
       case Map.lookup (Text.pack cmd) (rwDocs env) of
         Just d -> io $ putStr d
-- FIXME? can we restore the ability to lookup doc strings from Cryptol?
--  | Just (ec,_) <- lookup cmd builtIns =
--                io $ print $ helpDoc ec

         Nothing -> do io $ putStrLn $ "// No documentation is available."
                       typeOfCmd cmd


cdCmd :: FilePath -> REPL ()
cdCmd f | null f = io $ putStrLn $ "[error] :cd requires a path argument"
        | otherwise = do
  exists <- io $ doesDirectoryExist f
  if exists
    then io $ setCurrentDirectory f
    else raise $ DirectoryNotFound f

pwdCmd :: REPL ()
pwdCmd = io $ getCurrentDirectory >>= putStrLn

-- SAWScript commands ----------------------------------------------------------

{- Evaluation is fairly straightforward; however, there are a few important
caveats:

  1. 'return' is type-polymorphic.  This means that 'return "foo"' will produce
     a type-polymorphic function 'm -> m String', for any monad 'm'.  It also
     means that if you type 'return "foo"' into a naively-written interpreter,
     you won't see 'foo'!  The solution is to force each statement that comes
     into the REPL to have type 'TopLevel t' ('TopLevel' is the SAWScript
     version of 'IO').  This gets done as soon as the statement is parsed.

  2. Handling binding variables to values is somewhat tricky.  When you're
     allowed to bind variables in the REPL, you're basically working in the
     context of a partially evaluated module: all the results of all the old
     computations are in scope, and you're allowed to add new computations that
     depend on them.  It's insufficient to merely hang onto the AST for the
     old computations, as that could cause them to be evaluated multiple times;
     it could also cause their type to be inferred differently several times,
     which is bad.  Instead, we hang onto the inferred types of previous
     computations and use them to seed the name resolver and the typechecker;
     we also hang onto the results and use them to seed the interpreter. -}
sawScriptCmd :: String -> REPL ()
sawScriptCmd str = do
  let (tokens, optmsg) = SAWScript.Lexer.lexSAW replFileName (Text.pack str)
  case optmsg of
    Nothing -> return ()
    Just (_vrb, pos, msg) -> do
      -- XXX wrap printing of positions in the message-printing infrastructure
      let msg' = show pos ++ ": " ++ Text.unpack msg
      io $ putStrLn msg'
  case SAWScript.Parser.parseStmtSemi tokens of
    Left err -> io $ print err
    Right stmt ->
      do mr <- getProofStateRef
         case mr of
           Nothing -> void $ liftTopLevel (interpretStmt True stmt)
           Just r  -> void $ liftProofScript (interpretStmt True stmt) r

replFileName :: String
replFileName = "<stdin>"

-- C-c Handlings ---------------------------------------------------------------

-- XXX this should probably do something a bit more specific.
handleCtrlC :: REPL ()
handleCtrlC  = io (putStrLn "Ctrl-C")


-- Utilities -------------------------------------------------------------------

-- | Lift a parsing action into the REPL monad.
replParse :: (String -> Either ParseError a) -> String -> REPL a
replParse parse str = case parse str of
  Right a -> return a
  Left e  -> raise (ParseError e)

type CommandMap = Trie CommandDescr


-- Command Parsing -------------------------------------------------------------

-- | Strip leading space.
sanitize :: String -> String
sanitize  = dropWhile isSpace

-- | Strip trailing space.
sanitizeEnd :: String -> String
sanitizeEnd = reverse . sanitize . reverse

-- | Split at the first word boundary.
splitCommand :: String -> Maybe (String,String)
splitCommand txt =
  case sanitize txt of
    ':' : more
      | (as,bs) <- span (\x -> isPunctuation x || isSymbol x) more
      , not (null as) -> Just (':' : as, sanitize bs)

      | (as,bs) <- break isSpace more
      , not (null as) -> Just (':' : as, sanitize bs)

      | otherwise -> Nothing

    expr -> guard (not (null expr)) >> return (expr,[])

-- | Look up a string in a command list. If given a string that's both
-- itself a command and a prefix of something else, choose that
-- command; otherwise such commands are inaccessible. Also, deduplicate
-- the list of results to avoid silliness with command aliases.
findSomeCommand :: String -> CommandMap -> [CommandDescr]
findSomeCommand str commandTable = nub $ lookupTrieWithExact str commandTable

-- | Look up a string in the command list.
findCommand :: String -> [CommandDescr]
findCommand str = findSomeCommand str commands

-- | Look up a string in the notebook-safe command list.
findNbCommand :: String -> [CommandDescr]
findNbCommand str = findSomeCommand str nbCommands

-- | Parse a line as a command.
parseCommand :: (String -> [CommandDescr]) -> String -> Maybe Command
parseCommand findCmd line = do
  (cmd,args) <- splitCommand line
  let args' = sanitizeEnd args
  case findCmd cmd of
    -- nothing matched; if it doesn't begin with a colon, eval it
    [] -> case cmd of
      []      -> Nothing
      ':' : _ -> Just (Unknown cmd)
      _       -> Just (Command (sawScriptCmd line))

    -- matched exactly one command; run it
    [c] -> case cBody c of
      ExprArg     body -> Just (Command (body args'))
      FilenameArg body -> Just (Command (body =<< expandHome args'))
      ShellArg    body -> Just (Command (body args'))
      NoArg       body -> Just (Command  body)

    -- matched several things; complain
    cs -> Just (Ambiguous cmd (map cName cs))

  where
  expandHome path =
    case path of
      '~' : c : more | isPathSeparator c -> do dir <- io getHomeDirectory
                                               return (dir </> more)
      _ -> return path
