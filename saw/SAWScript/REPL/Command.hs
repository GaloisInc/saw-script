{-# LANGUAGE CPP, PatternGuards, FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : $Header$
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
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
import SAWScript.Utils (getPos)

import Cryptol.Parser (ParseError())
import Cryptol.Utils.PP

import Control.Monad (guard)
import Data.Char (isSpace,isPunctuation,isSymbol)
import Data.Function (on)
import Data.List (intercalate)
import System.FilePath((</>), isPathSeparator)
import System.Directory(getHomeDirectory,setCurrentDirectory,doesDirectoryExist)
import qualified Data.Map as Map

-- SAWScript imports
import qualified SAWScript.AST as SS
    (pShow,
     Located(..),
     Decl(..),
     Pattern(..))
import SAWScript.Exceptions
import SAWScript.MGU (checkDecl)
import SAWScript.Interpreter
    (interpretStmt,
     primDocEnv)
import qualified SAWScript.Lexer (lexSAW)
import qualified SAWScript.Parser (parseStmtSemi, parseExpression)
import SAWScript.TopLevel (TopLevelRW(..), runTopLevel)


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


-- | REPL command parsing.
commands :: CommandMap
commands  = foldl insert emptyTrie commandList
  where
  insert m d = insertTrie (cName d) d m

-- | Notebook command parsing.
nbCommands :: CommandMap
nbCommands  = foldl insert emptyTrie nbCommandList
  where
  insert m d = insertTrie (cName d) d m

-- | A subset of commands safe for Notebook execution
nbCommandList :: [CommandDescr]
nbCommandList  =
  [ CommandDescr ":env"    (NoArg envCmd)
    "display the current sawscript environment"
  , CommandDescr ":type"   (ExprArg typeOfCmd)
    "check the type of an expression"
  , CommandDescr ":?"      (ExprArg helpCmd)
    "display a brief description about a built-in operator"
  , CommandDescr ":help"   (ExprArg helpCmd)
    "display a brief description about a built-in operator"
  ]

commandList :: [CommandDescr]
commandList  =
  nbCommandList ++
  [ CommandDescr ":quit"   (NoArg quitCmd)
    "exit the REPL"
  , CommandDescr ":cd" (FilenameArg cdCmd)
    "set the current working directory"
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

  Command cmd -> cmd `SAWScript.REPL.Monad.catch` handler
                     `SAWScript.REPL.Monad.catchIO` handlerIO
                     `SAWScript.REPL.Monad.catchFail` handler2
                     `SAWScript.REPL.Monad.catchTypeErrors` handlerIO
    where
    handler re = io (putStrLn "" >> print (pp re))
    handler2 s = io (putStrLn "" >> putStrLn s)
    handlerIO e = io (putStrLn "" >> print e)

  Unknown cmd -> io (putStrLn ("Unknown command: " ++ cmd))

  Ambiguous cmd cmds -> io $ do
    putStrLn (cmd ++ " is ambiguous, it could mean one of:")
    putStrLn ("\t" ++ intercalate ", " cmds)


typeOfCmd :: String -> REPL ()
typeOfCmd str =
  do let tokens = SAWScript.Lexer.lexSAW replFileName str
     expr <- case SAWScript.Parser.parseExpression tokens of
       Left err -> fail (show err)
       Right expr -> return expr
     let decl = SS.Decl (getPos expr) (SS.PWild Nothing) Nothing expr
     rw <- getEnvironment
     SS.Decl _pos _ (Just schema) _expr' <-
       either failTypecheck return $ checkDecl (rwTypes rw) (rwTypedef rw) decl
     io $ putStrLn $ SS.pShow schema

quitCmd :: REPL ()
quitCmd  = stop


envCmd :: REPL ()
envCmd = do
  env <- getEnvironment
  let showLName = SS.getVal
  io $ sequence_ [ putStrLn (showLName x ++ " : " ++ SS.pShow v) | (x, v) <- Map.assocs (rwTypes env) ]

helpCmd :: String -> REPL ()
helpCmd cmd
  | null cmd = io (mapM_ putStrLn (genHelp commandList))
  | Just d <- Map.lookup cmd primDocEnv =
                io $ putStr d
-- FIXME? can we restore the ability to lookup doc strings from Cryptol?
--  | Just (ec,_) <- lookup cmd builtIns =
--                io $ print $ helpDoc ec

  | otherwise = do io $ putStrLn $ "// No documentation is available."
                   typeOfCmd cmd


cdCmd :: FilePath -> REPL ()
cdCmd f | null f = io $ putStrLn $ "[error] :cd requires a path argument"
        | otherwise = do
  exists <- io $ doesDirectoryExist f
  if exists
    then io $ setCurrentDirectory f
    else raise $ DirectoryNotFound f

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
  let tokens = SAWScript.Lexer.lexSAW replFileName str
  case SAWScript.Parser.parseStmtSemi tokens of
    Left err -> io $ print err
    Right stmt ->
      do ro <- getTopLevelRO
         ie <- getEnvironment
         ((), ie') <- io $ runTopLevel (interpretStmt True stmt) ro ie
         putEnvironment ie'

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

-- | Uncons a list.
uncons :: [a] -> Maybe (a,[a])
uncons as = case as of
  a:rest -> Just (a,rest)
  _      -> Nothing

-- | Lookup a string in the command list.
findCommand :: String -> [CommandDescr]
findCommand str = lookupTrie str commands

-- | Lookup a string in the notebook-safe command list.
findNbCommand :: String -> [CommandDescr]
findNbCommand str = lookupTrie str nbCommands

-- | Parse a line as a command.
parseCommand :: (String -> [CommandDescr]) -> String -> Maybe Command
parseCommand findCmd line = do
  (cmd,args) <- splitCommand line
  let args' = sanitizeEnd args
  case findCmd cmd of
    [c] -> case cBody c of
      ExprArg     body -> Just (Command (body args'))
      FilenameArg body -> Just (Command (body =<< expandHome args'))
      ShellArg    body -> Just (Command (body args'))
      NoArg       body -> Just (Command  body)

    [] -> case uncons cmd of
      Just (':',_) -> Just (Unknown cmd)
      Just _       -> Just (Command (sawScriptCmd line))
      _            -> Nothing

    cs -> Just (Ambiguous cmd (map cName cs))

  where
  expandHome path =
    case path of
      '~' : c : more | isPathSeparator c -> do dir <- io getHomeDirectory
                                               return (dir </> more)
      _ -> return path
