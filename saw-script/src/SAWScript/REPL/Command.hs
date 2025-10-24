{- |
Module      : SAWScript.REPL.Command
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE OverloadedStrings #-}

module SAWScript.REPL.Command (
    -- * Commands
    CommandDescr(..), CommandBody(..)
  , parseCommand
  , runCommand
  , splitCommand
  , findCommand

    -- Misc utilities
  , handleCtrlC
  , sanitize
  ) where

--import SAWCore.SharedTerm (SharedContext)

import qualified SAWSupport.ScopedMap as ScopedMap
import qualified SAWSupport.Trie as Trie
import SAWSupport.Trie (Trie)

import SAWCentral.Position (getPos, Pos)
import SAWCentral.Value (Environ(..))

import SAWScript.REPL.Monad
import SAWScript.Token (Token)

import Control.Monad (unless, void)

import Data.Char (isSpace,isPunctuation,isSymbol)
import Data.Function (on)
import Data.List (intersperse, nub)
import qualified Data.Text as Text
import Data.Text (Text)
import System.FilePath((</>), isPathSeparator)
import System.Directory(getHomeDirectory,getCurrentDirectory,setCurrentDirectory,doesDirectoryExist)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Text.IO as TextIO

import qualified SAWSupport.Pretty as PPS (pShowText)

-- SAWScript imports
import qualified SAWCentral.Options (Verbosity(..))
import qualified SAWCentral.Position as SS (Pos)
import qualified SAWCentral.AST as SS (
     Name,
     Decl(..),
     Pattern(..),
     Rebindable,
     Schema
 )
import SAWCentral.Exceptions

import SAWScript.Panic (panic)
import SAWScript.Typechecker (checkDecl, checkSchemaPattern)
import SAWScript.Search (compileSearchPattern, matchSearchPattern)
import SAWScript.Interpreter (interpretTopStmt)
import qualified SAWScript.Lexer (lexSAW)
import qualified SAWScript.Parser (parseStmtSemi, parseExpression, parseSchemaPattern)
import SAWCentral.TopLevel (TopLevelRW(..))
import SAWCentral.AST (PrimitiveLifecycle(..), everythingAvailable, Rebindable(..))


-- Commands --------------------------------------------------------------------

-- | Commands.
data Command
  = Command (REPL ())         -- ^ Successfully parsed command
  | Ambiguous Text [Text]     -- ^ Ambiguous command, list of conflicting
                              --   commands
  | Unknown Text              -- ^ The unknown command

-- | Command builder.
data CommandDescr = CommandDescr
  { cName :: Text
  , cAliases :: [Text]
  , cBody :: CommandBody
  , cHelp :: Text
  }

instance Show CommandDescr where
  show cd = Text.unpack $ cName cd

instance Eq CommandDescr where
  (==) = (==) `on` cName

instance Ord CommandDescr where
  compare = compare `on` cName

data CommandBody
  = ExprArg     (Text     -> REPL ())
  | TypeArg     (Text     -> REPL ())
  | FilenameArg (FilePath -> REPL ())
  | ShellArg    (Text     -> REPL ())
  | NoArg       (REPL ())


-- | Convert the command list to a Trie, expanding aliases.
makeCommands :: [CommandDescr] -> CommandMap
makeCommands list  = foldl insert Trie.empty (concatMap expandAliases list)
  where
  insert m (name, d) = Trie.insert name d m
  expandAliases :: CommandDescr -> [(Text, CommandDescr)]
  expandAliases d = (cName d, d) : zip (cAliases d) (repeat d)

-- | REPL command parsing.
commands :: CommandMap
commands = makeCommands commandList

-- | A subset of commands safe for Notebook execution
nbCommandList :: [CommandDescr]
nbCommandList  =
  [ CommandDescr ":env"  []      (NoArg envCmd)
    "display the current sawscript environment"
  , CommandDescr ":search" []    (TypeArg searchCmd)
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

genHelp :: [CommandDescr] -> [Text]
genHelp cs = map cmdHelp cs
  where
  cmdHelp cmd = Text.concat [ "  ", cName cmd, pad (cName cmd), cHelp cmd ]
  padding     = 2 + maximum (map (Text.length . cName) cs)
  pad n       = Text.replicate (max 0 (padding - Text.length n)) " "


-- Command Evaluation ----------------------------------------------------------

-- | Run a command.
runCommand :: Command -> REPL ()
runCommand c = case c of

  Command cmd -> exceptionProtect cmd

  Unknown cmd -> io (TextIO.putStrLn ("Unknown command: " <> cmd))

  Ambiguous cmd cmds -> io $ do
    TextIO.putStrLn (cmd <> " is ambiguous; it could mean one of:")
    TextIO.putStrLn ("\t" <> Text.intercalate ", " cmds)


lexSAW :: FilePath -> Text.Text -> REPL [Token Pos]
lexSAW fileName str = do
  -- XXX wrap printing of positions in the message-printing infrastructure
  case SAWScript.Lexer.lexSAW fileName str of
    Left (_, pos, msg) ->
         fail $ show pos ++ ": " ++ Text.unpack msg
    Right (tokens', Nothing) -> pure tokens'
    Right (_, Just (SAWCentral.Options.Error, pos, msg)) ->
         fail $ show pos ++ ": " ++ Text.unpack msg
    Right (tokens', Just _) -> pure tokens'

typeOfCmd :: Text -> REPL ()
typeOfCmd str
  | Text.null str = io $ putStrLn "[error] :type requires an argument"
  | otherwise =
  do tokens <- lexSAW replFileName str
     expr <- case SAWScript.Parser.parseExpression tokens of
       Left err -> fail (show err)
       Right expr -> return expr
     let pos = getPos expr
         decl = SS.Decl pos (SS.PWild pos Nothing) Nothing expr
     rw <- getTopLevelRW
     decl' <- do
       let primsAvail = rwPrimsAvail rw
           -- XXX it should not be necessary to do this munging
           Environ varenv tyenv _cryenvs = rwEnviron rw
           squash (defpos, lc, ty, _val, _doc) = (defpos, lc, ReadOnlyVar, ty)
           varenv' = Map.map squash $ ScopedMap.flatten varenv
           tyenv' = ScopedMap.flatten tyenv
           rbenv = rwRebindables rw
           rbsquash (defpos, ty, _val) = (defpos, Current, RebindableVar, ty)
           rbenv' = Map.map rbsquash rbenv
           varenv'' = Map.union varenv' rbenv'
       let (errs_or_results, warns) = checkDecl primsAvail varenv'' tyenv' decl
       let issueWarning (msgpos, msg) =
             -- XXX the print functions should be what knows how to show positions...
             putStrLn (show msgpos ++ ": Warning: " ++ msg)
       io $ mapM_ issueWarning warns
       either failTypecheck return errs_or_results
     let schema = case SS.dType decl' of
           Just sch -> sch
           Nothing ->
               -- If the typechecker didn't insert a type, it's bust,
               -- so panic. Not much point in printing the expression
               -- or position in panic, since it's what the user just
               -- typed.
               panic "typeOfCmd" ["Typechecker failed to produce a type"]
     io $ TextIO.putStrLn $ PPS.pShowText schema

searchCmd :: Text -> REPL ()
searchCmd str
  | Text.null str = io $ putStrLn $ "[error] :search requires at least one argument"
  | otherwise =
  do tokens <- lexSAW replFileName str
     pat <- case SAWScript.Parser.parseSchemaPattern tokens of
       Left err -> fail (show err)
       Right pat -> return pat
     rw <- getTopLevelRW

     -- Always search the entire environment and recognize all type
     -- names in the user's pattern, regardless of whether
     -- enable_experimental or enable_deprecated is in effect. It is
     -- definitely confusing to search for a hidden type and have
     -- search treat that as a free type variable and match all kinds
     -- of things you didn't intend. It is also better to retrieve
     -- invisible/deprecated items and report their existence than to
     -- hide them from the search.

     -- FUTURE: it would be nice to be able to use the words
     -- "experimental" and "deprecated" in the search term to match
     -- against the lifecycle, to allow doing stuff like searching
     -- for deprecated functions that take Terms.

     let primsAvail = rwPrimsAvail rw
         -- XXX it should not be necessary to do this munging
         Environ varenv tyenv _cryenv = rwEnviron rw
         rbenv = rwRebindables rw
         squash (pos, lc, ty, _val, _doc) = (pos, lc, ReadOnlyVar, ty)
         varenv' = Map.map squash $ ScopedMap.flatten varenv
         tyenv' = ScopedMap.flatten tyenv
         rbsquash (pos, ty, _val) = (pos, Current, RebindableVar, ty)
         rbenv' = Map.map rbsquash rbenv
         varenv'' = Map.union varenv' rbenv'
         (errs_or_results, warns) = checkSchemaPattern everythingAvailable varenv'' tyenv' pat
     let issueWarning (msgpos, msg) =
           -- XXX the print functions should be what knows how to show positions...
           putStrLn (show msgpos ++ ": Warning: " ++ msg)
     io $ mapM_ issueWarning warns
     pat' <- either failTypecheck return $ errs_or_results
     let search = compileSearchPattern tyenv pat'
         keep (_pos, _lc, _rb, ty) = matchSearchPattern search ty
         allMatches = Map.filter keep varenv'

         -- Divide the results into visible, experimental-not-visible,
         -- and deprecated-not-visible.
         inspect ::
             SS.Name ->
             (SS.Pos, PrimitiveLifecycle, SS.Rebindable, SS.Schema) ->
             (Map SS.Name (PrimitiveLifecycle, SS.Schema),
              Map SS.Name (PrimitiveLifecycle, SS.Schema),
              Map SS.Name (PrimitiveLifecycle, SS.Schema)) ->
             (Map SS.Name (PrimitiveLifecycle, SS.Schema),
              Map SS.Name (PrimitiveLifecycle, SS.Schema),
              Map SS.Name (PrimitiveLifecycle, SS.Schema))
         inspect name (_pos, lc, _rb, ty) (vis, ex, dep) =
             if Set.member lc primsAvail then
                 (Map.insert name (lc, ty) vis, ex, dep)
             else case lc of
               Current -> oops
               WarnDeprecated -> oops
               HideDeprecated ->
                 (vis, ex, Map.insert name (lc, ty) dep)
               Experimental ->
                 (vis, Map.insert name (lc, ty) ex, dep)
             where
               oops =
                 panic "searchCmd" [
                     "Found non-visible object " <> Text.pack (show name) <>
                     " with unexpected lifecycle " <> Text.pack (show lc)
                 ]
         (visMatches, expMatches, depMatches) =
             Map.foldrWithKey inspect (Map.empty, Map.empty, Map.empty) allMatches

         printMatch (name, (lc, ty)) = do
           let ty' = PPS.pShowText ty
               lc' = case lc of
                   Current -> ""
                   WarnDeprecated -> "  (DEPRECATED AND WILL WARN)"
                   HideDeprecated -> "  (DEPRECATED AND UNAVAILABLE BY DEFAULT)"
                   Experimental -> "  (EXPERIMENTAL)"
           TextIO.putStrLn (name <> " : " <> ty' <> lc')
         printMatches matches =
           io $ mapM_ printMatch (Map.assocs matches)

         moreMatches matches =
             let n = Map.size matches in
             if n == 1 then "1 more match"
             else show n ++ " more matches"
         alsoExperimental =
             if not (Map.null expMatches) then
                 io $ putStrLn $ moreMatches expMatches ++ " tagged " ++
                                 "experimental; use enable_experimental to " ++
                                 "see them"
             else
                 pure ()
         alsoDeprecated =
             if not (Map.null depMatches) then
                 io $ putStrLn $ moreMatches depMatches ++ " tagged " ++
                                 "deprecated; use enable_deprecated to " ++
                                 "see them"
             else
                 pure ()

     if not (Map.null visMatches) then do
         printMatches visMatches
         alsoExperimental
         alsoDeprecated
     else do
         io $ putStrLn "No matches."
         if not (Map.null expMatches) then do
             io $ putStrLn $ "The following experimental matches require " ++
                             "enable_experimental:"
             printMatches expMatches
             alsoDeprecated
         else if not (Map.null depMatches) then do
             io $ putStrLn $ "The following deprecated matches require " ++
                             "enable_deprecated:"
             printMatches depMatches
         else
             pure ()


quitCmd :: REPL ()
quitCmd  = stop


envCmd :: REPL ()
envCmd = do
  rw <- getTopLevelRW
  let Environ varenv _tyenv _cryenv = rwEnviron rw
      rbenv = rwRebindables rw
      avail = rwPrimsAvail rw

  -- print the rebindable globals first, if any
  unless (Map.null rbenv) $ do
      let rbsay (x, (_pos, ty, _v)) = do
              let ty' = PPS.pShowText ty
              TextIO.putStrLn (x <> " : rebindable " <> ty')
      io $ mapM_ rbsay $ Map.assocs rbenv
      io $ TextIO.putStrLn ""

  -- print the normal environment
  let say (x, (_pos, _lc, ty, _v, _doc)) = do
          let ty' = PPS.pShowText ty
          TextIO.putStrLn (x <> " : " <> ty')
      -- Print only the visible objects
      keep (_x, (_pos, lc, _ty, _v, _doc)) = Set.member lc avail
      -- Insert a blank line in the output where there's a scope boundary
      printScope mItems = case mItems of
          Nothing -> TextIO.putStrLn ""
          Just items -> mapM_ say $ filter keep items
      -- Reverse the list of scopes so the innermost prints last,
      -- because that's what people will expect to see.
      itemses = reverse $ ScopedMap.scopedAssocs varenv
  io $ mapM_ printScope $ intersperse Nothing $ map Just itemses

tenvCmd :: REPL ()
tenvCmd = do
  rw <- getTopLevelRW
  let avail = rwPrimsAvail rw
      Environ _varenv tyenv _cryenv = rwEnviron rw
      say (x, (_lc, ty)) = do
          let ty' = PPS.pShowText ty
          TextIO.putStrLn (x <> " : " <> ty')
      -- Print only the visible objects
      keep (_x, (lc, _ty)) = Set.member lc avail
      -- Insert a blank line in the output where there's a scope boundary
      printScope mItems = case mItems of
          Nothing -> TextIO.putStrLn ""
          Just items -> mapM_ say $ filter keep items
      -- Reverse the list of scopes so the innermost prints last,
      -- because that's what people will expect to see.
      itemses = reverse $ ScopedMap.scopedAssocs tyenv
  io $ mapM_ printScope $ intersperse Nothing $ map Just itemses

helpCmd :: Text -> REPL ()
helpCmd cmd
  | Text.null cmd = io (mapM_ TextIO.putStrLn (genHelp commandList))
  | otherwise =
    do rw <- getTopLevelRW
       -- Note: there's no rebindable builtins and thus no way to
       -- attach help text to anything rebindable, so we can ignore
       -- the rebindables.
       let Environ varenv _tyenv _cryenvs = rwEnviron rw
       case ScopedMap.lookup cmd varenv of
         Just (_pos, _lc, _ty, _v, Just doc) ->
           io $ mapM_ TextIO.putStrLn doc
         Just (_pos, _lc, _ty, _v, Nothing) -> do
           io $ putStrLn $ "// No documentation is available."
           typeOfCmd cmd
         Nothing ->
           io $ putStrLn "// No such command."
-- FIXME? can we restore the ability to lookup doc strings from Cryptol?
--  | Just (ec,_) <- lookup cmd builtIns =
--                io $ print $ helpDoc ec


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
sawScriptCmd :: Text -> REPL ()
sawScriptCmd str = do
  tokens <- lexSAW replFileName str
  case SAWScript.Parser.parseStmtSemi tokens of
    Left err -> io $ print err
    Right stmt ->
      do mr <- getProofStateRef
         case mr of
           Nothing -> void $ liftTopLevel (interpretTopStmt True stmt)
           Just r  -> void $ liftProofScript (interpretTopStmt True stmt) r

replFileName :: FilePath
replFileName = "<stdin>"

-- C-c Handlings ---------------------------------------------------------------

-- XXX this should probably do something a bit more specific.
handleCtrlC :: REPL ()
handleCtrlC  = io (putStrLn "Ctrl-C")


-- Utilities -------------------------------------------------------------------

type CommandMap = Trie CommandDescr


-- Command Parsing -------------------------------------------------------------

-- | Strip leading space.
sanitize :: Text -> Text
sanitize  = Text.dropWhile isSpace

-- | Strip trailing space.
sanitizeEnd :: Text -> Text
sanitizeEnd = Text.dropWhileEnd isSpace

-- | Split at the first word boundary.
splitCommand :: Text -> Maybe (Text, Text)
splitCommand txt = do
  (c, more) <- Text.uncons (sanitize txt) 
  case c of
    ':'
      | (as,bs) <- Text.span (\x -> isPunctuation x || isSymbol x) more
      , not (Text.null as) -> Just (Text.cons ':' as, sanitize bs)

      | (as,bs) <- Text.break isSpace more
      , not (Text.null as) -> Just (Text.cons ':' as, sanitize bs)

      | otherwise -> Nothing

    _ -> Just (Text.cons c more, "")

-- | Look up a string in a command list. If given a string that's both
-- itself a command and a prefix of something else, choose that
-- command; otherwise such commands are inaccessible. Also, deduplicate
-- the list of results to avoid silliness with command aliases.
findSomeCommand :: Text -> CommandMap -> [CommandDescr]
findSomeCommand str commandTable = nub $ Trie.lookupWithExact str commandTable

-- | Look up a string in the command list.
findCommand :: Text -> [CommandDescr]
findCommand str = findSomeCommand str commands

-- | Parse a line as a command.
parseCommand :: (Text -> [CommandDescr]) -> Text -> Maybe Command
parseCommand findCmd line = do
  (cmd,args) <- splitCommand line
  let args' = sanitizeEnd args
  case findCmd cmd of
    -- nothing matched; if it doesn't begin with a colon, eval it
    [] -> case Text.uncons cmd of
      Nothing -> Nothing
      Just (':', _) -> Just (Unknown cmd)
      Just _ -> Just (Command (sawScriptCmd line))

    -- matched exactly one command; run it
    [c] -> case cBody c of
      ExprArg     body -> Just (Command (body args'))
      TypeArg     body -> Just (Command (body args'))
      FilenameArg body -> Just (Command (body =<< expandHome args'))
      ShellArg    body -> Just (Command (body args'))
      NoArg       body -> Just (Command  body)

    -- matched several things; complain
    cs -> Just (Ambiguous cmd (map cName cs))

  where
  expandHome path =
    case Text.unpack path of
      '~' : c : more | isPathSeparator c -> do dir <- io getHomeDirectory
                                               return (dir </> more)
      path' -> pure path'
