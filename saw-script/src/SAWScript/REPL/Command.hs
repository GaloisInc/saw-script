{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWScript.REPL.Command
Description :
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

REPL :-commands and execution of REPL text.
-}

module SAWScript.REPL.Command (
    executeText,

    -- Commands
    CommandDescr(..), CommandBody(..),

    -- Command table access
    searchCommandsByPrefix,
    searchExactCommandByPrefix,

    -- Misc utilities
    sanitize
  ) where

import Control.Monad (unless, void)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (modify)
import Data.Char (isSpace)
import Data.Function (on)
import Data.List (intersperse, nub, sortOn)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import System.FilePath ((</>), isPathSeparator)
import System.Directory (
    getHomeDirectory,
    getCurrentDirectory,
    setCurrentDirectory,
    doesDirectoryExist
 )

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import qualified Cryptol.ModuleSystem.Env as ME
import qualified Cryptol.ModuleSystem.Interface as MI
import qualified Cryptol.ModuleSystem.Name as MN (
    nameIdent, nameModPathMaybe, nameTopModuleMaybe
 )
import qualified Cryptol.Parser.AST as CP (ImpName(..))
import qualified Cryptol.REPL.Browse as CB
import qualified Cryptol.TypeCheck.AST as T (ModuleG(..), Submodule(..))
import qualified Cryptol.Utils.Ident as CI (
    identText, modNameChunksText, modNameToText, modPathSplit,
    textToModName
 )

import CryptolSAWCore.GlobalCryptolEnv (eModuleEnv)

import qualified SAWSupport.Pretty as PPS
import qualified SAWSupport.ScopedMap as ScopedMap
import qualified SAWSupport.Trie as Trie
import SAWSupport.Trie (Trie)

import qualified SAWCentral.AST as SS (Name, Schema)
import SAWCentral.AST (PrimitiveLifecycle(..), everythingAvailable, ppSchema, prettySchema, prettyNamedType)
import SAWCentral.Value (Environ(..), TopLevelRO(..), TopLevelRW(..))

import SAWScript.Panic (panic)
import qualified SAWScript.Loader as Loader
import SAWScript.Search (compileSearchPattern, matchSearchPattern)
import SAWScript.Interpreter (interpretReplStmts)

import SAWScript.REPL.Monad
import SAWScript.REPL.Data

import SAWScript.REPL.Command.LLVMCommands ( llvmDisCmd, llvmDisCmdHelp )


replFileName :: FilePath
replFileName = "<stdin>"


------------------------------------------------------------
-- REPL commands

cdCmd :: FilePath -> REPL ()
cdCmd f
    | null f =
        liftIO $ putStrLn "Error: The :cd command requires a path argument"
    | otherwise = do
  exists <- liftIO $ doesDirectoryExist f
  if exists
    then liftIO $ setCurrentDirectory f
    else do
        let f' = "`" <> Text.pack f <> "'"
            msg = "Directory " <> f' <> " not found or not a directory"
        liftIO $ TextIO.putStrLn msg

-- | Display the contents of a Cryptol module (@:cbrowse MODULENAME@)
--   or submodule (@:cbrowse submodule SUBMODULENAME@).  Any loaded
--   (sub)module can be browsed, whether or not it has been imported;
--   it is named by its original name (not by an @import ... as@
--   qualifier).  Private definitions are always included.  With no
--   arguments (@:cbrowse@), all loaded top-level modules are shown.
cbrowseCmd :: [Text] -> REPL ()
cbrowseCmd args =
  case args of
    []                     -> browseAll
    [modName] | modName /= "submodule"
                           -> browseTop modName
    ["submodule", modName] -> browseSub modName
    _ -> liftIO $ TextIO.putStrLn $
           "Usage: :cbrowse [MODULENAME]"
           <> " | :cbrowse submodule SUBMODULENAME"
  where
  -- Show every loaded top-level module (loaded directly or
  -- indirectly), in order of module name.
  browseAll = do
    modEnv <- getModEnv
    let lms = sortOn ME.lmName $
                ME.getLoadedModules (ME.meLoadedModules modEnv)
        showOne lm = do
          let modName = CI.modNameToText (ME.lmName lm)
          say $ "Module `" <> modName <> "':"
          showTop modEnv lm
    sequence_ $ intersperse (say "") $ map showOne lms

  -- Show a loaded top-level module (loaded directly or indirectly).
  browseTop modName = do
    modEnv <- getModEnv
    let mName = CI.textToModName modName
    case ME.lookupModule mName modEnv of
      Nothing -> say $ "Module `" <> modName <> "' is not loaded."
      Just lm -> showTop modEnv lm

  showTop modEnv lm = do
    let ctx0 = ME.lmModContext modEnv lm
        names = MI.ifNames (ME.lmInterface lm)
    showCtx $ withPrivate (MI.ifsDefines names) ctx0

  -- Show a loaded submodule (or submodule alias), named by its path
  -- within its top-level module (e.g. @S1::S2@), or by its fully
  -- qualified path (e.g. @Browse::S1::S2@).  The submodule need not
  -- have been imported.
  browseSub modName = do
    modEnv <- getModEnv
    let want = Text.splitOn "::" modName
        cands = nub [ nm | lm <- ME.getLoadedModules
                                   (ME.meLoadedModules modEnv)
                         , let m = ME.lmModule lm
                         , nm <- Map.keys (T.mSubmodules m)
                                 ++ Map.keys (T.mModAliases m)
                         , want `elem` subPaths nm
                    ]
    case cands of
      [] -> say $ "Submodule `" <> modName <> "' is not loaded."
      [nm] ->
        case ME.modContextOf (CP.ImpNested nm) modEnv of
          Nothing -> say $ "Submodule `" <> modName <> "' not found."
          Just ctx0 -> do
            let defined = fromMaybe (ME.mctxExported ctx0)
                                    (definedIn modEnv (CP.ImpNested nm))
            showCtx $ withPrivate defined ctx0
      nms -> say $ Text.intercalate "\n" $
               ("Submodule `" <> modName <> "' is ambiguous:")
               : [ "  " <> Text.intercalate "::" (last (subPaths nm))
                 | nm <- nms ]

  -- The ways to name a submodule: its path within its top-level
  -- module, and its fully qualified path.
  subPaths nm =
    case MN.nameModPathMaybe nm of
      Nothing -> []
      Just p ->
        let (top, ids) = CI.modPathSplit p
            rel = map CI.identText (ids ++ [MN.nameIdent nm])
        in  [rel, CI.modNameChunksText top ++ rel]

  -- Show all defined names, private ones included.
  withPrivate defined ctx = ctx { ME.mctxExported = defined }

  -- All the names defined in a (sub)module, following module aliases
  -- (bounded, to guard against alias cycles).
  definedIn modEnv = go (10 :: Int)
    where
    go 0 _ = Nothing
    go n imp =
      case imp of
        CP.ImpTop mn ->
          MI.ifsDefines . MI.ifNames . ME.lmInterface
            <$> ME.lookupModule mn modEnv
        CP.ImpNested nm -> do
          top <- MN.nameTopModuleMaybe nm
          m <- ME.lmModule <$> ME.lookupModule top modEnv
          case Map.lookup nm (T.mSubmodules m) of
            Just sm -> Just (MI.ifsDefines (T.smIface sm))
            Nothing -> go (n - 1) =<< Map.lookup nm (T.mModAliases m)

  getModEnv = do
    rw <- getTopLevelRW
    liftIO $ eModuleEnv (rwSharedContext rw)

  say = liftIO . TextIO.putStrLn

  showCtx ctx = do
    ppopts <- getPPOpts
    let doc = PP.unAnnotate $ CB.browseModContext CB.BrowseExported ctx
        -- Cryptol's output has whitespace-only lines; trim them.
        trim = Text.intercalate "\n" . map Text.stripEnd . Text.lines
    say $ trim $ PPS.renderText ppopts doc

envCmd :: REPL ()
envCmd = do
  (rbenv, scopes) <- getSAWScriptVarEnv
  ppopts <- getPPOpts
  liftIO $ do
      let blankline = TextIO.putStrLn ""

      unless (null rbenv) $ do
          let printrb (x, ty) = do
                let x' = PP.pretty x
                    ty' = prettySchema ppopts ty
                    line1 = x' <+> ":"
                    line2 = "rebindable" <+> ty'
                    line2' = PP.flatAlt (PP.indent 3 line2) line2
                    body = PP.group (line1 <> PP.line <> line2')
                TextIO.putStrLn $ PPS.renderText ppopts body
          mapM_ printrb rbenv
          blankline

      let printscope entries = do
            let printentry (x, ty) = do
                  let x' = PP.pretty x
                      ty' = prettySchema ppopts ty
                      line1 = x' <+> ":"
                      line2 = ty'
                      line2' = PP.flatAlt (PP.indent 3 line2) line2
                      body = PP.group (line1 <> PP.line <> line2')
                  TextIO.putStrLn $ PPS.renderText ppopts body
            mapM_ printentry entries

      -- Insert a blank line in the output where there's a scope boundary
      sequence_ $ intersperse blankline $ map printscope scopes

helpCmd :: Text -> REPL ()
helpCmd cmd
  | Text.null cmd = liftIO (mapM_ TextIO.putStrLn genericHelp)
  | otherwise =
    do rw <- getTopLevelRW
       -- Note: there's no rebindable builtins and thus no way to
       -- attach help text to anything rebindable, so we can ignore
       -- the rebindables.
       let Environ varenv _tyenv _cryenvs = rwEnviron rw
       case ScopedMap.lookup cmd varenv of
         Just (_pos, _lc, _ty, _v, Just doc) ->
           liftIO $ mapM_ TextIO.putStrLn doc
         Just (_pos, _lc, _ty, _v, Nothing) -> do
           liftIO $ putStrLn $ "// No documentation is available."
           typeOfCmd cmd
         Nothing ->
           liftIO $ putStrLn "// No such command."
-- FIXME? can we restore the ability to lookup doc strings from Cryptol?
--  | Just (ec,_) <- lookup cmd builtIns =
--                liftIO $ print $ helpDoc ec

pwdCmd :: REPL ()
pwdCmd = liftIO $ do
    cwd <- getCurrentDirectory
    putStrLn cwd

quitCmd :: REPL ()
quitCmd =
    modify (\st -> st { rContinue = False })

searchCmd :: Text -> REPL ()
searchCmd str
  | Text.null str =
      let msg = "Error: The :search command requires at least one argument" in
      liftIO $ putStrLn msg
  | otherwise = do

     -- FUTURE: it would be nice to be able to use the words
     -- "experimental" and "deprecated" in the search term to match
     -- against the lifecycle, to allow doing stuff like searching
     -- for deprecated functions that take Terms.

     -- Always search the entire environment and recognize all type
     -- names in the user's pattern, regardless of whether
     -- enable_experimental or enable_deprecated is in effect. It is
     -- definitely confusing to search for a hidden type and have
     -- search treat that as a free type variable and match all kinds
     -- of things you didn't intend. It is also better to retrieve
     -- invisible/deprecated items and report their existence than to
     -- hide them from the search.
     let avail = everythingAvailable

     ro <- getTopLevelRO
     rw <- getTopLevelRW
     ppopts <- getPPOpts
     let opts = roOptions ro
         environ = rwEnviron rw
         rebindables = rwRebindables rw
     pat <- liftIO $
         Loader.readSchemaPattern opts ppopts replFileName environ rebindables avail str

     let primsAvail = rwPrimsAvail rw
     let Environ varenv tyenv _cryenv = environ

     let search = compileSearchPattern tyenv pat
         check (_pos, lc, ty, _v, _docs) =
             if matchSearchPattern search ty then
                 Just (lc, ty)
             else
                 Nothing
         checkRb (_pos, ty, _v) =
             if matchSearchPattern search ty then
                 Just (Current, ty)
             else
                 Nothing
         varMatches = Map.mapMaybe check $ ScopedMap.flatten varenv
         rbMatches = Map.mapMaybe checkRb rebindables
         allMatches = Map.union varMatches rbMatches

         -- Divide the results into visible, experimental-not-visible,
         -- and deprecated-not-visible.
         inspect ::
             SS.Name ->
             (PrimitiveLifecycle, SS.Schema) ->
             (Map SS.Name (PrimitiveLifecycle, SS.Schema),
              Map SS.Name (PrimitiveLifecycle, SS.Schema),
              Map SS.Name (PrimitiveLifecycle, SS.Schema)) ->
             (Map SS.Name (PrimitiveLifecycle, SS.Schema),
              Map SS.Name (PrimitiveLifecycle, SS.Schema),
              Map SS.Name (PrimitiveLifecycle, SS.Schema))
         inspect name (lc, ty) (vis, ex, dep) =
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
             let empty = (Map.empty, Map.empty, Map.empty) in
             Map.foldrWithKey inspect empty allMatches

         printMatch (name, (lc, ty)) = do
           let name' = PP.pretty name
               ty' = prettySchema ppopts ty
               lc' = case lc of
                   Current -> Nothing
                   WarnDeprecated -> Just "(DEPRECATED AND WILL WARN)"
                   HideDeprecated -> Just "(DEPRECATED AND UNAVAILABLE BY DEFAULT)"
                   Experimental -> Just "(EXPERIMENTAL)"
               line1 = name' <+> ":"
               line2long = PP.indent 3 $ case lc' of
                   Nothing -> ty'
                   Just banner -> ty' <> PP.line <> banner
               line2short = case lc' of
                   Nothing -> ty'
                   Just banner -> ty' <> "  " <> banner  -- separate by 2 spaces
               line2 = PP.flatAlt line2long line2short
               body = PP.group (line1 <> PP.line <> line2)
           TextIO.putStrLn $ PPS.renderText ppopts body
         printMatches matches =
           liftIO $ mapM_ printMatch (Map.assocs matches)

         moreMatches matches =
             let n = Map.size matches in
             if n == 1 then "1 more match"
             else show n ++ " more matches"
         alsoExperimental =
             if not (Map.null expMatches) then
                 liftIO $ putStrLn $ moreMatches expMatches ++ " tagged " ++
                                 "experimental; use enable_experimental to " ++
                                 "see them"
             else
                 pure ()
         alsoDeprecated =
             if not (Map.null depMatches) then
                 liftIO $ putStrLn $ moreMatches depMatches ++ " tagged " ++
                                 "deprecated; use enable_deprecated to " ++
                                 "see them"
             else
                 pure ()

     if not (Map.null visMatches) then do
         printMatches visMatches
         alsoExperimental
         alsoDeprecated
     else do
         liftIO $ putStrLn "No matches."
         if not (Map.null expMatches) then do
             liftIO $ putStrLn $ "The following experimental matches " ++
                                 "require enable_experimental:"
             printMatches expMatches
             alsoDeprecated
         else if not (Map.null depMatches) then do
             liftIO $ putStrLn $ "The following deprecated matches require " ++
                                 "enable_deprecated:"
             printMatches depMatches
         else
             pure ()

tenvCmd :: REPL ()
tenvCmd = do
  scopes <- getSAWScriptTypeEnv
  ppopts <- getPPOpts
  liftIO $ do
      let blankline = TextIO.putStrLn ""

      let printscope entries = do
            let printentry (x, ty) = do
                  let x' = PP.pretty x
                      ty' = prettyNamedType ppopts ty
                      body = x' <+> "=" <+> ty'
                      body' = PP.group body
                  TextIO.putStrLn $ PPS.renderText ppopts body'
            mapM_ printentry entries

      -- Insert a blank line in the output where there's a scope boundary
      sequence_ $ intersperse blankline $ map printscope scopes

typeOfCmd :: Text -> REPL ()
typeOfCmd str
  | Text.null str =
        liftIO $ putStrLn "Error: The :type command requires an argument"
  | otherwise = do
     ro <- getTopLevelRO
     rw <- getTopLevelRW
     ppopts <- getPPOpts
     let opts = roOptions ro
         environ = rwEnviron rw
         rebindables = rwRebindables rw
         avail = rwPrimsAvail rw
     (schema, _expr) <- liftIO $
         Loader.readExpression opts ppopts replFileName environ rebindables avail str
     liftIO $ TextIO.putStrLn $ ppSchema ppopts schema


------------------------------------------------------------
-- Command table

-- | Command description.
data CommandDescr = CommandDescr
  { cName :: Text
  , cAliases :: [Text]
  , cBody :: CommandBody
  , cHelp :: Text
  }

-- When we use `nub` on lists of commands, do the comparison by name.
instance Eq CommandDescr where
  (==) = (==) `on` cName

-- | Schema for argument types of REPL commands.
--
-- XXX: we could distinguish commands that take directories
-- (like :cd) from those that take regular files (though we
-- don't have any)
--
-- XXX: should maybe also distinguish "multiple args of this type"
-- from "one arg of this type".
data CommandBody
  = ExprArg       (Text     -> REPL ())
  | SymbolNameArg (Text     -> REPL ())
  | ModuleTargetArgs (Text -> Text -> REPL ())
  | TypeArgs      (Text     -> REPL ())
  | WordArgs      ([Text]   -> REPL ())
  | FilenameArg   (FilePath -> REPL ())
  | NoArg         (REPL ())

type CommandMap = Trie CommandDescr


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
  , CommandDescr ":search" []    (TypeArgs searchCmd)
    "search the environment by type"
  , CommandDescr ":tenv" []      (NoArg tenvCmd)
    "display the current sawscript type environment"
  , CommandDescr ":type" [":t"]  (ExprArg typeOfCmd)
    "check the type of an expression"
  , CommandDescr ":cbrowse" []   (WordArgs cbrowseCmd)
    "browse all modules, MODULE, or 'submodule SUBMODULE'"
  , CommandDescr ":llvmdis" []   (ModuleTargetArgs llvmDisCmd)
    llvmDisCmdHelp
  , CommandDescr ":?"    []      (SymbolNameArg helpCmd)
    "display a brief description about a built-in operator"
  , CommandDescr ":help" []      (SymbolNameArg helpCmd)
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

genericHelp :: [Text]
genericHelp = map cmdHelp commandList
  where
  cmdHelp cmd = Text.concat [ "  ", cName cmd, pad (cName cmd), cHelp cmd ]
  padding     = 2 + maximum (map (Text.length . cName) commandList)
  pad n       = Text.replicate (max 0 (padding - Text.length n)) " "


------------------------------------------------------------
-- SAWScript execution

-- | Execute some SAWScript text.
executeSAWScriptText :: Text -> REPL ()
executeSAWScriptText str = exceptionProtect $ do
  ro <- getTopLevelRO
  ppopts <- getPPOpts
  let opts = roOptions ro
  -- XXX: for now use liftTopLevel as well as liftIO to make sure this uses
  -- TopLevel's MonadIO instance and therefore goes through the exception goo
  -- in Value.hs. That will make sure stack traces get printed from anything
  -- that blows up in the loader. (Note that while by default stack traces
  -- from here aren't particularly interesting, we might be in a nested REPL.)
  stmts <- liftTopLevel $ liftIO $ Loader.readREPLTextUnchecked opts ppopts replFileName str
  mbPst <- getProofState
  case mbPst of
      Nothing -> void $ liftTopLevel (interpretReplStmts stmts)
      Just _  -> void $ liftProofScript (interpretReplStmts stmts)


------------------------------------------------------------
-- Command execution

-- | Strip leading space.
sanitize :: Text -> Text
sanitize  = Text.dropWhile isSpace

-- | Find commands that begin with a given prefix.
--
-- If given a string that's both itself a command and a prefix of
-- something else, choose that command.
--
-- Deduplicate the results to avoid silliness with command aliases.
searchCommandsByPrefix :: Text -> [CommandDescr]
searchCommandsByPrefix prefix =
    nub $ Trie.lookupWithExact prefix commands

-- | Find the single command that begins with a given prefix.
--
-- If given a string that's both itself a command and a prefix of
-- something else, choose that command. If given a string that's a
-- prefix of one thing, choose that thing. If given a string that's a
-- prefix of multiple things, fail.
--
-- Deduplicate the results to avoid silliness with command aliases.
searchExactCommandByPrefix :: Text -> Maybe CommandDescr
searchExactCommandByPrefix prefix =
    case searchCommandsByPrefix prefix of
        [cmd] -> Just cmd
        _ -> Nothing

-- | Do tilde-expansion on filenames.
expandHome :: Text -> REPL FilePath
expandHome path =
    case Text.uncons path of
        Nothing -> pure ""
        Just ('~', more) -> case Text.uncons more of
            Just (c, more') | isPathSeparator c -> do
                dir <- liftIO getHomeDirectory
                return (dir </> Text.unpack more')
            _ ->
                pure $ Text.unpack path
        Just _ ->
            pure $ Text.unpack path

-- | Execute a REPL :-command.
executeReplCommand :: CommandDescr -> [Text] -> REPL ()
executeReplCommand cmd args0 =
    let noargs action args = case args of
          [] -> action
          _ -> do
              let msg = "The command " <> cName cmd <> " takes no arguments"
              liftIO $ TextIO.putStrLn msg
    in
    let onearg action args = case args of
          [] -> action ""
          [arg] -> action arg
          _ -> do
              let msg = "The command " <> cName cmd <>
                        " takes only one argument"
              liftIO $ TextIO.putStrLn msg
    in
    let twoarg action = \case
          [arg1, arg2] -> action arg1 arg2
          _ -> do
              let msg = "The command " <> cName cmd <>
                        " takes two arguments"
              liftIO $ TextIO.putStrLn msg
              action "" "" -- allow action to generate additional help
    in
    exceptionProtect $ case cBody cmd of
        ExprArg action ->
            action (Text.intercalate " " args0)
        SymbolNameArg action ->
            onearg action args0
        ModuleTargetArgs action -> twoarg action args0
        TypeArgs action ->
            action (Text.intercalate " " args0)
        WordArgs action ->
            action args0
        FilenameArg action -> do
            args' <- mapM expandHome args0
            onearg action args'
        NoArg action ->
            noargs action args0

-- | Execute REPL :-command text.
executeReplCommandText :: Text -> REPL ()
executeReplCommandText text =
    let textWords =
           filter (\w -> not $ Text.null w) $ Text.split isSpace text
    in
    case textWords of
        [] -> pure ()
        cmdName : args ->
            case searchCommandsByPrefix cmdName of
                [] ->
                    -- Historically SAW accepts ":?cmd" without a space
                    if Text.isPrefixOf ":?" cmdName then
                        executeReplCommandText $ ":? " <> Text.drop 2 cmdName
                    else do
                        let msg = "Unknown command: " <> cmdName
                        liftIO $ TextIO.putStrLn msg
                [cmd] ->
                    executeReplCommand cmd args
                cmds -> liftIO $ do
                    let msg1 = cmdName <> " is ambiguous; it could mean one of:"
                        msg2 = Text.intercalate ", " $ map cName cmds
                    TextIO.putStrLn $ msg1
                    TextIO.putStrLn $ "\t" <> msg2

-- | Execute some text typed at the REPL.
executeText :: Text -> REPL ()
executeText text = do
    -- skip whitespace
    let text' = sanitize text
    case Text.uncons text' of
        Nothing ->
            pure ()
        Just (':', _) ->
            executeReplCommandText text'
        Just _ ->
            executeSAWScriptText text'
