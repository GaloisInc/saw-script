{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWScript.REPL.Command.CryptolCommands
Description :
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

REPL :-commands for working with Cryptol modules.

  NOTE on structure:
    This follows the existing Command/*.hs pattern:
      - little is put in ../Command.hs
      - here we do argument parsing, IO, and the output formatting.
      - we call external worker functions as needed.
-}

module SAWScript.REPL.Command.CryptolCommands
  (
    cbrowseCmd, cbrowseCmdHelp
  )
where

import Control.Monad.IO.Class (liftIO)
import Data.List (dropWhileEnd, intersperse)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO

import qualified CryptolSAWCore.Browse as Browse
import CryptolSAWCore.GlobalCryptolEnv (eModuleEnv)

import qualified SAWSupport.Pretty as PPS

import SAWCentral.Value (TopLevelRW(..))

import SAWScript.REPL.Monad


cbrowseCmdHelp :: Text
cbrowseCmdHelp =
  "list modules '-l', or browse modules ['MODULE' | 'submodule SUBMODULE']"

-- | Display the contents of a Cryptol module (@:cbrowse MODULENAME@)
--   or submodule (@:cbrowse submodule SUBMODULENAME@).  Any loaded
--   (sub)module can be browsed, whether or not it has been imported;
--   it is named by its original name (not by an @import ... as@
--   qualifier).  Private definitions are always included.  With no
--   arguments (@:cbrowse@), all loaded top-level modules are shown;
--   with @:cbrowse -l@, just their names are listed.
--   See "CryptolSAWCore.Browse".
cbrowseCmd :: [Text] -> REPL ()
cbrowseCmd args =
  case args of
    []                     -> browseAll
    ["-l"]                 -> mapM_ say . Browse.loadedModuleNames
                                =<< getModEnv
    [modName] | modName /= "submodule"
                           -> browseWith Browse.moduleContext modName
    ["submodule", modName] -> browseWith Browse.submoduleContext modName
    _ -> say $
           "Usage: :cbrowse -l"
           <> " | :cbrowse [MODULENAME]"
           <> " | :cbrowse submodule SUBMODULENAME"
  where
  browseAll = do
    ctxs <- Browse.allModuleContexts <$> getModEnv
    sequence_ $ intersperse (say "") $ map (uncurry showCtx) ctxs

  browseWith find modName = do
    modEnv <- getModEnv
    case find modEnv modName of
      Left err          -> say (Browse.browseErrorText err)
      Right (name, ctx) -> showCtx name ctx

  say = liftIO . TextIO.putStrLn

  -- Show a (sub)module's contents under a "From MODNAME" header,
  -- underlined, with the contents indented by 2.
  showCtx :: Text -> Browse.ModContext -> REPL ()
  showCtx modName ctx = do
    ppopts <- getPPOpts
    let header = "From " <> modName
        -- Cryptol's output has whitespace-only lines and trailing
        -- blank lines; trim them.
        body = dropWhileEnd Text.null $ map Text.stripEnd $
                 Text.lines $ PPS.renderText ppopts (Browse.browseDoc ctx)
        indent l = if Text.null l then l else "  " <> l
    say $ Text.intercalate "\n" $
      header : Text.replicate (Text.length header) "-" : map indent body

getModEnv :: REPL Browse.ModuleEnv
getModEnv = do
  rw <- getTopLevelRW
  liftIO $ eModuleEnv (rwSharedContext rw)
