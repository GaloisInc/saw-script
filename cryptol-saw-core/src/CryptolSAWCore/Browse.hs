{- |
Module      : CryptolSAWCore.Browse
Description : Browsing the contents of loaded Cryptol (sub)modules
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Queries over a Cryptol 'ME.ModuleEnv' for browsing loaded modules and
submodules (as done by the SAW REPL's @:cbrowse@ command).

Any loaded (sub)module can be browsed, whether or not it has been
imported; it is named by its original name (not by an @import ... as@
qualifier).  Private definitions are always included; the virtual
submodules that Cryptol generates are not.
-}

{-# LANGUAGE OverloadedStrings #-}

module CryptolSAWCore.Browse
  ( ME.ModuleEnv
  , ME.ModContext
  , BrowseError(..)
  , browseErrorText
  , loadedModuleNames
  , allModuleContexts
  , moduleContext
  , submoduleContext
  , browseDoc
  ) where

import Data.List (nub, sortOn)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Prettyprinter as PP

import qualified Cryptol.ModuleSystem.Env as ME
import qualified Cryptol.ModuleSystem.Interface as MI
import qualified Cryptol.ModuleSystem.Name as MN (
    Name, nameIdent, nameModPathMaybe
 )
import qualified Cryptol.Parser.AST as CP (ImpName(..))
import qualified Cryptol.REPL.Browse as CB
import qualified Cryptol.TypeCheck.AST as T (ModuleG(..), Submodule(..))
import qualified Cryptol.Utils.Ident as CI (
    identText, modNameChunksText, modNameToText, modPathSplit,
    textToModName
 )


-- | Why a (sub)module could not be browsed.  Each constructor holds
--   the name as given.
data BrowseError
  = ModuleNotLoaded Text
  | SubmoduleNotLoaded Text
  | SubmoduleNotFound Text
  | SubmoduleAmbiguous Text [Text]
      -- ^ with the fully qualified names of the candidates

browseErrorText :: BrowseError -> Text
browseErrorText err =
  case err of
    ModuleNotLoaded nm    -> "Module `" <> nm <> "' is not loaded."
    SubmoduleNotLoaded nm -> "Submodule `" <> nm <> "' is not loaded."
    SubmoduleNotFound nm  -> "Submodule `" <> nm <> "' not found."
    SubmoduleAmbiguous nm cands ->
      Text.intercalate "\n" $
        ("Submodule `" <> nm <> "' is ambiguous:")
        : map ("  " <>) cands

-- | All loaded top-level modules (loaded directly or indirectly), in
--   order of module name.
loadedModules :: ME.ModuleEnv -> [ME.LoadedModule]
loadedModules modEnv =
  sortOn ME.lmName $ ME.getLoadedModules (ME.meLoadedModules modEnv)

-- | The names of all loaded top-level modules, in order.
loadedModuleNames :: ME.ModuleEnv -> [Text]
loadedModuleNames = map (CI.modNameToText . ME.lmName) . loadedModules

-- | The names and contexts of all loaded top-level modules, in order.
allModuleContexts :: ME.ModuleEnv -> [(Text, ME.ModContext)]
allModuleContexts modEnv = map (topContext modEnv) (loadedModules modEnv)

-- | The (fully qualified) name and context of a loaded top-level
--   module (loaded directly or indirectly).
moduleContext ::
  ME.ModuleEnv -> Text -> Either BrowseError (Text, ME.ModContext)
moduleContext modEnv modName =
  case ME.lookupModule (CI.textToModName modName) modEnv of
    Nothing -> Left (ModuleNotLoaded modName)
    Just lm -> Right (topContext modEnv lm)

topContext :: ME.ModuleEnv -> ME.LoadedModule -> (Text, ME.ModContext)
topContext modEnv lm =
  ( CI.modNameToText (ME.lmName lm)
  , withoutVirtuals modEnv (ME.lmModContextWith MI.ifsDefines modEnv lm)
  )

-- | The fully qualified name and context of a loaded submodule,
--   submodule alias, or submodule functor (or a submodule nested in a
--   functor), named by its path within its top-level module (e.g.
--   @S1::S2@), or by its fully qualified path (e.g. @M::S1::S2@).
--   Interface submodules are not supported (Cryptol's
--   'ME.modContextOfWith' does not support them).
submoduleContext ::
  ME.ModuleEnv -> Text -> Either BrowseError (Text, ME.ModContext)
submoduleContext modEnv modName =
  case cands of
    [] -> Left (SubmoduleNotLoaded modName)
    [nm] ->
      case ME.modContextOfWith MI.ifsDefines (CP.ImpNested nm) modEnv of
        Nothing  -> Left (SubmoduleNotFound modName)
        Just ctx -> Right (fullName nm, withoutVirtuals modEnv ctx)
    nms -> Left (SubmoduleAmbiguous modName (map fullName nms))
  where
  want = Text.splitOn "::" modName
  cands = nub [ nm | lm <- ME.getLoadedModules (ME.meLoadedModules modEnv)
                   , nm <- nestedIn (ME.lmModule lm)
                   , want `elem` subPaths nm
              ]
  fullName nm = Text.intercalate "::" (last (subPaths nm))

-- | The ways to name a submodule: its path within its top-level
--   module, and its fully qualified path.
subPaths :: MN.Name -> [[Text]]
subPaths nm =
  case MN.nameModPathMaybe nm of
    Nothing -> []
    Just p ->
      let (top, ids) = CI.modPathSplit p
          rel = map CI.identText (ids ++ [MN.nameIdent nm])
      in  [rel, CI.modNameChunksText top ++ rel]

-- | The submodules, submodule aliases, and submodule functors in a
--   module, including those nested in functors.  (Those nested in
--   ordinary submodules are already included in the module's maps.)
nestedIn :: T.ModuleG a -> [MN.Name]
nestedIn m =
     Map.keys (T.mSubmodules m)
  ++ Map.keys (T.mModAliases m)
  ++ Map.keys (T.mFunctors m)
  ++ concatMap nestedIn (Map.elems (T.mFunctors m))

-- | The virtual submodules in all loaded modules (including those
--   nested in functors): these are generated by Cryptol, e.g., to hold
--   the arguments of a functor instantiation.
virtuals :: ME.ModuleEnv -> Set MN.Name
virtuals modEnv =
  Set.fromList
    [ nm | lm <- ME.getLoadedModules (ME.meLoadedModules modEnv)
         , nm <- virtualIn (ME.lmModule lm)
    ]
  where
  virtualIn :: T.ModuleG a -> [MN.Name]
  virtualIn m =
       Map.keys (Map.filter T.smVirtual (T.mSubmodules m))
    ++ concatMap virtualIn (Map.elems (T.mFunctors m))

-- | Don't show virtual submodules (which Cryptol keeps private, but
--   we show private names).
withoutVirtuals :: ME.ModuleEnv -> ME.ModContext -> ME.ModContext
withoutVirtuals modEnv ctx =
  ctx { ME.mctxExported =
          Set.difference (ME.mctxExported ctx) (virtuals modEnv) }

-- | Display the names in a context's 'ME.mctxExported': Cryptol's
--   @:browse@ sections, plus a section for submodule aliases.
browseDoc :: ME.ModContext -> PP.Doc ann
browseDoc ctx =
  PP.unAnnotate $
    CB.browseModContextWith sections CB.BrowseExported ctx
  where
  sections =
    [ CB.browseSignatures
    , CB.browseMods
    , CB.browseModAliases
    , CB.browseFunctors
    , CB.browseTSyns
    , CB.browsePrimTys
    , CB.browseNominalTypes
    , CB.browseVars
    ]
