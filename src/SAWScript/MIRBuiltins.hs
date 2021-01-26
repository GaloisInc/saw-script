{-# LANGUAGE ImplicitParams #-}

-- |
-- Module      : SAWScript.MIRBuiltins
-- Description : Implementations of MIR-related SAW-Script primitives.
-- License     : BSD3
-- Stability   : provisional
module SAWScript.MIRBuiltins where

import           Control.Lens ((^.))
import           Data.List (find, isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import           GHC.Stack (HasCallStack)
import           Lang.Crucible.FunctionHandle (HandleAllocator)
import           Mir.DefId (DefId)
import           Mir.Generate (generateMIR)
import           Mir.Generator (CollectionState (..), RustModule (..), collection, rmCFGs)
import           Mir.Mir (Collection (..))
import           Mir.Pass (rewriteCollection)
import           Mir.Trans (transCollection)
import           Mir.TransCustom (customOps)
import           SAWScript.Value (TopLevel, SAW_CFG (..), getHandleAlloc, io, throwTopLevel)

import Debug.Trace

mir_load_module :: FilePath -> TopLevel RustModule
mir_load_module file = do
  halloc <- getHandleAlloc
  let ?debug = 1
      ?assertFalseOnError = True
      ?printCrucible = False
  io $ loadAndTranslateMIR file halloc
  
crucible_mir_cfg :: RustModule -> String -> TopLevel SAW_CFG
crucible_mir_cfg rm fn_name = do
  -- TODO: This just does infix matching instead of actually getting the RefId
  let keys = Map.keys $ rm ^. rmCFGs
  case find (isInfixOf fn_name . Text.unpack) keys of
    Nothing -> throwTopLevel "No matching function found in the environment"
    Just key -> do
      traceM $ "Matched function with RefId: " <> Text.unpack key
      case Map.lookup key (rm ^. rmCFGs) of
        Just cfg -> return $ MIR_CFG cfg
        Nothing -> throwTopLevel "This should never happen"

rustModuleFunctions :: RustModule -> [String]
rustModuleFunctions rm = undefined

rustModuleDefs :: RustModule -> DefId
rustModuleDefs rm = undefined



-- These functions borrowed from Stuart's branch of crucible/crux-mir.
-- Temporarily moved here so that we can make changes without having to move
-- Heapster over to that branch.

-- | Translate a MIR collection to Crucible
translateMIR ::
  (HasCallStack, ?debug :: Int, ?assertFalseOnError :: Bool, ?printCrucible :: Bool) =>
  CollectionState ->
  Collection ->
  HandleAllocator ->
  IO RustModule
translateMIR lib col halloc =
  let ?customOps = customOps
   in let col0 = let ?mirLib = lib ^. collection in rewriteCollection col
       in let ?libCS = lib in transCollection col0 halloc

loadAndTranslateMIR ::
  (HasCallStack, ?debug :: Int, ?assertFalseOnError :: Bool, ?printCrucible :: Bool) =>
  FilePath ->
  HandleAllocator ->
  IO RustModule
loadAndTranslateMIR path halloc = do
  col <- generateMIR path False
  translateMIR mempty col halloc