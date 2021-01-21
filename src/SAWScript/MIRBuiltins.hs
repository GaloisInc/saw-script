{-# LANGUAGE ImplicitParams #-}

-- |
-- Module      : SAWScript.MIRBuiltins
-- Description : Implementations of MIR-related SAW-Script primitives.
-- License     : BSD3
-- Stability   : provisional
module SAWScript.MIRBuiltins where

import           Control.Lens ((^.))
import qualified Data.Map.Strict as Map
import           GHC.Stack (HasCallStack)
import           Lang.Crucible.FunctionHandle (HandleAllocator)
import           Mir.Generate (generateMIR)
import           Mir.Generator (CollectionState (..), RustModule (..), collection, rmCFGs)
import           Mir.Mir (Collection (..))
import           Mir.Pass (rewriteCollection)
import           Mir.Trans (transCollection)
import           Mir.TransCustom (customOps)
import           SAWScript.Value (TopLevel, SAW_CFG (..), getHandleAlloc, io)

mir_load_module :: FilePath -> TopLevel RustModule
mir_load_module file = do
  halloc <- getHandleAlloc
  let ?debug = 1
      ?assertFalseOnError = True
      ?printCrucible = True
  io $ loadAndTranslateMIR file halloc
  
crucible_mir_cfg :: RustModule -> String -> TopLevel SAW_CFG
crucible_mir_cfg rm fn_name = do
  io $ mapM_ print $ Map.keys $ rm ^. rmCFGs 
  return MIR_CFG 
  


--   crucible_llvm_cfg ::
--   Some LLVMModule ->
--   String ->
--   TopLevel SAW_CFG
-- crucible_llvm_cfg (Some lm) fn_name =
--   do let ctx = modTrans lm ^. Crucible.transContext
--      let ?lc = ctx^.Crucible.llvmTypeCtx
--      setupLLVMCrucibleContext False lm $ \cc ->
--        case Map.lookup (fromString fn_name) (Crucible.cfgMap (ccLLVMModuleTrans cc)) of
--          Nothing  -> throwTopLevel $ unwords ["function", fn_name, "not found"]
--          Just (_,cfg) -> return (LLVM_CFG cfg)


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