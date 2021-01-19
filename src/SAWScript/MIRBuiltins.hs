{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}

-- |
-- Module      : SAWScript.MIRBuiltins
-- Description : Implementations of MIR-related SAW-Script primitives.
-- License     : BSD3
-- Stability   : provisional
module SAWScript.MIRBuiltins where

import Control.Lens ((^.))
import GHC.Stack (HasCallStack)
import Lang.Crucible.FunctionHandle (HandleAllocator (..))
import Mir.Generate (generateMIR)
import Mir.Generator (CollectionState (..), RustModule (..), collection)
import Mir.Mir (Collection (..))
import Mir.Pass (rewriteCollection)
import Mir.Trans (transCollection)
import Mir.TransCustom (customOps)
import SAWScript.Value (TopLevel, getHandleAlloc, io)

mir_load_module :: FilePath -> TopLevel RustModule
mir_load_module file = do
  halloc <- getHandleAlloc
  let ?debug = 0
      ?assertFalseOnError = False
      ?printCrucible = False
  io $ loadAndTranslateMIR file halloc
  

-- llvm_load_module :: FilePath -> TopLevel (Some CMS.LLVMModule)
-- llvm_load_module file =
--   do laxArith <- gets rwLaxArith
--      let ?laxArith = laxArith
--      halloc <- getHandleAlloc
--      io (CMS.loadLLVMModule file halloc) >>= \case
--        Left err -> fail (LLVM.formatError err)
--        Right llvm_mod -> return llvm_mod

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