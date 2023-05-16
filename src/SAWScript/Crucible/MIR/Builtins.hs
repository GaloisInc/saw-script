{-# LANGUAGE ImplicitParams #-}

-- | Implementations of Crucible-related SAWScript primitives for MIR.
module SAWScript.Crucible.MIR.Builtins
  ( mir_load_module
  ) where

import qualified Data.ByteString.Lazy as BSL

import Mir.Generator
import Mir.ParseTranslate

import SAWScript.Options
import SAWScript.Value

-- | Load a MIR JSON file and return a handle to it.
mir_load_module :: String -> TopLevel RustModule
mir_load_module inputFile = do
   b <- io $ BSL.readFile inputFile

   opts <- getOptions
   let ?debug = simVerbose opts
   -- For now, we use the same default settings for implicit parameters as in
   -- crux-mir. We may want to add options later that allow configuring these.
   let ?assertFalseOnError = True
   let ?printCrucible = False

   halloc <- getHandleAlloc
   col <- io $ parseMIR inputFile b
   io $ translateMIR mempty col halloc
