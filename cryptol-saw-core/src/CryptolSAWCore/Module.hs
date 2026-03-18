{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK not-home #-}

{- |
Module      : CryptolSAWCore.Prelude.Module
Description : Cryptol support module for SAWCore
Copyright   : Galois, Inc. 2025-2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module loads the Cryptol support module at compile time using
Template Haskell.
-}

module CryptolSAWCore.Module
  ( cryptolModule
  ) where

import SAWCore.Parser.TH

-- | The SAWCore `SAWCore.Module.Module` handle for the Cryptol module.
$(defineModuleFromFile "cryptolModule" "cryptol-saw-core/saw/Cryptol.sawcore")
