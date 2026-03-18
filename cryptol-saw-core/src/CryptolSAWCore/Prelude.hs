{- |
Module      : CryptolSAWCore.Prelude
Description : Cryptol prelude module for SAWCore
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module provides access to the SAWCore Cryptol support module.

The actual module is found in "Module"; this module wraps that one to
avoid recompiling it as often.

XXX: this module also re-exports SAWCore's `scLoadPreludeModule`,
which loads the SAWCore prelude, and probably shouldn't.
-}

module CryptolSAWCore.Prelude
  ( module CryptolSAWCore.Prelude
  , cryptolModule
  , scLoadPreludeModule
  ) where

import SAWCore.Prelude
import SAWCore.SharedTerm (SharedContext)
import SAWCore.Typechecker (tcInsertModule)

import CryptolSAWCore.Module (cryptolModule)

-- | Function to load the Cryptol support module into a SAWCore `SharedContext`.
scLoadCryptolModule :: SharedContext -> IO ()
scLoadCryptolModule sc = tcInsertModule sc cryptolModule
