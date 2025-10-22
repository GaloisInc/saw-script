{- |
Module      : CryptolSAWCore.Prelude
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
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

scLoadCryptolModule :: SharedContext -> IO ()
scLoadCryptolModule sc = tcInsertModule sc cryptolModule
