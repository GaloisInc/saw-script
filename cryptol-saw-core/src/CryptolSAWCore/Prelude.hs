{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : CryptolSAWCore.Prelude
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module CryptolSAWCore.Prelude
  ( Module
  , module CryptolSAWCore.Prelude
  , scLoadPreludeModule
  ) where

import SAWCore.Prelude
import SAWCore.ParserUtils

$(defineModuleFromFileWithFns
  "cryptolModule" "scLoadCryptolModule" "cryptol-saw-core/saw/Cryptol.sawcore")
