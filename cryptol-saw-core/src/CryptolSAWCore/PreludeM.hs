{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : CryptolSAWCore.PreludeM
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module CryptolSAWCore.PreludeM
  ( Module
  , module CryptolSAWCore.PreludeM
  , scLoadPreludeModule
  ) where

import SAWCore.Prelude
import SAWCore.ParserUtils

$(defineModuleFromFileWithFns
  "specMModule" "scLoadSpecMModule" "cryptol-saw-core/saw/SpecM.sawcore")

$(defineModuleFromFileWithFns
  "cryptolMModule" "scLoadCryptolMModule" "cryptol-saw-core/saw/CryptolM.sawcore")
