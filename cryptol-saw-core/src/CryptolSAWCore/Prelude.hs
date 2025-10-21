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
  ( module CryptolSAWCore.Prelude
  , cryptolModule
  , scLoadPreludeModule
  ) where

import SAWCore.Prelude
import SAWCore.ParserUtils

import CryptolSAWCore.Module (cryptolModule)

$(defineModuleFns cryptolModule "scLoadCryptolModule")
