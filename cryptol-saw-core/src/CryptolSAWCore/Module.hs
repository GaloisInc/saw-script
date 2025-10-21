{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : CryptolSAWCore.Prelude.Module
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module CryptolSAWCore.Module
  ( cryptolModule
  ) where

import SAWCore.Parser.TH

$(defineModuleFromFile "cryptolModule" "cryptol-saw-core/saw/Cryptol.sawcore")
