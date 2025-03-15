{- |
Module      : SAWCore.SAWCore
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

{-# LANGUAGE TemplateHaskell #-}

module SAWCore.SAWCore
  ( module SAWCore.SharedTerm
  , module SAWCore.ExternalFormat
  , Module
  , preludeModule
  , scLoadPreludeModule
  ) where

import SAWCore.SharedTerm
import SAWCore.Prelude
import SAWCore.ExternalFormat
