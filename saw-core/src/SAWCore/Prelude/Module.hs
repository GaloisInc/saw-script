{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : SAWCore.Prelude.Module
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Prelude.Module
  ( preludeModule
  ) where

import SAWCore.Parser.TH

$(defineModuleFromFile "preludeModule" "saw-core/prelude/Prelude.sawcore")
