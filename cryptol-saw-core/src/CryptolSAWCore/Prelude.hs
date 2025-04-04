{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : Verifier.SAW.Cryptol.Prelude
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Cryptol.Prelude
  ( Module
  , module Verifier.SAW.Cryptol.Prelude
  , scLoadPreludeModule
  ) where

import Verifier.SAW.Prelude
import Verifier.SAW.ParserUtils

$(defineModuleFromFileWithFns
  "cryptolModule" "scLoadCryptolModule" "cryptol-saw-core/saw/Cryptol.sawcore")
