{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : Verifier.SAW.Cryptol.Prelude
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Cryptol.PreludeM
  ( Module
  , module Verifier.SAW.Cryptol.PreludeM
  , scLoadPreludeModule
  ) where

import Verifier.SAW.Prelude
import Verifier.SAW.ParserUtils

$(defineModuleFromFileWithFns
  "specMModule" "scLoadSpecMModule" "saw/SpecM.sawcore")

$(defineModuleFromFileWithFns
  "cryptolMModule" "scLoadCryptolMModule" "saw/CryptolM.sawcore")
