{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : Verifier.SAW.Cryptol.Prelude
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Cryptol.Prelude
  ( Module
  , module Verifier.SAW.Cryptol.Prelude
  ) where

import Verifier.SAW.Prelude
import Verifier.SAW.ParserUtils

$(runDecWriter $ do
    prelude <- defineImport [|preludeModule|] preludeModule
    cryptol <- defineModuleFromFile [prelude] "cryptolModule" "saw/Cryptol.sawcore"
    declareSharedModuleFns "Cryptol" (decVal cryptol)
 )
