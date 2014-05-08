{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Verifier.SAW.CryptolPrelude
  ( Module
  , module Verifier.SAW.CryptolPrelude
  ) where

import Verifier.SAW.Prelude
import Verifier.SAW.ParserUtils

$(runDecWriter $ do
    prelude <- defineImport [|preludeModule|] preludeModule
    cryptol <- defineModuleFromFile [prelude] "cryptolModule" "prelude/Cryptol.sawcore"
    declareSharedModuleFns "Cryptol" (decVal cryptol)
 )
