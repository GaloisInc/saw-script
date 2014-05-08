{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
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
