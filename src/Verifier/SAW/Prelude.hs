{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Verifier.SAW.Prelude
  ( Module
  , module Verifier.SAW.Prelude
  , module Verifier.SAW.Prelude.Constants
  ) where

import Verifier.SAW.ParserUtils
import Verifier.SAW.Prelude.Constants

$(runDecWriter $ do
    prelude <- defineModuleFromFile [] "preludeModule" "prelude/Prelude.saw"
    declareSharedModuleFns "Prelude" (decVal prelude)
 )

