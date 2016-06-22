{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : Verifier.SAW.Prelude
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Prelude
  ( Module
  , module Verifier.SAW.Prelude
  , module Verifier.SAW.Prelude.Constants
  ) where

import Verifier.SAW.ParserUtils
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.SharedTerm

$(runDecWriter $ do
    prelude <- defineModuleFromFile [] "preludeModule" "prelude/Prelude.sawcore"
    declareSharedModuleFns "Prelude" (decVal prelude)
 )

scEq :: SharedContext -> Term -> Term -> IO Term
scEq sc x y = do
  xty <- scTypeOf sc x
  eqOp <- scApplyPrelude_eq sc
  eqOp xty x y
