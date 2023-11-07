{- |
Module      : Verifier.SAW
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

{-# LANGUAGE TemplateHaskell #-}

module Verifier.SAW
  ( module Verifier.SAW.SharedTerm
  , module Verifier.SAW.ExternalFormat
  , Module
  , preludeModule
  , scLoadPreludeModule
  ) where

import Verifier.SAW.SharedTerm
import Verifier.SAW.Prelude
import Verifier.SAW.ExternalFormat

-- The following type-checks the Prelude at compile time, as a sanity check
-- NOTE: this is now done in Verifier.SAW.Cryptol, which also type-checks the
-- Cryptol-related SAW core modules as well
--
-- import Language.Haskell.TH
-- $(runIO (mkSharedContext >>= \sc -> scLoadPreludeModule sc >> return []))
