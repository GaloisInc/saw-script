{- |
Module      : Verifier.SAW.Utils
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Provides utility functions about general data structured used by SAW.
Declarations here should refer primarily to terms defined in other packages.
SAW-specific declarations should be stored in separate modules.
-}

{-# LANGUAGE Trustworthy, TemplateHaskell #-}

module Verifier.SAW.Utils
  ( internalError
  , panic
  , sumBy
  ) where

import Data.Foldable

import Panic hiding (panic)
import qualified Panic as Panic

sumBy :: (Foldable t, Num b) => (a -> b) -> t a -> b
sumBy f = foldl' fn 0
  where fn e v = e + f v

internalError :: String -> a
internalError msg = error $ "internal: " ++ msg

data SawCore = SawCore

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic SawCore

instance PanicComponent SawCore where
  panicComponentName _ = "SawCore"
  panicComponentIssues _ = "https://github.com/GaloisInc/saw-core/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision
