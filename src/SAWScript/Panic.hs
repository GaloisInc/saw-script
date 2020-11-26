{- |
Module      : SAWScript.Panic
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

{-# LANGUAGE Trustworthy, TemplateHaskell #-}
module SAWScript.Panic
  (HasCallStack, SawPanic, Saw, Panic, panic) where

import Panic hiding (panic)
import qualified Panic as Panic

data Saw = Saw

type SawPanic = Panic Saw

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic Saw

instance PanicComponent Saw where
  panicComponentName _ = "Saw"
  panicComponentIssues _ = "https://github.com/GaloisInc/saw-script/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision
