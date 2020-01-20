-- |
-- Module      :  Verifier.SAW.Panic
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  huffman@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Trustworthy, TemplateHaskell #-}
module Verifier.SAW.Panic
  (HasCallStack, SawCorePanic, SawCore, Panic, panic) where

import Panic hiding (panic)
import qualified Panic as Panic

data SawCore = SawCore

type SawCorePanic = Panic SawCore

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic SawCore

instance PanicComponent SawCore where
  panicComponentName _ = "SawCore"
  panicComponentIssues _ = "https://github.com/GaloisInc/saw-core/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision
