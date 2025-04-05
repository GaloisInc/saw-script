{- |
Module      : SAWCentral.Panic
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

{-# LANGUAGE Trustworthy, TemplateHaskell #-}
module SAWCentral.Panic
  (HasCallStack, panic) where

import Panic hiding (panic)
import qualified Panic as Panic

data SAWCentral = SAWCentral

-- | Raise a fatal error. The purpose of 'panic' is to indicate
-- conditions caused by programmer errors (e.g. violation of datatype
-- invariants), not problems caused by bad user input.
panic ::
  HasCallStack =>
  -- | Location of problem
  String ->
  -- | Problem description (lines)
  [String] ->
  a
panic = Panic.panic SAWCentral

instance PanicComponent SAWCentral where
  panicComponentName _ = "SAWCentral"
  panicComponentIssues _ = "https://github.com/GaloisInc/saw-script/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision
