module Language.Isabelle.Panic
  (HasCallStack, IsabellePanic, Isabelle, Panic, panic) where

import Panic hiding (panic)
import qualified Panic as Panic

data Isabelle = Isabelle

type IsabellePanic = Panic Isabelle

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic Isabelle


instance PanicComponent Isabelle where
  panicComponentName _ = "Isabelle"
  panicComponentIssues _ = "https://github.com/GaloisInc/cryptol/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = \_ -> ("0","0")
