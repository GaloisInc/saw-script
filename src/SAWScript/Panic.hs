{-# LANGUAGE Trustworthy, TemplateHaskell #-}
module SAWScript.Panic
  (HasCallStack, SAWScript, Panic, panic) where

import Panic hiding (panic)
import qualified Panic as Panic

data SAWScript = SAWScript

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic SAWScript

instance PanicComponent SAWScript where
  panicComponentName _ = "saw-script"
  panicComponentIssues _ = "https://github.com/GaloisInc/saw-script/issues"
  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision
