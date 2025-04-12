{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TemplateHaskell #-}

module SAWCoreWhat4.Panic
  ( panic
  ) where

import Panic hiding (panic)
import qualified Panic

data SAWCoreWhat4 = SAWCoreWhat4

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic SAWCoreWhat4

instance PanicComponent SAWCoreWhat4 where
  panicComponentName _ = "SAWCoreWhat4"
  panicComponentIssues _ = "https://github.com/GaloisInc/saw-script/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision

