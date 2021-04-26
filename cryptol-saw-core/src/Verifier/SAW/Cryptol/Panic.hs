{-# LANGUAGE TemplateHaskell #-}

module Verifier.SAW.Cryptol.Panic
 ( panic, unimplemented )
 where

import Panic hiding (panic)
import qualified Panic as Panic

data CryptolSawCore = CryptolSawCore

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic CryptolSawCore

instance PanicComponent CryptolSawCore where
  panicComponentName _ = "cryptol-saw-core"
  panicComponentIssues _ = "https://github.com/GaloisInc/saw-script/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision

unimplemented :: HasCallStack => String -> a
unimplemented name = panic "unimplemented" [name]

