{-# LANGUAGE TemplateHaskell #-}

module Verifier.SAW.Cryptol.Panic
 ( panic, unimplemented )
 where

import Panic hiding (panic)
import qualified Panic as Panic

data CryptolVerifier = CryptolVerifier

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic CryptolVerifier

instance PanicComponent CryptolVerifier where
  panicComponentName _ = "cryptol-verifier"
  panicComponentIssues _ = "https://github.com/GaloisInc/cryptol-verifier/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision

unimplemented :: HasCallStack => String -> a
unimplemented name = panic "unimplemented" [name]

