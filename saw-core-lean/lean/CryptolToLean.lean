/-
Root module for the `CryptolToLean` library — the Lean 4 support
library that generated output from `saw-core-lean` imports. Each
sub-module lives under `CryptolToLean/` and corresponds to one file
the backend's emitted preamble references.
-/

import CryptolToLean.SAWCoreScaffolding
import CryptolToLean.SAWCoreVectors
import CryptolToLean.SAWCoreBitvectors
