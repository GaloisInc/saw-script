import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

#reduce match Observed 0 with
  | Except.ok v =>
      bif bvEq 8 v (bvNat 8 3) then "LEAN_OBSERVED: zero-branch value 3"
      else "LEAN_OBSERVED: wrong zero-branch value"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e

#reduce match Observed 1 with
  | Except.ok v =>
      bif bvEq 8 v (bvNat 8 5) then "LEAN_OBSERVED: succ-branch value 5"
      else "LEAN_OBSERVED: wrong succ-branch value"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
