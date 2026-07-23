import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

-- The width itself is the observed raw select: with n = 0 the def's
-- result type reduces (if0NatRaw is @[reducible]) to Vec 4 Bool, so
-- `bvEq 4` only typechecks if the zero branch computed; likewise
-- width 8 for n = 1.
#reduce match Observed 0 with
  | Except.ok v =>
      bif bvEq 4 v (bvNat 4 3) then "LEAN_OBSERVED: width-4 zero-branch"
      else "LEAN_OBSERVED: wrong zero-branch value"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e

#reduce match Observed 1 with
  | Except.ok v =>
      bif bvEq 8 v (bvNat 8 3) then "LEAN_OBSERVED: width-8 succ-branch"
      else "LEAN_OBSERVED: wrong succ-branch value"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
