import Emitted

open CryptolToLean.SAWCorePrimitives

/- Apply the emitted OPEN function to the same concrete argument SAW
evaluated (0x8f = 143) and compare against the expected zero-extension
(0x008f = 143 at width 16). -/
#reduce match Observed (Pure.pure (bvNat 8 143)) with
  | Except.ok v =>
      match bvEq 16 v (bvNat 16 143) with
      | true => "LEAN_OBSERVED: true"
      | false => "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
