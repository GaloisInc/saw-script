import Emitted

open CryptolToLean.SAWCorePrimitives

/- Apply the emitted OPEN function to the same concrete argument SAW
evaluated (0x8f = 143, negative MSB) and compare against the expected
sign-extension (0xff8f = 65423 at width 16). -/
#reduce match Observed (Pure.pure (bvNat 8 143)) with
  | Except.ok v =>
      match bvEq 16 v (bvNat 16 65423) with
      | true => "LEAN_OBSERVED: true"
      | false => "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
