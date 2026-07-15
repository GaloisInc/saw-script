/-
Discharge for test_cryptol_zn_arith.negcancel_prove0 (workflow row
workflows/cryptol_zn_arith).

Cryptol property: \(x : Z 7) -> x + (- x) == 0.

`intModNeg 7 x = Int.fmod (-x) 7` and `intModAdd 7 a b = Int.fmod (a+b) 7`,
so the left operand is `Int.fmod (x + Int.fmod (-x) 7) 7`; the right is
`toIntMod 7 (natToInt 0) = Int.fmod 0 7`. The load-bearing fact is that
adding a value to its own (fmod'd) negation is ≡ 0 mod n — proved below
as `fmod_add_neg_self` from core Lean's `Int.dvd_fmod_sub_self` (the
representative differs from the input by a multiple of n) and
`Int.add_mul_fmod_self_left` (adding a multiple of n leaves fmod fixed).
With the left side reduced to 0, the remaining `decide` over closed
`Int.fmod` terms is `rfl`.

No Mathlib: this uses only the `Int.fmod` lemma family in Lean core.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives

/-- `x + (-x mod N)` is divisible by `N`, hence `≡ 0 (mod N)`. -/
theorem fmod_add_neg_self (N x : Int) : Int.fmod (x + Int.fmod (-x) N) N = 0 := by
  obtain ⟨k, hk⟩ := Int.dvd_fmod_sub_self (x := -x) (m := N)
  have hval : x + Int.fmod (-x) N = 0 + N * k := by omega
  rw [hval, Int.add_mul_fmod_self_left, Int.zero_fmod]

theorem goal_closed : goal := by
  intro x
  simp only [Pure.pure, Bind.bind, Except.pure, Except.bind]
  simp only [intModEq, intModAdd, intModNeg, toIntMod, natToInt, fmod_add_neg_self]
  rfl
