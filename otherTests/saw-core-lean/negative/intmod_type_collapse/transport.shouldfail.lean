/-
LIB-W2-1 pin (wave-2 release-gate audit, 2026-07-29, CRITICAL).

SAWCore declares `primitive IntMod : Nat -> sort 0` — OPAQUE, with no
reduction rule identifying one modulus with another. The Lean
realization was `@[reducible] def IntMod : Nat -> Type := fun _ => Int`,
so `IntMod 5`, `IntMod 7` and `Integer` all whnf-ed to `Int` and were
mutually defeq.

Why that was CRITICAL rather than untidy: SAW 'unsafeAssert' is SAW's
explicit admission that it has NO proof of an equality, and the emitted
discharge is `(first | rfl | skip); all_goals sorry`. With the collapse
the `rfl` arm closed a false type assertion, `all_goals` then had no
goals, and the artifact elaborated with NO `declaration uses `sorry``
and a clean `#print axioms` — then fed `coerce` (= `cast`) to
reinterpret a `Z 5` value as a `Z 7` one.

ONE CLAIM PER FILE, deliberately. The sibling `float_double_collapse`
row carried three claims in one file until 2026-07-29, which is the
S-1 masking defect: the first failing claim makes the row pass while
the others could have gone green unnoticed.
-/
import CryptolToLean
open CryptolToLean.SAWCorePrimitives

-- A value must not transport between moduli for free.
theorem intmod_transport (x : IntMod 5) : IntMod 7 := x
