/-
"Attack" pattern: try to use `unsafeAssert` at a higher universe
than SAW's `sort 1`. SAW's primitive is fixed at `sort 1`
(= Lean's `Type 0` = `Type`); a Lean stand-in that admits `Type 1`
or higher is *broader than SAW* — even though no translator-
emitted code reaches that surface, the asymmetry violates
faithful transposition.

Two probes:

  1. `unsafeAssert Type Bool Nat` — `α := Type` requires
     `Type : Type` (i.e. `Type 0 : Type 0`). False — `Type 0 : Type 1`.
     Lean must reject.

  2. `unsafeAssert (Type 1) Bool Bool` — same shape one universe
     higher.

If either of these elaborates, the axiom shape has drifted away
from SAW's `sort 1`-only constraint.

Note: `unsafeAssert Prop True False` IS admitted (because
`Prop : Type 0`) and is NOT tested here. SAW's primitive admits
the same attack — see SAW Prelude `unsafeCoerce` at
`Prelude.sawcore:292` — so we faithfully transport it.
-/

import CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePrimitives

-- Probe 1: α at Type 0's universe (Type 1).
theorem too_high_universe_0 : @Eq Type Bool Nat :=
  unsafeAssert Type Bool Nat

-- Probe 2: α at Type 1's universe (Type 2).
theorem too_high_universe_1 : @Eq (Type 1) Bool Bool :=
  unsafeAssert (Type 1) Bool Bool
