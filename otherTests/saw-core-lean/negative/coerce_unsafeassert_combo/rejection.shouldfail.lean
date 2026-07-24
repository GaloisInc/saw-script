/-
Combinational probe: build `Eq Type Bool Empty` via unsafeAssert
at α = Type, then `coerce true : Bool` to `Empty`, then
`Empty.elim` to `False`.

This SHOULD fail at elaboration because the universe levels of
`unsafeAssert`'s output Eq don't match `coerce`'s expected Eq:
- `unsafeAssert : (α : Type) → (x y : α) → @Eq α x y` — α is at
  `Type 0`, so the Eq lives at universe 1.
- `coerce` expects `@Eq Type α β` — Type here is `Type 0 = Sort 1`,
  so the Eq lives at universe 2 (one bump above α's universe).

The level mismatch means Lean can't unify the two Eqs. If a
future tightening of either signature accidentally aligns the
universe levels, this probe trips immediately — making the
combinational probe a regression alarm, not a silent unsoundness.

Pinned by the 2026-05-04 exposure-surface inventory:
  saw-core-lean/doc/archive/2026-05-04_exposure-surface.md
  (row "coerce α β (unsafeAssert _ α β) x" — currently blocked by
  the universe-level wall, even though the broader residual
  remains via direct unsafeAssert misuse).
-/

import CryptolToLean
open CryptolToLean.SAWCorePrimitives

noncomputable def probeCoerceUnsafeAssert : False := by
  have h : @Eq Type Bool Empty := unsafeAssert _ _ _
  have e : Empty := coerce Bool Empty h true
  exact Empty.elim e
