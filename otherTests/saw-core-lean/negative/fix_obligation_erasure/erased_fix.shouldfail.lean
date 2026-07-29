/-
S-1 pin, Class F half (audit-2 finding S-1, 2026-07-24; fix
2026-07-25; probe 2026-07-28, CORRECTED 2026-07-29 after the session
audit found the original claim red for the wrong reason).

Pre-fix, `saw_fix_bounded_choose` drew its seed via
`Classical.choice h.seed`, whose argument is `Nonempty (Vec n α)` —
a Prop, hence proof-irrelevant, hence satisfiable by `⟨v⟩` for ANY
`v`. So a completed outline could write
`saw_fix_bounded_iter_from n α (Classical.choice ⟨v⟩) body n`, never
state `total`/`lookback`, and pass the drift check by `rfl`
(verified in-report 2026-07-24; the witness is quoted at
SAWCorePrimitives.lean's seed-existential docstring and in
doc/2026-07-24_semantic-trust-kernel-plan.md §S-1(b)).

The RHS below must therefore be spelled the way that witness is —
the seed laundered through `Classical.choice` of a `Nonempty` — NOT
as a bare universally-quantified seed. That was the original probe's
defect: `Classical.choice` is an opaque axiom with no reduct, so a
bare-seed equation fails `rfl` against the PRE-FIX definition too,
making the claim red for a reason unrelated to S-1 and unable to
turn green under the regression it names.

The fix routes the value through `Classical.choose` of an
existential CONTAINING the obligation, which has no reduct to write
instead. This claim must FAIL. If it ever elaborates, the seed is
proof-irrelevantly erasable again and S-1 is back.

ONE CLAIM PER FILE — see the sibling probe's header for why.
-/

import CryptolToLean.SAWCorePrimitives
import CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

example (n : Nat) (α : Type)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (h : saw_fix_bounded_productive n α body)
    (seed : Vec n α) :
    saw_fix_bounded_choose n α body h
      = saw_fix_bounded_iter_from n α
          (Classical.choice (⟨seed⟩ : Nonempty (Vec n α))) body n := by rfl
