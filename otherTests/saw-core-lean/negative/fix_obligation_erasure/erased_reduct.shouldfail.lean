/-
S-1 pin (audit-2, 2026-07-24; fix 2026-07-25; probe landed
2026-07-28 with the owed-pins batch). The Class-F / Class-S
productivity obligations were ERASABLE on the completed-outline
path: `saw_stream_realize`'s body was
`Pure.pure (saw_stream_unfold α x0 step)` — mentioning neither
`mkfn` nor the proof — and `saw_fix_bounded_choose` drew its seed
via `Classical.choice` of a `Nonempty` (proof-irrelevant), so a
completed outline could write the reduct verbatim, never state
`total`/`lookback`/`faithful`, and pass the drift check by `rfl`
with a clean axiom audit (verified in-report 2026-07-24).

The fix routes both realizations through `Classical.choose` of an
existential CONTAINING the obligation. `Classical.choose` has no
reduct, so the erased forms below are recoverable only
PROPOSITIONALLY (`saw_stream_realize_eq_unfold`), never by `rfl` —
and "fails the defeq drift check" is precisely the property this
probe pins. Each claim must FAIL with "Not a definitional
equality". If this file ever compiles clean, the obligations are
erasable again and S-1 is back.
-/

import CryptolToLean.SAWCorePrimitives
import CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

-- Class S-single: the pre-fix reduct of the stream realization.
example (α : Type) (x0 : α) (step : α → α)
    (mkfn : Except String (Stream α) → Nat → Except String α)
    (h : saw_stream_single_productive α x0 step mkfn) :
    saw_stream_realize α x0 step mkfn h
      = Pure.pure (saw_stream_unfold α x0 step) := by rfl

-- Class F: the pre-fix any-seed iteration reduct of the bounded
-- fix realization (the S-1 report's witness shape: iteration from
-- an arbitrary Classical.choice seed, obligation never load-bearing).
example (n : Nat) (α : Type)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (h : saw_fix_bounded_productive n α body)
    (seed : Vec n α) :
    saw_fix_bounded_choose n α body h
      = saw_fix_bounded_iter_from n α seed body n := by rfl
