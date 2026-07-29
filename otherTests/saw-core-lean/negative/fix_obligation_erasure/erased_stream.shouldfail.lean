/-
S-1 pin, Class S-single half (audit-2 finding S-1, 2026-07-24; fix
2026-07-25; probe 2026-07-28, SPLIT AND CORRECTED 2026-07-29 after
the session audit found the combined probe vacuous — see the sidecar).

Pre-fix, `saw_stream_realize`'s body was
`Pure.pure (saw_stream_unfold α x0 step)` — mentioning neither `mkfn`
nor the proof — so a completed outline could write that reduct
verbatim, never state `faithful`/`lookback`, and pass the drift check
by `rfl` with a clean axiom audit (verified in-report 2026-07-24).

The fix routes the realization through `Classical.choose` of an
existential CONTAINING the obligation. `Classical.choose` has no
reduct, so the erased form below is recoverable only PROPOSITIONALLY
(`saw_stream_realize_eq_unfold`), never by `rfl`. This claim must
FAIL. If it ever elaborates, the Class-S obligation is erasable
again and S-1 is back.

ONE CLAIM PER FILE, deliberately: the negative harness runs one Lean
invocation per FILE and greps the whole capture for the pinned
substring, so a second claim in this file could satisfy the pin on
this claim's behalf and let a real regression pass green.
-/

import CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePrimitives

example (α : Type) (x0 : α) (step : α → α)
    (mkfn : Except String (Stream α) → Nat → Except String α)
    (h : saw_stream_single_productive α x0 step mkfn) :
    saw_stream_realize α x0 step mkfn h
      = Pure.pure (saw_stream_unfold α x0 step) := by rfl
