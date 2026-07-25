import Emitted

open CryptolToLean.SAWCorePrimitives

/-- The realized stream is the total unfold.

Updated 2026-07-25 for the S-1 contract fix. This proof used to be
`rfl`, with a docstring asserting "`rfl` holds because the emitted
value IS the realization (no choice principle)". That was true, and
it was precisely the defect: because the realization's value did not
depend on the obligation, a completed outline could write the unfold
directly and never state `faithful`/`lookback` at all. The
realization now draws its stream via `Classical.choose` of an
existential CONTAINING the obligation, so the identity is
propositional rather than definitional — recovered here by the
library lemma. `rfl` no longer proves it, which is the point. -/
theorem allTrue_realized :
    RecOnes.allTrue =
      Pure.pure (saw_stream_unfold Bool Bool.true (fun prev_ => prev_)) := by
  unfold RecOnes.allTrue
  exact saw_stream_realize_eq_unfold _ _ _ _ _
