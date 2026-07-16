import Emitted

open CryptolToLean.SAWCorePrimitives

/-- The realized stream is definitionally the total unfold — the
named closer for the axiom audit; `rfl` holds because the emitted
value IS the realization (no choice principle). -/
theorem allTrue_realized :
    RecOnes.allTrue =
      Pure.pure (saw_stream_unfold Bool Bool.true (fun prev_ => prev_)) :=
  rfl
