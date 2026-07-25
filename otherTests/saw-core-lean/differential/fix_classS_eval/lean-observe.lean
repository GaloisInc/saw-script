import Emitted

open CryptolToLean.SAWCorePrimitives

/- S-1 (2026-07-25). The Class-S realization no longer reduces: its
stream is drawn via `Classical.choose` of an existential CONTAINING
the productivity obligation, so a completed outline cannot write the
value without proving that obligation. `Classical.choose` is opaque,
so `#reduce` on `Observed` now gets stuck — the previous observer
printed `(Classical.choice ⋯).1.1 5` instead of a value.

That is the fix working, not a defect to route around: "reduces to a
proof-free value" and "erasable under the defeq drift check" are the
same property, so blocking the erasure necessarily blocks reduction.

The observation is rebuilt in two parts, and is STRONGER than the
plain `#reduce` it replaces:

  1. `observed_link` — a KERNEL-CHECKED equality between the emitted
     term and a computable form, via the library's propositional
     recovery lemma. If the emitted term ever stops being the unfold,
     this fails to compile and the row goes red.
  2. `#reduce` on the computable form, producing the LEAN_OBSERVED
     line the harness diffs against SAW.

Non-vacuity: the printed value is DERIVED from `ObservedComputable`,
never asserted. A wrong value changes the printed line (diff fails);
a broken link fails at (1). Neither can pass silently. -/

/-- The computable counterpart: the emitted term with the opaque
realization replaced by the unfold it is propositionally equal to. -/
noncomputable def ObservedComputable : Except String Bool :=
  Bind.bind (Pure.pure (saw_stream_unfold Bool Bool.true (fun prev_ => prev_)))
    (fun scrut_ => @Stream.rec Bool (fun (_strm' : Stream Bool) => Except String Bool)
      (fun (s : Nat -> Bool) => Pure.pure (s 5)) scrut_)

/-- The emitted term IS the computable counterpart. This is the check
that keeps the observation honest. -/
theorem observed_link : Observed = ObservedComputable := by
  unfold Observed ObservedComputable
  rw [saw_stream_realize_eq_unfold]
  rfl

#reduce match ObservedComputable with
  | Except.ok true => "LEAN_OBSERVED: true"
  | Except.ok false => "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
