import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
W5-1 reject-side H_prod pin (wave-4 report §3 / GAP 1, 2026-07-30;
`doc/2026-07-30_release-gate-audit-wave4.md`).

Wave 4's severity architecture rests on one claim: a FixRecognizer
false positive yields an UNDISCHARGEABLE kernel obligation, so the
recognizer is a diagnostic gate and the per-instance obligation is
the load-bearing barrier. Until this row, every corpus occurrence of
`saw_fix_bounded_productive` / `saw_stream_single_productive` was an
accept-side discharge — nothing pinned that the obligation
DISCRIMINATES. These theorems are the kernel-checked evidence: for
each obligation field, a body of the exact semantic shape the
recognizer must refuse makes that field FALSE — hence unprovable in
a consistent logic, hence a loud undischargeable placeholder (caught
by the zero-tolerance sorry scan and the exact-match axiom audit),
never a silent wrong value.

Witnesses match the wave-4 findings:

- FXC-1 (Class F, the FixRecognizer.hs:350 inner at-index guard): a
  same-index read `at rec i2` makes the body the identity on pure
  vectors — `lookback` is false.  `seed` and `total` hold for that
  body (companion below), so `lookback` alone does the refusing.
- FXC-2 (Class S, `isIdentityStreamRead`): a self-referential step
  reads the stream AT `i` — stream `lookback` is false while
  `faithful` holds (companion); an iterate-family transform breaks
  `faithful` while `lookback` holds (companion). The two stream
  fields are refuted by COMPLEMENTARY witnesses, so each is
  independently load-bearing.

If any refutation here stops elaborating, the obligation shape was
weakened: wave-4's FXC-1/FXC-2 LOW-provisional downgrades revert to
MEDIUM and docket item 1 reopens (TODO.md, W5-1).
-/

/-- Class F / FXC-1: the same-index-read body (`result[i] = rec[i]`)
is the identity on `Except`; its `lookback` fails at `i = 0`, where
the agree-below-`i` premise is vacuous but the outputs still differ. -/
theorem same_index_read_body_not_productive :
    ¬ saw_fix_bounded_productive 1 Bool (fun v => v) := by
  intro h
  have hlb :=
    h.lookback #v[false] #v[true] #v[false] #v[true] rfl rfl
      0 (by omega) (fun j _ hlt => absurd hlt (Nat.not_lt_zero j))
  simp at hlb

/-- Companion: `seed` and `total` HOLD for the same-index body, so
the refutation above isolates `lookback` as the discriminating
field for Class F. -/
theorem same_index_read_body_seed_total :
    Nonempty (Vec 1 Bool) ∧
      ∀ v : Vec 1 Bool, ∃ w : Vec 1 Bool,
        (fun v : Except String (Vec 1 Bool) => v) (Pure.pure v)
          = Pure.pure w :=
  ⟨⟨#v[false]⟩, fun v => ⟨v, rfl⟩⟩

/-- Class S / FXC-2, self-reference: an element function reading the
stream AT `i` (the classic `\s -> s i`) violates stream `lookback`
at `i = 0`. -/
theorem self_reference_step_not_productive :
    ¬ saw_stream_single_productive Bool false (fun prev => prev)
        (fun s i => s >>= fun t => Pure.pure (streamIdx Bool t i)) := by
  intro h
  have hlb :=
    h.lookback (Stream.MkStream fun _ => false)
      (Stream.MkStream fun _ => true) 0
      (fun j hj => absurd hj (Nat.not_lt_zero j))
  exact Bool.noConfusion (Except.ok.inj hlb)

/-- Companion: `faithful` HOLDS for the self-reference witness (the
identity read at `i` is literally the faithful equation), so the
refutation above isolates stream `lookback`. -/
theorem self_reference_step_faithful :
    ∀ i : Nat,
      ((Pure.pure (saw_stream_unfold Bool false (fun prev => prev))
            : Except String (Stream Bool))
          >>= fun t =>
            (Pure.pure (streamIdx Bool t i) : Except String Bool))
        = (Pure.pure
            (streamIdx Bool
              (saw_stream_unfold Bool false (fun prev => prev)) i)
            : Except String Bool) :=
  fun _ => rfl

/-- Class S / FXC-2, iterate family: an element function that
TRANSFORMS the element rather than reading it back violates
`faithful` against the identity-step realization — the realization
from seed `false` is constantly `false`, the function produces
`true`. -/
theorem transforming_step_not_productive :
    ¬ saw_stream_single_productive Bool false (fun prev => prev)
        (fun _ _ => Pure.pure true) := by
  intro h
  have hf := h.faithful 0
  exact Bool.noConfusion (Except.ok.inj hf)

/-- Companion: stream `lookback` HOLDS for the transforming witness
(it reads no stream element at all), so the refutation above
isolates `faithful`. -/
theorem transforming_step_lookback :
    ∀ (t₁ t₂ : Stream Bool) (i : Nat),
      (∀ j : Nat, j < i → streamIdx Bool t₁ j = streamIdx Bool t₂ j) →
      (Pure.pure true : Except String Bool)
        = (Pure.pure true : Except String Bool) :=
  fun _ _ _ _ => rfl

end
