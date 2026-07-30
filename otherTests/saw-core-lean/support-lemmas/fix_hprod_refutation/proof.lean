import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
W5-1 reject-side H_prod pin (wave-4 report §3 / GAP 1, 2026-07-30;
`doc/2026-07-30_release-gate-audit-wave4.md`; witnesses corrected
same day by the fix audit of the first cut — see below).

Wave 4's severity architecture rests on one claim: a FixRecognizer
false positive yields an UNDISCHARGEABLE kernel obligation, so the
recognizer is a diagnostic gate and the per-instance obligation is
the load-bearing barrier. Until this row, every corpus occurrence of
`saw_fix_bounded_productive` / `saw_stream_single_productive` was an
accept-side discharge — nothing pinned that the obligation
DISCRIMINATES. These theorems are the kernel-checked evidence: for
each of the three REFUTED fields (Class F `lookback`; stream
`lookback`; stream `faithful` — Class F's `seed`/`total` carry
positive companions only, wave-5 W5C-9 wording fix), a body IN THE
IMAGE of the mutated recognizer (the false positive the wave-4
findings describe) makes that field FALSE — hence unprovable in a
consistent logic, hence a loud undischargeable placeholder (caught
by the zero-tolerance sorry scan and the exact-match axiom audit),
never a silent wrong value.

WITNESS SHAPE (fix-audit correction, 2026-07-30): every body the
recognizer can admit — with or without the FXC-1/FXC-2 guard
mutations — is seed-guarded at index 0 (`FixRecognizer.hs:240`
requires the `ltNat i 1` element guard with a rec-free seed branch,
`:245`; the stream dispatch `:134-152` requires a rec-free
length-1 `atWithDefault` seed). So an honest witness must carry the
rec-free index-0 case and be refuted at index 1, where the mutated
guard first admits a bad read. The first cut of this row refuted
index-0-exposed bodies outside that image, which pinned only the
weaker "H_prod is not vacuously true".

Witnesses (all named `def`s so companion statements cannot
beta-reduce them away — the V-H1 vacuity the fix audit caught in
the first cut's `transforming_step_lookback`):

- FXC-1 (Class F, the `FixRecognizer.hs:350` inner at-index guard):
  the guard requires a rec-containing `at`-selection to be indexed
  by EXACTLY the inner gen binder `i2` — which composes with the
  tail's `subNat i 1` to the ACCEPTED lookback-1 read
  `output[i] = rec[i-1]`. The read it refuses is
  `at rec (addNat i2 1)`, i.e. `output[i] = rec[i]` for `i ≥ 1`
  under the seed guard. `sameIndexBodyF` below is that semantics at
  `n = 2`: `w[0]` constant, `w[1] = v[1]`. Its `lookback` is FALSE
  at `i = 1`; `seed`/`total` hold, and `lookback` restricted to
  `i = 0` also holds (companions) — so the refutation isolates the
  exact index the guard protects.
- FXC-2 (Class S, `isIdentityStreamRead`): both stream witnesses
  carry the index-0 seed case returning `x0 = false`, matching how
  `lowerClassSSingle` derives `x0` from the same seed the element
  function's 0-case reads. `selfRefMkfn` reads the stream AT `i`
  for `i ≥ 1` (the self-reference shape): stream `lookback` is
  FALSE at `i = 1` while `faithful` HOLDS (companion).
  `transformMkfn` reads index `i-1` but negates it (the
  iterate-family shape): `faithful` is FALSE at `i = 1` while
  stream `lookback` HOLDS (companion). Complementary witnesses, so
  each stream field is independently load-bearing.

If any refutation here stops elaborating, the obligation shape was
weakened: wave-4's FXC-1/FXC-2 downgrades revert to MEDIUM and
docket item 1 reopens (TODO.md, W5-1). The companions are stated
against the named witnesses with the field shapes written out; they
do not track field-shape drift (only the `¬` theorems, which
project `h.lookback`/`h.faithful`, do).
-/

/-- FXC-1 witness, Class F at `n = 2`: seed-guarded at index 0,
same-index read at index 1 (`w[1] = v[1]` — the semantics of
`at rec (addNat i2 1)`, the read the `:350` guard refuses). -/
def sameIndexBodyF :
    Except String (Vec 2 Bool) → Except String (Vec 2 Bool) :=
  fun ev => ev >>= fun v => Pure.pure #v[false, v[1]]

/-- FXC-2 witness, self-reference: index-0 seed case returns
`x0 = false`; index `i ≥ 1` reads the stream AT `i`. -/
def selfRefMkfn :
    Except String (Stream Bool) → Nat → Except String Bool :=
  fun s i =>
    match i with
    | 0 => Pure.pure false
    | n + 1 => s >>= fun t => Pure.pure (streamIdx Bool t (n + 1))

/-- FXC-2 witness, iterate family: index-0 seed case returns
`x0 = false`; index `i ≥ 1` reads index `i - 1` but TRANSFORMS it
(negation) instead of reading it back. -/
def transformMkfn :
    Except String (Stream Bool) → Nat → Except String Bool :=
  fun s i =>
    match i with
    | 0 => Pure.pure false
    | n + 1 => s >>= fun t => Pure.pure (!(streamIdx Bool t n))

/-- Class F / FXC-1: `lookback` is FALSE for the same-index body —
at `i = 1`, inputs agreeing at index 0 still produce differing
outputs at index 1. -/
theorem same_index_read_body_not_productive :
    ¬ saw_fix_bounded_productive 2 Bool sameIndexBodyF := by
  intro h
  have hlb :=
    h.lookback #v[false, false] #v[false, true]
      #v[false, false] #v[false, true] rfl rfl
      1 (by omega)
      (fun j _ hlt =>
        match j, hlt with
        | 0, _ => rfl)
  simp at hlb

/-- Companion: `seed` and `total` HOLD for the same-index body. -/
theorem same_index_read_body_seed_total :
    Nonempty (Vec 2 Bool) ∧
      ∀ v : Vec 2 Bool, ∃ w : Vec 2 Bool,
        sameIndexBodyF (Pure.pure v) = Pure.pure w :=
  ⟨⟨#v[false, false]⟩, fun v => ⟨#v[false, v[1]], rfl⟩⟩

/-- Companion: `lookback` RESTRICTED TO `i = 0` holds for the
same-index body (its index-0 output is the rec-free seed) — the
witness is inside the seed-guarded image every admissible Class-F
body inhabits; only index 1, the index the `:350` guard protects,
refutes. -/
theorem same_index_read_body_lookback_at_zero :
    ∀ (v₁ v₂ w₁ w₂ : Vec 2 Bool),
      sameIndexBodyF (Pure.pure v₁) = Pure.pure w₁ →
      sameIndexBodyF (Pure.pure v₂) = Pure.pure w₂ →
      w₁[0] = w₂[0] := by
  intro v₁ v₂ w₁ w₂ h₁ h₂
  have e₁ : w₁ = #v[false, v₁[1]] := (Except.ok.inj h₁).symm
  have e₂ : w₂ = #v[false, v₂[1]] := (Except.ok.inj h₂).symm
  subst e₁; subst e₂; rfl

/-- Class S / FXC-2, self-reference: stream `lookback` is FALSE at
`i = 1` — streams agreeing at index 0 still give differing values. -/
theorem self_reference_step_not_productive :
    ¬ saw_stream_single_productive Bool false (fun prev => prev)
        selfRefMkfn := by
  intro h
  have hlb :=
    h.lookback (Stream.MkStream fun _ => false)
      (Stream.MkStream fun j =>
        match j with
        | 0 => false
        | _ + 1 => true)
      1
      (fun j hj =>
        match j, hj with
        | 0, _ => rfl)
  exact Bool.noConfusion (Except.ok.inj hlb)

/-- Companion: `faithful` HOLDS for the self-reference witness —
its index-0 case returns exactly `x0`, and reading the realization
back at `i ≥ 1` is the faithful equation itself. -/
theorem self_reference_step_faithful :
    ∀ i : Nat,
      selfRefMkfn
          (Pure.pure (saw_stream_unfold Bool false (fun prev => prev))) i
        = Pure.pure
            (streamIdx Bool
              (saw_stream_unfold Bool false (fun prev => prev)) i) :=
  fun i =>
    match i with
    | 0 => rfl
    | _ + 1 => rfl

/-- Class S / FXC-2, iterate family: `faithful` is FALSE at `i = 1`
— the realization from seed `false` under the identity step is
constantly `false`, but the transforming function produces
`!false = true`. -/
theorem transforming_step_not_productive :
    ¬ saw_stream_single_productive Bool false (fun prev => prev)
        transformMkfn := by
  intro h
  have hf := h.faithful 1
  exact Bool.noConfusion (Except.ok.inj hf)

/-- Companion: stream `lookback` HOLDS for the transforming witness
(stated with `transformMkfn` applied, not beta-reduced away — the
first cut's version of this statement was vacuous, V-H1): index 0
reads nothing, index `i = n + 1` reads only index `n < i`. -/
theorem transforming_step_lookback :
    ∀ (t₁ t₂ : Stream Bool) (i : Nat),
      (∀ j : Nat, j < i → streamIdx Bool t₁ j = streamIdx Bool t₂ j) →
      transformMkfn (Pure.pure t₁) i = transformMkfn (Pure.pure t₂) i := by
  intro t₁ t₂ i hagree
  match i with
  | 0 => rfl
  | n + 1 =>
      show (Pure.pure (!(streamIdx Bool t₁ n)) : Except String Bool)
             = Pure.pure (!(streamIdx Bool t₂ n))
      rw [hagree n (Nat.lt_succ_self n)]

end
