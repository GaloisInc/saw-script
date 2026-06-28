/-
`CryptolToLean.SAWCorePrelude_proofs` — non-bitvector lemmas
about the support library's axioms / `@[reducible]` defs.

P3-4. Mirrors the lemma set in
`saw-core-rocq/rocq/handwritten/CryptolToRocq/SAWCorePrelude_proofs.v`.
The bv lemmas live in their own file
(`SAWCoreBitvectors_proofs.lean`); this one collects round-trip
properties of `gen` / `atWithDefault` / `foldr` / `foldl`, the
trivial Nat-arithmetic bridges, and a handful of vector lemmas
users might reach for.

Some lemmas reduce by definitional equality (the `addNat = Nat.add`
family below — our Lean-side `addNat` is `@[reducible] def addNat
:= Nat.add`, so the equation is `rfl`). Others are axiomatic
transpositions of Rocq theorems whose proofs depend on a `Vector
α n` representation we don't expose. Each axiom cites its Rocq
counterpart.
-/

import CryptolToLean.SAWCorePrimitives
import CryptolToLean.SAWCoreVectors
import CryptolToLean.SAWCorePreludeExtra

namespace CryptolToLean.SAWCorePreludeProofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

/-! ## Nat-arithmetic alias `@[simp]` lemmas (proof ergonomics)

**Not "theorems about SAW behavior" — convenience plumbing.** These
all reduce by `rfl` because our Lean-side `addNat` / `subNat` /
`mulNat` / `equalNat` / etc. are `@[reducible] def` aliases for
the Lean stdlib operation. The `@[simp]` tag means user proofs
can `simp` to rewrite SAW-named goals into Lean-stdlib form
without manually unfolding the alias depth. They mirror Rocq's
identical plumbing (`addNat_add`, `mulNat_mul`, etc.).

If you're looking for substantive theorems about translator-emitted
output, see the Vector round-trip / Bool-Nat decision-bridge
sections below or `SAWCoreBitvectors_proofs.lean`. -/

/-- SAW `addNat` is Lean `Nat.add`. Rocq: `rewrite_addNat`. -/
@[simp] theorem addNat_eq_natAdd (m n : Nat) : addNat m n = m + n := rfl

/-- SAW `subNat` is Lean `Nat.sub` (saturating). Both saturate
at zero on under-flow. -/
@[simp] theorem subNat_eq_natSub (m n : Nat) : subNat m n = m - n := rfl

/-- SAW `equalNat` is decidable Nat equality. -/
@[simp] theorem equalNat_eq_decide_eq (m n : Nat) :
    equalNat m n = decide (m = n) := rfl

/-- SAW `ltNat` matches Lean's strict less-than. -/
@[simp] theorem ltNat_eq_decide_lt (m n : Nat) :
    ltNat m n = decide (m < n) := rfl

/-- SAW `leNat` matches Lean's less-than-or-equal. -/
@[simp] theorem leNat_eq_decide_le (m n : Nat) :
    leNat m n = decide (m ≤ n) := rfl

/-- SAW `mulNat` is Lean `Nat.mul`. Rocq: `mulNat_mul`. -/
@[simp] theorem mulNat_eq_natMul (m n : Nat) : mulNat m n = m * n := rfl

/-- SAW `minNat` is Lean `Nat.min`. Rocq: `minNat_min`. -/
@[simp] theorem minNat_eq_natMin (m n : Nat) : minNat m n = Nat.min m n := rfl

/-- SAW `maxNat` is Lean `Nat.max`. Rocq: `maxNat_max`. -/
@[simp] theorem maxNat_eq_natMax (m n : Nat) : maxNat m n = Nat.max m n := rfl

/-- SAW `expNat` is Lean `Nat.pow`. -/
@[simp] theorem expNat_eq_natPow (m n : Nat) : expNat m n = Nat.pow m n := rfl

/-- SAW `pred` is Lean `Nat.pred`. -/
@[simp] theorem pred_eq_natPred (n : Nat) : pred n = Nat.pred n := rfl

/-- SAW `doubleNat n` equals `2 * n`. -/
@[simp] theorem doubleNat_eq (n : Nat) : doubleNat n = 2 * n := rfl

/-! ## Vector round-trip theorems

`gen` and `atWithDefault` form an isomorphism: enumerating an
`n`-element vector by index reconstructs the same vector;
indexing into `gen f` returns `f i` for in-bounds `i`.

Phase 8 (2026-05-02 evening): these were axioms before
`gen` / `atWithDefault` became structural defs over Lean's
`Vector`. Now provable from `Vector.getElem_ofFn` and
`Vector.ext`. The previous axiom names are preserved as
theorems for downstream-proof compatibility. -/

@[simp] theorem ofFnM_except_ok {α : Type} {n : Nat} (f : Fin n → α) :
    Vector.ofFnM (m := Except String) (fun i => Except.ok (f i)) =
      Except.ok (Vector.ofFn f) := by
  simpa [Pure.pure, Except.pure] using
    (Vector.ofFnM_pure (m := Except String) (f := f))

/-- If every generated element succeeds, the monadic `genM` is exactly
the pure `gen` wrapped in `Except.ok`.

This is the safe form of the tempting but false rule
`atWithDefaultM d (genM f) i = f i`: `genM` is eager and sequences the
whole vector, so selecting one element is equal to `f i` only after Lean
has proved the other generated elements also succeed. -/
theorem genM_eq_ok_gen {α : Type} (n : Nat)
    (f : Nat → Except String α) (g : Nat → α)
    (h : ∀ i : Nat, i < n → f i = Except.ok (g i)) :
    genM n α f = Except.ok (gen n α g) := by
  unfold genM gen
  have hf :
      (fun i : Fin n => f i.val) =
        (fun i : Fin n => Except.ok (g i.val)) := by
    funext i
    exact h i.val i.isLt
  rw [hf]
  exact Vector.ofFnM_pure (m := Except String)
    (f := fun i : Fin n => g i.val)

theorem vecSequenceM_singleton_ok {α : Type} (x : α) :
    vecSequenceM 1 α #v[Except.ok x] = Except.ok #v[x] := by
  unfold vecSequenceM
  rw [show
    (fun i : Fin 1 => (#v[Except.ok x] : Vec 1 (Except String α))[i]) =
      (fun i : Fin 1 => Except.ok ((#v[x] : Vec 1 α)[i])) from by
    funext i
    cases i with
    | mk val isLt =>
        cases val with
        | zero => rfl
        | succ _ => omega]
  exact Vector.ofFnM_pure (m := Except String)
    (f := fun i : Fin 1 => (#v[x] : Vec 1 α)[i])

/-- Wrapped indexing through an already-successful vector, in bounds.
This is the direct Phase-beta counterpart of `atWithDefault_lt`. -/
theorem atWithDefaultM_ok_lt {α : Type} (n : Nat)
    (d : Except String α) (vM : Except String (Vec n α)) (v : Vec n α)
    (i : Nat) (hVec : vM = Except.ok v) (hLt : i < n) :
    atWithDefaultM n α d vM i = Except.ok (v[i]'hLt) := by
  unfold atWithDefaultM
  rw [hVec]
  simp [hLt, Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Wrapped indexing through an already-successful vector, out of bounds.
The vector must still succeed because `atWithDefaultM` evaluates it eagerly. -/
theorem atWithDefaultM_ok_ge {α : Type} (n : Nat)
    (d : Except String α) (vM : Except String (Vec n α)) (v : Vec n α)
    (i : Nat) (hVec : vM = Except.ok v) (hGe : n ≤ i) :
    atWithDefaultM n α d vM i = d := by
  unfold atWithDefaultM
  rw [hVec]
  simp [Nat.not_lt.mpr hGe, Bind.bind, Except.bind]

/-! ### Wrapped self-referential comprehension helpers

These definitions name the wrapped Phase-beta shape emitted for Cryptol
comprehensions of the form `[seed] # [ if b then step prev else prev
| b <- inputs | prev <- self ]`.  They are intentionally close to the emitted
term: the proof library reasons about the literal wrapped model, then derives
the pure recurrence view. -/

@[reducible] noncomputable def sawSelfRefCompInnerM
    (n : Nat) (α : Type)
    (d_pair : Except String (PairType Bool (PairType α UnitType)))
    (inputsM : Except String (Vec n Bool)) (stepTrue : α → α)
    (lookup : Nat → α) (j : Nat) : Except String α :=
  let rec_ := Pure.pure (gen (n+1) α lookup)
  let x__' := atWithDefaultM (Nat.min n (n+1))
    (PairType Bool (PairType α UnitType)) d_pair
    (Bind.bind inputsM (fun v_4 =>
      Bind.bind rec_ (fun v_5 =>
        Pure.pure (zip Bool α n (n+1) v_4 v_5)))) j
  let x__'' := Bind.bind
    (Bind.bind x__' (fun v_2 =>
      Pure.pure (Pair_snd Bool (PairType α UnitType) v_2)))
    (fun v_2' => Pure.pure (Pair_fst α UnitType v_2'))
  CryptolToLean.SAWCorePreludeExtra.iteM α
    (Bind.bind x__' (fun v_2 =>
      Pure.pure (Pair_fst Bool (PairType α UnitType) v_2)))
    (Bind.bind x__'' (fun v_1 => Pure.pure (stepTrue v_1)))
    x__''

@[reducible] noncomputable def sawSelfRefCompBodyM
    (n : Nat) (α : Type)
    (d_at : Except String α)
    (d_pair : Except String (PairType Bool (PairType α UnitType)))
    (seed : α) (inputsM : Except String (Vec n Bool))
    (stepTrue : α → α) :
    (Nat → α) → Nat → Except String α :=
  fun lookup i =>
    CryptolToLean.SAWCorePreludeExtra.iteM α (Pure.pure (ltNat i 1))
      (atWithDefaultM 1 α d_at
        (vecSequenceM 1 α #v[Pure.pure seed]) i)
      (atWithDefaultM n α d_at
        (genM n α
          (sawSelfRefCompInnerM n α d_pair inputsM stepTrue lookup))
        (subNat i 1))

theorem sawSelfRefCompInnerM_ok
    (n : Nat) (α : Type)
    (d_pair : Except String (PairType Bool (PairType α UnitType)))
    (inputsM : Except String (Vec n Bool)) (inputs : Vec n Bool)
    (stepTrue : α → α) (lookup : Nat → α) (j : Nat)
    (hInputs : inputsM = Except.ok inputs) (hLt : j < n) :
    sawSelfRefCompInnerM n α d_pair inputsM stepTrue lookup j =
      Except.ok
        (CryptolToLean.SAWCorePreludeExtra.ite α
          (atWithDefault n Bool false inputs j)
          (stepTrue (lookup j))
          (lookup j)) := by
  simp [sawSelfRefCompInnerM, hInputs, atWithDefaultM, hLt,
    zip, gen, atWithDefault, Pair_fst, Pair_snd,
    Vector.get, Vector.getElem_ofFn, CryptolToLean.SAWCorePreludeExtra.iteM,
    CryptolToLean.SAWCorePreludeExtra.ite,
    Bind.bind, Pure.pure, Except.bind, Except.pure]
  cases inputs[j] <;> rfl

theorem sawSelfRefCompBodyM_ok_of_success
    (n : Nat) (α : Type) [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType Bool (PairType α UnitType)))
    (seed : α) (inputsM : Except String (Vec n Bool)) (inputs : Vec n Bool)
    (stepTrue : α → α) (lookup : Nat → α) (i : Nat)
    (hInputs : inputsM = Except.ok inputs) (hLt : i < n+1) :
    sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue lookup i =
      Except.ok
        (CryptolToLean.SAWCorePreludeExtra.ite α (ltNat i 1)
          seed
          (CryptolToLean.SAWCorePreludeExtra.ite α
            (atWithDefault n Bool false inputs (subNat i 1))
            (stepTrue (lookup (subNat i 1)))
            (lookup (subNat i 1)))) := by
  cases i with
  | zero =>
      change
        atWithDefaultM 1 α d_at
          (vecSequenceM 1 α #v[Except.ok seed]) 0 = Except.ok seed
      rw [vecSequenceM_singleton_ok seed]
      simp [atWithDefaultM, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | succ k =>
      have hk : k < n := Nat.succ_lt_succ_iff.mp hLt
      have hFalse : ltNat (k+1) 1 = false := by simp [ltNat]
      rw [show
        sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue lookup (k+1) =
          atWithDefaultM n α d_at
            (genM n α
              (sawSelfRefCompInnerM n α d_pair inputsM stepTrue lookup))
            k from by
          simp [sawSelfRefCompBodyM, hFalse, subNat,
            CryptolToLean.SAWCorePreludeExtra.iteM, Pure.pure,
            Except.pure]]
      rw [genM_eq_ok_gen n
        (sawSelfRefCompInnerM n α d_pair inputsM stepTrue lookup)
        (fun j => CryptolToLean.SAWCorePreludeExtra.ite α
          (atWithDefault n Bool false inputs j)
          (stepTrue (lookup j)) (lookup j))]
      · simp [atWithDefaultM, gen, atWithDefault, hk, hFalse, subNat,
          Vector.getElem_ofFn,
          CryptolToLean.SAWCorePreludeExtra.ite, Bind.bind, Pure.pure,
          Except.bind, Except.pure]
      · intro j hj
        exact sawSelfRefCompInnerM_ok n α d_pair inputsM inputs stepTrue
          lookup j hInputs hj

@[reducible] noncomputable def sawSelfRefCompInnerSelfFirstM
    (n : Nat) (β α : Type)
    (d_pair : Except String (PairType α (PairType β UnitType)))
    (inputsM : Except String (Vec n β)) (step : α → β → α)
    (lookup : Nat → α) (j : Nat) : Except String α :=
  let rec_ := Pure.pure (gen (n+1) α lookup)
  let x__' := atWithDefaultM (Nat.min (n+1) n)
    (PairType α (PairType β UnitType)) d_pair
    (Bind.bind rec_ (fun v_4 =>
      Bind.bind inputsM (fun v_5 =>
        Pure.pure (zip α β (n+1) n v_4 v_5)))) j
  Bind.bind
    (Bind.bind x__' (fun v_1 =>
      Pure.pure (Pair_fst α (PairType β UnitType) v_1)))
    (fun prev =>
      Bind.bind
        (Bind.bind
          (Bind.bind x__' (fun v_2 =>
            Pure.pure (Pair_snd α (PairType β UnitType) v_2)))
          (fun v_2' => Pure.pure (Pair_fst β UnitType v_2')))
        (fun input => Pure.pure (step prev input)))

@[reducible] noncomputable def sawSelfRefCompBodySelfFirstM
    (n : Nat) (β α : Type)
    (d_at : Except String α)
    (d_pair : Except String (PairType α (PairType β UnitType)))
    (seed : α) (inputsM : Except String (Vec n β))
    (step : α → β → α) :
    (Nat → α) → Nat → Except String α :=
  fun lookup i =>
    CryptolToLean.SAWCorePreludeExtra.iteM α (Pure.pure (ltNat i 1))
      (atWithDefaultM 1 α d_at
        (vecSequenceM 1 α #v[Pure.pure seed]) i)
      (atWithDefaultM n α d_at
        (genM n α
          (sawSelfRefCompInnerSelfFirstM n β α d_pair inputsM step lookup))
        (subNat i 1))

theorem sawSelfRefCompInnerSelfFirstM_ok
    (n : Nat) (β α : Type) [Inhabited β]
    (d_pair : Except String (PairType α (PairType β UnitType)))
    (inputsM : Except String (Vec n β)) (inputs : Vec n β)
    (step : α → β → α) (lookup : Nat → α) (j : Nat)
    (hInputs : inputsM = Except.ok inputs) (hLt : j < n) :
    sawSelfRefCompInnerSelfFirstM n β α d_pair inputsM step lookup j =
      Except.ok (step (lookup j) (atWithDefault n β default inputs j)) := by
  simp [sawSelfRefCompInnerSelfFirstM, hInputs, atWithDefaultM, hLt,
    zip, gen, atWithDefault, Pair_fst, Pair_snd,
    Vector.get, Vector.getElem_ofFn,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem sawSelfRefCompBodySelfFirstM_ok_of_success
    (n : Nat) (β α : Type) [Inhabited β] [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType α (PairType β UnitType)))
    (seed : α) (inputsM : Except String (Vec n β)) (inputs : Vec n β)
    (step : α → β → α) (lookup : Nat → α) (i : Nat)
    (hInputs : inputsM = Except.ok inputs) (hLt : i < n+1) :
    sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step lookup i =
      Except.ok
        (CryptolToLean.SAWCorePreludeExtra.ite α (ltNat i 1)
          seed
          (step (lookup (subNat i 1))
            (atWithDefault n β default inputs (subNat i 1)))) := by
  cases i with
  | zero =>
      change
        atWithDefaultM 1 α d_at
          (vecSequenceM 1 α #v[Except.ok seed]) 0 = Except.ok seed
      rw [vecSequenceM_singleton_ok seed]
      simp [atWithDefaultM, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | succ k =>
      have hk : k < n := Nat.succ_lt_succ_iff.mp hLt
      have hFalse : ltNat (k+1) 1 = false := by simp [ltNat]
      rw [show
        sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step
            lookup (k+1) =
          atWithDefaultM n α d_at
            (genM n α
              (sawSelfRefCompInnerSelfFirstM n β α d_pair inputsM step lookup))
            k from by
          simp [sawSelfRefCompBodySelfFirstM, hFalse, subNat,
            CryptolToLean.SAWCorePreludeExtra.iteM, Pure.pure,
            Except.pure]]
      rw [genM_eq_ok_gen n
        (sawSelfRefCompInnerSelfFirstM n β α d_pair inputsM step lookup)
        (fun j => step (lookup j) (atWithDefault n β default inputs j))]
      · simp [atWithDefaultM, gen, atWithDefault, hk, hFalse, subNat,
          Vector.getElem_ofFn,
          CryptolToLean.SAWCorePreludeExtra.ite, Bind.bind, Pure.pure,
          Except.bind, Except.pure]
      · intro j hj
        exact sawSelfRefCompInnerSelfFirstM_ok n β α d_pair inputsM inputs
          step lookup j hInputs hj

/-- In-bounds selected indexing through `genM`, under an explicit
all-elements-success premise. This keeps the eager sequencing semantics
visible in the theorem statement rather than hiding it in Haskell. -/
theorem atWithDefaultM_genM_ok_lt {α : Type} (n : Nat)
    (d : Except String α) (f : Nat → Except String α) (g : Nat → α)
    (i : Nat) (hOk : ∀ j : Nat, j < n → f j = Except.ok (g j))
    (hLt : i < n) :
    atWithDefaultM n α d (genM n α f) i = f i := by
  rw [genM_eq_ok_gen n f g hOk]
  rw [hOk i hLt]
  unfold atWithDefaultM
  simp [hLt]
  show Except.ok ((gen n α g)[i]'hLt) = Except.ok (g i)
  simp [gen]

/-- Out-of-bounds selected indexing through `genM`, again under an
explicit all-elements-success premise. This premise is required because
`atWithDefaultM` sequences the vector argument before checking bounds. -/
theorem atWithDefaultM_genM_ok_ge {α : Type} (n : Nat)
    (d : Except String α) (f : Nat → Except String α) (g : Nat → α)
    (i : Nat) (hOk : ∀ j : Nat, j < n → f j = Except.ok (g j))
    (hGe : n ≤ i) :
    atWithDefaultM n α d (genM n α f) i = d := by
  rw [genM_eq_ok_gen n f g hOk]
  unfold atWithDefaultM
  simp [Nat.not_lt.mpr hGe]
  cases d <;> rfl

/-- Congruence for selected in-bounds indexing through eager `genM`.
The selected element may be compared directly only after both generated
vectors are known to be all-success. -/
theorem atWithDefaultM_genM_congr_lt {α : Type} (n : Nat)
    (d : Except String α)
    (f₁ f₂ : Nat → Except String α) (g₁ g₂ : Nat → α)
    (i : Nat)
    (hOk₁ : ∀ j : Nat, j < n → f₁ j = Except.ok (g₁ j))
    (hOk₂ : ∀ j : Nat, j < n → f₂ j = Except.ok (g₂ j))
    (hLt : i < n) (hEq : f₁ i = f₂ i) :
    atWithDefaultM n α d (genM n α f₁) i =
      atWithDefaultM n α d (genM n α f₂) i := by
  rw [atWithDefaultM_genM_ok_lt n d f₁ g₁ i hOk₁ hLt]
  rw [atWithDefaultM_genM_ok_lt n d f₂ g₂ i hOk₂ hLt]
  exact hEq

/-- Out-of-bounds congruence for selected indexing through eager `genM`.
Even though the default branch is returned, both vector computations must
first succeed. -/
theorem atWithDefaultM_genM_congr_ge {α : Type} (n : Nat)
    (d : Except String α)
    (f₁ f₂ : Nat → Except String α) (g₁ g₂ : Nat → α)
    (i : Nat)
    (hOk₁ : ∀ j : Nat, j < n → f₁ j = Except.ok (g₁ j))
    (hOk₂ : ∀ j : Nat, j < n → f₂ j = Except.ok (g₂ j))
    (hGe : n ≤ i) :
    atWithDefaultM n α d (genM n α f₁) i =
      atWithDefaultM n α d (genM n α f₂) i := by
  rw [atWithDefaultM_genM_ok_ge n d f₁ g₁ i hOk₁ hGe]
  rw [atWithDefaultM_genM_ok_ge n d f₂ g₂ i hOk₂ hGe]

/-- In-bounds selected indexing through eager `genM`, phrased using
success evidence rather than an explicit pure generator. This is often
the ergonomic form for generated proof obligations: the proof must show
every eager element succeeds, while the selected result remains exactly
the original wrapped element. -/
theorem atWithDefaultM_genM_ok_lt_of_success {α : Type} [Inhabited α] (n : Nat)
    (d : Except String α) (f : Nat → Except String α)
    (i : Nat) (hOk : ∀ j : Nat, j < n → ∃ x : α, f j = Except.ok x)
    (hLt : i < n) :
    atWithDefaultM n α d (genM n α f) i = f i := by
  let g : Nat → α := fun j =>
    if h : j < n then Classical.choose (hOk j h) else default
  have hOk' : ∀ j : Nat, j < n → f j = Except.ok (g j) := by
    intro j hj
    dsimp [g]
    rw [dif_pos hj]
    exact Classical.choose_spec (hOk j hj)
  exact atWithDefaultM_genM_ok_lt n d f g i hOk' hLt

/-- Out-of-bounds selected indexing through eager `genM`, using
success evidence. Even out of bounds, `genM` is sequenced first. -/
theorem atWithDefaultM_genM_ok_ge_of_success {α : Type} [Inhabited α] (n : Nat)
    (d : Except String α) (f : Nat → Except String α)
    (i : Nat) (hOk : ∀ j : Nat, j < n → ∃ x : α, f j = Except.ok x)
    (hGe : n ≤ i) :
    atWithDefaultM n α d (genM n α f) i = d := by
  let g : Nat → α := fun j =>
    if h : j < n then Classical.choose (hOk j h) else default
  have hOk' : ∀ j : Nat, j < n → f j = Except.ok (g j) := by
    intro j hj
    dsimp [g]
    rw [dif_pos hj]
    exact Classical.choose_spec (hOk j hj)
  exact atWithDefaultM_genM_ok_ge n d f g i hOk' hGe

/-- Congruence for selected in-bounds indexing through eager `genM`,
using success evidence for the eager parts and equality only at the
selected index. -/
theorem atWithDefaultM_genM_congr_lt_of_success {α : Type} [Inhabited α]
    (n : Nat) (d : Except String α)
    (f₁ f₂ : Nat → Except String α) (i : Nat)
    (hOk₁ : ∀ j : Nat, j < n → ∃ x : α, f₁ j = Except.ok x)
    (hOk₂ : ∀ j : Nat, j < n → ∃ x : α, f₂ j = Except.ok x)
    (hLt : i < n) (hEq : f₁ i = f₂ i) :
    atWithDefaultM n α d (genM n α f₁) i =
      atWithDefaultM n α d (genM n α f₂) i := by
  rw [atWithDefaultM_genM_ok_lt_of_success n d f₁ i hOk₁ hLt]
  rw [atWithDefaultM_genM_ok_lt_of_success n d f₂ i hOk₂ hLt]
  exact hEq

/-- Out-of-bounds congruence for selected indexing through eager `genM`,
using success evidence for both eager vectors. -/
theorem atWithDefaultM_genM_congr_ge_of_success {α : Type} [Inhabited α]
    (n : Nat) (d : Except String α)
    (f₁ f₂ : Nat → Except String α) (i : Nat)
    (hOk₁ : ∀ j : Nat, j < n → ∃ x : α, f₁ j = Except.ok x)
    (hOk₂ : ∀ j : Nat, j < n → ∃ x : α, f₂ j = Except.ok x)
    (hGe : n ≤ i) :
    atWithDefaultM n α d (genM n α f₁) i =
      atWithDefaultM n α d (genM n α f₂) i := by
  rw [atWithDefaultM_genM_ok_ge_of_success n d f₁ i hOk₁ hGe]
  rw [atWithDefaultM_genM_ok_ge_of_success n d f₂ i hOk₂ hGe]

/-- The fundamental vector round-trip: indexing every element of
`v` and re-`gen`-ing yields `v` back. Rocq: `gen_sawAt`. -/
theorem gen_atWithDefault
    (n : Nat) (α : Type) (d : α) (v : Vec n α) :
    gen n α (fun i => atWithDefault n α d v i) = v := by
  apply Vector.ext
  intro i hi
  simp [gen, atWithDefault]

/-- Indexing into a freshly `gen`-erated vector returns the
generator's output, for any in-bounds index. -/
theorem atWithDefault_gen
    (n : Nat) (α : Type) (d : α) (f : Nat → α) (i : Nat)
    (h : i < n) :
    atWithDefault n α d (gen n α f) i = f i := by
  simp [atWithDefault, gen, h]

/-- Vector reverse-self-inverse for our `gen`/`atWithDefault`
formulation. Given any default, double-reversing a vector via
the `gen n (fun i => at v (subNat (subNat n 1) i))` shape
recovers the original.

This is the lemma needed for stress-test E5
(`reverse (reverse xs) == xs`) and is one of the building
blocks for the deferred Salsa20 littleendian round-trip. The
lemma is stated using `subNat` (not `n - 1 - i`) so it
directly matches the translator's emitted shape — `subNat` is
a reducible alias but `simp only` doesn't unfold reducibles by
default. -/
theorem gen_atWithDefault_double_reverse
    (n : Nat) (α : Type) [Inhabited α] (d : α) (xs : Vec n α) :
    gen n α (fun i => atWithDefault n α d
      (gen n α (fun j => atWithDefault n α d xs (subNat (subNat n 1) j)))
      (subNat (subNat n 1) i)) = xs := by
  apply Vector.ext
  intro k hk
  simp only [gen, atWithDefault, subNat, Vector.getElem_ofFn]
  have h1 : n - 1 - k < n := by omega
  have h3 : n - 1 - (n - 1 - k) = k := by omega
  simp [h1, h3, hk]

/-- Out-of-bounds index returns the default. The translator's
emitted `error _ "at: index out of bounds"` plays this role at
emission time; this theorem states the corresponding semantic
fact for downstream proofs. -/
theorem atWithDefault_out_of_bounds
    (n : Nat) (α : Type) (d : α) (v : Vec n α) (i : Nat)
    (h : n ≤ i) : atWithDefault n α d v i = d := by
  simp [atWithDefault, Nat.not_lt.mpr h]

/-- Indexing a singleton literal vector at position 0 returns the
element. Used by Phase 5b's recursion-discharge proofs over
emitted `[seed] # …` shapes. Phase 8: now provable directly
from the structural `atWithDefault`. -/
theorem atWithDefault_singleton_zero
    (α : Type) (d : α) (x : α) :
    atWithDefault 1 α d #v[x] 0 = x := by
  simp [atWithDefault]

/-! ### Outer-wrapper peeling lemmas (Case Studies B/D)

`atWithDefault N α d (gen N α f) k = f k` and the analogous
`atWithDefault … (genFix …) i = genFixIdx … i` reduce the SAW
emission's outer wrapper one `Vector.ofFn` layer at a time without
forcing whnf on the body. Critical for proofs over deeply-nested
`gen`/`genFix` shapes where the body contains another `gen` —
`Vector.ofFn` materializes strictly, so naive `show`/`rfl` triggers
cartesian-product whnf cost (Case D, 2026-05-05 finding). -/

theorem atWithDefault_gen_lt {α : Type} (n : Nat) (d : α) (f : Nat → α)
    (k : Nat) (h : k < n) :
    atWithDefault n α d (gen n α f) k = f k := by
  unfold atWithDefault gen
  simp [h, Vector.getElem_ofFn]

/-- Generic `atWithDefault` peel: when the index is in bounds, the
default is unused and the result is the underlying vector indexing.
Used to bridge SAW's `atWithDefault N _ d v k` to Lean's `v[k]`
without committing to `v`'s specific shape (gen / genFix / zip /
arbitrary). Compose with shape-specific reductions (e.g.
`zip_getElem_lt`) downstream.

`@[simp]` so it fires on every emission where `k < n` is in
context — the dominant `atWithDefault` use pattern. Side condition
`h : k < n` is consumed via simp's standard hypothesis-discharge. -/
@[simp] theorem atWithDefault_lt {α : Type} {n : Nat}
    (d : α) (v : Vec n α) (k : Nat) (h : k < n) :
    atWithDefault n α d v k = v[k]'h := by
  unfold atWithDefault; simp [h]

theorem atWithDefault_genFix_lt {α : Type} (n : Nat) (d_at d_fix : α)
    (body : (Nat → α) → Nat → α) (i : Nat) (h : i < n) :
    atWithDefault n α d_at (genFix n α d_fix body) i = genFixIdx α d_fix body i := by
  unfold atWithDefault genFix
  simp [h, Vector.getElem_ofFn]

/-- Local helper: `v.get ⟨k, h⟩ = v[k]'h`. Used to bridge the
`.get`-based form `zip` produces to `[]` notation. -/
theorem Vector_get_eq_getElem {α : Type} {n : Nat}
    (v : Vector α n) (k : Nat) (h : k < n) :
    v.get ⟨k, h⟩ = v[k]'h := by
  unfold Vector.get; simp

/-- `zip` indexed at `k < min m n` gives a literal `PairValue` of
the elements at `k`. Lets a `zip`-using body's per-index proofs go
through without whnf-ing the underlying `Vector.ofFn`. -/
theorem zip_getElem_lt {α β : Type} (m n : Nat) (v : Vec m α) (w : Vec n β)
    (k : Nat) (h : k < Nat.min m n) :
    (zip α β m n v w)[k]'h
    = PairType.PairValue
        (v[k]'(Nat.lt_of_lt_of_le h (Nat.min_le_left m n)))
        (PairType.PairValue
          (w[k]'(Nat.lt_of_lt_of_le h (Nat.min_le_right m n)))
          UnitType.Unit) := by
  unfold zip
  rw [Vector.getElem_ofFn]
  have hm : k < m := Nat.lt_of_lt_of_le h (Nat.min_le_left m n)
  have hn : k < n := Nat.lt_of_lt_of_le h (Nat.min_le_right m n)
  show PairType.PairValue (v.get ⟨k, hm⟩) (PairType.PairValue (w.get ⟨k, hn⟩) UnitType.Unit) = _
  rw [Vector_get_eq_getElem v k hm, Vector_get_eq_getElem w k hn]

/-! ### `atWithDefault` on small literal vectors (Case Study C)

These specialized `@[simp]` lemmas reduce `atWithDefault N α d
#v[…] i` for small concrete `N` and `i` directly to the indexed
element, side-stepping the dependent-`if` whnf cost that bloats
when many such lookups are nested. Vec-of-4 covers the Salsa20
quarterround pattern; vec-of-3 / vec-of-2 / longer widths can
be added the same way as case studies surface them. -/

@[simp] theorem atWithDefault_4_lit_0 {α : Type} (d a b c d2 : α) :
    atWithDefault 4 α d #v[a, b, c, d2] 0 = a := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_4_lit_1 {α : Type} (d a b c d2 : α) :
    atWithDefault 4 α d #v[a, b, c, d2] 1 = b := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_4_lit_2 {α : Type} (d a b c d2 : α) :
    atWithDefault 4 α d #v[a, b, c, d2] 2 = c := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_4_lit_3 {α : Type} (d a b c d2 : α) :
    atWithDefault 4 α d #v[a, b, c, d2] 3 = d2 := by
  unfold atWithDefault; simp

/-! Vec-of-16 literal peelers — covers ChaCha20's 16-word state.
Each indexes into a 16-element literal vec at concrete `i ∈ [0, 16)`.
The naming `_16_lit_<i>` mirrors the vec-of-4 family above. -/

@[simp] theorem atWithDefault_16_lit_0 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 0 = x0 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_1 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 1 = x1 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_2 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 2 = x2 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_3 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 3 = x3 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_4 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 4 = x4 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_5 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 5 = x5 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_6 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 6 = x6 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_7 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 7 = x7 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_8 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 8 = x8 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_9 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 9 = x9 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_10 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 10 = x10 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_11 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 11 = x11 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_12 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 12 = x12 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_13 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 13 = x13 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_14 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 14 = x14 := by
  unfold atWithDefault; simp

@[simp] theorem atWithDefault_16_lit_15 {α : Type} (d x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    atWithDefault 16 α d #v[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] 15 = x15 := by
  unfold atWithDefault; simp

/-! ### `coerce` identity collapse

SAW's `coerce α β h x` where `α = β` (the dominant case for
emitted Cryptol type-arithmetic equalities like `n - 0 = n`,
`min n m = n` when `m ≥ n`, etc.) is just identity. The proof
witness `h` is irrelevant — proof irrelevance on `Eq Type α α`
makes any two proofs interchangeable, so the coerce reduces to
the input value regardless of how `h` was constructed
(including `unsafeAssert` synthesized witnesses).

Tier 2 readability fix per `doc/2026-05-09_readability-review.md`:
collapses the entire `Eq.rec`/`unsafeAssert` ceremony from goals
where the source and target types are syntactically equal —
which is virtually every emitted polymorphic Cryptol use of
`coerce`. -/

@[simp] theorem coerce_id {α : Type} (h : @Eq Type α α) (x : α) :
    coerce α α h x = x := by
  unfold coerce
  -- `cast h x` where `h : α = α` is `x` by proof irrelevance on Eq.
  rfl

/-! ### §4.4 SAW-emission peelers

The translator emits a small alphabet of SAW Prelude primitives
whose reduction in symbolic contexts requires explicit peelers —
Lean's reducer alone cannot unfold `gen` / `atWithDefault` /
`Pair_fst`/`Pair_snd` / `zip` past metavariables or in-bound
checks. These peelers reduce a goal in SAW emission shape down to
underlying primitives that `bv_decide` / `decide` / `rfl` can
close.

Validated end-to-end against the popcount-shape body emitted by
the `[seed]#[…|<-self]` comprehension lowering (Phase 5
BoundedVecFold). See `intTestsProbe/popcount_via_bridge/probe.lean`
for the symbolic-`k` step-equation discharge that motivated this
section.

Together these are the building blocks of a `saw_simp` simp-set
(forthcoming as a `@[saw_peeler]` attribute when the surface
stabilizes; for now they're individually `@[simp]`-tagged so a
user-written `simp` invocation can pick them up).

The peelers split into three groups:

1. **Pair projection** (`Pair_fst_PairValue`, `Pair_snd_PairValue`)
   — eta on SAW `PairValue`. Definitional but symbolic-`k` proofs
   need them explicitly because `Pair_fst` is not `@[reducible]`.

2. **`atWithDefault` on `zip`** (`atWithDefault_zip_lt`) — combines
   the in-bounds atWithDefault rule with `zip_getElem_lt` into a
   single rewrite for the common SAW-emitted shape `atWithDefault N
   _ _ (zip α β m n v w) k` with `k < N`.

3. **Arithmetic micro-rules** — `subNat (k+1) 1 = k`,
   `ltNat_succ_one_eq_false`. These could be derived via
   `simp [subNat_eq_natSub]; omega` chains, but having them as
   `@[simp]` lemmas keeps the peeler invocation a one-liner. -/

/-- Pair projection eta on `Pair_fst` over a literal `PairValue`.
SAW emits `Pair_fst α β (PairValue x y)` and we want to project to
`x`. Reduces by definition, but `Pair_fst` is `def`-not-`@[reducible]`
so we need the rewrite available to `simp`. -/
@[simp] theorem Pair_fst_PairValue {α β : Type} (x : α) (y : β) :
    Pair_fst α β (PairType.PairValue x y) = x := rfl

/-- Pair projection eta on `Pair_snd`. Companion to `Pair_fst_PairValue`. -/
@[simp] theorem Pair_snd_PairValue {α β : Type} (x : α) (y : β) :
    Pair_snd α β (PairType.PairValue x y) = y := rfl

/-- `atWithDefault` over a `zip` at an in-bounds index reduces to the
literal `PairValue` of the per-element values. The atWithDefault
length is `Nat.min m n`, matching what `zip` produces. -/
theorem atWithDefault_zip_lt {α β : Type} (m n : Nat)
    (v : Vec m α) (w : Vec n β) (d : PairType α (PairType β UnitType))
    (k : Nat) (h : k < Nat.min m n) :
    atWithDefault (Nat.min m n) (PairType α (PairType β UnitType))
      d (zip α β m n v w) k
    = PairType.PairValue
        (v[k]'(Nat.lt_of_lt_of_le h (Nat.min_le_left m n)))
        (PairType.PairValue
          (w[k]'(Nat.lt_of_lt_of_le h (Nat.min_le_right m n)))
          UnitType.Unit) := by
  unfold atWithDefault
  simp only [h, ↓reduceDIte]
  exact zip_getElem_lt m n v w k h

/-! Note on length normalization for `zip`: when SAW emits
`atWithDefault L PT d (zip α β m n v w) k` the elaborator may have
already reduced `minNat m n` (zip's return-type length) to a
concrete `m` or `n`. The peeler `atWithDefault_zip_lt` is stated at
the type-correct length `Nat.min m n`. To apply it on a goal where
the length appears as `m` or `n` directly, the user rewrites first
via the standard library's `Nat.min_eq_left`/`Nat.min_eq_right`
(no wrapper needed). The `simp` invocation pattern is:

  -- goal has `atWithDefault m PT d (zip α β m n v w) k`, m ≤ n
  rw [show m = Nat.min m n from (Nat.min_eq_left ‹m ≤ n›).symm]
  rw [atWithDefault_zip_lt m n v w d k ‹k < Nat.min m n›]

This is one rewrite step; the alternative of stating
`_left`/`_right` adapter variants would force a `cast` over the
underlying `zip` value (since `Vec m ≠ Vec (minNat m n)`
syntactically) and is not principled. -/

/-- `ltNat (k+1) 1 = false`. The SAW comprehension lowering emits
`ite (ltNat i' 1) seed-branch step-branch`; after the outer `gen`
unfolds to step `i' = k+1`, this peeler takes the False branch.

Justified as a focused peeler: `simp [ltNat_eq_decide_lt]` reduces
to `decide ((k+1) < 1)`, but `decide` won't close that for symbolic
`k` without an additional `omega`/`Nat.succ_ne_zero` hop. Packaging
the chain here keeps downstream `simp` invocations terse. -/
@[simp] theorem ltNat_succ_one_eq_false (k : Nat) : ltNat (k+1) 1 = false := by
  show decide ((k+1) < 1) = false
  apply decide_eq_false; omega

theorem sawSelfRefCompBodyM_productive_of_success
    (n : Nat) (α : Type) [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType Bool (PairType α UnitType)))
    (seed : α) (inputsM : Except String (Vec n Bool)) (inputs : Vec n Bool)
    (stepTrue : α → α)
    (hInputs : inputsM = Except.ok inputs) :
    GenFixBodyProductive α
      (sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue) := by
  unfold GenFixBodyProductive
  intro i lookup₁ lookup₂ hLookup
  cases i with
  | zero =>
      simp [sawSelfRefCompBodyM, atWithDefaultM, vecSequenceM,
        CryptolToLean.SAWCorePreludeExtra.iteM, Bind.bind, Pure.pure,
        Except.bind, Except.pure]
  | succ k =>
      have hFalse : ltNat (k+1) 1 = false := ltNat_succ_one_eq_false k
      by_cases hk : k < n
      · rw [show
          sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue lookup₁ (k+1) =
            atWithDefaultM n α d_at
              (genM n α
                (sawSelfRefCompInnerM n α d_pair inputsM stepTrue lookup₁))
              k from by
            simp [sawSelfRefCompBodyM, hFalse, subNat,
              CryptolToLean.SAWCorePreludeExtra.iteM,
              Pure.pure, Except.pure]]
        rw [show
          sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue lookup₂ (k+1) =
            atWithDefaultM n α d_at
              (genM n α
                (sawSelfRefCompInnerM n α d_pair inputsM stepTrue lookup₂))
              k from by
            simp [sawSelfRefCompBodyM, hFalse, subNat,
              CryptolToLean.SAWCorePreludeExtra.iteM,
              Pure.pure, Except.pure]]
        apply atWithDefaultM_genM_congr_lt_of_success
        · intro j hj
          exact ⟨CryptolToLean.SAWCorePreludeExtra.ite α
            (atWithDefault n Bool false inputs j)
            (stepTrue (lookup₁ j)) (lookup₁ j),
            sawSelfRefCompInnerM_ok n α d_pair inputsM inputs
              stepTrue lookup₁ j hInputs hj⟩
        · intro j hj
          exact ⟨CryptolToLean.SAWCorePreludeExtra.ite α
            (atWithDefault n Bool false inputs j)
            (stepTrue (lookup₂ j)) (lookup₂ j),
            sawSelfRefCompInnerM_ok n α d_pair inputsM inputs
              stepTrue lookup₂ j hInputs hj⟩
        · exact hk
        · rw [sawSelfRefCompInnerM_ok n α d_pair inputsM inputs
              stepTrue lookup₁ k hInputs hk]
          rw [sawSelfRefCompInnerM_ok n α d_pair inputsM inputs
              stepTrue lookup₂ k hInputs hk]
          rw [hLookup k (Nat.lt_succ_self k)]
      · have hge : n ≤ k := Nat.le_of_not_gt hk
        rw [show
          sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue lookup₁ (k+1) =
            atWithDefaultM n α d_at
              (genM n α
                (sawSelfRefCompInnerM n α d_pair inputsM stepTrue lookup₁))
              k from by
            simp [sawSelfRefCompBodyM, hFalse, subNat,
              CryptolToLean.SAWCorePreludeExtra.iteM,
              Pure.pure, Except.pure]]
        rw [show
          sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue lookup₂ (k+1) =
            atWithDefaultM n α d_at
              (genM n α
                (sawSelfRefCompInnerM n α d_pair inputsM stepTrue lookup₂))
              k from by
            simp [sawSelfRefCompBodyM, hFalse, subNat,
              CryptolToLean.SAWCorePreludeExtra.iteM,
              Pure.pure, Except.pure]]
        apply atWithDefaultM_genM_congr_ge_of_success
        · intro j hj
          exact ⟨CryptolToLean.SAWCorePreludeExtra.ite α
            (atWithDefault n Bool false inputs j)
            (stepTrue (lookup₁ j)) (lookup₁ j),
            sawSelfRefCompInnerM_ok n α d_pair inputsM inputs
              stepTrue lookup₁ j hInputs hj⟩
        · intro j hj
          exact ⟨CryptolToLean.SAWCorePreludeExtra.ite α
            (atWithDefault n Bool false inputs j)
            (stepTrue (lookup₂ j)) (lookup₂ j),
            sawSelfRefCompInnerM_ok n α d_pair inputsM inputs
              stepTrue lookup₂ j hInputs hj⟩
        · exact hge

theorem sawSelfRefCompBodyM_productive
    (n : Nat) (α : Type) [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType Bool (PairType α UnitType)))
    (seed : α) (inputsM : Except String (Vec n Bool))
    (stepTrue : α → α) :
    GenFixBodyProductive α
      (sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue) := by
  cases hInputs : inputsM with
  | ok inputs =>
      exact sawSelfRefCompBodyM_productive_of_success n α d_at d_pair
        seed (Except.ok inputs) inputs stepTrue rfl
  | error msg =>
      unfold GenFixBodyProductive
      intro i lookup₁ lookup₂ hLookup
      cases i with
      | zero =>
          simp [sawSelfRefCompBodyM, atWithDefaultM, vecSequenceM,
            CryptolToLean.SAWCorePreludeExtra.iteM, Bind.bind, Pure.pure,
            Except.bind, Except.pure]
      | succ k =>
          have hFalse : ltNat (k+1) 1 = false := ltNat_succ_one_eq_false k
          simp [sawSelfRefCompBodyM, sawSelfRefCompInnerM, hFalse,
            subNat, atWithDefaultM, genM, Bind.bind, Pure.pure, Except.bind,
            Except.pure, CryptolToLean.SAWCorePreludeExtra.iteM]

theorem sawSelfRefCompBodySelfFirstM_productive_of_success
    (n : Nat) (β α : Type) [Inhabited β] [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType α (PairType β UnitType)))
    (seed : α) (inputsM : Except String (Vec n β)) (inputs : Vec n β)
    (step : α → β → α)
    (hInputs : inputsM = Except.ok inputs) :
    GenFixBodyProductive α
      (sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step) := by
  unfold GenFixBodyProductive
  intro i lookup₁ lookup₂ hLookup
  cases i with
  | zero =>
      simp [sawSelfRefCompBodySelfFirstM, atWithDefaultM, vecSequenceM,
        CryptolToLean.SAWCorePreludeExtra.iteM, Bind.bind, Pure.pure,
        Except.bind, Except.pure]
  | succ k =>
      have hFalse : ltNat (k+1) 1 = false := ltNat_succ_one_eq_false k
      by_cases hk : k < n
      · rw [show
          sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step lookup₁ (k+1) =
            atWithDefaultM n α d_at
              (genM n α
                (sawSelfRefCompInnerSelfFirstM n β α d_pair inputsM step lookup₁))
              k from by
            simp [sawSelfRefCompBodySelfFirstM, hFalse, subNat,
              CryptolToLean.SAWCorePreludeExtra.iteM,
              Pure.pure, Except.pure]]
        rw [show
          sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step lookup₂ (k+1) =
            atWithDefaultM n α d_at
              (genM n α
                (sawSelfRefCompInnerSelfFirstM n β α d_pair inputsM step lookup₂))
              k from by
            simp [sawSelfRefCompBodySelfFirstM, hFalse, subNat,
              CryptolToLean.SAWCorePreludeExtra.iteM,
              Pure.pure, Except.pure]]
        apply atWithDefaultM_genM_congr_lt_of_success
        · intro j hj
          exact ⟨step (lookup₁ j) (atWithDefault n β default inputs j),
            sawSelfRefCompInnerSelfFirstM_ok n β α d_pair inputsM inputs
              step lookup₁ j hInputs hj⟩
        · intro j hj
          exact ⟨step (lookup₂ j) (atWithDefault n β default inputs j),
            sawSelfRefCompInnerSelfFirstM_ok n β α d_pair inputsM inputs
              step lookup₂ j hInputs hj⟩
        · exact hk
        · rw [sawSelfRefCompInnerSelfFirstM_ok n β α d_pair inputsM inputs
              step lookup₁ k hInputs hk]
          rw [sawSelfRefCompInnerSelfFirstM_ok n β α d_pair inputsM inputs
              step lookup₂ k hInputs hk]
          rw [hLookup k (Nat.lt_succ_self k)]
      · have hge : n ≤ k := Nat.le_of_not_gt hk
        rw [show
          sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step lookup₁ (k+1) =
            atWithDefaultM n α d_at
              (genM n α
                (sawSelfRefCompInnerSelfFirstM n β α d_pair inputsM step lookup₁))
              k from by
            simp [sawSelfRefCompBodySelfFirstM, hFalse, subNat,
              CryptolToLean.SAWCorePreludeExtra.iteM,
              Pure.pure, Except.pure]]
        rw [show
          sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step lookup₂ (k+1) =
            atWithDefaultM n α d_at
              (genM n α
                (sawSelfRefCompInnerSelfFirstM n β α d_pair inputsM step lookup₂))
              k from by
            simp [sawSelfRefCompBodySelfFirstM, hFalse, subNat,
              CryptolToLean.SAWCorePreludeExtra.iteM,
              Pure.pure, Except.pure]]
        apply atWithDefaultM_genM_congr_ge_of_success
        · intro j hj
          exact ⟨step (lookup₁ j) (atWithDefault n β default inputs j),
            sawSelfRefCompInnerSelfFirstM_ok n β α d_pair inputsM inputs
              step lookup₁ j hInputs hj⟩
        · intro j hj
          exact ⟨step (lookup₂ j) (atWithDefault n β default inputs j),
            sawSelfRefCompInnerSelfFirstM_ok n β α d_pair inputsM inputs
              step lookup₂ j hInputs hj⟩
        · exact hge

theorem sawSelfRefCompBodySelfFirstM_productive
    (n : Nat) (β α : Type) [Inhabited β] [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType α (PairType β UnitType)))
    (seed : α) (inputsM : Except String (Vec n β))
    (step : α → β → α) :
    GenFixBodyProductive α
      (sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step) := by
  cases hInputs : inputsM with
  | ok inputs =>
      exact sawSelfRefCompBodySelfFirstM_productive_of_success n β α d_at
        d_pair seed (Except.ok inputs) inputs step rfl
  | error msg =>
      unfold GenFixBodyProductive
      intro i lookup₁ lookup₂ hLookup
      cases i with
      | zero =>
          simp [sawSelfRefCompBodySelfFirstM, atWithDefaultM, vecSequenceM,
            CryptolToLean.SAWCorePreludeExtra.iteM, Bind.bind, Pure.pure,
            Except.bind, Except.pure]
      | succ k =>
          have hFalse : ltNat (k+1) 1 = false := ltNat_succ_one_eq_false k
          simp [sawSelfRefCompBodySelfFirstM, sawSelfRefCompInnerSelfFirstM,
            hFalse, subNat, atWithDefaultM, genM, Bind.bind, Pure.pure,
            Except.bind, Except.pure, CryptolToLean.SAWCorePreludeExtra.iteM]

/-! ## genFix bridge library (§4.1, Case Studies B/D)

The translator emits Cryptol's bounded-vector self-referential
comprehensions (`xs = [seed] # [body i | i <- inputs | prev <- xs]`)
as `genFix N α d body` (Phase 5 BoundedVecFold lowering). The
emission is faithful to SAW semantics, but `bv_decide` can't see
through `genFix` (Case Study B/D, 2026-05-05). Per the
obvious-correctness principle (long-term plan §2.4), the bridge
back to a `bv_decide`-friendly shape lives here as a Lean theorem
— not as a translator-side rewrite.

The strategy: prove that if a body satisfies a single-step
accumulator recurrence, `genFixIdx` agrees with `Nat.rec`'d
unfolding of that recurrence. Closed-form unfolding (via
`Nat.rec`) is what `bv_decide` can handle once unrolled at a
concrete index. -/

/-- The empty/zero base case. `genFixIdx` at index 0 calls the
body with the all-default lookup; the result is whatever body
returns at index 0. -/
theorem genFixIdx_zero (α : Type) (d : α) (body : (Nat → α) → Nat → α) :
    genFixIdx α d body 0 = body (fun _ => d) 0 := by
  unfold genFixIdx genFixListBuild
  rfl

/-- The list-build at length n has length n. -/
theorem genFixListBuild_length (α : Type) (d : α) (body : (Nat → α) → Nat → α) :
    ∀ n, (genFixListBuild α d body n).length = n
  | 0     => rfl
  | k + 1 => by
      unfold genFixListBuild
      simp [genFixListBuild_length α d body k]

/-- Generic `getD` on append: in-bounds indexing is stable under
extension by one element. -/
private theorem getD_append_left {α : Type} (xs : List α) (y : α) (j : Nat) (d : α)
    (h : j < xs.length) : (xs ++ [y]).getD j d = xs.getD j d := by
  have h2 : j < (xs ++ [y]).length := by simp; omega
  rw [(List.getElem_eq_getD (l := xs ++ [y]) (h := h2) d).symm]
  rw [(List.getElem_eq_getD (l := xs) (h := h) d).symm]
  exact List.getElem_append_left h

/-- The new last element of an append at the boundary index. -/
private theorem getD_append_right {α : Type} (xs : List α) (y : α) (d : α) :
    (xs ++ [y]).getD xs.length d = y := by
  have h2 : xs.length < (xs ++ [y]).length := by simp
  rw [(List.getElem_eq_getD (l := xs ++ [y]) (h := h2) d).symm]
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

/-- Convenience: index-aware version of `getD_append_right` that
takes the equality `i = xs.length` instead of demanding the goal
already be normalized. -/
private theorem getD_append_right_at
    {α : Type} (xs : List α) (y : α) (d : α) (i : Nat) (h : i = xs.length) :
    (xs ++ [y]).getD i d = y := by
  subst h; exact getD_append_right xs y d

/-- Indices below `n` are stable when extending the list-build by
one more step. -/
theorem genFixListBuild_succ_getD_lt
    (α : Type) (d : α) (body : (Nat → α) → Nat → α) (n j : Nat) (h : j < n) :
    (genFixListBuild α d body (n+1)).getD j d
      = (genFixListBuild α d body n).getD j d := by
  show (genFixListBuild α d body n ++
        [body (fun i => (genFixListBuild α d body n).getD i d) n]).getD j d
      = (genFixListBuild α d body n).getD j d
  have hlen : (genFixListBuild α d body n).length = n :=
    genFixListBuild_length α d body n
  have h' : j < (genFixListBuild α d body n).length := by rw [hlen]; exact h
  exact getD_append_left _ _ j d h'

/-- For `j < n`, the j-th element of the list-build at length `n`
agrees with `genFixIdx … j`. Together with the unfolding equation
this gives a clean way to reason about lookups inside body. -/
theorem genFixListBuild_getD_eq_genFixIdx
    (α : Type) (d : α) (body : (Nat → α) → Nat → α) (n j : Nat) (h : j < n) :
    (genFixListBuild α d body n).getD j d = genFixIdx α d body j := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hjk : j < k
    · rw [genFixListBuild_succ_getD_lt α d body k j hjk]
      exact ih hjk
    · -- j = k (the new element)
      have hjk' : j = k := by omega
      subst hjk'
      show (genFixListBuild α d body j ++
            [body (fun i => (genFixListBuild α d body j).getD i d) j]).getD j d
        = genFixIdx α d body j
      have hlen : (genFixListBuild α d body j).length = j :=
        genFixListBuild_length α d body j
      rw [getD_append_right_at _ _ _ j hlen.symm]
      -- Goal: body (fun i => prev.getD i d) j = genFixIdx α d body j.
      -- The RHS unfolds to the same expression via genFixIdx's definition.
      show _ = (genFixListBuild α d body (j+1)).getD j d
      show _ = (genFixListBuild α d body j ++
                [body (fun i => (genFixListBuild α d body j).getD i d) j]).getD j d
      rw [getD_append_right_at _ _ _ j hlen.symm]

/-- Successor unfold: `genFixIdx … (k+1)` equals body applied at
index `k+1`, with lookup substituted by `genFixIdx … j` for j ≤ k.
The lookup function is `fun j => (genFixListBuild α d body (k+1)).getD j d`,
which agrees with `genFixIdx α d body j` for j < k+1 (i.e., j ≤ k). -/
theorem genFixIdx_succ
    (α : Type) (d : α) (body : (Nat → α) → Nat → α) (k : Nat) :
    genFixIdx α d body (k+1) =
      body (fun j => (genFixListBuild α d body (k+1)).getD j d) (k+1) := by
  show (genFixListBuild α d body (k+1+1)).getD (k+1) d = _
  show (genFixListBuild α d body (k+1) ++
        [body (fun i => (genFixListBuild α d body (k+1)).getD i d) (k+1)]).getD (k+1) d
      = _
  have hlen : (genFixListBuild α d body (k+1)).length = k+1 :=
    genFixListBuild_length α d body (k+1)
  exact getD_append_right_at _ _ _ (k+1) hlen.symm

/-- The headline bridge. If the body's behavior at every index is
determined by a single-step accumulator recurrence — `body lookup 0 =
seed`, and `body lookup (k+1) = step (lookup k)` whenever lookup
agrees with `genFixIdx` for indices ≤ k — then `genFixIdx … k`
equals the k-fold unfolding of the recurrence.

Once a user verifies their body satisfies these two equations
(usually a one-liner via `simp` on the body's specific shape),
this bridge unrolls `genFix` into a `Nat.rec` that `bv_decide` can
reason about at any concrete index. -/
theorem genFixIdx_eq_recurrence
    (α : Type) (d : α) (body : (Nat → α) → Nat → α)
    (seed : α) (step : Nat → α → α)
    (h_seed : body (fun _ => d) 0 = seed)
    (h_step : ∀ (lookup : Nat → α) (k : Nat),
      (∀ j, j ≤ k → lookup j = genFixIdx α d body j) →
      body lookup (k+1) = step k (lookup k)) :
    ∀ k, genFixIdx α d body k = Nat.rec seed (fun i acc => step i acc) k := by
  intro k
  induction k with
  | zero => rw [genFixIdx_zero]; exact h_seed
  | succ k ih =>
    rw [genFixIdx_succ]
    have hlu : ∀ j, j ≤ k →
        (genFixListBuild α d body (k+1)).getD j d = genFixIdx α d body j := by
      intro j hj
      exact genFixListBuild_getD_eq_genFixIdx α d body (k+1) j (by omega)
    rw [h_step _ k hlu]
    rw [hlu k (Nat.le_refl k), ih]

/-- Bounded variant of `genFixIdx_eq_recurrence`: `h_step` is only
required on indices `k < n`, and the conclusion is at the specific
n. This is the form that scales for popcount-shape bodies (where
the body's step equation can be verified at concrete k via `rfl`,
but does NOT hold universally for k ≥ n where the body's inner
`gen n` runs out of bounds).

Use case: discharge `genFixIdx body N = Nat.rec seed step N` by
case-splitting on k via `match k, hk with | 0, _ => ...rfl | ...
| N-1, _ => ...rfl | k'+N, hk' => omega`-style pattern. The
Nat.rec-form conclusion is a single shared expression — no
exponential blowup even for popcount-shape bodies whose step
expression references the previous accumulator twice (in then-
and else- branches of an ite). -/
theorem genFixIdx_eq_recurrence_bounded
    (α : Type) (d : α) (body : (Nat → α) → Nat → α)
    (seed : α) (step : Nat → α → α) (n : Nat)
    (h_seed : body (fun _ => d) 0 = seed)
    (h_step : ∀ (lookup : Nat → α) (k : Nat), k < n →
      (∀ j, j ≤ k → lookup j = genFixIdx α d body j) →
      body lookup (k+1) = step k (lookup k)) :
    genFixIdx α d body n = Nat.rec seed (fun i acc => step i acc) n := by
  induction n with
  | zero => rw [genFixIdx_zero]; exact h_seed
  | succ k ih =>
    rw [genFixIdx_succ]
    have hlu : ∀ j, j ≤ k →
        (genFixListBuild α d body (k+1)).getD j d = genFixIdx α d body j := by
      intro j hj
      exact genFixListBuild_getD_eq_genFixIdx α d body (k+1) j (by omega)
    rw [h_step _ k (Nat.lt_succ_self k) hlu]
    rw [hlu k (Nat.le_refl k)]
    rw [ih (fun lookup j hj h_lk => h_step lookup j (Nat.lt_succ_of_lt hj) h_lk)]

/-! ### Wrapped bounded-vector fix bridge

The translator's Phase-beta output is intentionally literal: recursive
bounded-vector bodies are emitted in `Except`, using `genM` and
`atWithDefaultM`.  The theorems in this section are the checked bridge from
that dumb wrapped obligation to the pure `genFix` recurrence library above.

The key precondition is also literal: Lean must prove that every body element
the fix actually builds succeeds.  Once that is known, the wrapped structural
build is equal to the pure structural build for the corresponding raw body.
No Haskell classifier conclusion is trusted here; any generated proof is just
a proof attempt for these Lean statements. -/

theorem genFixListBuildM_eq_ok_genFixListBuild_of_ok_lt
    (α : Type) (d : α)
    (bodyM : (Nat → α) → Nat → Except String α)
    (body : (Nat → α) → Nat → α) :
    ∀ n : Nat,
      (∀ (lookup : Nat → α) (i : Nat), i < n →
        bodyM lookup i = Except.ok (body lookup i)) →
      genFixListBuildM α d bodyM n =
        Except.ok (genFixListBuild α d body n)
  | 0, _ => rfl
  | k + 1, hOk => by
      unfold genFixListBuildM genFixListBuild
      rw [genFixListBuildM_eq_ok_genFixListBuild_of_ok_lt
        α d bodyM body k]
      · change
          (Bind.bind
            (bodyM (fun i => (genFixListBuild α d body k).getD i d) k)
            (fun next => Except.ok
              (genFixListBuild α d body k ++ [next]))) =
            Except.ok
              (genFixListBuild α d body k ++
                [body (fun i => (genFixListBuild α d body k).getD i d) k])
        rw [hOk (fun i => (genFixListBuild α d body k).getD i d)
          k (Nat.lt_succ_self k)]
        rfl
      · intro lookup i hi
        exact hOk lookup i (Nat.lt_succ_of_lt hi)

theorem genFixM_eq_ok_genFix_of_ok_lt
    (n : Nat) (α : Type) (dM : Except String α) (d : α)
    (bodyM : (Nat → α) → Nat → Except String α)
    (body : (Nat → α) → Nat → α)
    (hDefault : dM = Except.ok d)
    (hOk : ∀ (lookup : Nat → α) (i : Nat), i < n →
      bodyM lookup i = Except.ok (body lookup i)) :
    genFixM n α dM bodyM = Except.ok (genFix n α d body) := by
  unfold genFixM
  rw [hDefault]
  change
    (Bind.bind (genFixListBuildM α d bodyM n)
      (fun lst => Except.ok (Vector.ofFn (fun i => lst.getD i.val d)))) =
      Except.ok (genFix n α d body)
  rw [genFixListBuildM_eq_ok_genFixListBuild_of_ok_lt α d bodyM body n hOk]
  unfold genFix
  change
    Except.ok (Vector.ofFn
      (fun i => (genFixListBuild α d body n).getD i.val d)) =
      Except.ok (Vector.ofFn (fun i => genFixIdx α d body i.val))
  apply congrArg Except.ok
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  exact genFixListBuild_getD_eq_genFixIdx α d body n i hi

theorem atWithDefaultM_genFixM_ok_lt_of_ok_lt
    (n : Nat) (α : Type) (dAt dM : Except String α) (d : α)
    (bodyM : (Nat → α) → Nat → Except String α)
    (body : (Nat → α) → Nat → α) (i : Nat)
    (hDefault : dM = Except.ok d)
    (hOk : ∀ (lookup : Nat → α) (k : Nat), k < n →
      bodyM lookup k = Except.ok (body lookup k))
    (hLt : i < n) :
    atWithDefaultM n α dAt (genFixM n α dM bodyM) i =
      Except.ok (genFixIdx α d body i) := by
  rw [genFixM_eq_ok_genFix_of_ok_lt n α dM d bodyM body hDefault hOk]
  unfold atWithDefaultM
  simp [hLt, Bind.bind, Pure.pure, Except.bind, Except.pure]
  unfold genFix
  simp [Vector.getElem_ofFn]

theorem genFixVecChecked_eq_ok_genFix_of_ok_lt
    (n : Nat) (α : Type) (dM : Except String α) (d : α)
    (bodyVec : (Nat → α) → Except String (Vec n α))
    (bodyM : (Nat → α) → Nat → Except String α)
    (body : (Nat → α) → Nat → α)
    (hSound : GenFixVecBodySound n α bodyVec bodyM)
    (hProductive : GenFixBodyProductive α bodyM)
    (hDefault : dM = Except.ok d)
    (hOk : ∀ (lookup : Nat → α) (i : Nat), i < n →
      bodyM lookup i = Except.ok (body lookup i)) :
    genFixVecChecked n α dM bodyVec bodyM hSound hProductive =
      Except.ok (genFix n α d body) := by
  unfold genFixVecChecked
  exact genFixM_eq_ok_genFix_of_ok_lt n α dM d bodyM body hDefault hOk

theorem atWithDefaultM_genFixVecChecked_ok_lt_of_ok_lt
    (n : Nat) (α : Type) (dAt dM : Except String α) (d : α)
    (bodyVec : (Nat → α) → Except String (Vec n α))
    (bodyM : (Nat → α) → Nat → Except String α)
    (body : (Nat → α) → Nat → α) (i : Nat)
    (hSound : GenFixVecBodySound n α bodyVec bodyM)
    (hProductive : GenFixBodyProductive α bodyM)
    (hDefault : dM = Except.ok d)
    (hOk : ∀ (lookup : Nat → α) (k : Nat), k < n →
      bodyM lookup k = Except.ok (body lookup k))
    (hLt : i < n) :
    atWithDefaultM n α dAt
      (genFixVecChecked n α dM bodyVec bodyM hSound hProductive) i =
      Except.ok (genFixIdx α d body i) := by
  unfold genFixVecChecked
  exact atWithDefaultM_genFixM_ok_lt_of_ok_lt n α dAt dM d
    bodyM body i hDefault hOk hLt

theorem selfRefCompGenFixVecCheckedM_at_zero_eq_natRec
    (n : Nat) (α : Type) [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType Bool (PairType α UnitType)))
    (d_fix seed : α)
    (inputsM : Except String (Vec n Bool)) (inputs : Vec n Bool)
    (stepTrue : α → α)
    (bodyVec : (Nat → α) → Except String (Vec (n+1) α))
    (hSound : GenFixVecBodySound (n+1) α bodyVec
      (sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue))
    (hProductive : GenFixBodyProductive α
      (sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue))
    (hInputs : inputsM = Except.ok inputs) :
    atWithDefaultM (n+1) α d_at
      (genM (n+1) α (fun i =>
        atWithDefaultM (n+1) α d_at
          (genFixVecChecked (n+1) α (Except.ok d_fix) bodyVec
            (sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue)
            hSound hProductive)
          (subNat n i)))
      0 =
    Except.ok
      (Nat.rec (motive := fun _ => α) seed
        (fun i acc => CryptolToLean.SAWCorePreludeExtra.ite α
          (atWithDefault n Bool false inputs i) (stepTrue acc) acc)
        n) := by
  let body : (Nat → α) → Nat → α := fun lookup i =>
    CryptolToLean.SAWCorePreludeExtra.ite α (ltNat i 1)
      seed
      (CryptolToLean.SAWCorePreludeExtra.ite α
        (atWithDefault n Bool false inputs (subNat i 1))
        (stepTrue (lookup (subNat i 1)))
        (lookup (subNat i 1)))
  rw [atWithDefaultM_genM_ok_lt (n+1) d_at
    (fun i =>
      atWithDefaultM (n+1) α d_at
        (genFixVecChecked (n+1) α (Except.ok d_fix) bodyVec
          (sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue)
          hSound hProductive)
        (subNat n i))
    (fun i => genFixIdx α d_fix body (subNat n i)) 0
    (by
      intro i hi
      change
        atWithDefaultM (n+1) α d_at
          (genFixVecChecked (n+1) α (Except.ok d_fix) bodyVec
            (sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue)
            hSound hProductive)
          (subNat n i) =
        Except.ok (genFixIdx α d_fix body (subNat n i))
      rw [atWithDefaultM_genFixVecChecked_ok_lt_of_ok_lt (n+1) α d_at
        (Except.ok d_fix) d_fix bodyVec
        (sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue)
        body (subNat n i) hSound hProductive rfl
        (by
          intro lookup j hj
          exact sawSelfRefCompBodyM_ok_of_success n α d_at d_pair seed
            inputsM inputs stepTrue lookup j hInputs hj)
        (by
          simp [subNat]; omega)])
    (Nat.succ_pos n)]
  rw [atWithDefaultM_genFixVecChecked_ok_lt_of_ok_lt (n+1) α d_at
    (Except.ok d_fix) d_fix bodyVec
    (sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue)
    body (subNat n 0) hSound hProductive rfl
    (by
      intro lookup j hj
      exact sawSelfRefCompBodyM_ok_of_success n α d_at d_pair seed
        inputsM inputs stepTrue lookup j hInputs hj)
    (by
      simp [subNat])]
  change Except.ok (genFixIdx α d_fix body n) = _
  apply congrArg Except.ok
  exact genFixIdx_eq_recurrence_bounded α d_fix body seed
    (fun i acc => CryptolToLean.SAWCorePreludeExtra.ite α
      (atWithDefault n Bool false inputs i) (stepTrue acc) acc) n
    (by
      unfold body
      simp [ltNat, CryptolToLean.SAWCorePreludeExtra.ite])
    (by
      intro lookup k hk hLookup
      unfold body
      simp [subNat,
        CryptolToLean.SAWCorePreludeExtra.ite, hLookup k (Nat.le_refl k)])

theorem selfRefCompGenFixVecCheckedM_at_zero_eq_natRec_of_bodyAt
    (n : Nat) (α : Type) [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType Bool (PairType α UnitType)))
    (d_fix seed : α)
    (inputsM : Except String (Vec n Bool)) (inputs : Vec n Bool)
    (stepTrue : α → α)
    (bodyVec : (Nat → α) → Except String (Vec (n+1) α))
    (bodyAt : (Nat → α) → Nat → Except String α)
    (hBodyAt :
      bodyAt = sawSelfRefCompBodyM n α d_at d_pair seed inputsM stepTrue)
    (hSound : GenFixVecBodySound (n+1) α bodyVec bodyAt)
    (hProductive : GenFixBodyProductive α bodyAt)
    (hInputs : inputsM = Except.ok inputs) :
    atWithDefaultM (n+1) α d_at
      (genM (n+1) α (fun i =>
        atWithDefaultM (n+1) α d_at
          (genFixVecChecked (n+1) α (Except.ok d_fix) bodyVec bodyAt
            hSound hProductive)
          (subNat n i)))
      0 =
    Except.ok
      (Nat.rec (motive := fun _ => α) seed
        (fun i acc => CryptolToLean.SAWCorePreludeExtra.ite α
          (atWithDefault n Bool false inputs i) (stepTrue acc) acc)
        n) := by
  subst hBodyAt
  exact selfRefCompGenFixVecCheckedM_at_zero_eq_natRec n α d_at d_pair
    d_fix seed inputsM inputs stepTrue bodyVec hSound hProductive hInputs

theorem selfRefCompGenFixVecCheckedSelfFirstM_at_zero_eq_natRec
    (n : Nat) (β α : Type) [Inhabited β] [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType α (PairType β UnitType)))
    (d_fix seed : α)
    (inputsM : Except String (Vec n β)) (inputs : Vec n β)
    (step : α → β → α)
    (bodyVec : (Nat → α) → Except String (Vec (n+1) α))
    (hSound : GenFixVecBodySound (n+1) α bodyVec
      (sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step))
    (hProductive : GenFixBodyProductive α
      (sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step))
    (hInputs : inputsM = Except.ok inputs) :
    atWithDefaultM (n+1) α d_at
      (genM (n+1) α (fun i =>
        atWithDefaultM (n+1) α d_at
          (genFixVecChecked (n+1) α (Except.ok d_fix) bodyVec
            (sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step)
            hSound hProductive)
          (subNat n i)))
      0 =
    Except.ok
      (Nat.rec (motive := fun _ => α) seed
        (fun i acc => step acc (atWithDefault n β default inputs i))
        n) := by
  let body : (Nat → α) → Nat → α := fun lookup i =>
    CryptolToLean.SAWCorePreludeExtra.ite α (ltNat i 1)
      seed
      (step (lookup (subNat i 1))
        (atWithDefault n β default inputs (subNat i 1)))
  rw [atWithDefaultM_genM_ok_lt (n+1) d_at
    (fun i =>
      atWithDefaultM (n+1) α d_at
        (genFixVecChecked (n+1) α (Except.ok d_fix) bodyVec
          (sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step)
          hSound hProductive)
        (subNat n i))
    (fun i => genFixIdx α d_fix body (subNat n i)) 0
    (by
      intro i hi
      change
        atWithDefaultM (n+1) α d_at
          (genFixVecChecked (n+1) α (Except.ok d_fix) bodyVec
            (sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step)
            hSound hProductive)
          (subNat n i) =
        Except.ok (genFixIdx α d_fix body (subNat n i))
      rw [atWithDefaultM_genFixVecChecked_ok_lt_of_ok_lt (n+1) α d_at
        (Except.ok d_fix) d_fix bodyVec
        (sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step)
        body (subNat n i) hSound hProductive rfl
        (by
          intro lookup j hj
          exact sawSelfRefCompBodySelfFirstM_ok_of_success n β α d_at d_pair
            seed inputsM inputs step lookup j hInputs hj)
        (by
          simp [subNat]; omega)])
    (Nat.succ_pos n)]
  rw [atWithDefaultM_genFixVecChecked_ok_lt_of_ok_lt (n+1) α d_at
    (Except.ok d_fix) d_fix bodyVec
    (sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step)
    body (subNat n 0) hSound hProductive rfl
    (by
      intro lookup j hj
      exact sawSelfRefCompBodySelfFirstM_ok_of_success n β α d_at d_pair
        seed inputsM inputs step lookup j hInputs hj)
    (by
      simp [subNat])]
  change Except.ok (genFixIdx α d_fix body n) = _
  apply congrArg Except.ok
  exact genFixIdx_eq_recurrence_bounded α d_fix body seed
    (fun i acc => step acc (atWithDefault n β default inputs i)) n
    (by
      unfold body
      simp [ltNat, CryptolToLean.SAWCorePreludeExtra.ite])
    (by
      intro lookup k hk hLookup
      unfold body
      simp [subNat,
        CryptolToLean.SAWCorePreludeExtra.ite, hLookup k (Nat.le_refl k)])

theorem selfRefCompGenFixVecCheckedSelfFirstM_at_zero_eq_natRec_of_bodyAt
    (n : Nat) (β α : Type) [Inhabited β] [Inhabited α]
    (d_at : Except String α)
    (d_pair : Except String (PairType α (PairType β UnitType)))
    (d_fix seed : α)
    (inputsM : Except String (Vec n β)) (inputs : Vec n β)
    (step : α → β → α)
    (bodyVec : (Nat → α) → Except String (Vec (n+1) α))
    (bodyAt : (Nat → α) → Nat → Except String α)
    (hBodyAt :
      bodyAt = sawSelfRefCompBodySelfFirstM n β α d_at d_pair seed inputsM step)
    (hSound : GenFixVecBodySound (n+1) α bodyVec bodyAt)
    (hProductive : GenFixBodyProductive α bodyAt)
    (hInputs : inputsM = Except.ok inputs) :
    atWithDefaultM (n+1) α d_at
      (genM (n+1) α (fun i =>
        atWithDefaultM (n+1) α d_at
          (genFixVecChecked (n+1) α (Except.ok d_fix) bodyVec bodyAt
            hSound hProductive)
          (subNat n i)))
      0 =
    Except.ok
      (Nat.rec (motive := fun _ => α) seed
        (fun i acc => step acc (atWithDefault n β default inputs i))
        n) := by
  subst hBodyAt
  exact selfRefCompGenFixVecCheckedSelfFirstM_at_zero_eq_natRec n β α
    d_at d_pair d_fix seed inputsM inputs step bodyVec hSound hProductive hInputs

/-! ## Self-referential comprehension shape (the popcount-shape bridge)

The SAW emission for `result = ic ! 0 where ic = [seed] # [step inp prev | inp <- inputs | prev <- ic]`
is a fixed wrapper around `genFix`: outer `atWithDefault (n+1) _ _ (gen (n+1) _ (\i ->
… genFix … (subNat n i))) 0`, and the body uses
`zip Bool α n (n+1) inputs ic` to thread the input bit and previous accumulator.

This shape recurs in:
- popcount (E6 width-4, popcount32 width-32);
- running-sum (Case D);
- ChaCha20 round-folding (n = 10 doublerounds, headline demo);
- any Cryptol comprehension of `[seed] # [body | input <- inputs | prev <- self]`.

The bridge `genFixIdx_eq_recurrence_bounded` covers the inner genFix step. The
remaining work is peeling the OUTER wrapper (atWithDefault on gen at index 0,
giving subNat n 0 = n; atWithDefault on genFix at index n) plus reducing the
body's per-step shape (atWithDefault on zip, Pair_fst/snd projections). At
concrete N=32 the body's nested gen-32 forces `Vector.ofFn` materialization of
1056 cells via whnf, blowing the heartbeat budget. The parametric theorem
below avoids that by doing the reduction once, parametrically in n. -/

/-- `[seed] # [step input prev | input <- inputs | prev <- self] ! 0`
expressed in SAW's emitted shape, equals the n-fold iterate of `step`
over `inputs` starting from `seed`.

The body shape matches what the translator's BoundedVecFold lowering
emits for self-referential single-input comprehensions. The accumulator
type α is fully polymorphic, so popcount (α := Vec 32 Bool, step b acc =
ite α b (bvAdd 32 acc 1) acc) and ChaCha20 round-folding (α := state,
step _ acc = round acc) both instantiate. -/
theorem saw_self_ref_comp_iterate
    (n : Nat) (α : Type) [Inhabited α]
    (d_at d_fix : α) (d_pair : PairType Bool (PairType α UnitType))
    (seed : α) (inputs : Vec n Bool) (step : Bool → α → α) :
    atWithDefault (n+1) α d_at
      (gen (n+1) α (fun i =>
        atWithDefault (n+1) α d_at
          (genFix (n+1) α d_fix (fun lookup_ i_ =>
            atWithDefault (n+1) α d_fix
              (gen (n+1) α (fun i' =>
                CryptolToLean.SAWCorePreludeExtra.ite α (ltNat i' 1)
                  (atWithDefault 1 α d_at #v[seed] i')
                  (atWithDefault n α d_at
                    (gen n α (fun i'' =>
                      step
                        (Pair_fst _ _ (atWithDefault (Nat.min n (n+1))
                          (PairType Bool (PairType α UnitType)) d_pair
                          (zip Bool α n (n+1) inputs (gen (n+1) α lookup_)) i''))
                        (Pair_fst _ _ (Pair_snd _ _ (atWithDefault (Nat.min n (n+1))
                          (PairType Bool (PairType α UnitType)) d_pair
                          (zip Bool α n (n+1) inputs (gen (n+1) α lookup_)) i'')))))
                    (subNat i' 1))))
              i_))
          (subNat n i)))
      0
    = Nat.rec seed (fun i acc => step (atWithDefault n Bool false inputs i) acc) n := by
  -- Step 1: peel outer atWithDefault on gen at index 0.
  rw [atWithDefault_gen_lt (n+1) _ _ 0 (Nat.succ_pos n)]
  -- Step 2: subNat n 0 = n.
  rw [show subNat n 0 = n from rfl]
  -- Step 3: atWithDefault on genFix at index n converts to genFixIdx.
  rw [atWithDefault_genFix_lt (n+1) _ _ _ n (Nat.lt_succ_self n)]
  -- Step 4: apply the bridge `genFixIdx_eq_recurrence_bounded` to convert
  -- genFixIdx body n to Nat.rec seed step n.
  apply genFixIdx_eq_recurrence_bounded α d_fix _ seed
    (fun i acc => step (atWithDefault n Bool false inputs i) acc) n
  -- h_seed: body (fun _ => d) 0 = seed.
  case h_seed =>
    -- Reduce body at i_=0: atWithDefault on gen at 0 picks the i'=0 path,
    -- which is the seed branch.
    rw [atWithDefault_gen_lt (n+1) _ _ 0 (Nat.succ_pos n)]
    -- ite cond is `ltNat 0 1 = true`; ite_True picks the first branch.
    rw [show ltNat 0 1 = true from rfl]
    rw [CryptolToLean.SAWCorePreludeExtra.ite_True]
    -- atWithDefault on the singleton vector at 0 gives seed.
    exact atWithDefault_singleton_zero _ _ _
  -- h_step: ∀ lookup k, k < n → body lookup (k+1) = step inputs[k] (lookup k).
  case h_step =>
    intro lookup k hk h_lk
    -- Reduce body at i_=k+1: atWithDefault on gen at (k+1).
    rw [atWithDefault_gen_lt (n+1) _ _ (k+1) (Nat.succ_lt_succ hk)]
    -- ite cond is `ltNat (k+1) 1 = false`; ite_False picks the second branch.
    rw [ltNat_succ_one_eq_false, CryptolToLean.SAWCorePreludeExtra.ite_False]
    -- subNat (k+1) 1 = k.
    rw [show subNat (k+1) 1 = k from by simp [subNat]]
    -- atWithDefault on inner gen n at index k.
    rw [atWithDefault_gen_lt n _ _ k hk]
    -- Both `Pair_fst _ _ (atWithDefault (Nat.min n (n+1)) _ _ (zip…) k)`
    -- terms collapse via `atWithDefault_zip_lt` directly (statement is at
    -- length `Nat.min n (n+1)`).
    have h_min : k < Nat.min n (n+1) := by
      have : Nat.min n (n+1) = n := Nat.min_eq_left (Nat.le_succ n)
      rw [this]; exact hk
    rw [atWithDefault_zip_lt n (n+1) inputs (gen (n+1) α lookup) d_pair k h_min]
    -- Apply Pair_fst_PairValue / Pair_snd_PairValue.
    simp only [Pair_fst_PairValue, Pair_snd_PairValue]
    -- (gen (n+1) α lookup)[k] = lookup k.
    rw [show (gen (n+1) α lookup)[k]'(Nat.lt_of_lt_of_le h_min (Nat.min_le_right n (n+1)))
            = lookup k from by unfold gen; rw [Vector.getElem_ofFn]]
    -- inputs[k] = atWithDefault n Bool false inputs k.
    rw [show inputs[k]'(Nat.lt_of_lt_of_le h_min (Nat.min_le_left n (n+1)))
            = atWithDefault n Bool false inputs k from
        (atWithDefault_lt _ _ _ _).symm]

/-! ## Fold reduction theorems

Phase 8: `foldr` / `foldl` are now defined via `Vector.foldr` /
`Vector.foldl`, so the empty-vec equations hold by reduction. -/

/-- `foldr` over a 0-vector is the seed. Rocq's `foldr` mirrors
this by definition. -/
theorem foldr_zero
    (α β : Type) (f : α → β → β) (z : β) (v : Vec 0 α) :
    foldr α β 0 f z v = z := by
  unfold foldr
  obtain ⟨arr, harr⟩ := v
  have : arr = #[] := Array.eq_empty_of_size_eq_zero harr
  subst this
  rfl

/-- `foldl` over a 0-vector is the seed. -/
theorem foldl_zero
    (α β : Type) (f : β → α → β) (z : β) (v : Vec 0 α) :
    foldl α β 0 f z v = z := by
  unfold foldl
  obtain ⟨arr, harr⟩ := v
  have : arr = #[] := Array.eq_empty_of_size_eq_zero harr
  subst this
  rfl

/- `foldlM` bridge for pure successful SAW fold bodies.  The Haskell
emitter still produces the literal `Except`-wrapped fold; proofs use
this theorem to move from the monadic emitted shape to the pure
`foldl` recurrence after proving the step succeeds on successful
inputs. -/
theorem foldlM_pure_eq_foldl
    (α β : Type) (n : Nat)
    (fM : Except String β → Except String α → Except String β)
    (f : β → α → β) (z : β) (v : Vec n α)
    (hStep : ∀ acc a, fM (Except.ok acc) (Except.ok a) = Except.ok (f acc a)) :
    foldlM α β n fM (Except.ok z) (Except.ok v) =
      Except.ok (foldl α β n f z v) := by
  unfold foldlM foldl
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  induction n with
  | zero =>
      obtain ⟨arr, harr⟩ := v
      have : arr = #[] := Array.eq_empty_of_size_eq_zero harr
      subst this
      rfl
  | succ k ih =>
      conv =>
        lhs
        rw [show v = v.pop.push v.back from (Vector.push_pop_back v).symm]
      conv =>
        rhs
        rw [show v = v.pop.push v.back from (Vector.push_pop_back v).symm]
      change Vector.foldl (fun acc a => fM acc (Except.ok a)) (Except.ok z)
          (Vector.push v.pop v.back) =
        Except.ok (Vector.foldl f z (Vector.push v.pop v.back))
      rw [Vector.foldl_push, Vector.foldl_push]
      have hpop :
          Vector.foldl (fun acc a => fM acc (Except.ok a)) (Except.ok z) v.pop =
            Except.ok (Vector.foldl f z v.pop) := by
        simpa [Nat.succ_sub_one] using ih v.pop
      conv =>
        lhs
        arg 1
        rw [hpop]
      exact hStep (Vector.foldl f z v.pop) v.back

/-! ## Stream / genFix equivalence

`mkStreamFix` (used by Phase 5 Slice A — Cryptol `iterate f x` lowering)
and `genFix` (used by Phase 5 Slice B — bounded comprehension lowering)
share their `getD`-of-prefix-build implementation. The prefix builders
are syntactically identical defs (`mkStreamFixPrefix` vs
`genFixListBuild`); the index getters differ only in name.

These equivalences let `saw_self_ref_comp_iterate` (stated for `genFix`)
discharge ChaCha20-style `iterate cdround x @ n` goals, where the
emission has `mkStreamFixIdx` instead of `genFixIdx`. -/

theorem mkStreamFixPrefix_eq_genFixListBuild
    (α : Type) (d : α) (body : (Nat → α) → Nat → α) (k : Nat) :
    mkStreamFixPrefix α d body k = genFixListBuild α d body k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show mkStreamFixPrefix α d body k ++ _ = genFixListBuild α d body k ++ _
    rw [ih]

theorem mkStreamFixIdx_eq_genFixIdx
    (α : Type) (d : α) (body : (Nat → α) → Nat → α) (n : Nat) :
    mkStreamFixIdx α d body n = genFixIdx α d body n := by
  unfold mkStreamFixIdx genFixIdx
  rw [mkStreamFixPrefix_eq_genFixListBuild]

/-- Iterate-shape bridge: `iterate f x @ n` (Cryptol's
`iterate : (a → a) → a → [inf]a` indexed at finite n) equals
`Nat.rec x f n`. The SAW translator (Phase 5 Slice A) lowers
`iterate f x` to `mkStreamFix _ _ body` with body shape:
  `body lookup_ i_ = ite α (ltNat i_ 1) (#v[x] @ i_) (f (lookup_ (i_-1)))`

This is the headline bridge for ChaCha20 round-folding (n = 10
doublerounds, f = cdround, x = initial state). The proof reuses
`mkStreamFixIdx_eq_genFixIdx` to fall back to the genFix machinery
and then `genFixIdx_eq_recurrence_bounded` for the recurrence. -/
theorem mkStreamFixIdx_iterate_eq_natRec
    (α : Type) (d : α) (f : α → α) (seed : α) (n : Nat) :
    mkStreamFixIdx α d
      (fun lookup_ i_ =>
        CryptolToLean.SAWCorePreludeExtra.ite α (ltNat i_ 1)
          (atWithDefault 1 α d #v[seed] i_)
          (f (lookup_ (subNat i_ 1))))
      n
    = Nat.rec (motive := fun _ => α) seed (fun _ acc => f acc) n := by
  rw [mkStreamFixIdx_eq_genFixIdx]
  apply genFixIdx_eq_recurrence_bounded α d _ seed (fun _ acc => f acc) n
  case h_seed =>
    -- body (fun _ => d) 0 = seed.
    rw [show ltNat 0 1 = true from rfl]
    rw [CryptolToLean.SAWCorePreludeExtra.ite_True]
    exact atWithDefault_singleton_zero _ _ _
  case h_step =>
    intro lookup k _ _
    -- body lookup (k+1) = f (lookup k).
    rw [ltNat_succ_one_eq_false, CryptolToLean.SAWCorePreludeExtra.ite_False]
    rw [show subNat (k+1) 1 = k from by simp [subNat]]

/-- Bridge: `foldl` over a `Vec n α` equals `Nat.rec` iterated `n` times,
where each step indexes into the vector via `atWithDefault`. The default
value `d` is unused since iteration only touches in-bounds indices.

Together with `saw_self_ref_comp_iterate`, this lets us close popcount/
ChaCha20-style equivalences by bridging both the SAW emission's foldl
form (LHS) and the SAW emission's self-referential comprehension form
(RHS) to the same `Nat.rec` shape — at which point `bv_decide` can
discharge concrete-width instances. -/
theorem foldl_eq_natRec_atWithDefault
    (α β : Type) (n : Nat) (f : β → α → β) (z : β) (v : Vec n α) (d : α) :
    foldl α β n f z v
      = Nat.rec (motive := fun _ => β) z
          (fun i acc => f acc (atWithDefault n α d v i)) n := by
  induction n with
  | zero =>
    rw [foldl_zero]
    rfl
  | succ k ih =>
    -- Decompose v as v.pop.push v.back; foldl_push handles the inductive
    -- step; ih bridges the k-prefix.
    conv =>
      lhs
      rw [show v = v.pop.push v.back from (Vector.push_pop_back v).symm]
    show Vector.foldl f z (v.pop.push v.back) = _
    rw [Vector.foldl_push]
    show f (foldl α β k f z v.pop) v.back = _
    rw [ih v.pop]
    -- Goal: f (Nat.rec z step_k k) v.back = Nat.rec z step_{k+1} (k+1)
    -- where step_k uses atWithDefault k α d v.pop, and
    -- step_{k+1} uses atWithDefault (k+1) α d v.
    -- Nat.rec at (k+1) unfolds: step (Nat.rec z step k) at i=k.
    show _ = (fun i acc => f acc (atWithDefault (k+1) α d v i)) k _
    -- The two Nat.rec applications must be shown equal; their step funcs
    -- agree on i < k via `pop[i] = v[i]`. The outer `f _ v.back` matches
    -- `f _ (atWithDefault (k+1) α d v k)` since `v.back = v[k]`.
    have h_step_eq : ∀ j, j ≤ k →
        Nat.rec (motive := fun _ => β) z
          (fun i acc => f acc (atWithDefault k α d v.pop i)) j
        = Nat.rec (motive := fun _ => β) z
          (fun i acc => f acc (atWithDefault (k+1) α d v i)) j := by
      intro j hj
      induction j with
      | zero => rfl
      | succ m ihm =>
        show f (Nat.rec _ _ m) (atWithDefault k α d v.pop m)
           = f (Nat.rec _ _ m) (atWithDefault (k+1) α d v m)
        rw [ihm (by omega : m ≤ k)]
        congr 1
        -- Need: atWithDefault k α d v.pop m = atWithDefault (k+1) α d v m for m < k.
        have hm : m < k := by omega
        rw [atWithDefault_lt _ _ _ hm]
        rw [atWithDefault_lt _ _ _ (by omega : m < k+1)]
        -- v.pop[m] = v[m]'(by omega : m < k+1)
        simp
    rw [h_step_eq k (Nat.le_refl k)]
    -- Now: f (Nat.rec ... k) v.back = f (Nat.rec ... k) (atWithDefault (k+1) α d v k)
    -- Need: v.back = atWithDefault (k+1) α d v k
    congr 1
    rw [atWithDefault_lt _ _ _ (Nat.lt_succ_self k)]
    haveI : NeZero (k+1) := ⟨Nat.succ_ne_zero k⟩
    show v.back = v[k]
    rw [Vector.back_eq_getElem (xs := v)]
    congr 1

/-- `foldr` over a `gen`-built `Bool`-vec with `(∧, true)` reduces to
the conjunction of the generator's outputs over `[0, n)`. SAW emits
this shape for `llvm_points_to`-style state-equality goals: each
position contributes a `bvEq` and the points-to assertion is the
foldr-of-AND.

This bridge lets the user discharge such goals by case-splitting on
the index, with `bv_decide` closing each per-position bvEq. The
parametric statement avoids the Vector.foldr / Vector.ofFn
materialization cost at concrete `n`.

Direction: `(∀ i < n, f i = true) → foldr ∧ true (gen n f) = true`.
The reverse direction would also hold but isn't needed for discharge. -/
theorem foldr_and_gen_eq_true_of_all
    (n : Nat) (f : Nat → Bool)
    (h : ∀ i, i < n → f i = true) :
    foldr Bool Bool n
      (fun b1 b2 => CryptolToLean.SAWCorePreludeExtra.ite Bool b1 b2 false)
      Bool.true (gen n Bool f) = Bool.true := by
  induction n with
  | zero =>
    rw [foldr_zero]
  | succ k ih =>
    -- foldr over (gen (k+1)) = ite_∧ (gen[0]) (foldr over (gen-shifted k))
    -- Use foldr's structural decomposition; reduce the outer step.
    -- Strategy: gen (k+1) f = (gen k (f ∘ id)).push (f k); then foldr_push.
    -- Equivalent: peel foldr's first step as f 0 ∧ (foldr over k-tail).
    -- Cleanest: use Vector.foldr's relation to Array.foldr and List.foldr.
    -- We unfold to Vector.foldr; the Vec is `Vector.ofFn (fun i : Fin (k+1) => f i.val)`
    -- which equals `(Vector.ofFn (fun i : Fin k => f i.val)).push (f k)` by
    -- Vector.ofFn_succ. But that's not a stdlib lemma name we can rely on.
    -- Use the Vector.foldr_push / push_pop_back symmetry as in foldl.
    show Vector.foldr _ true (gen (k+1) Bool f) = true
    -- gen (k+1) f = Vector.ofFn (fun i : Fin (k+1) => f i.val)
    --             = (Vector.ofFn (fun i : Fin k => f i.val)).push (f k)   -- via ofFn-push
    -- via the analog of push_pop_back.
    have h_split : (gen (k+1) Bool f) = (gen k Bool f).push (f k) := by
      apply Vector.ext
      intro i hi
      unfold gen
      simp only [Vector.getElem_ofFn]
      by_cases hk : i < k
      · simp [Vector.getElem_push_lt hk]
      · have : i = k := by omega
        subst this
        simp
    rw [h_split]
    rw [Vector.foldr_push]
    -- Goal: (fun b1 b2 => ite Bool b1 b2 false) (f k) (Vector.foldr _ true (gen k Bool f)) = true
    -- = ite Bool (f k) (foldr ... gen k) false
    -- f k = true (by h applied at k); foldr-rec for k = true (by ih)
    have hk : f k = true := h k (Nat.lt_succ_self k)
    rw [hk]
    show CryptolToLean.SAWCorePreludeExtra.ite Bool true (Vector.foldr _ true (gen k Bool f)) false = true
    rw [CryptolToLean.SAWCorePreludeExtra.ite_True]
    -- Goal: Vector.foldr ... = true. This is foldr ... = true at length k.
    show foldr Bool Bool k _ Bool.true (gen k Bool f) = true
    exact ih (fun i hi => h i (Nat.lt_succ_of_lt hi))

end CryptolToLean.SAWCorePreludeProofs
