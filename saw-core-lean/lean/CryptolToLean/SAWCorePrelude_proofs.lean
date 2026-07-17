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
:= Nat.add`, so the equation is `rfl`). The rest are proven
theorems; this file contains ZERO axiom declarations (audit
2026-07-14 — the former "axiomatic transpositions of Rocq
theorems" have all been proved). Rocq-counterpart citations on
individual lemmas remain as audit trail.
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

/-- SAW `subNat` is Lean `Nat.sub` (saturating). Both saturate
at zero on under-flow. -/
@[simp] theorem subNat_eq_natSub (m n : Nat) : subNat m n = m - n := rfl

/-- SAW `ltNat` matches Lean's strict less-than. -/
@[simp] theorem ltNat_eq_decide_lt (m n : Nat) :
    ltNat m n = decide (m < n) := rfl

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

/-- If every element of a wrapped vector is successful, eager vector
sequencing succeeds with the corresponding pure vector.

This is the all-width form behind literal-vector simplifications such as
`vecSequenceM_singleton_ok`. It keeps the proof obligation explicit:
`vecSequenceM` is eager, so callers must prove every element succeeds, not only
the element they later index. -/
theorem vecSequenceM_ok_of_get {α : Type} {n : Nat}
    (vM : Vec n (Except String α)) (v : Vec n α)
    (h : ∀ i : Fin n, vM[i] = Except.ok v[i]) :
    vecSequenceM n α vM = Except.ok v := by
  unfold vecSequenceM
  have hv :
      (fun i : Fin n => vM[i]) =
        (fun i : Fin n => Except.ok v[i]) := by
    funext i
    exact h i
  rw [hv]
  rw [show
    Vector.ofFnM (m := Except String) (fun i : Fin n => Except.ok v[i]) =
      Except.ok (Vector.ofFn (fun i : Fin n => v[i])) from by
    change Vector.ofFnM (m := Except String) (fun i : Fin n => pure v[i]) =
      pure (Vector.ofFn (fun i : Fin n => v[i]))
    exact Vector.ofFnM_pure (m := Except String) (f := fun i : Fin n => v[i])]
  congr 1
  apply Vector.ext
  intro i
  simp

@[simp] theorem vecSequenceM_singleton_ok {α : Type} (x : α) :
    vecSequenceM 1 α #v[Except.ok x] = Except.ok #v[x] := by
  apply vecSequenceM_ok_of_get
  intro i
  cases i with
  | mk val isLt =>
      cases val with
      | zero => rfl
      | succ _ => omega

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

/-- In-bounds indexing through an eagerly sequenced vector.

The premise deliberately states success for every element of `vM`: sequencing
is eager, so this is the safe all-width form of the common generated pattern
`atWithDefaultM ... (vecSequenceM ... #v[...]) i`. -/
theorem atWithDefaultM_vecSequenceM_ok_lt {α : Type} {n : Nat}
    (d : Except String α) (vM : Vec n (Except String α)) (v : Vec n α)
    (i : Nat) (hOk : ∀ j : Fin n, vM[j] = Except.ok v[j]) (hLt : i < n) :
    atWithDefaultM n α d (vecSequenceM n α vM) i =
      Except.ok (v[i]'hLt) := by
  rw [vecSequenceM_ok_of_get vM v hOk]
  exact atWithDefaultM_ok_lt n d (Except.ok v) v i rfl hLt

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

/-! ### Outer-wrapper peeling lemmas

`atWithDefault N α d (gen N α f) k = f k` reduces SAW emission's
outer wrapper one `Vector.ofFn` layer at a time without forcing whnf
on the body. Critical for proofs over deeply-nested `gen` shapes where
the body contains another `gen` — `Vector.ofFn` materializes strictly,
so naive `show`/`rfl` can trigger cartesian-product whnf cost. -/

/-- Generic `atWithDefault` peel: when the index is in bounds, the
default is unused and the result is the underlying vector indexing.
Used to bridge SAW's `atWithDefault N _ d v k` to Lean's `v[k]`
without committing to `v`'s specific shape (gen / zip / arbitrary).
Compose with shape-specific reductions (e.g. `zip_getElem_lt`)
downstream.

`@[simp]` so it fires on every emission where `k < n` is in
context — the dominant `atWithDefault` use pattern. Side condition
`h : k < n` is consumed via simp's standard hypothesis-discharge. -/
@[simp] theorem atWithDefault_lt {α : Type} {n : Nat}
    (d : α) (v : Vec n α) (k : Nat) (h : k < n) :
    atWithDefault n α d v k = v[k]'h := by
  unfold atWithDefault; simp [h]

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

/-! ### §4.4 SAW-emission peelers

The translator emits a small alphabet of SAW Prelude primitives
whose reduction in symbolic contexts requires explicit peelers —
Lean's reducer alone cannot unfold `gen` / `atWithDefault` /
`Pair_fst`/`Pair_snd` / `zip` past metavariables or in-bound
checks. These peelers reduce a goal in SAW emission shape down to
underlying primitives that checked Lean-side proof scripts can close.

These peelers are intentionally local facts about ordinary emitted
SAW Prelude syntax. Larger recurrence/fix reasoning should be expressed
as separate Lean proof obligations rather than hidden in Haskell-side
shape rewrites.

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

/- `foldrM` bridge for pure successful SAW fold bodies.  This is the
right-fold counterpart of `foldlM_pure_eq_foldl`: it preserves the eager
`Except` semantics and rewrites to the pure fold only after Lean has checked
that every successful step maps to a successful pure step. -/
theorem foldrM_pure_eq_foldr
    (α β : Type) (n : Nat)
    (fM : Except String α → Except String β → Except String β)
    (f : α → β → β) (z : β) (v : Vec n α)
    (hStep : ∀ a acc, fM (Except.ok a) (Except.ok acc) =
      Except.ok (f a acc)) :
    foldrM α β n fM (Except.ok z) (Except.ok v) =
      Except.ok (foldr α β n f z v) := by
  unfold foldrM foldr
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  induction n generalizing z with
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
      change Vector.foldr (fun a acc => fM (Except.ok a) acc) (Except.ok z)
          (Vector.push v.pop v.back) =
        Except.ok (Vector.foldr f z (Vector.push v.pop v.back))
      rw [Vector.foldr_push, Vector.foldr_push]
      rw [hStep v.back z]
      exact ih (f v.back z) v.pop

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

/-- Bridge: `foldl` over a `Vec n α` equals `Nat.rec` iterated `n` times,
where each step indexes into the vector via `atWithDefault`. The default
value `d` is unused since iteration only touches in-bounds indices.

Together with a recurrence-side bridge in the
`saw_self_ref_comp_iterate` style (the retired May parametric-bridge
family — a design-doc name, not a current library def; the OP-3
successor design decides its revival), this lets us close popcount/
ChaCha20-style equivalences by bridging both the SAW emission's foldl
form (LHS) and the SAW emission's self-referential comprehension form
(RHS) to the same `Nat.rec` shape. Concrete-width bitvector work still
requires checked lemmas or manual proof scripts under the current trust
policy. -/
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
the index, then using checked bitvector lemmas for each per-position
bvEq. The parametric statement avoids the Vector.foldr / Vector.ofFn
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

/-- Seed-generalized foldr-AND characterization. `Vector.foldr_push` in
this toolchain folds the pushed element into the ACCUMULATOR (not the
head), so the induction must generalize the seed: the fold is `true` iff
the seed is `true` AND every generated bit is `true`. -/
theorem foldr_and_gen_seed
    (n : Nat) (f : Nat → Bool) (s : Bool) :
    foldr Bool Bool n
      (fun b1 b2 => CryptolToLean.SAWCorePreludeExtra.ite Bool b1 b2 false)
      s (gen n Bool f) = true
      ↔ (s = true ∧ ∀ i, i < n → f i = true) := by
  induction n generalizing s with
  | zero =>
    rw [foldr_zero]
    constructor
    · intro h; exact ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · intro ⟨h, _⟩; exact h
  | succ k ih =>
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
    show Vector.foldr
        (fun b1 b2 => CryptolToLean.SAWCorePreludeExtra.ite Bool b1 b2 false)
        s (Vector.push (gen k Bool f) (f k)) = true ↔ _
    rw [Vector.foldr_push]
    show foldr Bool Bool k
        (fun b1 b2 => CryptolToLean.SAWCorePreludeExtra.ite Bool b1 b2 false)
        (CryptolToLean.SAWCorePreludeExtra.ite Bool (f k) s false)
        (gen k Bool f) = true ↔ _
    rw [ih]
    constructor
    · intro ⟨hite, hlt⟩
      have hfk : f k = true := by
        cases hh : f k with
        | false =>
          rw [hh, CryptolToLean.SAWCorePreludeExtra.ite_False] at hite
          exact absurd hite (by simp)
        | true => rfl
      rw [hfk, CryptolToLean.SAWCorePreludeExtra.ite_True] at hite
      refine ⟨hite, ?_⟩
      intro i hi
      by_cases hik : i < k
      · exact hlt i hik
      · have : i = k := by omega
        subst this; exact hfk
    · intro ⟨hs, hall⟩
      have hfk : f k = true := hall k (Nat.lt_succ_self k)
      refine ⟨?_, fun i hi => hall i (Nat.lt_succ_of_lt hi)⟩
      rw [hfk, CryptolToLean.SAWCorePreludeExtra.ite_True]; exact hs

/-- Bidirectional form of `foldr_and_gen_eq_true_of_all`: the foldr-AND
over a `gen`-built Bool vector is `true` IFF every generated bit is
`true`. The REVERSE direction (true → all) is what the byte-decomposition
crux (`bvEq128_eq_foldr_byteEq`) needs: a successful 16-byte equality
fold forces every per-byte equality, so a differing byte would falsify
the fold. Special case of `foldr_and_gen_seed` at seed `true`. -/
theorem foldr_and_gen_eq_true_iff
    (n : Nat) (f : Nat → Bool) :
    foldr Bool Bool n
      (fun b1 b2 => CryptolToLean.SAWCorePreludeExtra.ite Bool b1 b2 false)
      Bool.true (gen n Bool f) = Bool.true
      ↔ ∀ i, i < n → f i = true := by
  rw [foldr_and_gen_seed]
  simp

/-! ## `saw_fix_bounded` faithfulness core (OP-3 successor, Slice R1)

The three L-lemmas of doc/2026-07-15_op3-successor-design.md Part 2,
plus the purity and seed-irrelevance corollaries. Everything is
conditional on the PER-INSTANCE obligation
`saw_fix_bounded_productive` (H_prod) — these lemmas are proved once,
H_prod is proved per concrete body at Slice R2 emission sites. -/

/-- `genWithBoundsM` with elementwise-pure elements is pure — the
bounds-carrying analog of `genM_eq_ok_gen`. This is the workhorse of
per-instance H_prod discharges (Slice R2): it turns one application
of a translated Class-F body on a pure input into a pure `ofFn`
vector. -/
theorem genWithBoundsM_eq_ok {α : Type} {n : Nat}
    (f : (i : Nat) → i < n → Except String α)
    (g : (i : Nat) → i < n → α)
    (h : ∀ (i : Nat) (hi : i < n), f i hi = Except.ok (g i hi)) :
    genWithBoundsM n α f =
      Except.ok (Vector.ofFn (fun i : Fin n => g i.val i.isLt)) := by
  unfold genWithBoundsM
  have hf : (fun i : Fin n => f i.val i.isLt) =
      (fun i : Fin n => Except.ok (g i.val i.isLt)) := by
    funext i
    exact h i.val i.isLt
  rw [hf]
  exact Vector.ofFnM_pure (m := Except String)
    (f := fun i : Fin n => g i.val i.isLt)

/-- Proof-carrying selection through an elementwise-pure
bounds-carrying gen (composition form). -/
theorem atWithProof_gen_ok {α : Type} {n : Nat}
    (f : (i : Nat) → i < n → Except String α)
    (g : (i : Nat) → i < n → α)
    (i : Nat) (hsel : i < n)
    (helem : ∀ (j : Nat) (hj : j < n), f j hj = Except.ok (g j hj)) :
    atWithProof_checkedM n α (genWithBoundsM n α f) i hsel =
      Except.ok (g i hsel) := by
  rw [genWithBoundsM_eq_ok f g helem]
  simp [atWithProof_checkedM, Pure.pure, Bind.bind, Except.bind,
        Except.pure]

/-- In-bounds runtime-checked indexing through an already-successful
vector is the plain element read. The OP-2 accessor
`atRuntimeCheckedM` guards the read with a RUNTIME bound test (the
bound was not derivable at the emission site); once the index is
proven in bounds on the proof side, the throw branch is dead and the
read is pure. W2 seed (byte_add): emission's zero-pad branches
(`atRuntimeCheckedM _ (pure (bvNat n 0)) i`) and fused-reassembly
reads reduce through this. -/
theorem atRuntimeCheckedM_ok_lt {α : Type} (n : Nat)
    (v : Vec n α) (i : Nat) (h : i < n) :
    atRuntimeCheckedM n α (Except.ok v) i = Except.ok (v[i]'h) := by
  unfold atRuntimeCheckedM
  simp [h, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- `iteM` on an already-pure `true` condition selects the then
branch. -/
theorem iteM_pure_true {α : Type} (T E : Except String α) :
    CryptolToLean.SAWCorePreludeExtra.iteM α (Pure.pure true) T E = T :=
  rfl

/-- `iteM` on an already-pure `false` condition selects the else
branch. -/
theorem iteM_pure_false {α : Type} (T E : Except String α) :
    CryptolToLean.SAWCorePreludeExtra.iteM α (Pure.pure false) T E = E :=
  rfl

/-- `iteM` on a pure but SYMBOLIC Boolean condition with pure branches
is the pure `cond`. The popcount-family Class-F bodies (Slice R2)
branch on a VALUE-LEVEL bit (`iteM` applied to `bits[i-1]`, not to a
decidable `ltNat` test), so neither `iteM_pure_true` nor
`iteM_pure_false` applies; this is the elementwise characterization
those discharges rewrite with once both branches have been reduced to
`Except.ok` values. -/
theorem iteM_ok_ok {α : Type} (b : Bool) (t e : α) :
    CryptolToLean.SAWCorePreludeExtra.iteM α (Except.ok b)
      (Except.ok t) (Except.ok e) = Except.ok (bif b then t else e) := by
  cases b <;> rfl

/-- Every iterate from a pure seed is pure (given `H.total`). -/
theorem saw_fix_bounded_iter_from_pure
    (n : Nat) (α : Type) (s : Vec n α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    ∀ k : Nat, ∃ v : Vec n α,
      saw_fix_bounded_iter_from n α s body k = Pure.pure v := by
  intro k
  induction k with
  | zero => exact ⟨s, rfl⟩
  | succ m ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨w, hw⟩ := H.total u
    refine ⟨w, ?_⟩
    show body (saw_fix_bounded_iter_from n α s body m) = Pure.pure w
    rw [hu]
    exact hw

/-- Replicated-placeholder specialization of
`saw_fix_bounded_iter_from_pure`. -/
theorem saw_fix_bounded_iter_pure
    (n : Nat) (α : Type) (d : α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    ∀ k : Nat, ∃ v : Vec n α,
      saw_fix_bounded_iter n α d body k = Pure.pure v :=
  saw_fix_bounded_iter_from_pure n α (Vector.replicate n d) body H

/-- L1, master form (stabilization): element `i` of ANY iterate past
`i` agrees with element `i` of any other iterate past `i`, even from
a different seed. Strong induction on `i`: iterate `k+1`'s element
`i` is determined (via `H.lookback`) by the prefix `< i` of iterate
`k`, and that prefix is already stable by the induction hypothesis. -/
theorem saw_fix_bounded_iter_from_stable
    (n : Nat) (α : Type)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    ∀ (i : Nat) (hi : i < n) (s₁ s₂ : Vec n α) (k₁ k₂ : Nat),
      i < k₁ → i < k₂ →
      ∀ (v₁ v₂ : Vec n α),
        saw_fix_bounded_iter_from n α s₁ body k₁ = Pure.pure v₁ →
        saw_fix_bounded_iter_from n α s₂ body k₂ = Pure.pure v₂ →
        v₁[i] = v₂[i] := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i IH =>
    intro hi s₁ s₂ k₁ k₂ hk₁ hk₂ v₁ v₂ h₁ h₂
    obtain ⟨m₁, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by omega⟩
    obtain ⟨m₂, rfl⟩ : ∃ m, k₂ = m + 1 := ⟨k₂ - 1, by omega⟩
    obtain ⟨u₁, hu₁⟩ := saw_fix_bounded_iter_from_pure n α s₁ body H m₁
    obtain ⟨u₂, hu₂⟩ := saw_fix_bounded_iter_from_pure n α s₂ body H m₂
    have hb₁ : body (Pure.pure u₁) = Pure.pure v₁ := by
      rw [← hu₁]; exact h₁
    have hb₂ : body (Pure.pure u₂) = Pure.pure v₂ := by
      rw [← hu₂]; exact h₂
    refine H.lookback u₁ u₂ v₁ v₂ hb₁ hb₂ i hi ?_
    intro j hj hji
    exact IH j hji (by omega) s₁ s₂ m₁ m₂ (by omega) (by omega)
      u₁ u₂ hu₁ hu₂

/-- Replicated-placeholder specialization (the R1 statement). -/
theorem saw_fix_bounded_iter_stable
    (n : Nat) (α : Type)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body)
    (i : Nat) (hi : i < n) (d₁ d₂ : α) (k₁ k₂ : Nat)
    (hk₁ : i < k₁) (hk₂ : i < k₂)
    (v₁ v₂ : Vec n α)
    (h₁ : saw_fix_bounded_iter n α d₁ body k₁ = Pure.pure v₁)
    (h₂ : saw_fix_bounded_iter n α d₂ body k₂ = Pure.pure v₂) :
    v₁[i] = v₂[i] :=
  saw_fix_bounded_iter_from_stable n α body H i hi
    (Vector.replicate n d₁) (Vector.replicate n d₂) k₁ k₂ hk₁ hk₂
    v₁ v₂ h₁ h₂

/-- L2 (pure survival), general-seed form: the realization succeeds —
no error is manufactured from a pure seed. (That errors are also
never DROPPED is `H.total`'s per-instance content: a body whose
element computation errors on pure input has no `total` proof.) -/
theorem saw_fix_bounded_pure
    (n : Nat) (α : Type) (d : α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    ∃ v : Vec n α, saw_fix_bounded n α d body = Pure.pure v :=
  saw_fix_bounded_iter_pure n α d body H n

/-- Condition-4 witness, strongest form: iteration to `n` from ANY
two seed vectors gives the same result. -/
theorem saw_fix_bounded_iter_from_seed_irrelevant
    (n : Nat) (α : Type) (s₁ s₂ : Vec n α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    saw_fix_bounded_iter_from n α s₁ body n =
      saw_fix_bounded_iter_from n α s₂ body n := by
  obtain ⟨v₁, h₁⟩ := saw_fix_bounded_iter_from_pure n α s₁ body H n
  obtain ⟨v₂, h₂⟩ := saw_fix_bounded_iter_from_pure n α s₂ body H n
  rw [h₁, h₂]
  have : v₁ = v₂ := by
    apply Vector.ext
    intro i hi
    exact saw_fix_bounded_iter_from_stable n α body H i hi s₁ s₂ n n
      hi hi v₁ v₂ h₁ h₂
  rw [this]

/-- Condition-4 witness at replicated placeholders. -/
theorem saw_fix_bounded_seed_irrelevant
    (n : Nat) (α : Type) (d₁ d₂ : α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    saw_fix_bounded n α d₁ body = saw_fix_bounded n α d₂ body :=
  saw_fix_bounded_iter_from_seed_irrelevant n α
    (Vector.replicate n d₁) (Vector.replicate n d₂) body H

/-- The emitted chooser computes: it equals the computable
`saw_fix_bounded` at ANY placeholder element. This is the lemma a
discharge uses to replace the emitted `saw_fix_bounded_choose … h`
with a concrete evaluable iteration. -/
theorem saw_fix_bounded_choose_eq_bounded
    (n : Nat) (α : Type) (d : α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    saw_fix_bounded_choose n α body H = saw_fix_bounded n α d body :=
  saw_fix_bounded_iter_from_seed_irrelevant n α
    (Classical.choice H.seed) (Vector.replicate n d) body H

/-- L3 (unfolding agreement — the SAW link), general-seed form: `n`
iterates from any pure seed reach a fixed point of the body. SAW's
only spec for `fix` is `fix_unfold` (SAW's value is a fixed point);
L1 pins every element of a bounded-lookback fixed point uniquely, so
the SAW value and this realization coincide elementwise. -/
theorem saw_fix_bounded_iter_from_fixed_point
    (n : Nat) (α : Type) (s : Vec n α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    body (saw_fix_bounded_iter_from n α s body n) =
      saw_fix_bounded_iter_from n α s body n := by
  obtain ⟨v, hv⟩ := saw_fix_bounded_iter_from_pure n α s body H n
  obtain ⟨w, hw⟩ := saw_fix_bounded_iter_from_pure n α s body H (n + 1)
  have hstep :
      body (saw_fix_bounded_iter_from n α s body n) =
        saw_fix_bounded_iter_from n α s body (n + 1) := rfl
  rw [hstep, hv, hw]
  have : w = v := by
    apply Vector.ext
    intro i hi
    exact saw_fix_bounded_iter_from_stable n α body H i hi s s
      (n + 1) n (by omega) hi w v hw hv
  rw [this]

/-- L3 at replicated placeholders. -/
theorem saw_fix_bounded_fixed_point
    (n : Nat) (α : Type) (d : α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    body (saw_fix_bounded n α d body) = saw_fix_bounded n α d body :=
  saw_fix_bounded_iter_from_fixed_point n α (Vector.replicate n d)
    body H

/-- L3 for the emitted chooser. -/
theorem saw_fix_bounded_choose_fixed_point
    (n : Nat) (α : Type)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body) :
    body (saw_fix_bounded_choose n α body H) =
      saw_fix_bounded_choose n α body H :=
  saw_fix_bounded_iter_from_fixed_point n α
    (Classical.choice H.seed) body H

/-- Uniqueness among PURE fixed points (the honest strengthening the
retired `saw_fix_unique_exists` contract could not have: uniqueness
here follows from bounded lookback, it is not an assumed side
condition — and divergent bodies simply have no H_prod proof). Any
pure fixed point of a productive body equals the `n`-th iterate from
any pure seed. -/
theorem saw_fix_bounded_iter_from_unique_pure_fixed_point
    (n : Nat) (α : Type) (s : Vec n α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body)
    (x : Vec n α) (hx : body (Pure.pure x) = Pure.pure x) :
    Pure.pure x = saw_fix_bounded_iter_from n α s body n := by
  obtain ⟨v, hv⟩ := saw_fix_bounded_iter_from_pure n α s body H n
  rw [hv]
  -- `pure x` is its own iterate chain: compare elementwise against
  -- the stabilized tower by strong induction on the element index.
  have hx_elem : ∀ (i : Nat) (hi : i < n), x[i] = v[i] := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i IH =>
      intro hi
      -- v = iterate n; x = body's own output at every index. Compare
      -- via lookback: both are body-outputs of inputs agreeing < i.
      obtain ⟨u, hu⟩ := saw_fix_bounded_iter_from_pure n α s body H
        (n - 1)
      have hv' : body (Pure.pure u) = Pure.pure v := by
        have hiter : saw_fix_bounded_iter_from n α s body ((n - 1) + 1) =
            Pure.pure v := by
          have hn : (n - 1) + 1 = n := by omega
          rw [hn]; exact hv
        rw [← hiter, ← hu]
        rfl
      refine H.lookback x u x v hx hv' i hi ?_
      intro j hj hji
      -- x[j] = v[j] by IH; v[j] = u[j] by stabilization (j < n-1+1).
      have hxv : x[j] = v[j] := IH j hji hj
      have hvu : v[j] = u[j] :=
        saw_fix_bounded_iter_from_stable n α body H j hj s s n (n - 1)
          (by omega) (by omega) v u hv hu
      rw [hxv, hvu]
  have : x = v := by
    apply Vector.ext
    intro i hi
    exact hx_elem i hi
  rw [this]

/-- Uniqueness at replicated placeholders (the R1 statement). -/
theorem saw_fix_bounded_unique_pure_fixed_point
    (n : Nat) (α : Type) (d : α)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body)
    (x : Vec n α) (hx : body (Pure.pure x) = Pure.pure x) :
    Pure.pure x = saw_fix_bounded n α d body :=
  saw_fix_bounded_iter_from_unique_pure_fixed_point n α
    (Vector.replicate n d) body H x hx

/-- Uniqueness for the emitted chooser. -/
theorem saw_fix_bounded_choose_unique_pure_fixed_point
    (n : Nat) (α : Type)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (H : saw_fix_bounded_productive n α body)
    (x : Vec n α) (hx : body (Pure.pure x) = Pure.pure x) :
    Pure.pure x = saw_fix_bounded_choose n α body H :=
  saw_fix_bounded_iter_from_unique_pure_fixed_point n α
    (Classical.choice H.seed) body H x hx

/-! ## `saw_stream_unfold` faithfulness core (OP-3 successor, R3b)

The stream analog of the `saw_fix_bounded` lemmas, conditional only
on the per-instance `saw_stream_single_productive` obligation. -/

/-- The realization satisfies the elementwise equation the emitted
element function defines — restated from `H.faithful` for symmetry
with the uniqueness theorem's hypothesis. -/
theorem saw_stream_unfold_faithful
    (α : Type) (x0 : α) (step : α → α)
    (mkfn : Except String (Stream α) → Nat → Except String α)
    (H : saw_stream_single_productive α x0 step mkfn) :
    ∀ i : Nat,
      mkfn (Pure.pure (saw_stream_unfold α x0 step)) i =
        Pure.pure (streamIdx α (saw_stream_unfold α x0 step) i) :=
  H.faithful

/-- Uniqueness among TOTAL streams (fifth-audit amendment 3): any
raw stream whose elements satisfy the emitted element equation is
the realization, elementwise — by strong induction on the index via
`lookback`. SAW's `fix_unfold` says SAW's stream fix satisfies
exactly that equation; this theorem pins its elements to the
realization with no choice principle involved. -/
theorem saw_stream_unfold_unique
    (α : Type) (x0 : α) (step : α → α)
    (mkfn : Except String (Stream α) → Nat → Except String α)
    (H : saw_stream_single_productive α x0 step mkfn)
    (t : Stream α)
    (ht : ∀ i : Nat,
      mkfn (Pure.pure t) i = Pure.pure (streamIdx α t i)) :
    ∀ i : Nat,
      streamIdx α t i = streamIdx α (saw_stream_unfold α x0 step) i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i IH =>
    have hsame :
        mkfn (Pure.pure t) i =
          mkfn (Pure.pure (saw_stream_unfold α x0 step)) i :=
      H.lookback t (saw_stream_unfold α x0 step) i
        (fun j hj => IH j hj)
    have h1 := ht i
    have h2 := H.faithful i
    have :
        Pure.pure (f := Except String) (streamIdx α t i) =
          Pure.pure (streamIdx α (saw_stream_unfold α x0 step) i) := by
      rw [← h1, hsame, h2]
    exact congrArg (fun e => match e with
      | Except.ok v => v
      | Except.error _ => streamIdx α t i) this

/-- Whole-stream form of uniqueness. -/
theorem saw_stream_unfold_unique_stream
    (α : Type) (x0 : α) (step : α → α)
    (mkfn : Except String (Stream α) → Nat → Except String α)
    (H : saw_stream_single_productive α x0 step mkfn)
    (t : Stream α)
    (ht : ∀ i : Nat,
      mkfn (Pure.pure t) i = Pure.pure (streamIdx α t i)) :
    t = saw_stream_unfold α x0 step := by
  cases t with
  | MkStream f =>
    have h := saw_stream_unfold_unique α x0 step mkfn H
      (Stream.MkStream f) ht
    show Stream.MkStream f = saw_stream_unfold α x0 step
    unfold saw_stream_unfold
    have hf : f = fun n => Nat.rec x0 (fun _ prev => step prev) n := by
      funext n
      exact h n
    rw [hf]

end CryptolToLean.SAWCorePreludeProofs
