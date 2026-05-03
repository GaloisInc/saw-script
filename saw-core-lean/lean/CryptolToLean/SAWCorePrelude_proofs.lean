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

namespace CryptolToLean.SAWCorePreludeProofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

/-! ## Nat arithmetic bridges

These reduce by `rfl` because our Lean side declares `addNat` /
`subNat` / `equalNat` / etc. as `@[reducible] def` aliases for
the Lean stdlib operation. Provided here so user proofs can
appeal to a SAW-named lemma rather than knowing the alias depth. -/

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

/-! ## Vector round-trip theorems

`gen` and `atWithDefault` form an isomorphism: enumerating an
`n`-element vector by index reconstructs the same vector;
indexing into `gen f` returns `f i` for in-bounds `i`.

Phase 8 (2026-05-02 evening): these were axioms before
`gen` / `atWithDefault` became structural defs over Lean's
`Vector`. Now provable from `Vector.getElem_ofFn` and
`Vector.ext`. The previous axiom names are preserved as
theorems for downstream-proof compatibility. -/

/-- The fundamental vector round-trip: indexing every element of
`v` and re-`gen`-ing yields `v` back. Rocq: `gen_sawAt`. -/
theorem gen_atWithDefault
    (n : Nat) (α : Type) (d : α) (v : Vec n α) :
    gen n α (fun i => atWithDefault n α d v i) = v := by
  apply Vector.ext
  intro i hi
  simp [gen, atWithDefault, hi]

/-- Indexing into a freshly `gen`-erated vector returns the
generator's output, for any in-bounds index. -/
theorem atWithDefault_gen
    (n : Nat) (α : Type) (d : α) (f : Nat → α) (i : Nat)
    (h : i < n) :
    atWithDefault n α d (gen n α f) i = f i := by
  simp [atWithDefault, gen, h]

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

/-! ## Bool-Nat decision bridges

These chain Bool-valued SAW predicates with Lean's propositional
equality. Useful when a proof has `equalNat m n = Bool.true` as a
hypothesis and wants `m = n` directly. -/

/-- `equalNat m n = Bool.true` implies propositional equality. -/
theorem equalNat_eq_true_imp_eq (m n : Nat) :
    equalNat m n = Bool.true → m = n := by
  unfold equalNat
  intro h
  exact decide_eq_true_eq.mp h

/-- The converse. -/
theorem eq_imp_equalNat_eq_true (m n : Nat) :
    m = n → equalNat m n = Bool.true := by
  intro h
  unfold equalNat
  exact decide_eq_true_eq.mpr h

end CryptolToLean.SAWCorePreludeProofs
