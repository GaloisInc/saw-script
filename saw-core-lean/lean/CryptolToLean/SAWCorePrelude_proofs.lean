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

/-! ## Small min/max identities for `minNat` (Phase 6 / Rocq parity)

These mirror Rocq's `min_nn`, `min_nSn`, `min_Snn`. Stated about
SAW's `minNat` (the name the translator emits for Cryptol size
arithmetic) rather than Lean's `Nat.min` directly — the proof
reduces by `rfl` since our `minNat` is a reducible alias for
`Nat.min`, but the theorem name matches Rocq's intent and the
lemmas land where users searching for `minNat`-related rewrites
would look. Useful when Cryptol's `tcMin` / `unsafeAssert`-driven
size arithmetic surfaces these shapes. -/

theorem min_nn (n : Nat) : minNat n n = n := Nat.min_self n

theorem min_nSn (n : Nat) : minNat n (n + 1) = n :=
  Nat.min_eq_left (Nat.le_succ n)

theorem min_Snn (n : Nat) : minNat (n + 1) n = n :=
  Nat.min_eq_right (Nat.le_succ n)

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
