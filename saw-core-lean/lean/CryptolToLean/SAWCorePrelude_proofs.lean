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
`zip_getElem_lt`) downstream. -/
theorem atWithDefault_lt {α : Type} {n : Nat}
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

end CryptolToLean.SAWCorePreludeProofs
