# LIB-1: scoping the element-wise carrier (option (a))

2026-07-26. Status: SCOPING ONLY — no code written. Produced after
option (b) was measured and rejected and option (c) was prototyped.

## The defect, restated

SAW's vectors are element-lazy: `genOp` builds delayed thunks and
`atWithDefaultOp` forces only the selected one, so an `error` in a
slot that is never read is never observed.

The Lean carrier for a value-position `Vec n α` is
`Except String (Vec n α)`. That type cannot represent "error in one
slot, good values elsewhere", so `genWithBoundsM` sequences and
short-circuits. The adaptation is NON-INJECTIVE: two computations SAW
distinguishes both collapse to the same Lean `Except.error`, and a
SAW-FALSE equation closes by `rfl`.

Witness: SAW gives `7` and `9`; Lean proves them equal with only
`[propext, Quot.sound]`.

This is a CARRIER defect. The emitted statement is well-formed,
genuinely proved, kernel-checked and allowlist-clean — and false in
SAW. No gate reaches it, because nothing is wrong with the proof.

## What options (b) and (c) established

**(b) reject bodies that can throw — REJECTED, measured.** Costs 24
rows: 12 emission rows (including every flagship LLVM workflow) and
12 downstream proofs (including the whole E-series). The check is far
more conservative than the hazard: `atRuntimeCheckedM` inside a `gen`
body means "the translator could not PROVE this index in bounds", not
"this throws". The first body inspected has its throw guarded by an
`iteM` condition in the emitted text itself.

**(c) emit a totality obligation — VIABLE, prototyped.** The
obligation `∀ i (h : i < n), ∃ a, f i h = Except.ok a` discharges on
the real guarded shape in 6 lines with clean axioms, and it genuinely
discriminates (an unguarded body is provably NOT total). Needs 5
support lemmas; `iteM_ok` is load-bearing, because `iteM` discards the
untaken branch.

Its cost is scale. The discharge mirrors term structure, one lemma
application per node:

| row | sites | structural nodes | largest site |
|---|---|---|---|
| `cryptol_module_popcount` | 2 | 41 | 21 |
| `llvm_s20hash_comp` | 112 | 672 | 6 |
| `llvm_byte_add_verify` | 50 | 1672 | 111 |

~2,400 lemma applications across three rows — not hand-writable, so
(c) only exists as an EMITTED discharge tactic. That is an
established pattern here (`h_bounds_obligation_` already works this
way), but it inherits A-10: emitted discharge tactics end in
`all_goals sorry`, the token survives in the source, and the
completed path zero-tolerances it.

## Option (a): move the `Except` inside the element

`Vec n α` at a value position translates to `Vec n (Except String α)`
rather than `Except String (Vec n α)`. Element failure is then local
to the slot, matching SAW.

### Measured surface

| surface | count |
|---|---|
| `Except String (Vec …)` in the support library | 84 (44 in `SAWCorePrimitives`, 16 in `SAWCorePrelude_proofs`) |
| `SpecialTreatment` entries for vector-shaped ops | 47 |
| hand-written proof / support-lemma rows referencing the carrier | 22 |
| emitted goldens referencing it | 101 |

Plus the position/callee calculus core — `shouldWrapBinder`,
`classifyDomain`, `adaptTo` — since the carrier IS the value
convention.

### The blocker

**`Vec n Bool` is the bitvector type**, and it is bridged to Lean's
`BitVec n` through `vecToBitVec` / `bitVecToVec`:

- 46 references in `SAWCorePrimitives.lean`
- **184 references in `SAWCoreBitvectors_proofs.lean`**, which
  currently has ZERO axioms — every one is a machine-checked lemma

`BitVec n` has no per-bit error slot. `Vec n (Except String Bool)`
therefore cannot reach `BitVec n` without sequencing — which is
exactly the collapse being removed. **Option (a) as stated is not
viable**: it would cost the entire bitvector story, including the
`bv_decide` rows and the two-tier trust work.

### The way the blocker points

The reason it blocks is also the constraint that makes a smaller fix
sound: **SAW's bitvector operations are strict in every bit.**
`bvAdd` reads all of them. So for a vector that is fully consumed,
eager sequencing is FAITHFUL — SAW fails too, and there is no
divergence to exploit. LIB-1 needs PARTIAL consumption.

That suggests a type-directed carrier:

- `Vec n Bool` → eager `Except String (Vec n Bool)` (bitvector
  compatible, faithful because bv ops are strict)
- `Vec n α`, α ≠ Bool → lazy `Vec n (Except String α)`

It is decidable, local, and preserves the BitVec bridge untouched.

### The split does NOT hold — SETTLED 2026-07-26, negative

The obvious hope was that partial consumption only happens on
sequences-of-things, so the outer vector would never have element
type `Bool` and the split would be sufficient. **It is not.** Direct
witness, translated end to end:

```
at 2 Bool (gen 2 Bool (\(i : Nat) ->
  ite Bool (equalNat i 0) True (error Bool "boom"))) 0
```

SAW reads slot 0 only and returns `True`. The emitted Lean is

```lean
atWithProof_checkedM 2 Bool
  (genWithBoundsM 2 Bool (fun i h => iteM Bool
     (Pure.pure (equalNat i zero_macro))
     (Pure.pure Bool.true)
     (saw_throw_error Bool (Pure.pure "boom"))))
  zero_macro h_bounds_'
```

`genWithBoundsM` sequences, slot 1 is `Except.error "boom"`, so the
whole vector — and therefore the read — is an error. **The hazard
exists at element type `Bool`, i.e. on a bitvector**, which is exactly
the case a type-directed carrier must leave eager to keep the
`BitVec` bridge.

So the two requirements are in direct conflict:

- keeping `bv_decide`, the two-tier trust work and 184
  machine-checked lemmas requires `Vec n Bool` to reach `BitVec n`,
  which requires eager sequencing;
- closing LIB-1 at element type `Bool` requires the lazy carrier,
  which cannot reach `BitVec n`.

There is no type-directed split that satisfies both. The remaining
shapes are: two carriers with adapters at every use site, or a scoped
residual.

### Op-by-op bucketing (for the two-carrier design)

The split is dead, but this bucketing survives it — it is what makes
the two-carrier rewrite bounded rather than open-ended. The 47
vector-op entries fall into four buckets, and only two need real
work:

- **structural** (permute or select slots without reading values) —
  `take0`, `drop0`, `head`, `tail`, `head_gen`, `tail_gen`,
  `at_single`, `rotateL`, `rotateR`, `shiftL`, `shiftR`, `zip`,
  `EmptyVec`. A permutation of `Vec n (Except String α)` is the same
  code; these pass the lazy carrier through unchanged.
- **producers** — `gen` (and `genM`). Build the lazy vector directly;
  no sequencing.
- **partial readers** — `at`, `atWithDefault`, `atRuntimeCheckedM`,
  `atWithProof_checkedM`. Read the selected slot's own `Except`.
  This is where the fix actually lives.
- **whole-vector consumers** — `foldl`, `foldr`, `map`, `vecEq_refl`,
  the bv family. Sequence at the boundary; faithful, because they
  read everything. **This is the bucket that saves the `BitVec`
  bridge**: bitvector ops sequence on entry, which is exactly what
  they do today, so `vecToBitVec` and its 184 lemmas are untouched.

Adapters between the two carriers become a new position in the
calculus, with the usual rule: only the sound direction is
representable (lazy → eager by sequencing is always sound; eager →
lazy is `Vec.map Except.ok` after a bind, and is sound too).

### Honest estimate

- **Uniform lazy carrier**: not viable. Costs the `BitVec` bridge,
  46 library references and 184 machine-checked bitvector lemmas,
  plus the `bv_decide` two-tier work.
- **Two carriers with adapters**: closes LIB-1 completely. Touches
  the 47 vector-op entries (though ~13 are structural pass-throughs),
  adds a position to the calculus, restates the 16 eager-carrier
  lemmas in `SAWCorePrelude_proofs`, and churns 22 hand-written proof
  rows and 101 goldens. The `BitVec` bridge survives because
  bitvector ops sit in the "sequence at the boundary" bucket. This is
  the real 0.03-scale item.
- **(a) for α ≠ Bool plus a pinned residual**: bounded, but does NOT
  close LIB-1 — the witness above stays live. Honest only if the
  residual is stated as an open soundness defect, not as closure.

## Recommendation — REVISED after the witness

The scoping reverses the earlier lean toward (a). (a) is blocked at
exactly the element type the `BitVec` bridge needs, so the only
options that actually CLOSE LIB-1 are the two-carrier rewrite (large)
and (c) (bounded, prototyped, works).

So:

1. **(c) is back in play as the only bounded closure.** Its cost is
   an emitted discharge tactic; the prototype shows the obligation is
   dischargeable and discriminating, and the five support lemmas are
   written. It inherits A-10, which is a real but separate defect.
2. **The two-carrier rewrite is the right end state**, and it is a
   0.03 item, not a pre-release one.
3. **(a) restricted to non-`Bool` is NOT a closure** and should not
   be described as one.

The decision this forces: either build (c)'s tactic now, or ship with
LIB-1 open and stated. Those are the two honest choices —
"(a) narrowly" is neither.

---

## Appendix — the option (c) prototype, verbatim

Preserved here because it is the EVIDENCE for the claims above and
lived only in a session scratchpad. It elaborates against the
support library as-is. Both theorems check with axioms
`[propext, Quot.sound]`:

- `sampleBody_total` — the guarded shape IS total, so the obligation
  is dischargeable on real emitted bodies;
- `sampleBadBody_not_total` — an unguarded body is provably NOT
  total, so the obligation genuinely discriminates rather than
  holding vacuously.

The second is the one that matters. It is what separates (c) from
(b): (b) rejected all 24 rows because it could not tell these two
apart, and this obligation can.

```lean
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePreludeExtra
open CryptolToLean.SAWCoreVectors

/-!
LIB-1 option (c) PROTOTYPE — 2026-07-26. Scratch, not for commit.

Question: if the emitter attached a totality obligation to every
`gen` whose element body can throw, how expensive is discharging it
on a REAL emitted shape?

The shape is taken from `drivers/cryptol_module_popcount`, whose
element body is

    iteM (Vec 32 Bool)
      (Pure.pure (ltNat i' 1))
      (atRuntimeCheckedM 1 _ v i')     -- guarded: only taken when i' < 1
      <else>

so the throw is unreachable, but only SEMANTICALLY — the guard is an
`iteM` condition, not a proof. A syntactic "can throw" scan rejects
this (and 23 other working rows); the obligation should discharge it.
-/

/-- The obligation shape: the element function never throws. -/
abbrev ElemTotal (n : Nat) (α : Type)
    (f : (i : Nat) → i < n → Except String α) : Prop :=
  ∀ (i : Nat) (h : i < n), ∃ a, f i h = Except.ok a

/-! ## The lemma set a discharge would lean on -/

theorem pure_ok {α : Type} (a : α) :
    ∃ b, (Pure.pure a : Except String α) = Except.ok b := ⟨a, rfl⟩

theorem bind_ok {α β : Type} {x : Except String α}
    {f : α → Except String β} {a : α}
    (hx : x = Except.ok a) (hf : ∃ b, f a = Except.ok b) :
    ∃ b, (Bind.bind x f : Except String β) = Except.ok b := by
  obtain ⟨b, hb⟩ := hf; exact ⟨b, by rw [hx]; exact hb⟩

/-- `atWithProof_checkedM` carries its bound, so it is ALWAYS ok
whenever its vector argument is. This is the cheap case. -/
theorem atWithProof_checkedM_ok {α : Type} {n : Nat}
    {xs : Except String (Vec n α)} {v : Vec n α} (hxs : xs = Except.ok v)
    (i : Nat) (h : i < n) :
    ∃ a, atWithProof_checkedM n α xs i h = Except.ok a := by
  refine ⟨v[i], ?_⟩
  unfold atWithProof_checkedM
  rw [hxs]; rfl

/-- `atRuntimeCheckedM` is ok exactly when the index is in range —
the side condition the obligation has to supply. -/
theorem atRuntimeCheckedM_ok_of_lt {α : Type} {n : Nat}
    {xs : Except String (Vec n α)} {v : Vec n α} (hxs : xs = Except.ok v)
    (i : Nat) (h : i < n) :
    ∃ a, atRuntimeCheckedM n α xs i = Except.ok a := by
  refine ⟨v[i], ?_⟩
  unfold atRuntimeCheckedM
  rw [hxs]
  simp only [h, dif_pos]
  rfl

/-- The load-bearing one: `iteM` discards the untaken branch, so only
the SELECTED branch has to be total. This is what makes the popcount
shape dischargeable at all — the `atRuntimeCheckedM` error sits in a
branch that is never selected for an out-of-range index. -/
theorem iteM_ok {α : Type} {c : Bool} {b : Except String Bool}
    {x y : Except String α}
    (hb : b = Except.ok c)
    (hx : c = true → ∃ a, x = Except.ok a)
    (hy : c = false → ∃ a, y = Except.ok a) :
    ∃ a, iteM α b x y = Except.ok a := by
  unfold iteM
  rw [hb]
  cases c with
  | false => exact hy rfl
  | true  => exact hx rfl

/-! ## The prototype discharge

A structurally representative popcount element body: the guarded
`atRuntimeCheckedM` in the then-branch, a `Pure.pure` else-branch,
under a `Bind.bind`. -/

noncomputable def sampleBody (v : Vec 1 Bool) (i : Nat) (_h : i < 32) :
    Except String Bool :=
  iteM Bool (Pure.pure (ltNat i 1))
    (atRuntimeCheckedM 1 Bool (Pure.pure v) i)
    (Pure.pure false)

theorem sampleBody_total (v : Vec 1 Bool) :
    ElemTotal 32 Bool (sampleBody v) := by
  intro i _h
  unfold sampleBody
  refine iteM_ok (c := ltNat i 1) rfl ?_ ?_
  · intro hlt
    -- the guard is what supplies the bound the runtime check needs
    exact atRuntimeCheckedM_ok_of_lt rfl i (by
      simpa [ltNat] using hlt)
  · intro _; exact pure_ok false

#print axioms sampleBody_total

-- NON-VACUITY: the same obligation for a body whose throw is NOT
-- guarded must be unprovable. `sampleBadBody` indexes a length-1
-- vector at `i` with no guard, so at i = 1 it genuinely throws.
noncomputable def sampleBadBody (v : Vec 1 Bool) (i : Nat) (_h : i < 32) :
    Except String Bool :=
  atRuntimeCheckedM 1 Bool (Pure.pure v) i

theorem sampleBadBody_not_total (v : Vec 1 Bool) :
    ¬ ElemTotal 32 Bool (sampleBadBody v) := by
  intro hcon
  obtain ⟨a, ha⟩ := hcon 1 (by omega)
  unfold sampleBadBody atRuntimeCheckedM at ha
  simp at ha

#print axioms sampleBadBody_not_total
```
