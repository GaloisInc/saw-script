# Residual trust catalog

*2026-05-02 — Phase 1a's missing exit-criterion deliverable
(per `2026-05-02_revised-plan.md` §"Phase 5b / L-discipline-1").
This is the canonical index of the soundness assumptions our
translator inherits but does not itself test, plus the comment-
grade items still pending a future gate.*

The lockdown principle (`2026-05-02_revised-plan.md` §"Soundness
as the bar") demands every soundness claim either pin a regression
test or live in this catalog. Items here are what's **not**
backed by a regression test that would fire if the property were
violated. Each entry says why, and what would have to break for
the violation to manifest.

For the user-facing summary of soundness boundaries — what
shapes the translator accepts vs refuses, what mappings imply
— see [`2026-04-24_soundness-boundaries.md`](2026-04-24_soundness-boundaries.md).
This catalog is the auditor-facing complement: where do we trust,
and what does the trust depend on?

## Categories

Residual trust falls into four categories:

1. **SAW-inherent** — assumptions in SAW we transport faithfully.
   Tightening would diverge from SAW semantics.
2. **Mapping-level** — choices of Lean representation. Documented
   alternatives exist; the chosen alternative is faithful but
   exposes Lean stdlib internals.
3. **Pending-gate** — comment-grade today, scoped for a future
   lockdown item. Each cites the planned closure work.
4. **Architectural / inductive** — claims that hold by the
   translator's structure rather than a per-instance test;
   would need a corresponding meta-theorem or fuzz check to be
   gate-grade.

---

## Category 1 — SAW-inherent residual trust

### 1.1 `unsafeAssert` at `α = Prop`

**Status:** Intentional residual (faithful to SAW).

**Where exercised:**
[`lean/CryptolToLean/SAWCorePrimitives.lean:421`](../lean/CryptolToLean/SAWCorePrimitives.lean#L421) —
`axiom unsafeAssert : (α : Type) → (x y : α) → @Eq α x y`. SAW's
declaration: `Prelude.sawcore:212`,
`primitive unsafeAssert : (a : sort 1) → (x y : a) → Eq a x y`.

**What we trust:** SAWCore's `unsafeAssert` admits `α = Prop`
(since `Prop : Type 0`, instantiable wherever `α : Type` is
required), and SAW Prelude itself uses
`unsafeAssert (sort 0) a b` inside `unsafeCoerce`
(`Prelude.sawcore:292`). A user CAN derive `Eq Prop True False`
from this and transport `True.intro` to `False`.

**Why not killable:** Tightening Lean's universe to forbid Prop
(`α : Sort 1` instead of `α : Type`, etc.) would diverge from SAW's
primitive — code that SAW accepts would no longer translate. L-2
explicitly rejected this widening attempt.

**Manifestation if violated:** N/A — this *is* the residual.
A user weaponizing it would derive `False`; SAW's documentation
warns of this.

**Adjacent test:**
`otherTests/saw-core-lean/shape/unsafe_assert_prop/` — L-2 pins the
shape (uses at `Type 1` must fail; common translator-emitted shapes
must succeed). The Prop attack is documented as the residual, not
tested.

---

### 1.2 `error.{u}` two-tier design (revised 2026-05-04, was Phase 9)

**Status:** Intentional residual on `error_unrestricted` (faithful
to SAW); user-facing `error` is **closed** to the L-17 attack
class.

**Where exercised:**
[`SAWCorePrimitives.lean`](../lean/CryptolToLean/SAWCorePrimitives.lean):
* `axiom error_unrestricted.{u} : (α : Sort (u+1)) → String → α`
  — SAW-faithful axiom. Translator emission target only.
* `def error.{u} (α : Type u) [Inhabited α] (msg : String) : α :=
  default` — user-facing constrained def.

SAW's declaration: `Prelude.sawcore:121`,
`primitive error : (a : isort 1) → String → a`.

**What we trust:**
* `error_unrestricted` matches SAW's `isort 1` semantics exactly
  (advisory inhabitedness, not enforced). Faithful to SAW's
  emission shape.
* `error` is sound to the bar that `Inhabited α` synthesizes —
  every legitimate user usage at an inhabited type works; every
  user attempt at an uninhabited type (`Empty`, `PEmpty`,
  `Fin 0`, `Inhabited Empty`, etc.) fails at instance synthesis.

**Phase 9 investigation (2026-05-03), superseded by 2026-05-04
two-tier design.** Phase 9 attempted to tighten the *single*
`error` axiom to `[Inhabited α]` and found it incompatible with
emission: SAW emits `error <T> "invalid instance"` in dead
dictionary branches even when `T` may be uninhabited (e.g., `Eq`
over `Stream a` for free `a`). The 2026-05-04 mitigation
sidesteps that by splitting the surface — translator routes to
`error_unrestricted` (no Inhabited constraint, free type
variables work), users see `error` (constrained, blocks the
attack class).

**Manifestation of remaining residual:** A user who *explicitly*
writes `error_unrestricted Empty "..."` can extract a fake
inhabitant of `Empty` and transport to `False`. This is an
explicit opt-out of safety — same semantic class as
`unsafeAssert` misuse — not silent unsoundness. The translator
never emits `error_unrestricted` at uninhabited types (Cryptol's
surface has no Empty type), so faithful translation is unaffected.

**Adjacent test:**
`otherTests/saw-core-lean/shape/error_prop/`:
* `attack.shouldfail.lean` — `error False ""` (Prop) must fail.
* `attack_empty.shouldfail.lean` — `error Empty ""` (uninhabited
  Type) must fail at Inhabited synthesis (closes L-17 attack
  class).

---

### 1.3 `coerce` at `α β : sort 0` — *closed by Phase 9*

**Status:** Closed 2026-05-03 (Phase 9 follow-up). `coerce` is
no longer an axiom — it's now a `@[reducible] def` defined as
`fun _ _ h x => cast h x`.

**Reasoning:** `coerce` is *type-equality transport* given a real
`Eq Type α β` proof. Lean's `cast` is exactly this. The combined
`coerce + unsafeAssert` unsoundness path is preserved — fabricating
a fake type-equality via `unsafeAssert (sort 0) α β` and feeding
it to `coerce` still yields the SAW `unsafeCoerce` attack — but
that lives entirely in `unsafeAssert`'s residual, not `coerce`'s.

**Adjacent test:**
`otherTests/saw-core-lean/shape/coerce/` — L-8 pins the
universe shape (still applies to the def-form: rejects use at
`Type 1`, accepts at `Type`).

(Entry preserved for the audit trail; no further action.)

---

### 1.4 SAWCore Prelude axioms transported as Lean axioms — *eliminated by Phase 9*

**Status:** Intentional residual (faithful to SAW), substantially
narrowed by Phase 9 (2026-05-02 evening).

**Where exercised:** Remaining `axiom ...` declarations in
[`SAWCorePrimitives.lean`](../lean/CryptolToLean/SAWCorePrimitives.lean):
- **Vec ↔ BitVec coherence (Phase 9):** `vecToBitVec_bitVecToVec`,
  `bitVecToVec_vecToBitVec` — the two round-trip axioms documenting
  that our MSB-first `Vec n Bool` and Lean's packed `BitVec n`
  carry the same information. Decidable for any concrete `n`
  (verifiable by `by decide`).
- **Bv ops still axiomatic:** `bvSDiv`, `bvSRem`, `bvSShr`,
  `bvSExt` (length-arithmetic mismatch with Lean's `BitVec` API);
  `bvPopcount`, `bvCountLeadingZeros`, `bvCountTrailingZeros`,
  `bvLg2` (bit-level coherence with `BitVec` versions deferred).
- **Integer ops:** `Integer` (the type), `intAdd`/`intSub`/`intMul`/
  `intDiv`/`intMod`/`intNeg`/`intEq`/`intLe`/`intLt`, `natToInt`,
  `intToNat`.
- **IntMod / Rational / Float / Double ops:** Phase 6 additions —
  axiomatic as a SAW-faithful surface (Lean has no native `IntMod`;
  `Rational`/`Float`/`Double` map outputs but coherence with SAW's
  semantics is uncommitted).

**What we trust:** Each axiom's signature matches SAW's primitive
declaration in `Prelude.sawcore`. SAW's semantics for the operation
is what governs its meaning; Lean does not see a body.

**Phase 9 conversions (closed):** Most bv ops are now
`noncomputable def`s routing through Lean's `BitVec`:
- Defined: `bvNat`, `bvToNat`, `bvToInt`, `intToBv`, `sbvToInt`,
  `bvAdd`, `bvSub`, `bvMul`, `bvNeg`, `bvUDiv`, `bvURem`, `bvShl`,
  `bvShr`, `bvNot`, `bvAnd`, `bvOr`, `bvXor`, `bvEq`,
  `bvult`/`bvule`/`bvugt`/`bvuge`/`bvslt`/`bvsle`/`bvsgt`/`bvsge`,
  `bvUExt`.
- `Vec ↔ BitVec` is bridged by `vecToBitVec` (Vec MSB-first folds
  into Nat, packed via `BitVec.ofNat`) and `bitVecToVec` (read
  bits MSB-first via `BitVec.getMsbD`).
- The corresponding axioms in `SAWCoreBitvectors_proofs.lean`
  are now **theorems** proven from Lean's `BitVec` library plus
  the two coherence axioms:
  - Arithmetic: `bvAdd_id_l`/`_id_r`/`_comm`/`_assoc`,
    `bvSub_n_zero`/`_zero_n`, `bvNeg_bvAdd_distrib`,
    `bvSub_eq_bvAdd_neg`.
  - Bitwise: `bvXor_same`/`_zero`/`_assoc`/`_comm`.
  - Equality: `bvEq_refl`/`_sym`/`_iff`,
    `bvEq_bvSub_l`/`bvEq_bvSub_r`.
  - Round-trip: `bvNat_bvToNat_id`, `bvToNat_bvNat`,
    `bvToNat_bounds`.
  - Comparison predicates: `isBvult_to_isBvule`,
    `isBvule_to_isBvult_or_eq`, `isBvslt_to_isBvsle`,
    `isBvslt_to_bvEq_false`, `isBvult_to_bvEq_false`,
    `isBvslt_antirefl`, `isBvsle_antisymm`,
    `isBvule_zero_n`, `isBvult_n_zero`, `isBvule_n_zero`.

**Phase 9 final state (2026-05-03):** Every theorem in
`SAWCoreBitvectors_proofs.lean` is now a *proven theorem*, not
an axiom. Including the previously-deferred:
- Signed bvsmin/bvsmax boundary: `not_isBvslt_bvsmin`,
  `not_isBvslt_bvsmax` — proven from `BitVec.intMin_le` and
  `BitVec.toInt_le`. (Also: bvsmin/bvsmax themselves were
  buggy under MSB-first convention pre-Phase-9 and are now
  routed through `BitVec.intMin`/`intMax`.)
- Successor/predecessor signed: `isBvslt_to_isBvsle_suc`,
  `isBvslt_suc_r`, `isBvsle_suc_r`, `isBvslt_pred_l`,
  `isBvsle_pred_l` — proven via `Int.bmod_eq_of_le_mul_two`
  with case-split on `w ∈ {0, 1, ≥2}`.
- Signed/unsigned bridges: `isBvult_to_isBvslt_pos`,
  `isBvule_to_isBvsle_pos`, `bvule_to_bvslt_zero`,
  `bvule_to_zero_bvsle` — proven via the `toInt`↔`toNat`
  case-bridge helpers `toInt_eq_toNat_of_nonneg` and
  `toInt_eq_toNat_sub_of_neg`.

**Net trust improvement (final):** Started with ~80 opaque
axioms across both files (one per bv operation, Integer/IntMod/
Rational/Float operation, and proof-library lemma); narrowed
to **2** in `SAWCorePrimitives.lean`:
- 2 Vec↔BitVec round-trip coherence axioms
  (`vecToBitVec_bitVecToVec`, `bitVecToVec_vecToBitVec`) —
  auditable by `decide` at any finite width.

All other Phase 6/9 ops are now defined: bv ops via
`Lean.BitVec` (sdiv, srem, sshiftRight, signExtend), popcount/
clz/ctz/lg2 via folds and `Nat.log2`, Integer ops via Lean's
native `Int` (with `Int.fdiv`/`Int.fmod` matching SAW's floor-
convention concrete simulator), IntMod via `Int` with
`Int.fmod`, Rational via Lean's `Rat`, Float/Double as
`Int × Int` mantissa-exponent pairs (faithful since SAW has
no operations on these), and `zip` via `Vector.ofFn`.

`SAWCoreBitvectors_proofs.lean` has **zero axioms**: every
arithmetic, bitwise, comparison, round-trip, signed/unsigned,
successor/predecessor, and boundary lemma is a machine-checked
theorem proven from the 2 coherence axioms + Lean's `BitVec`
library.

The remaining axioms in the codebase are the SAW-faithful
trust commitments: `coerce`, `unsafeAssert`, `error.{u}` (all
Category 1, intentional residual matching SAW's primitive
declarations).

**Phase 8 conversions (closed):** `gen`, `atWithDefault`, `foldr`,
`foldl`, `shiftL`, `shiftR`, `rotateL`, `rotateR`, `Pair_fst`,
`Pair_snd` are now structural defs over Lean's `Vector` /
`PairType`. The corresponding round-trip axioms in
`SAWCorePrelude_proofs.lean` (`gen_atWithDefault`,
`atWithDefault_gen`, `atWithDefault_out_of_bounds`,
`atWithDefault_singleton_zero`, `foldr_zero`, `foldl_zero`)
are theorems, not axioms.

**Manifestation if violated:** A wrong-type axiom would let users
derive false equalities at the term level. We mitigate by
docstring-citing `Prelude.sawcore:NNN` for each axiom and by L-14's
startup audit (any new SAW Prelude primitive without a matching
entry is caught at translator init). The Phase 9 round-trip
axioms are decidable per width — auditors can spot-check any
concrete `n` with `decide`.

---

### 1.5 `Pair_fst` / `Pair_snd` — *closed by Phase 8*

**Status:** Closed 2026-05-02 evening (Phase 8 chunk 2). Both
are now structural defs in
[`SAWCorePrimitives.lean`](../lean/CryptolToLean/SAWCorePrimitives.lean):
```
def Pair_fst (α β : Type) : PairType α β → α
  | PairType.PairValue a _ => a
def Pair_snd (α β : Type) : PairType α β → β
  | PairType.PairValue _ b => b
```

(Entry preserved for the audit trail; no further action.)

---

## Category 2 — Mapping-level residual trust

### 2.1 `Vec n α := Vector α n` abbreviation

**Status:** Intentional residual (L-4 analyzed; alternatives
considered and rejected).

**Where exercised:**
[`lean/CryptolToLean/SAWCoreVectors.lean:61`](../lean/CryptolToLean/SAWCoreVectors.lean#L61):
`abbrev Vec (n : Nat) (α : Type) : Type := Vector α n`.

**What we trust:** Pattern-matching a `Vec` value via `Vector.mk`
exposes the underlying `Array α` representation. SAW's `Vec n α`
and Lean's `Vector α n` are mathematically isomorphic — both
length-`n` tuples of `α` — so reaching into the alias doesn't
introduce divergence.

**Why not killable:** Sealing our `Vec` does not actually hide
Lean's `Vector` (it lives in stdlib; any `import Std` user can
construct values directly). The chosen abbrev is faithful.

**Detailed analysis:**
[`lean/CryptolToLean/SAWCoreVectors.lean:9-46`](../lean/CryptolToLean/SAWCoreVectors.lean#L9)
walks through the four arguments for keeping the abbrev.

**Manifestation:** A user constructing a malformed `Vector` via
`Vector.mk` with a wrong length-proof would crash at type-check;
no soundness path goes through this.

---

### 2.2 SAWCore `Nat` ≡ Lean `Nat` (different binary representations)

**Status:** Intentional residual (mapping is total).

**Where exercised:** SpecialTreatment maps `NatPos`/`Bit0`/`Bit1`/
`One`/`Zero` to numeric literals via `UseMacro`
([`SpecialTreatment.hs`](../src/SAWCoreLean/SpecialTreatment.hs)).
Concrete SAW Nat values collapse to Lean Nat literals at
translation time.

**What we trust:** SAW's binary-positive `Nat` and Lean's unary
`Nat` represent the same abstract values. The collapse to literals
is correct on closed Nat terms.

**Why not killable / what's gated:** Surviving `Nat#rec` with
SAW's `Zero / NatPos` case-split applied through Lean's
`zero / succ` recursor would silently miscompile.
`UnsoundRecursor` at
[`Term.hs:651-652`](../src/SAWCoreLean/Term.hs#L651) refuses
this — pinned by `otherTests/saw-core-lean/saw-boundary/natrec/` and the
L-3 auto-derive smoketest.

**Adjacent doc:** [`2026-04-24_audit-nat-mapping.md`](2026-04-24_audit-nat-mapping.md).

---

### 2.3 Universe collapse: every non-Prop SAW sort → Lean `Type`

**Status:** Intentional residual (single trust point; pinned).

**Where exercised:**
[`Term.hs:149-152`](../src/SAWCoreLean/Term.hs#L149) — collapses
every non-Prop SAW sort to Lean's `Type`. Combined with L-1
(which rejects `(t : sort k > 0)` binders), the maximum universe
a translator-emitted term can produce is `Type`.

**What we trust:** Cryptol-emitted SAWCore terms don't depend on
the universe distinction beyond Prop-vs-not. SAW's
universe-polymorphism (`isort`, sort variables) is squashed at
translation time.

**Pin:** L-10 smoketests (`translateSort: SAW sort 0 collapses to
Lean Type`, `SAW Prop stays as Lean Prop`).

---

## Category 3 — Pending-gate residual trust

These are comment-grade today; each has scoped follow-up work.

### 3.1 `Bool#rec` direct-emission gap — *closed by L-discipline-3*

**Status (2026-05-06):** Closed. Translator hard-rejects every
`Bool#rec` emission path with `RejectedPrimitive "Bool#rec"`. Pinned
by `otherTests/saw-core-lean/saw-boundary/boolrec/`.

**Gate site:** the Recursor case in
[`SAWCoreLean.Term.translateFTermF`](../src/SAWCoreLean/Term.hs)
checks the inductive's identifier against `preludeBool`; if it
matches, it throws `RejectedPrimitive` with a diagnostic pointing
the user at `ite` / `iteDep` in
`CryptolToLean.SAWCorePreludeExtra`. Both routes — L-16's
`scNormalize` unfolding path and the parse-core / hand-written
direct-emission path — refuse loudly.

**Why a refusal rather than a permutation.** SAW declares
`data Bool { True; False; }` (True-first), Lean's auto-generated
`Bool.rec` is False-first; emitting `@Bool.rec` with SAW's argument
order would silently swap every if/then/else branch. The right
contract for the user is always "use `ite` / `iteDep`" rather than
"trust the translator to permute correctly," so the gate refuses
instead of silently re-ordering.

---

### 3.2 Cryptol frontend productivity (Phase 5 Link 1)

**Status:** Pending catalog acknowledgment (this entry); no
test-grade gate planned. Inheritable.

**Where exercised:** Phase 5's `mkStreamFix` / `mkStreamFixPair`
lowering at
[`SAWCorePrimitives.lean:266-394`](../lean/CryptolToLean/SAWCorePrimitives.lean#L266)
and `lowerStreamCorec` / `lowerPairStreamCorec` at
[`Term.hs:429-505`](../src/SAWCoreLean/Term.hs#L429).

**What we trust:** Cryptol's type checker enforces productivity
at source level — a recursive stream definition `xs = body xs` is
accepted only if `body xs[i]` depends on `xs[j]` for `j < i`.
Under this guarantee, the `Prelude.fix` shapes that survive
`scNormalizeForLean` have a unique LFP equal to the bottom-up
index-by-index computation our `mkStreamFix` performs.

**Why not killable from inside the Lean backend:** Productivity is
a Cryptol-source-level property. Verifying it at the SAWCore-term
level would require either (a) a separate productivity checker on
each fix term we lower (substantial work, syntactic
under-approximation), or (b) trusting Cryptol's type checker as we
do today.

**Equivalent in Rocq backend:** N/A — Rocq rejects all `Prelude.fix`,
sidestepping the trust. Phase 5 is an architectural advantage
specifically because we accept the trust to gain the coverage.

**Manifestation if violated:** A non-productive Cryptol stream
that somehow survived Cryptol's type checker would translate to
a Lean term where `mkStreamFixIdx` builds a value using `default`
where the LFP would be `⊥`. The Lean term would compute (returning
`default` everywhere reachable past the non-productive index),
but it would NOT match SAW's denotational semantics.

**No test pins this.** A future fuzz pass that constructs synthetic
non-productive SAWCore terms (bypassing Cryptol's frontend) and
verifies they hit the L-5 reject *or* the L-6 normalization-cap
would tighten this from inheritable trust to architectural-pending
(Category 4).

---

### 3.3 `scNormalizeForLean` semantics-preservation (Phase 5 Link 2)

**Status:** Pending catalog acknowledgment (this entry); SAWCore
meta-theory.

**Where exercised:** All translator output. `scNormalizeForLean`
runs at
[`Exporter.hs`](../../saw-central/src/SAWCentral/Prover/Exporter.hs).

**What we trust:** SAWCore's normalization steps (β, ι, η,
defined-name unfolding, recursor reduction) preserve semantic
equivalence with the input term. Specifically: a productive `fix`
input remains productive after normalization, and an
elaboration-equivalent term remains elaboration-equivalent.

**Why not killable from the Lean side:** This is a property of
SAWCore's reduction relation, not our backend. The L-6 cap (100
iterations) catches non-convergence, but it doesn't verify
semantic preservation per step.

**Manifestation if violated:** Hard to construct without an
upstream SAWCore bug. Such a bug would manifest as Lean output
that elaborates but disagrees with `saw`-side `prove_print` /
`assume`-mode evaluation. (This would be a SAW bug, not a Lean
backend bug, and would affect the Rocq backend identically.)

---

### 3.4 L-1 polymorphismResidual scope — *closed by L-discipline-5*

**Status:** Closed 2026-05-02 evening. The gate now checks both
Pi and Lambda binders for sort `k ≥ 1`; pinned by the smoketest
"polymorphismResidual catches Lambda-side sort 1 binder
(L-discipline-5)" in `SmokeTest.hs`.

The Lambda-side check is defensive (post-`scNormalizeForLean`
type terms shouldn't contain unreduced Lambdas), but covering
hand-constructed SAW terms that bypass normalization or future
normalizer regressions is cheap insurance — three lines of
walker code mirroring the Pi case.

(Entry preserved for the audit trail; no further action.)

---

## Category 4 — Architectural / inductive residual

### 4.1 `leanOpaqueBuiltins` textual list (post-L-3)

**Status:** Convenience-only (per L-3 lockdown), but
inductively-load-bearing if the auto-derive misses a case.

**Where exercised:**
[`Exporter.hs`](../../saw-central/src/SAWCentral/Prover/Exporter.hs)
— `discoverNatRecReachers` auto-detects defs whose body contains
recursors over `Nat`, `Pos`, `Z`, `AccessibleNat`, or
`AccessiblePos`. The textual `leanOpaqueBuiltins` list keeps
adjacent entries opaque for surface cleanliness.

**What we trust:** The auto-derive is exhaustive (verified by L-3
smoketest covering all 5 unsound recursor types). The textual list
is convenience and would not, by itself, cause unsoundness if a
human dropped an entry — the auto-derive catches anything reaching
an unsound recursor.

**Why this is "architectural":** The argument is inductive
("every code path that reaches an unsound recursor is auto-marked
opaque"). A failure mode would require BOTH a missed auto-derive
case AND a textual-list omission of the same name. Pinned
indirectly by the auto-derive smoketest plus extensive integration
tests.

---

## Closing the catalog

Items in **Category 3 (pending-gate)** are the actionable residue.
Each is scoped in `2026-05-02_revised-plan.md` §"Phase 5b" or
§"Phase 8". When an item closes, this catalog should be updated:
the entry moves to a "Closed (date)" appendix or is removed
outright if the gate fully replaces the trust.

Items in **Categories 1, 2, and 4** are the steady-state residual:
either SAW-inherent (cannot be killed without diverging from SAW),
mapping-level (faithful but inherits Lean stdlib), or
architectural (inductively safe under the translator's structure).
These don't move; they stay catalogued.

**This catalog is the canonical answer** to "what does the saw-core-lean
backend trust that it doesn't itself test?" If a soundness claim
points here, it is documented residual trust; if a soundness claim
points to a regression test, it is gated; if a soundness claim
points to neither, the lockdown discipline rejects it.
