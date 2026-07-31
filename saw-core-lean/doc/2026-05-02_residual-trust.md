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
— see [`archive/2026-04-24_soundness-boundaries.md`](archive/2026-04-24_soundness-boundaries.md).
This catalog is the auditor-facing complement: where do we trust,
and what does the trust depend on?

## Threat model (decided 2026-07-30)

*User decision, 2026-07-30, during the wave-3 down-scope: the
replay trust kernel defends against **error, not adversarial
action**. This section is the citable statement of that decision;
guard severities — here, in the audit ledgers, and in future audit
scoring — are derived from it. It was previously unstated, and its
absence is why three audit waves scored text-inspection defects as
release-blocking CRITICALs.*

**In model — what the checks defend against.** Honest mistakes in
the normal workflow, from either side of the boundary:

- **Backend errors (ours).** An emission bug that makes the checked
  Lean statement differ from — especially, weaker than — the SAW
  obligation. This is why the goal-shape gates exist and why §3.2b
  extends the replay TCB to the emission pipeline itself.
- **User errors.** Staging the wrong file; leaving a `sorry` or a
  placeholder; proving a statement other than the goal; editing a
  completed outline's goal out of sync with the fresh emission; and
  foreseeable shortcuts taken *without intent to defeat the
  checker* — the classic being an `axiom` added to make a proof
  close, which is why the axiom audit exact-matches names and the
  proof-source lint bans top-level axiom declarations.
- **Tool failures.** A subprocess dying, a staged file vanishing
  mid-check, a timeout. These must fail closed (contributing.md
  rule C3) — empty output from a crashed check must never read as
  a clean result.

**Out of model — what the checks do NOT defend against.** An
adversarial proof author: someone who studies the checker in order
to defeat it. Concretely: Lean elaboration executes user code, so a
proof-side file can carry metaprograms, elaboration-time IO, and
environment manipulation, and a determined author can construct a
file whose *elaboration* rewrites what the gates inspect or forges
what they look for. Text linting cannot close that class — the
wave-3 record (K-1: a `simproc` escaping a denylist that its own
author had audited twice) is the demonstration — and pursuing it
produced fixes whose defect rate exceeded the risk they retired.

**Three consequences:**

1. **Severity derivation.** CRITICAL is reserved for defects
   reachable from within the model — ordinary use, no deliberately
   constructed circumvention. A defect exploitable only by an
   author acting adversarially is OUT-OF-MODEL: documented here,
   fixed when the fix is small and obviously stable, and never
   release-blocking. The partition keys on exactly one question —
   does reaching the defect require an adversarial author? — so a
   defect that is not an evasion route at all (a wrong README line,
   a stale comment, a misleading diagnostic) is IN-MODEL: ordinary
   use encounters it with no one acting in bad faith. (Sentence
   added 2026-07-30: wave 4 scored nine findings by an exhaustive
   reading of the in-model bullet list and four by this rule; the
   consistency check resolved the split in this rule's favor.)
2. **Load-bearing vs. courtesy.** The load-bearing checks are the
   ones that ask Lean's kernel a question whose answer cannot be
   faked from within the model: the `goal_closed : goal` binding
   (§3.2b), the `#print axioms` exact-match audit, and the
   completed-outline drift check. The text-inspection guards are a
   courtesy layer that catches foreseeable shortcuts early with good
   diagnostics; they must stay small enough to be kept honest
   (the 2026-07-30 plan 3a narrows the proof-source lint
   accordingly).
3. **Trust-boundary consequence (user-facing).** `LeanReplayEvidence`
   is only as strong as this model. Accepting evidence — or proof
   files — across an adversarial trust boundary is out of scope: a
   receiving party should review the proof source as they would any
   code (elaborating a Lean file executes it) and re-run replay
   themselves from the SAW goal. Stated in the README alongside the
   LIB-1 caveat.

**Wave-3 kernel findings re-scored under this model** (original
scores in `2026-07-30_release-gate-audit-wave3.md`; dispositions
D1–D4 recorded in TODO.md and the decision log):

| finding | wave-3 score | under the error model | disposition |
|---|---|---|---|
| K-1 — lint denylist misses `simproc` | CRITICAL | out of model: requires an authored metaprogram | allowlist fix discarded (D4); lint narrowed instead (plan 3a) |
| K-2 — deletion-blind digest + unlatched path | CRITICAL | split: a staged file vanishing is an in-model tool failure (C3); mid-check deletion as an attack is out | down-scoped to the C3 fail-closed fix; path-latching dropped |
| CP-1 — digest not re-verified before post-elaboration consumers | HIGH | out of model: the rewriting agent is an authored metaprogram | discarded (D4) |
| K-3 — elaboration-time IO routes | HIGH | out of model (same route as K-1) | reinstated in the ledger for the record; not release-blocking |
| W2-UNRUN-1 — Except-carried hypothesis binder | CRITICAL | **in model**: reachable from ordinary Cryptol, no intent required | fixed — goal-shape gate 3, 2026-07-30 |
| B1 — user code elaborated before text gates read files (wave 2) | CRITICAL | the demonstrated exploit was out of model | fix already landed and stable; retained (same logic as keeping the drift check, D3) |

The pattern worth internalizing: in this table, exploiting any of
the trust-kernel CRITICALs requires an out-of-model author, while
the defects reachable from ordinary use — W2-UNRUN-1 here, LIB-1 in
§3.2e — are **emission-side**: the emitted goal means less than the
SAW obligation. Error lives where meaning is constructed; the
gates that matter most are therefore the ones checking what was
*emitted*, not what the user *wrote*.

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

**Status:** CLOSED as an axiom (updated 2026-07-24). `unsafeAssert`
is NO LONGER an axiom: fully applied `unsafeAssert α x y` emits a
LOCAL `Eq` proof obligation discharged by generated checked
evidence (`saw_unsafeAssert` tactic — rfl/decide/omega/simp only,
no fabricated proofs; see `translateUnsafeAssertObligation` and the
`obligations/unsafe_assert_*` rows), and under-applied uses reject.
The Prop-instantiation discussion below is the HISTORICAL record of
why the axiom form was dangerous; the residual it describes no
longer exists because the axiom no longer exists.

**Historical record (May 2026 axiom era):**
`axiom unsafeAssert : (α : Type) → (x y : α) → @Eq α x y`
(line-cite stale — the file has since grown). SAW's declaration:
`Prelude.sawcore:212`,
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
A user misusing it would derive `False`; SAW's documentation
warns of this.

**Adjacent test:**
`otherTests/saw-core-lean/negative/unsafe_assert_prop/` — L-2 pins the
shape (uses at `Type 1` must fail; common translator-emitted shapes
must succeed). The Prop Check is documented as the residual, not
tested.

---

### 1.2 `error.{u}` two-tier design (revised 2026-05-04, was Phase 9)

**Status:** CLOSED — BOTH error axioms are DELETED (updated
2026-07-24). Value-domain `Prelude.error` now routes to
`saw_throw_error` (a reducible def over the `Except String` carrier
— the error is a visible value, no axiom, no fake inhabitant);
raw-position `error` REJECTS at translation or lowers to the
constant-error function per the audited disposition
(`2026-07-14_reachable-raw-error-disposition.md`). The two-tier
`error_unrestricted`/`error` axiom design below is the HISTORICAL
May-2026 record; neither symbol exists in the library today, and
the negative rows cited at the end now pin the support library's
current shapes.

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
Check class).

**Manifestation of remaining residual:** A user who *explicitly*
writes `error_unrestricted Empty "..."` can extract a fake
inhabitant of `Empty` and transport to `False`. This is an
explicit opt-out of safety — same semantic class as
`unsafeAssert` misuse — not silent unsoundness. The translator
never emits `error_unrestricted` at uninhabited types (Cryptol's
surface has no Empty type), so faithful translation is unaffected.

**Adjacent test:**
`otherTests/saw-core-lean/negative/error_prop/`:
* `rejection.shouldfail.lean` — `error False ""` (Prop) must fail.
* `rejection_empty.shouldfail.lean` — `error Empty ""` (uninhabited
  Type) must fail at Inhabited synthesis (closes the L-17 risk
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
it to `coerce` still yields the SAW `unsafeCoerce` Check — but
that lives entirely in `unsafeAssert`'s residual, not `coerce`'s.

**Adjacent test:**
`otherTests/saw-core-lean/negative/coerce/` — L-8 pins the
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
  `Rational` maps outputs but coherence with SAW's semantics is
  uncommitted). `Float`/`Double` are no longer in that "maps
  outputs" class as of 2026-07-25 (audit-2 F-2): they are sealed
  `opaque` types with uninterpreted constructors, matching SAW's own
  declaration, so there is no output map to be coherent with.

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
convention concrete simulator AT NONZERO DIVISORS — the zero
points diverge and are gated by checked/runtime wrappers; audited
zero-point table in
`2026-07-18_underapplied-partial-op-wrapper.md`), IntMod via `Int` with
`Int.fmod`, Rational via Lean's `Rat`, Float/Double as two SEPARATE
sealed `opaque` carriers with uninterpreted `opaque` constructors,
and `zip` via `Vector.ofFn`.

**Corrected 2026-07-25 (audit-2 F-2).** This sentence used to read
"Float/Double as `Int × Int` mantissa-exponent pairs (faithful since
SAW has no operations on these)", and both the binding and its
justification were wrong. `Eq` is an observer — at the type level
and at the value level — so a shared transparent image made
`Float = Double`, `mkFloat m e = mkDouble m e` and
`mkFloat`-injectivity all provable in Lean while underivable in SAW.
The error generalizes and is worth carrying forward when reading the
rest of this catalog: **"no *executable* observer" is strictly
weaker than "no *equational* observer"**, and only the latter
licenses collapsing two SAW types onto one Lean type. Pinned by
`negative/float_double_collapse`.

`SAWCoreBitvectors_proofs.lean` has **zero axioms**: every
arithmetic, bitwise, comparison, round-trip, signed/unsigned,
successor/predecessor, and boundary lemma is a machine-checked
theorem proven from the 2 coherence axioms + Lean's `BitVec`
library.

The remaining axioms in the codebase are EXACTLY the two Vec↔BitVec
round-trip coherence axioms above — nothing else (updated
2026-07-24; the earlier version of this paragraph also listed
`coerce`, `unsafeAssert`, and `error.{u}`, all of which have since
been converted: `coerce` to a reducible `cast` def (§1.3),
`unsafeAssert` to a local proof obligation with checked evidence
(§1.1), and both error axioms deleted in favor of `saw_throw_error`
and the raw-error rejection disposition (§1.2)).

**Phase 8 conversions (closed):** `gen`, `atWithDefault`, `foldr`,
`foldl`, `shiftL`, `shiftR`, `rotateL`, `rotateR`, `Pair_fst`,
`Pair_snd` are now structural defs over Lean's `Vector` /
`PairType`. The corresponding round-trip axioms in
`SAWCorePrelude_proofs.lean` are theorems, not axioms. (Corrected
2026-07-24, audit category C2: this list previously named six
theorems, three of which — atWithDefault_gen,
atWithDefault_out_of_bounds, atWithDefault_singleton_zero — do not
exist under those names, and a fourth, gen_atWithDefault, exists
only as `gen_atWithDefault_double_reverse`. The surviving claim is
the one that matters and is mechanically checkable: that file
declares no axioms. Verify with
`grep -c '^axiom' SAWCorePrelude_proofs.lean`.)

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

**Adjacent doc:** [`archive/2026-04-24_audit-nat-mapping.md`](archive/2026-04-24_audit-nat-mapping.md).

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

### 3.2 Cryptol frontend productivity (RE-OPENED 2026-07-15 — OP-3 successor)

**Status:** LIVE again, with a proof-carrying mitigation the retired
Phase 5 helpers never had. (Was: retired 2026-05; the old structural
stream/vector fix helpers are still deleted and still forbidden.)

**Former trust shape (Phase 5, refuted):** Earlier prototypes trusted
Cryptol's source-level productivity check, then used Haskell
classifiers to lower recognized `Prelude.fix` terms to structural Lean
helper definitions. If the productivity claim was wrong or the
classifier selected the wrong shape, Lean could compute a value that
did not match SAW's denotational fixed point — SILENTLY.

**Re-opened shape (OP-3 successor, amendments A/E/F —
doc/2026-07-15_op3-successor-design.md; LANDED in full 2026-07-16,
slices R0–R4):** the backend again realizes recognized fix shapes
directly: Class F via `saw_fix_bounded_choose` (R2), Class S-single
via `saw_stream_realize` (R3b); every unrecognized wrapped fix
rejects with a named diagnostic, and the wrapped
unique-fixed-point contract was retired at R4. The difference from
the refuted Phase 5 shape is WHERE a wrong claim lands:

* the per-instance productivity obligation
  (`saw_fix_bounded_productive` — totality AND bounded lookback) is
  PROVEN in Lean against the emitted body at every emission site,
  never assumed. A wrong recognizer verdict makes that obligation
  UNPROVABLE — loud failure, not a wrong value;
* the faithfulness core (`saw_fix_bounded_iter_stable` /
  `_fixed_point` / `_unique_pure_fixed_point`,
  SAWCorePrelude_proofs) is proved once, unconditionally in the
  library, conditional only on the per-instance obligation; the
  realization is provably the UNIQUE pure fixed point of the body.

**Remaining live trust (named, not manufactured):** that SAW's `fix`
denotes a pure fixed point of the translated body. This decomposes
into `fix_unfold` (SAW's own spec for `fix`), §3.3
(`scNormalizeForLean` preservation), and the value-domain translation
itself — no NEW trust class beyond the catalog.

**Regression expectation:** live code and emitted goldens must not
reintroduce the RETIRED direct fix-helper names or unreachable
defaults; the driver harness's obsolete-helper scan enforces this and
its list comments name `saw_fix_bounded` / `saw_stream_unfold` as the
sanctioned proof-carrying successors (they are NOT to be added to the
forbidden list when R2/R3 land).

---

### 3.2a Evaluator grounding record (2026-07-16) — model commitments read against SAW's source

The Lean model's load-bearing commitments about SAW's OPERATIONAL
semantics, verified by reading the evaluator (dated; re-verify if the
simulator changes):

* **`fix` is lazy knot-tying.**
  `saw-core/src/SAWCore/Simulator/Prims.hs:1662-1667`:
  `fixOp = constFun $ strictFun $ \f -> Prim (force =<< mfix (\x ->
  delay (apply f x)))` — Haskell `mfix` over a delayed thunk. The
  recursive value unfolds on demand; divergent self-reference is
  genuine nontermination (⊥). This is the lazy-least-fixed-point
  reading every OP-3 audit assumed, now grounded in code. Crucially
  the SAME `fixOp` serves ALL simulator instances (Concrete / What4 /
  SBV / RME) through the `VMonadLazy l` class and the shared prim
  table (`Prims.hs:394`) — there is no per-backend fix semantics to
  diverge from.
* **Vectors are elementwise-lazy.**
  `saw-core/src/SAWCore/Simulator/Value.hs:110`:
  `VVector !(Vector (Thunk l))` — elements are individual thunks, so
  element `i` of a fix's value can be forced while element `j` is
  still ⊥. This is the pointwise domain of the fragment-semantics
  scoping doc (2026-07-16), structurally confirmed.
* **`error` is a message-carrying escape, with the fixed `at`
  message.** `Prims.hs:1479-1483` (`errorOp` raises
  `Prim.userError msg`); `saw-core/prelude/Prelude.sawcore:1564`
  (`at n a v i = atWithDefault n a (error a "at: index out of
  bounds") v i`) — byte-identical to the message
  `atRuntimeCheckedM` emits, confirming the message-identity
  assumption recorded on that accessor. Errors in SAW are escaping
  exceptions, not comparable first-class values; the Lean `Except`
  model REFINES this (errors are values, message-distinguishable).
  Agreement region: on all-success evaluations the two coincide, and
  a forced erroring element fails loudly on both sides. The models
  genuinely differ only in HOW MUCH is forced — the eager `Except`
  carrier can surface an error a lazy evaluation never touches.
  That difference is exactly the region the per-instance obligations
  fence off (pure-survival / totality / faithfulness): translated
  goals are equated only where all-success holds, and outside it the
  obligations are unprovable, not wrong.

  **CORRECTION (2026-07-25, audit finding LIB-1 — the paragraph
  above is BACKWARDS in its most important case, and the error was
  load-bearing.)** "Unprovable, not wrong" holds when the two sides
  surface DIFFERENT errors. When they surface the SAME error — which
  is the normal case, because the byte-exact message identity
  recorded just above was chosen deliberately to stop Lean
  OVER-DISTINGUISHING — the emitted equation does not become
  unprovable. It becomes trivially TRUE in Lean while FALSE in SAW.
  The eager `Except` carrier cannot represent "an error in one slot,
  good values elsewhere", so `Vec n (Except String T)` collapses to
  `Except String (Vec n T)`, and that adaptation is NON-INJECTIVE.

  Verified end-to-end 2026-07-25 (SAWCore via `parse_core`):

      A = at 2 T (gen 2 T (\i -> ite T (equalNat i 1) (error T "e") (bvNat 8 7))) 0
      B = at 2 T (gen 2 T (\i -> ite T (equalNat i 1) (error T "e") (bvNat 8 9))) 0

  SAW evaluates `A = 0x07` and `B = 0x09` (index 0 is read; the
  index-1 thunk holding `error` is never forced), so `Eq T A B` is
  FALSE. Lean reduces BOTH to `Except.error "e"`, and the emitted
  equation is provable using only allowlisted axioms
  (`propext`, `Quot.sound`) — i.e. a perfect trust kernel admits it,
  because the Lean statement really is proved. It is the WRONG
  statement.

  So the message identity that protects against over-distinguishing
  is exactly what enables over-EQUATING. This is an OPEN soundness
  defect (LIB-1), tracked in TODO.md; it is a translator/carrier
  problem, not a gate problem, and no checker hardening addresses it.

Remaining UNREAD/UNPROVEN after this pass (unchanged): §3.3
normalization preservation; the meaning link from SAW's proof
pipeline to the emitted goal term; Cryptol elaboration. The
fragment-semantics scoping doc's Phase C (fix/error differential
rows) is the continuous empirical pin for this record — code reading
is a snapshot, differential rows keep it honest as SAW evolves.

### 3.2b Replayed-goal TCB (offline_lean_replay, 2026-07-17)

For goals ADMITTED via `offline_lean_replay` (and only those), the
trusted base extends beyond the standing catalog to: Lean's kernel;
the pinned toolchain (lean-toolchain file, recorded in evidence);
the staged CryptolToLean support library; the factored checker
(`saw-core-lean/replay/lean-check-core.sh`); AND — seventh-audit amendment 1 —
the SAW-side emission pipeline itself (`propToTerm`, `scPiList`
free-var abstraction, `scNormalizeForLean`): replay converts an
emission bug into a false SAW theorem, so goal formation is
soundness-critical on this path. Mitigations at admission time: the
emitted goal must compile (dropped binders cannot). (An
anti-trivialization probe — an over-reduction guard rejecting
goals closable by rfl/trivial — existed here 2026-07-24 to
2026-07-31 and was DELETED by the kernel design review, user
decision; the residual it leaves is §3.2f.) LeanReplayEvidence is
a NON-RECHECKABLE
trust token: checkEvidence verifies sequent subsumption only; the
recorded toolchain/hashes/axiom list document the one-shot kernel
check and cannot re-verify it.

Tier note (2026-07-24 audit, TIER-1): `offline_lean_replay` runs
STRICT-tier only — it never reads a `.trust-tier` marker, so the
labeled `native-eval` tier (bv_decide's per-invocation proof-local
axioms) is a conformance-suite construct and is never honored at
product-runtime admission; a native-eval proof replayed through the
product path fails loudly with `axiom-outside-allowlist`. This
asymmetry is deliberate (replay is never looser than CI).

Completed-outline binding (R-1 fix, 2026-07-24 audit): on the
completed-outline path, goal-presence is decided by the fresh
emission (the authority), a completed file without a bare
`def goal :` line is rejected outright, and user files mentioning
the `GeneratedHarness` probe namespace are rejected — the
closer↔goal binding check (`goal_closed : goal`) therefore ALWAYS
runs on admitted replays.

**Elaboration order on the completed path (B1, 0.02 release-gate
audit, 2026-07-29 — CORRECTS this section's own premise).** Read
plainly, the paragraphs above rest on "the staged `Emitted.lean` is
the untouched fresh emission". On the completed-outline path that was
FALSE: the SAW caller stages the user's outline as BOTH
`completed.lean` and `Emitted.lean`, and the checker's first Lean
action compiled `Emitted.lean` — so user-authored Lean was elaborated
before any gate read it. Lean elaboration executes commands, so a
metaprogram in that file ran while the lint's target and the drift
check's authority were both on disk and rewritable; rewriting them
yielded `CHECK-OK` for a false obligation. Demonstrated end-to-end in
the project's own kernel selftest.

Closed 2026-07-29 by moving the pure-text gates ahead of the first
elaboration AND by making the ordering a CHECKED invariant: the
staged files are digested before anything runs and re-verified
before the gates the B1 fix covers — `Emitted.lean` at its first
elaboration, `Generated.lean` and `completed.lean` before the drift
probe, `proof.lean` and `completed.lean` before the re-run text
gates. (Narrowed 2026-07-30, wave-4 DC-1: the original sentence
here claimed "each consuming gate" universally, which this same
document's CP-1 row records as knowingly discarded — `Emitted.lean`
is not re-verified before its post-elaboration grep gates; the
verifier showed each such bypass is backstopped by the olean
import, the drift probe, and the completed-path re-scans.) What a reader should take
from this entry is not only the fix but the shape of the mistake —
the section reasoned about WHICH files are trusted and never about
WHEN each becomes trustworthy, and on a path where one file is a
copy of another, order was the whole question. Pins: `b1elab`,
`b1hash`, `b1contract` in the kernel selftest, and
`saw-boundary/replay_reject_elaboration_order` on the product path.

### 3.2c Deployment trust: the dev-override affordances (2026-07-25)

Named here because the plan's threat model (T3) treats them as OUT
OF SCOPE, and an out-of-scope boundary that is only implied is not
documented. These are affordances, not defects — but a reader
should not have to infer them.

- **`SAW_LEAN_ROOT`** substitutes BOTH the pinned support library
  and the checker script itself. Anyone who can set it can make the
  trust kernel say anything.
- **The staging cache** (`~/.cache/saw-core-lean/lean-<fp>/`) is
  reused on marker EXISTENCE only; staged contents are never
  re-hashed (audit RK-8). Write access there permits substituting
  the support library — adding *lemmas*, which the allowlist audit
  cannot see, since it audits axioms rather than theorems.
- **The toolchain** is trusted by construction: replay records the
  `lean-toolchain` in evidence but cannot verify the binary.

The trust kernel defends against a proof that does not prove the
emitted obligation. It does not, and cannot, defend against someone
who controls the checker, the library, or the compiler — such a
person could equally just assert the goal was proved. What this
boundary DOES mean in practice is that `LeanReplayEvidence` is
meaningful to a second party only to the extent they trust the
environment that produced it.

### 3.2d Two narrow type-image residuals (2026-07-25, audit-2)

Recorded here because they are the two surviving members of the
class F-2 belonged to, and F-2 showed that class is not benign. Both
are narrower than F-2 was, and neither has a demonstrated witness.

- **LIB-3 — `IntMod n := Int` maps residues to representatives.**
  A BOUND `IntMod n` variable in the emitted statement therefore
  ranges over representatives, not residues, so it quantifies over a
  strictly larger domain. In POSITIVE `∀` position that is harmless
  and in fact conservative: proving it for every representative
  proves it for every residue. It would be unsound in NEGATIVE
  position — an existential, or a hypothesis of the form
  "for all `x : IntMod n`, …" used to derive something — because
  there the larger domain is a weaker assumption. No emitted shape
  puts a bound `IntMod` in negative position, and every `IntMod`
  operation carries `n` explicitly and normalizes through
  `Int.fmod`. Distinct from the open F1 `n = 0` totalization, which
  is about partiality rather than the domain.

- **F-3b — `@Eq.rec` carries no constructor-order assertion.** It
  reaches emission through a hardcoded path that bypasses
  `translateFTermF`, so `recordCtorOrderAssertion` never fires for
  it. Deliberately left that way: the assertion exists to catch
  drift between SAWCore's declared constructor order and *this
  library's* realizing inductive, and `Eq` is neither — it is Lean
  CORE's `Eq`, whose single constructor and recursor signature are
  fixed by the kernel and by the pinned toolchain. An assertion
  about it could not fail for any reason the mechanism was built to
  detect. Emitting one would add a check that reads as coverage
  while proving nothing, which is the failure mode
  `doc-claim-lint.sh` exists to prevent.

### 3.2e LIB-1 — the wrapped-vector carrier collapse (OPEN, shipped documented; user decision 2026-07-28)

The one KNOWN OPEN unsound-acceptance surface in this catalog, and
the only entry that is a live soundness defect rather than a trust
assumption. Recorded with its full character because no gate in the
replay kernel can catch it: the accepted proof is well-formed,
kernel-checked and allowlist-clean — and false in SAW.

**Mechanism.** SAW vectors are element-lazy (§3.2a: `VVector` of
per-slot thunks; an unforced erring slot is never observed). The
Lean value carrier `Except String (Vec n T)` collapses any erring
element into failure of the whole vector (`genWithBoundsM` =
`Vector.ofFnM`, denotationally short-circuiting; same class:
`vecSequenceM` literals, and see the reference-closure caveat
below). The collapse is non-injective and appears on BOTH sides of
emitted equations, so a SAW-false equation whose falsity is hidden
behind an unread erring slot closes by `rfl` under
`[propext, Quot.sound]`.

**Evidence and scope** (all 2026-07-28):
- Pinned witness: `differential/lazy_vector_error_slot` — SAW
  `true/true/false` vs Lean `error ×3` through the real pipeline.
- Corpus: 59 of 350 baseline artifacts carry a thrower inside an
  element position (58 via `atRuntimeCheckedM`) —
  `doc/2026-07-28_lib1-scope-measurement.md`.
  **The 59 is EXACT for this corpus, not a floor** (corrected here
  2026-07-29 by the release-gate audit, finding F5; the retraction
  itself was made 2026-07-29 in the measurement doc and never
  propagated to this catalog, so for one day the two documents gave
  a reader OPPOSITE bounds on the same shipped number).
  What was retracted: an earlier version named
  differential/vector_literal_edges as a live witness of emitter
  let-sharing moving a thrower textually outside its element. It is
  not one — in that artifact the only throwing let-binding is bound
  INSIDE the element span it is used in, the two let-bound values
  actually referenced from its `vecSequenceM` element spans are
  non-throwing, and its `gen` there is zero-length so the element
  function is never applied. An independent scan over the whole
  baseline finds ZERO artifacts with a throwing let-RHS bound
  outside an element span and referenced inside.
  What SURVIVES the retraction, and is the reason this bullet still
  exists: "a gate must be REFERENCE-CLOSED" remains a real design
  requirement — a property any future rejection gate must HAVE, not
  an observed corpus escape. It prices in together with the
  genuinely interprocedural half (module translation emits elements
  that call module-local definitions, so "can this element throw"
  must traverse the translated module's call graph).
  **What a reader should take from the number:** it bounds THIS
  CORPUS exactly. It is not a property of the emitter, and a new
  artifact can add to it.
- No landed discharge is affected: every landed proof closes at
  explicit `Except.ok` values, the shape the collapse cannot help.
- Reachable from ordinary Cryptol (not `parse_core`-only), and an
  admitted false lemma amplifies through compositional replay
  chains.

**Disposition (user decision 2026-07-28): ship documented, no
interim gate.** Interim rejection at full scope would refuse ~17%
of the corpus including the discharged workflow proofs; the
evidence-gated variant was scrutinized and refuted
(`doc/2026-07-28_lib1-b-evidence-design.md` — foundationally, the
runtime-checked form exists exactly where evidence was underivable).
The user-facing flag is in `README.md` ("KNOWN SOUNDNESS
LIMITATION"), including the second-party caveat: until the remedy
lands, `LeanReplayEvidence` is evidence modulo LIB-1.

**Remedy (recorded):** the faithful per-element carrier
`Vec n (Except String T)` — a by-construction fix (nothing to
detect), planned for a later release; its migration proofs should
rest on the kernel-checkable element-totality lemma family proposed
(under the working name genWithBoundsM_ok_of_total — not yet in the
library) in the design-scrutiny doc. This entry closes (and the
README flag comes down) when that carrier lands and the pin row
flips from known-gap to true differential coverage.

### 3.2f Goal-formation trivialization at replay time (2026-07-31,
gate deleted by design review — user decision)

The anti-trivialization gate (a replay-time probe asking whether
`first | rfl | trivial` closes the emitted goal) was DELETED on
2026-07-31 (`doc/2026-07-31_kernel-design-review.md` §3.1 Option
B). Grounds: it was a text-discriminated negative probe outside
the threat model's load-bearing list (consequence 2 names three
checks; this was not among them), and it empirically could not be
kept "small enough to be kept honest" — its accept-condition
decoder went through three same-day audit rounds (fail-open →
position check → refutation allowlist → allowlist + give-up
denylist), each refuting the last, ending coupled to one
toolchain's error phrasing with an unpinned denylist half.

THE RESIDUAL, stated plainly: if an emission bug trivializes a
goal (over-reduction collapsing it to `True`/`x = x`-class), and
the user or their automation discharges that goal WITHOUT noticing
what it says, replay admits `LeanReplayEvidence` for a claim whose
SAW meaning was destroyed at emission. No kernel-side check
remains for this class: the binding check honestly binds the
trivialized goal, the drift check compares two outputs of the same
emitter, and the axiom audit sees a clean `rfl`.

What defends the class instead:
1. Development time: the differential/conformance corpus — an
   emitter change that over-reduces breaks evaluation-comparison
   and emission-golden rows before it ships.
2. Discharge time: the goal is VISIBLE. A trivialized goal reads
   `def goal : Prop := True` (or an evaluated closed equation) in
   the Emitted.lean the user must open to discharge. The residual
   is precisely the rubber-stamp case — automation or inattention
   discharging without reading.
3. The admission requires the CONJUNCTION of an in-model backend
   error and that unnoticed discharge.

This is the D2 pattern deliberately repeated: scope reduction plus
honest documentation, chosen over a hardened text discriminator
whose fix-defect rate three audits demonstrated. If the class ever
demonstrates in practice, the recorded re-entry path is an
EMISSION-side structural check (where meaning is constructed), not
a replay-side message parser — see contributing.md's
courtesy-layer fix rule.

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

**SCOPE CORRECTION (F6, 0.02 release-gate audit, 2026-07-29).**
Everything above is true of `scNormalize` — SAWCore's own reduction
relation — and that is now ALL this entry claims. It was written as
though `scNormalizeForLean` were only that, and it is not:
`Exporter.hs:573` composes SAWCore's normalizer with
`scLiteralFold`, a rewriting pass this backend owns. So the three
load-bearing sentences above were each half-false — "a property of
SAWCore's reduction relation, not our backend", "not killable from
the Lean side", and above all "would affect the Rocq backend
identically", which is backwards: the Rocq path never runs it. The
backend-owned half now has its own entry below, because a residual
that a reader cannot find is not catalogued.

---

### 3.3a `scLiteralFold` — backend-owned rewriting upstream of every gate (2026-07-29)

**Status:** OPEN residual, newly catalogued (F6, 0.02 release-gate
audit). Previously absorbed into §3.3 and thereby attributed to
SAWCore.

**Where exercised:** every goal and term on the LEAN path only.
`scNormalizeForLean` composes it with `scNormalize`
(`Exporter.hs:573`); a repo-wide search finds no other caller, so
the Rocq backend never runs it.

**What we trust:** 24 hand-written constant-folding rules
(`Exporter.hs:603` onward) agree with SAW's own evaluator on every
input they fire on — the Nat family (`addNat`, `subNat`, `mulNat`,
`minNat`, `maxNat`, `expNat`, `divNat`, `modNat`, `pred`,
`doubleNat`, `equalNat`, `ltNat`, `leNat`), the Int family
(`intAdd`, `intSub`, `intMul`, `intNeg`, `intEq`, `intLe`, `intLt`,
`intToNat`, `natToInt`), and the `ite`/`iteDep` selectors. Four
carry explicit guards at the partial points (`divNat`/`modNat`
require `bn /= 0`; `intToNat` requires `nv >= 0`; `subNat` is
saturating).

**Why this is a distinct residual, not a variant of §3.3.** Three
reasons, and the third is the one that matters. It is OURS — a
SAWCore-side normalization bug is an upstream bug, but a wrong rule
here is a defect in this backend. It is KILLABLE from the Lean side,
so "not killable" was never true of it. And it runs UPSTREAM OF THE
ENTIRE AUTHORITY: `writeLeanProp` computes the goal's arity and
telescope pins AFTER `scNormalizeForLean`, so the telescope
fingerprint, the sort gates and the replay drift check all compare
against a term this pass has already rewritten. No downstream gate
can see a rule that folded a term to the wrong value; every gate
would agree with itself.

**Manifestation if violated:** a folded constant that disagrees with
SAW's evaluator makes the emitted goal state something the SAW
obligation does not, silently — the emitted artifact is well-typed
and every gate passes. This is the same shape as LIB-1 (a
value-domain divergence no proof-side gate can catch), and unlike
LIB-1 it is not bounded by a measurement.

**What would close it:** per-rule differential rows against SAW's
own evaluator, so each rule's agreement is a tested fact rather than
a 2026-07-24 reading of the source; the guarded partial points
(`divNat`/`modNat` at zero, `intToNat` on negatives, `subNat`
saturation) are the ones to write first, since those are where a
rule and an evaluator most easily disagree. Tracked in TODO.md as
F6.

---

### 3.4 L-1 polymorphismResidual scope — *GATE REMOVED; entry superseded*

**Status (corrected 2026-07-24, audit finding A-3):** the
polymorphismResidual gate this entry describes **no longer exists**
— it was removed from the source in May and this catalog continued
to record it as a closed-and-pinned soundness gate for two months,
through two soundness audits and a doc-faithfulness pass. Nothing
refuses a sort-`k ≥ 1` binder today; such binders are TRANSLATED,
each getting a fresh Lean universe variable
(`Convention.hs:527-542`).

That replacement is sound in the direction that matters
(`∀ {u} (a : Sort u), P a` implies SAW's `∀ (a : sort k), P a`),
so removing the gate did not create the weakening this entry was
written to exclude. Three consequences were OPEN; **all three were
closed 2026-07-25**, by a single rule replacing the deleted gate:

> **A goal telescope may not quantify over a sort.**

`translateGoalDocWithTelescope` refuses, at translation time, any
goal emission that (i) allocates a universe variable, or (ii)
contains a sort-typed binder at any depth (`Prop` excepted — SAWCore
`Prop` maps to Lean `Prop` with no cumulativity gap). The gate is
GOAL-ONLY: module and term emission still translate sort binders and
still go universe-polymorphic, which is sound and needed. What the
rule closes:

- **A-2** — a universe-parameterized goal rendered `def goal.{u0}`,
  which the replay checker's goal-presence regex missed. The checker
  half was closed 2026-07-24 by making goal presence an invariant
  derived from the authority; the emitter half now prevents the
  shape from existing at all.
- **A-9** — the `goal_holds` stub is built from the bare name and
  dropped the universe binders, proving the goal at ONE inferred
  level instead of universally. Closed **by construction**: a goal
  reaching the stub has no universe binders to drop. Reopening the
  A-2 gate reopens A-9.
- **F-5** — `sort 0 → Type` NARROWS the quantifier, since SAWCore
  admits `Prop ≤ sort 0` cumulativity and Lean 4 has no term
  cumulativity. Note the removed gate would NOT have covered this
  one either: it gated only `k > 0`. The audit's alternative fix
  (emit `Sort u` for sort-0 binders) was rejected — it allocates a
  universe variable and so collides with A-2's gate; refusing is the
  only resolution that discharges both.

Pinned by `saw-boundary/goal_sort_binder_rejection/{sort0,sort1}_binder`.
Measured cost: zero — the full suite's known-gap count was unchanged
across the change (71 before, 71 after), because specialization
monomorphizes goals and the shape is reachable only from
hand-written `parse_core`.

### The second goal-shape rule — gate 3 (added 2026-07-30)

> **A goal telescope may not take a PROPOSITION whose domain mentions
> the `Except String` value carrier.**

Same home, same refuse-only discipline, third gate:
`leanExceptCarriedGoalBinders`. What it closes is **W2-UNRUN-1**, a
CRITICAL raised by the wave-2 audit, wrongly recommended for
retraction by me when I could not reproduce it, and reproduced by
wave 3 from ordinary Cryptol.

The shape: `sequentToProp` folds a `goal_cut` hypothesis into the
SAWCore arrow chain, and the emitter carried it into the Lean
statement as a binder whose domain is
`@Eq (Except String Bool) (…saw_throw_error…) (Pure.pure true)`.
SAW's vectors are lazy, so an erring element in an unforced slot
leaves the hypothesis TRUE; the Lean carrier is eager, so the same
hypothesis's image is `Except.error _ = Except.ok _` — uninhabited by
constructor no-confusion. The implication is therefore vacuously
provable and the Lean theorem is strictly WEAKER than the obligation.
**This is an emission-path defect**: a user of emission-only
`offline_lean` who discharges the goal in Lean has proven nothing,
with no replay involved.

Two distinctions the gate must make, both learned by getting them
wrong first:

- It exempts **value images**. A domain whose final codomain is
  carrier-headed (`Except String Bool`, or
  `Except String Bool -> Except String Bool` for a SAWCore
  `Bool -> Bool` binder) is the faithful image of something the goal
  quantifies over; it ranges over MORE inhabitants than the SAWCore
  type, so the statement is stronger, not weaker. The first cut
  refused these.
- It descends through the P-1 `let`. A share arising in the outermost
  binder's domain hoists above the whole Pi, so a spine walk stopping
  at the first non-Pi sees nothing. The first cut stopped there,
  leaving that class covered only by the arity half — accidentally.
  (Lets are not universally outermost: `translateTermLetAt` runs at
  every level, so `Pi … (Let …)` is the common emitted shape.)

**Residual, stated because the gate does not check it:** the test is
for the carrier, not for uninhabitedness. A raw uninhabited hypothesis
domain (`@Eq Bool Bool.false Bool.true`) emits past this gate. That is
faithful — a raw domain means the same thing on both sides, so the
SAWCore obligation is equally vacuous — but the safety of that class
rests on "raw implies faithful" as an argument, not as a mechanism.

Pinned by `saw-boundary/goal_except_carried_binder_refusal`
(error-free probe for the shape, erring probe for the ordinary-Cryptol
route; both refuse on the shape alone, so they are two instances of
one property, not two properties).

**Historical text follows, retained as the record of what was
believed:** the gate checked both Pi and Lambda binders for sort
`k ≥ 1`, pinned by a smoketest for the Lambda-side case.

The Lambda-side check is defensive (post-`scNormalizeForLean`
type terms shouldn't contain unreduced Lambdas), but covering
hand-constructed SAW terms that circumvent normalization or future
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
