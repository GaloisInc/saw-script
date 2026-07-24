# OP-3 successor design: bounded-iteration lowering for productive fix

**Date**: 2026-07-15. **Status**: AUDITED (fourth independent audit,
2026-07-15): **implementable with named amendments** — the first
OP-3 design to survive audit. The six amendments in the audit record
below are BINDING on the implementation; amendments A and D are
load-bearing.
[R4 LANDED 2026-07-16 — all slices R0–R4 complete; the wrapped
unique-fixed-point contract is retired and both class realizations
are live. This doc is the audited design + execution record.]

Successor to the REFUTED structural draft
(`archive/2026-07-12_op3-structural-fix-design.md`, kept as the
rejected-candidate record); implements
`2026-07-12_obligation-placement-design.md` §Instance 3's two-part
fix under the STRUCTURAL-FIRST entry decision. 0.02 W1 headline
(`2026-07-14_release-plan.md`).

## The six minimum conditions (third audit), restated as obligations

1. Match the ACTUAL normalized shapes: the recursive vector flows
   through `zip` (`at n (PairType …) (zip … rec xs) idx`), and the
   `[seed] # [comprehension]` shape nests
   `at (gen K (\i'' -> … rec …)) (i-1)` — never bare `at rec j`.
2. Reproduce SAW's LAZY selection (`at (gen K g) j = g j`): no
   strict intermediate gen/zip builds — a strict `Vector.ofFnM`
   prefix build forces later-index references and errors on every
   productive element (kernel-checked in the third audit).
3. The recursive handle must be the FULL wrapped vector (the body
   binds it whole: `Bind.bind rec (fun v => … zip … v …)`).
4. Preserve `atWithDefault` defaults (OP-2 binding condition 1).
5. No novel error strings outside SAW's divergence region (OP-2
   binding condition 2).
6. Decide the stream rows' fate BEFORE touching the wrapped
   contract: `rec_ones`/`stream_fibs` are wrapped-contract Stream
   rows; ChaCha20-iterate is on the RAW fix path.

## Design in one paragraph

A conservative, syntactic PRODUCTIVITY RECOGNIZER (gate) classifies
each wrapped `Prelude.fix` body. Recognized FINITE bounded-lookback
bodies lower to a Kleene bounded-iteration construction
`saw_fix_bounded`: iterate the UNTOUCHED translated body n times
from a pure default seed — the body itself is never rebuilt, so
conditions 1-3 hold by construction, and seed-independence of
stabilized prefixes (proved in Lean, once, as library lemmas) gives
the lazy-selection faithfulness that strict prefix-building lacked.
Recognized STREAM corecursion (single-step lookback over `[inf]`)
lowers through the existing MkStream pointwise realization
(`saw_stream_unfold`, the `iterate f x = MkStream (fun n => f^n x)`
family — the retired May parametric-bridge semantics, revived as
checked defs). EVERYTHING ELSE REJECTS with a named diagnostic —
including the audit's Bool divergence witness verbatim. The
`saw_fix_unique_exists` contract is then RETIRED (no emitter), not
revised: no fixed-point predicate can express productivity
(§Instance 3's general lesson), so nothing may emit it.

## Part 1 — the recognizer (gate b, mandatory)

Haskell decides ACCEPT-with-declared-lowering vs REJECT; it never
rewrites the body or proves anything (backend-minimality preserved).
Recognized classes, deliberately narrow:

**Class F (finite bounded-lookback).** The translated body has the
shape the corpus actually produces (condition 1):
`\rec -> <appendShape>` where every occurrence of `rec` in the body
is (i) bound whole (`Bind.bind rec (fun v => …)`, condition 3) and
(ii) consumed only under the append-shifted index family — the
compiled `[c] # [ f | x <- xs | p <- rec ]` pattern where element
`i` of the result reads `rec` only at indices `< i` (in the corpus:
through `at (gen K g) (i-1)` after the append shift, including the
zip-mediated form). The recognizer checks the SOURCE-side fix
argument shape (SAWCore term structure: `append (single c)
(gen n (\i -> body_elt))` with `rec` references inside `body_elt`
occurring only under the shifted projection of the zip/gen family),
NOT the emitted Lean. Anything with a non-shifted index, a computed
index the recognizer cannot bound, multi-step lookback, or `rec`
consumed outside the append arm → REJECT.

**Class S (stream single-step corecursion).** Same append shape at
`Stream` type (`[c] # [ f | p <- rec ]` over `[inf]`), plus the
`iterate`-compiled `fix (\rec -> MkStream-headed …)` family. Lowered
via MkStream index realization (Part 3).

**Reject set.** Everything else, with diagnostic
`unrecognized fix shape: <reason>` naming which condition failed.
Litmus rows: the Bool witness `fix Bool (\b -> ite Bool b True
True)` verbatim; a two-step-lookback comprehension; a fix whose rec
occurs outside the append arm. All expected-rejection rows in
`saw-boundary/`.

## Part 2 — Class F lowering: `saw_fix_bounded`

Support-library definition (names bikesheddable):

```lean
/-- n-fold iteration of the translated fix body from a pure seed. -/
def saw_fix_bounded (n : Nat) (α : Type) [Inhabited-free default d]
    (body : Except String (Vec n α) → Except String (Vec n α))
    : Except String (Vec n α) :=
  Nat.rec (pure (Vector.replicate n d)) (fun _ acc => body acc) n
```

(AMENDED per fourth audit B: `d` is a DISCARDED iteration seed — a
seed-independent placeholder, not an `atWithDefault` default; the
real bodies read the recursive vector through checked/runtime-checked
access, which has no default. Condition 4 is satisfied for free
because the body is untouched. The emitter supplies any convenient
total placeholder element explicitly; no Inhabited machinery.)

Key properties, proved ONCE in Lean as library lemmas (this is the
faithfulness core — the fourth audit should scrutinize exactly here):

- **L1 (stabilization).** For a body whose element `i` depends only
  on elements `< i` of its argument (stated semantically as a
  hypothesis `H_prod` on the Lean side, discharged per-instance by
  `rfl`-class unfolding of the concrete body):
  `∀ k > i, (saw_fix_bounded-iterates k).get i` is constant in k and
  seed. Formally: `bodyIter (i+1) s₁ =ᵢ bodyIter (i+1) s₂` at all
  indices `≤ i`.
- **L2 (pure survival).** Under `H_prod` with total element
  functions, `saw_fix_bounded n α d body = pure v` for a concrete
  `v` given elementwise success (the analog of
  `vecSequenceM_ok_of_get`) — errors are neither manufactured nor
  dropped: if any element computation errors at its own index, the
  iterate errors exactly there (condition 5: the error strings are
  the body's own).
- **L3 (unfolding agreement / the SAW link).** `body
  (saw_fix_bounded n α d body) = saw_fix_bounded n α d body` under
  `H_prod` — i.e. the construction IS a fixed point of the body.
  This is the statement that ties to SAW's only spec for `fix`
  (`fix_unfold`): SAW's `fix body` and `saw_fix_bounded` are both
  fixed points, SAW's lazy evaluation computes elementwise exactly
  the stabilized values (trust links: Cryptol productivity +
  scNormalize preservation, per the residual-trust catalog — named,
  not manufactured), and L1 pins the elementwise values uniquely
  for bounded-lookback bodies.

Emission: the translator emits `saw_fix_bounded n α d
(translated-body-verbatim)` — the body is the SAME term the current
lowering produces as the contract's body argument (conditions 1-3
free of charge: we never decompose it). NO obligation is emitted.
Discharge of the acceptance goals then proceeds by unfolding
`saw_fix_bounded` (a computable Nat.rec) plus the L-lemmas.
(AMENDED per fourth audit F: running_sum's spec side is an unrolled
bvAdd chain, NOT a foldl — the parked `foldl_eq_natRec_atWithDefault`
bridge is the wrong connector there; the discharge path is
elementwise gen-of-pure characterization lemmas. The foldl bridge
may still serve popcount's fold-side spec.)

**Why this evades the third audit's refutations.** The refuted draft
REBUILT the body as a strict per-element prefix construction —
wrong shapes (condition 1), strict forcing (condition 2), per-index
handle (condition 3), dropped defaults (condition 4), novel error
strings (condition 5). `saw_fix_bounded` rebuilds NOTHING: the body
is applied whole, n times. Laziness objection (condition 2) becomes
L1: strictness of intermediate iterates is harmless because iterate
k+1 only trusts prefix ≤ k of iterate k, which is already
stabilized-pure; the audit's every-element-errors scenario cannot
arise from a PURE seed (that scenario required the error-seeded
prefix build).

## Part 3 — Class S lowering: streams

(AMENDED per fourth audit D: `stream_fibs` emits a MUTUAL
paired-stream fix — `fix (PairType (Stream X) (Stream X)) …` — and
does NOT fit the single-stream form; it gets its OWN disposition:
either a paired-stream extension of Class S in a later slice, or an
explicit named REJECT with its module row re-pinned as a boundary
until then. Do not pair it with rec_ones in the ladder.)

`rec_ones`/`iterate`: lower to
`MkStream (fun idx => <elementwise closed form via bounded lookback
from index 0>)` — concretely `saw_stream_unfold : (α → α) → α →
Stream α := fun f x => MkStream (fun n => Nat.rec x (fun _ a => f a) n)`
for the iterate family, and the single-step append form as its
special case. This is the pointwise realization the existing
`saw_mkStream_total_exists` machinery already contracts for; no new
trust class. The Stream@core boundary rejections (the ChaCha20 pair,
`polymorphic_seq_module_rejection`'s stream half) re-open AFTER
Class S lands: their recursor-convention hole (raw result demanded
from Except-wrapped scrutinee) is a separate item this design only
UNBLOCKS, tracked as the ladder's step 5 — this doc does not claim
it.

## Part 4 — retirement and migration

- `saw_fix_unique_exists` loses its last emitter → deleted with its
  choose lemmas (`saw_fix_choose`); `obligations/fix_wrapped_unique`
  re-pins as a Class-F structural emission row;
  `saw-boundary/fix_obligation` family re-pins on the new
  diagnostics. The raw fix contract (`saw_fix_unique_exists_raw`)
  is explicitly untouched (per Instance 3) and ChaCha20-iterate's
  raw-path fate rides Class S + the recursor-convention follow-up.
- Acceptance ladder (in order, each a commit-gated slice):
  `cryptol_running_sum_verify` discharges end-to-end →
  `offline_lean_popcount32` + E6 → `llvm_popcount_eq` →
  `rec_ones`/`stream_fibs` module rows → Stream@core/Either@core
  path re-opened → `rev.cry` module translation (demo step 3).
- Litmus/negative rows land in the SAME slice as the recognizer
  (gate before lowering).

## Questions the fourth audit should scrutinize

1. Is L1's per-instance `H_prod` discharge (`rfl`-class unfolding of
   the concrete body at each index) actually closable for the
   running-sum body without heartbeat inflation, or does it need
   per-shape lemmas the library lacks?
2. Does the pure-seed iterate REALLY avoid the strict-forcing trap
   for the zip-mediated shape — i.e., is `bodyIter 1 (pure default)`
   elementwise-pure for the REAL running_sum body (whose element
   binds go through `Bind.bind rec`), or does some element of
   iterate 1 error on the default prefix in a way L2's hypothesis
   cannot exclude?
3. Is the recognizer's source-side shape check implementable without
   emitted-Lean inspection and without false ACCEPTs on computed
   indices (the calculus's never-classify-by-emitted-AST rule)?
4. Does the default `d` threading violate condition 4 in bodies
   whose own `atWithDefault` default differs from the
   comprehension's seed element?
5. Is condition 6 fully satisfied — do `rec_ones`/`stream_fibs`
   actually fit Class S's single-step form, or do they need the
   append-at-Stream shape the recognizer must treat separately?
6. Trust-link honesty: does L3's argument add any trust NOT already
   in the residual catalog?


---

## Fourth-audit record (2026-07-15) — binding amendments

Verdict: implementable with named amendments. Key confirmations: the
pure-seed iteration of the untouched strict body IS sound for the
running_sum/popcount class (hand-traced 2-element analogue; the
third audit's error-overriding cannot arise from a pure seed with
total element functions); off-by-one is correct but zero-slack
(element n-1 stabilizes exactly at iterate n).

Binding amendments:

- **A (soundness hinge).** `H_prod` — including element-function
  TOTALITY over the seed — must be a PROVEN per-instance Lean
  obligation, not a recognizer assertion. Witness: a body indexing
  `xs` by the recursive VALUE (`ys = [1] # [ xs @ prev | prev <- ys
  | x <- xs ]`) passes the syntactic single-step gate but errors
  under iteration from a bad seed — loud, not unsound, but it
  re-creates the undischargeable disease. Proving H_prod per
  instance turns the retired residual-trust §3.2 silent-unsoundness
  class into loud incompleteness.
- **B.** Prove the count lemma (n applications stabilize element
  n-1); recognizer verifies seed length = 1; the d-sourcing
  narrative corrected in place (above).
- **C (soundness).** The recognizer must pin the lookback shift to a
  CONSTANT -1 (a same-index body would stabilize to a pure value
  while SAW diverges — unsound) and pin the zip operand/projection
  order to the rec slot; computed/unbounded indices reject.
- **D (coverage, load-bearing).** stream_fibs disposition (above);
  without it, retiring the contract strands that row with no
  lowering.
- **E (process).** Reconcile `saw_fix_bounded`/`saw_stream_unfold`
  with the obsolete-helper scan in `lean-driver-test.sh` — they are
  textually new but categorically the "structural fix helper" the
  scan enforces the retirement of; the scan's list and the
  residual-trust catalog must be updated TOGETHER with the design's
  landing, not silently circumvented by the rename. Add
  `cryptol_module_popcount` to the golden re-pin list (eight
  wrapped-contract goldens total).
- **F (trust honesty).** Residual-trust §3.2 must be RE-OPENED as a
  live catalog item (this design deliberately revives a retired
  strategy, with amendment A as the new mitigation); L3's SAW-link
  is genuine live residual trust and is catalogued as such, not
  claimed pre-existing.

Implementation may begin only with amendments A-F incorporated into
the slice plan; A and D are load-bearing.

---

## Implementation slice plan (post-audit, amendments A-F binding)

Each slice is emitted-Lean-diff-reviewed and fence-green before
commit, per house rules.

- **Slice R0 (inert recognizer).** The productivity recognizer as a
  classifier + trace only (`SAW_LEAN_TRACE_FIX_CLASS`): classifies
  every wrapped-fix body Class F / Class S-single / Class S-paired /
  UNRECOGNIZED per the amended rules (constant -1 lookback pinned,
  rec zip-slot pinned, seed length 1 verified — amendments B/C);
  emission unchanged (byte-identical corpus). Trace sweep must
  classify all 8 wrapped-contract goldens as expected (running_sum,
  popcount32, E6, module popcount F; rec_ones S-single; stream_fibs
  S-paired; fix_wrapped_unique F; + the smoketest shapes).
- **Slice R1 (library).** `saw_fix_bounded` + the count lemma
  (n applications stabilize element n-1) + L1/L2 with `H_prod`
  stated as the PER-INSTANCE obligation interface (amendment A) +
  `#guard_msgs` self-tests. SAME COMMIT: obsolete-helper-scan
  reconciliation (the scan's list gains a comment naming
  `saw_fix_bounded`/`saw_stream_unfold` as the SANCTIONED successors
  under amendment-A mitigation; residual-trust §3.2 re-opened as
  live with the new mitigation recorded — amendments E/F).
- **Slice R2 (Class F swap + acceptance).** Emission flips for
  Class F: `saw_fix_bounded` + the emitted per-instance `H_prod`
  obligation replaces the contract emission. Goldens re-pin
  per-hunk (running_sum, popcount32, E6/e_series, module popcount,
  fix_wrapped_unique re-pins as structural row). ACCEPTANCE GATE:
  `proof-gaps/cryptol_running_sum_verify` discharges end-to-end
  (H_prod by unfolding + elementwise gen-of-pure lemmas + unrolled
  bvAdd spec side) and moves to `proofs/`. If the discharge stalls
  on heartbeats, the slice does NOT land (no-heartbeat-bump rule) —
  back to lemma design.
- **Slice R3 (Class S).** `saw_stream_unfold` + rec_ones emission
  flip + the iterate family; **stream_fibs: explicit REJECT with
  named diagnostic + its module row re-pinned as a boundary**
  (amendment D — paired-stream lowering is a separate later design,
  not introduced in here).
- **Slice R4 (retirement).** `saw_fix_unique_exists` + choose
  lemmas deleted (no emitter remains); smoketest fix cases
  re-pointed; TODO/STATUS/CONFORMANCE sync; the OP-3 census tier
  updated. Litmus negative rows (Bool witness, two-step lookback,
  same-index, computed-index, rec-outside-append) land in R0/R2 as
  their gates activate.
- **After R4** (separate program): the Stream@core/Either@core
  recursor-convention re-open (ladder step 5) and the rev.cry
  module-translation acceptance (step 6).

## Slice R0 implementation record (2026-07-15)

R0 landed as `classifyFixShape` in `SAWCoreLean.Term` (pure classifier
+ `SAW_LEAN_TRACE_FIX_CLASS` trace hook at the `Prelude.fix` dispatch;
nothing in emission reads the verdict). Three findings from tracing
the real corpus, binding on R1+:

1. **The normalized Class-F shape is FUSED, not append-headed.** The
   design above describes Class F as `\rec -> append [seed] (gen k
   elt)`; `scNormalizeForLean` folds that append away. What actually
   reaches the translator is
   `\rec -> gen N a (\i -> ite a (ltNat i 1) <seed, rec-free>
   (at K a (gen K a (\i2 -> elt)) (subNat i 1)))` — the constant -1
   shift (amendment C) lives at the tail BRANCH, so inside `elt` the
   recursive vector is read at the INNER binder exactly (`rec[j]`
   with `j = i-1 < i`). The recognizer matches this fused form; all
   five corpus Class-F goldens (running_sum, popcount32, e_series,
   module popcount, llvm_popcount) classify F under it. R1's
   `saw_fix_bounded` count lemma must be stated against the fused
   shape.
2. **Scan discipline tightened (audit-grade).** A rec-containing
   `at`-selection admits ONLY the bare recursive vector or zip slots
   beneath it — blessing the whole spine would classify
   `at (reverse rec) i2`, which flips the lookback direction
   (silently unsound if R2 activated it). Smoketest pins this
   negative (`index-permuting wrapper on the rec spine`), plus
   same-index tail, two-step lookback (`subNat i 2`), `atWithDefault`
   (out-of-family selector), rec-free element, non-gen body, and the
   Bool witness.
3. **Corrections to the R0 golden expectations.** Paired-stream fixes
   arrive at the sort-1 spelling `Prelude.PairType1` (not
   `Prelude.PairType`) — stream_fibs classifies S-paired only with
   both spellings accepted. And `obligations/fix_wrapped_unique` is a
   **Bool-typed witness → UNRECOGNIZED** (the slice-plan line calling
   it "F" was wrong); it is the litmus negative, exactly as the R2
   structural re-pin expects.

Verdict sweep (8/8 as amended): running_sum, popcount32, e_series,
module popcount, llvm_popcount → `FixClassF`; rec_ones →
`FixClassSSingle`; stream_fibs → `FixClassSPaired`;
fix_wrapped_unique → `FixUnrecognized` (Bool witness). Gates:
smoketest 67/67 (9 new classifier cases), corpus emission
byte-identical vs `.snapshots/op2-baseline`, full conformance green.

## Slice R1 implementation record (2026-07-15)

Library + lemmas landed; still NO emitter consumer (that is R2).

* Definitions (SAWCorePrimitives): `saw_fix_bounded_iter` (graded
  iterates from the pure discarded seed), `saw_fix_bounded` (the
  `n`-th iterate), `saw_fix_bounded_productive` (H_prod as a
  two-field Prop structure: `total` + `lookback`, both PROVEN per
  instance — amendment A). Three `#guard_msgs` self-tests: a
  concrete -1-lookback recurrence stabilizes to `[1,2,3]` from seed
  0 AND from seed 999 (condition 4 witnessed computationally), and
  an erroring body propagates its OWN error string (condition 5).
* Lemmas (SAWCorePreludeProofs), all conditional on H_prod only:
  `saw_fix_bounded_iter_pure`; `saw_fix_bounded_iter_stable` (L1
  master form: ANY two iterates past index `i`, even from different
  seeds, agree at `i` — strong induction on `i`);
  `saw_fix_bounded_pure` (L2); `saw_fix_bounded_seed_irrelevant`
  (condition 4); `saw_fix_bounded_fixed_point` (L3, the SAW link);
  PLUS `saw_fix_bounded_unique_pure_fixed_point` — uniqueness among
  pure fixed points is now a THEOREM (strong induction via lookback),
  which is exactly the honest strengthening the retired
  `saw_fix_unique_exists` contract assumed as a side condition. The
  audited hole (`project-op3-pure-uniqueness-hole`: divergent fixes
  admitted by uniqueness-among-pure-fixed-points) is closed the right
  way round: a divergent body simply has no H_prod proof.
* Axiom audit: all five lemmas depend on `propext` (+`Quot.sound`)
  only — no `Classical.choice`, no vec↔BitVec axioms.
* Amendment E: the obsolete-helper scan in `lean-driver-test.sh`
  now carries the sanctioned-successor comment (saw_fix_bounded /
  saw_stream_unfold must NOT join the forbidden list at R2/R3).
* Amendment F: residual-trust §3.2 re-opened as LIVE with the
  proof-carrying mitigation recorded; remaining trust decomposes into
  `fix_unfold` + §3.3 normalization preservation — no new class.

## Slice R2 implementation record (2026-07-15) — ACCEPTANCE GATE GREEN

Emission flipped for Class F, and `cryptol_running_sum_verify`
discharges END-TO-END: `proofs/cryptol_running_sum_verify` passes the
full harness (drift-check against the generated goal, elaboration,
sorry scan, axiom audit) in ~2.5 s wall clock — no heartbeat
inflation, answering audit Question 1 affirmatively. The row
graduates out of `proof-gaps/`; the census's
sound-but-undischargeable tier loses its first member.

**R2 amendment (placeholder location).** The fourth-audit `d : α`
emitter-supplied placeholder is NOT generically obtainable at
emission time: translated vector ELEMENTS are wrapped
(`Except String α`), so no raw `α` value exists to hand the
realization. The placeholder moves INSIDE the proven obligation:
`saw_fix_bounded_productive` gains a `seed : Nonempty (Vec n α)`
field, and emission targets the noncomputable
`saw_fix_bounded_choose n α body h` (iterates from
`Classical.choice h.seed`) — the same choice discipline as the
retired `saw_fix_choose`, but from an obligation every field of
which is PROVEN. `saw_fix_bounded_choose_eq_bounded` exchanges it
for the computable iterate at any placeholder; seed-irrelevance is
`saw_fix_bounded_iter_from_seed_irrelevant` (stabilization is proved
over iterates from ARBITRARY seed vectors — the `iter_from` family).

**Emission shape** (`lowerClassFBounded`, mirrors the retired
contract emission exactly):
`let fix_body_ := <body verbatim>; let h_fix_prod_obligation_ : Prop
:= saw_fix_bounded_productive n α fix_body_; let h_fix_prod_ := (by
sorry placeholder); saw_fix_bounded_choose n α fix_body_ h_fix_prod_`.
Unrecognized shapes keep the OLD unique-contract emission untouched
(R4 retires it).

**Discharge pattern** (the reusable recipe, in
`proofs/cryptol_running_sum_verify/completed.lean`):
1. name the emitted body (`rsBody`, definitionally the emitted
   lambda — drift-check-safe), state the one-step characterization
   `rsBody (pure x) (pure v) = pure (rsStep x v)` via the NEW library
   lemmas `genWithBoundsM_eq_ok` / `atWithProof_gen_ok` /
   `iteM_pure_true/false` (SAWCorePreludeProofs);
2. H_prod: `seed` by replicate; `total` by the characterization;
   `lookback` by `Vector.getElem_ofFn` + the prefix hypothesis at
   `i - 1`;
3. closed form (`rsSol`, the prefix-sum chain) is a fixed point —
   with concrete `n` this collapses DEFINITIONALLY (`congr 1`);
4. `saw_fix_bounded_choose_unique_pure_fixed_point` pins the emitted
   realization to `pure rsSol` — no 9-fold iteration in the proof;
5. numeral normalization (`natPos_macro` chains → literals via
   `Nat.reduceMul/Add` simprocs) BEFORE any simp-rewriting — the
   discrimination trees cannot see through the macro chains;
6. final seam: `bvAdd_id_l` (the spec's chain lacks the leading
   `+ 0`) + `bvEq_refl`.

Axioms: standard trio + the two vec↔BitVec round-trips only.
Goldens re-pinned: running_sum, popcount32, e_series (E6), module
popcount, llvm_popcount — snapshot diff confirmed exactly those five
artifacts changed; conformance exit 0; smoketest 67/67; baseline
re-cut at 311. Remaining R2 ladder (popcount32 + E6 → llvm_popcount_eq
gap rows) proceeds on this recipe; then R3 (Class S) and R4
(retirement of `saw_fix_unique_exists`).

## Slice R3 pre-slice concretization (2026-07-15) — for audit before R3 lands

Corpus facts (traced with `SAW_LEAN_TRACE_FIX_CLASS`):

* **rec_ones (S-single).** Body =
  `\rec -> MkStream Bool (fun i => atWithDefaultM 1 Bool
  <rec-read through Stream.rec at (subNat i 1)>
  (vecSequenceM 1 #v[pure true]) i)` — literal seed of length 1,
  tail reads the recursive stream at the constant -1 shift, no
  transformation applied (`f = id`). Today's emission carries a
  DOUBLE by-sorry obligation (`saw_mkStream_total_exists` +
  `saw_fix_unique_exists`) — the successor collapses both.
* **stream_fibs (S-paired).** Fix at
  `PairType1 (Stream (Vec 32 Bool)) (Stream (Vec 32 Bool))`, body a
  `PairValue1` of two `MkStream`s each reading both components via
  `PairType.rec`. Amendment D holds: own disposition, R3 REJECTS.

R3 plan, in slice order:

1. **R3a (recognizer hardening, inert).** `classifyStreamBody`
   currently accepts ANY MkStream-headed body as S-single — too lax
   to gate an emission flip. Extend to verify the canonical
   single-step shape: seed literal of length exactly 1 (amendment B
   analog), tail reads `rec` ONLY through the stream accessor at
   `subNat i 1` (amendment C analog), any elementwise step function
   captured syntactically as a RAW term. Anything else →
   Unrecognized. Same gates as R0 (byte-identical emission, trace
   sweep, smoketest cases incl. a two-step-lookback stream negative).
2. **R3b (realization).** The recognized shape is productive BY
   CONSTRUCTION: realize as
   `MkStream a (fun n => Nat.rec x0 (fun _ prev => step prev) n)`
   with `x0`/`step` from the recognized shape. ONE per-instance
   PROVEN obligation replaces today's two: the emitted wrapped
   element function at pure inputs equals `pure ∘` the raw
   realization elementwise (amendment-A discipline — H_prod-stream).
   The SAW link mirrors L1/L3: stream elements pinned by strong
   induction on the index; uniqueness among realized streams is a
   theorem. Acceptance gate: the rec_ones module row's obligations
   close for real (no by-sorry residue in its discharge tier).
3. **stream_fibs reject.** `FixClassSPaired` → named
   `RejectedPrimitive` diagnostic ("paired-stream mutual corecursion
   is not realized; amendment D"); module row re-pins as a
   saw-boundary expected rejection.

SCOPE NOTE for the auditor: R3b extracts a RAW step function from
the wrapped element body. This is claimed ONLY for the corpus
S-single shape (pure -1 lookback, rec_ones). Whether the extraction
generalizes to the iterate family (ChaCha20-core's
`saw_self_ref_comp_iterate` territory) is explicitly OUT of R3 —
that question rides the post-R4 flagship, and a false generalization
here would be the same silent-unsoundness class the third audit
killed. Reject-when-unsure stands.

## R2 ladder record (2026-07-15) — popcount32 + E6 GREEN; llvm_popcount re-characterized

`proofs/offline_lean_popcount32` (W=32/N=33) and
`proofs/E6_popcount_bridge` (W=3/N=5) discharge end-to-end on the R2
recipe + one new library lemma (`iteM_ok_ok`, the value-level-bit
conditional). Axioms: propext/Classical.choice/Quot.sound only — the
popcount rows do not even need the vec↔BitVec round-trips. Harness
11 s / 5 s. `proof-gaps/offline_lean_popcount32` retired.
`proof-gaps/llvm_popcount_eq` is NOT a recurrence gap anymore: its
GAP.md now records that the fix side discharges by this recipe and
the residue is the SWAR (Hacker's Delight) correctness theorem
`bvEq 32 (swar x) (pcChain x 32)` for symbolic x — a W2
masked-partial-sum lemma-family item, not an OP-3 item.

Recipe deviations (binding on future discharges):

1. Numerals-first applies INSIDE the body characterization lemmas
   too, not only in `goal_holds` — keyed matching never sees through
   the reducible macro chains.
2. `zip` selection at K=32: `simp [zip, Vector.get]` whnf-times-out,
   and `zip_getElem_lt` will not fire because its collection length
   is `Nat.min m n` while the goal's getElem instance carries the
   reduced literal. Pattern: a `have` restating the selection with
   the literal-length `@GetElem.getElem` instance, proved by
   defeq-coercion from `zip_getElem_lt`, then `rw`.
3. The `congr 1` definitional close of the fixed-point lemma is
   size-fragile (hit whnf heartbeats at N=33). The stable form is
   `congrArg` + `Vector.ext` + per-index cases — use it by default
   for N beyond single digits.
4. foldl spec sides connect via `foldlM_pure_eq_foldl` (hStep =
   `cases a <;> rfl`) and `foldl_eq_natRec_atWithDefault`, each
   applied through a `have` that restates the lambda with
   post-normalization literals; a local `Nat.rec = chain` induction
   (`rw [← ih]; rw [← atWithDefault_lt]`) closes the bridge.

## Fifth-audit record (2026-07-15) — R3b Class-S concretization: implementable WITH AMENDMENTS

Independent audit of the R3 pre-slice concretization (independent
auditor; checks 1-6). Verdict: the realization + single-obligation
core is SOUND for the identity step (rec_ones); NOT implementable as
written because the R3a recognizer as first coded was strictly looser
than the validated lowering — the structural draft's
gate-broader-than-lowering failure mode. BINDING amendments:

1. **(Load-bearing; APPLIED in R3a before it landed.)** The stream
   step must be the IDENTITY read exactly (`s (subNat i 1)`, nothing
   around it). A wrapping transformation (`f (s (i-1))` — the iterate
   family) is raw at the SAWCore layer the recognizer sees, but its
   Lean translation may be Except-valued (`xs @ prev`, checked
   division — the amendment-A witness class); no raw step exists to
   extract. `isIdentityStreamRead` replaces the too-loose
   `scanStreamStepUses`; iterate-family bodies reject with a named
   diagnostic. The raw-total-whitelist + step-extraction
   generalization is the post-R4 iterate program.
2. **(Load-bearing.)** R3b's single obligation is
   `∀ i, mkfn (pure (MkStream g)) i = pure (g i)` where `mkfn` is the
   VERBATIM Except-valued emitted element function and
   `g = Nat.rec x0 (fun _ prev => prev)` — never a raw-simplified
   copy, and pinned at the realization input, not "pure inputs"
   generically. NOTE for §3.2: the stream `total` analog is VACUOUS
   (Stream sits raw inside Except; the element read is
   unconditionally pure) — the loud-failure mitigation for Class S
   rests on this elementwise equation alone, not on totality.
3. Uniqueness must be stated among TOTAL realized streams by index
   induction (not bare fixed-point existence); its SAW-total premise
   is licensed only under amendment 1. The emitted value is the
   realization DIRECTLY (no choose among fixed points), so error
   fixed points of the wrapped body cannot infect it.
4. Boundary regression: sha512_fix and the ChaCha iterate/iround
   pair are confirmed rejected at EARLIER gates (their existing
   boundary/stretch rows are the regression pins). The synthetic
   `f≠id` negative cannot be unit-tested cheaply (recursor
   construction) and is DEFERRED to R3b as an end-to-end
   expected-rejection golden row (an iterate-shaped Cryptol module
   pinning the "not the identity read" diagnostic through the real
   pipeline) — stronger than a unit test, and only observable once
   the flip makes the verdict live.
5. `saw_mkStream_total_exists`/`saw_mkStream_choose` MUST survive
   R3/R4: six non-fix MkStream sites emit them (module simple map ×2
   + five obligations rows). rec_ones loses its mkStream obligation
   under the flip; no blanket removal. (Audit also confirmed
   rec_ones's current inner mkStream obligation is genuinely
   unprovable as stated — quantified over error handles — which is
   why the double stub exists; collapsing it is correct, not
   cosmetic.)

## Slice R3a implementation record (2026-07-15)

Landed with amendment 1 already applied: `classifyStreamBody` now
verifies the FULL canonical single-step shape (MkStream head → seeded
`atWithDefault` with literal length-1 rec-free seed → selection at
the MkStream binder → tail a `Stream.rec` elimination whose scrutinee
is exactly the recursive binder, rec absent from motive/case →
case body exactly the identity read at the constant -1 shift).
API note: `asRecursorApp` does not include the applied scrutinee
(Stream has zero indices) — peel the scrutinee App first. Trace
sweep: rec_ones → S-single, stream_fibs → S-paired, all Class-F and
Bool verdicts unchanged. Smoketest 69/69 (lax MkStream positive
replaced by three hardened negatives: bare MkStream, two-element
seed, constant selection index). Emission byte-identical
(recognizer verdicts do not route emission until R3b); stream driver
rows exit 0; conformance exit 0.

## Sixth-audit record (2026-07-16) — strategy-level review; Finding 0 REPAIRED

Independent review of the strategy framing itself (trusted translator
+ strong obligations + audited weakening descent + minimal runway).
Overall: HOLDS-WITH-AMENDMENTS, one mandatory repair (landed:
zip-slot scan hardening, commit f2db4aeef), one mandatory addition
(fix/error differential rows — folded into the exposure batch).

* **Finding 0 (repaired same day).** scanRecUses blessed entire
  zip-operand spines; wrapped rec inside a zip slot (reverse/opaque
  wrappers) classified Class F — the provable-obligation/wrong-value
  class. The landed fused-shape Class-F grammar had never been
  independently audited (R0 self-certified it); this was the cost.
  Repair: zip operands admit exactly the bare recursive vector;
  smoketest pins both directions; corpus-inert (verified).
* **A (descent).** The descent's terminal soundness premise is the
  RECOGNIZER, not the obligations: "a divergent body has no H_prod
  proof" is false in general — forcing-invisible divergent bodies
  have provable H_prod and are excluded only by the syntactic gate.
  State it that way. Unaudited post-audit deltas are allowed only
  when obligation-strengthening or lemma-exchanged (the R2
  placeholder relocation set the precedent).
* **B (layers).** Goal formation (prop → Pi-abstraction →
  normalization → `def goal` fabrication) is a THIRD layer; its
  dangerous direction (goal trivialization) is silent and
  differentially untestable; the 0.01 admitting-exporter bug lived
  there. Defenses: export-only boundary row, drift check, fails
  plumbing pins — named, not loudness-protected.
* **C (asymmetry).** Obligation strength and SAW-link sufficiency
  are orthogonal axes; "too strong ⇒ visible" holds on the value
  axis only — the forcing axis is guarded by the gate, whose bugs
  are silent. Visibility is a property of the corpus PROCESS
  (proofs tier + axiom audit), not of emission alone.
* **D (runway).** "Two-state fix story" holds for WRAPPED fixes
  only: the raw contract (saw_fix_unique_exists_raw) survives R4 by
  design — believed corpus-unreachable, must stay census-checked.
  R4's catch-all reject is designed, not yet implemented. Replay
  (0.02 W3) must treat sanctioned in-goal `by sorry` placeholders
  explicitly (defeq-modulo-placeholder-fill).
* **E (triggers).** "Another seam audit finding" fired WITH THIS
  AUDIT. The audit-scheduled trigger is otherwise structurally dead
  post-R4; replacements that fire autonomously: fix/error
  differential rows (land with the exposure batch) + an upstream
  tripwire expectation on Simulator/Prims.hs fixOp and
  Value.hs VVector (§3.2a says "re-verify if the simulator
  changes"; the rows are the watcher). R3b/R4 flips get an
  emitted-Lean-diff review by a non-implementer.
* **F (history).** "Six theory bugs, all strategy-layer" is scoped
  to the FIX PROGRAM; backend-wide, layer-(a) bugs exist
  (pre-Phase-9 bvsmin/bvsmax under MSB-first, §1.4), historically
  caught by proof effort, not differential rows — which is exactly
  why the bvUExt/bvSExt exposure priority stands. Post-batch Zone-1
  residue (~40 names) must be stated, not implied closed.

## W2 discharge record (2026-07-16) — byte_add; technique deviations binding on future discharges

`proofs/llvm_byte_add_eq` discharges the 4001-line byte-decomposed
carry-chain goal in ~43 s (axioms: standard trio + ONE round-trip
axiom). New library: vecToBitVec_bvSShr, getElem_bvNat_zero,
vecToBitVec_zeroPadWindow32 (covers all zext8 windows AND the 0xFFFF
mask), vecToBitVec_bytePack32, atRuntimeCheckedM_ok_lt — the W2
byte-split/carry seed set. Deviations:

1. **Goal restatement over named defeq defs (the load-bearing new
   move).** The completed outline restates `def goal` COMPOSITIONALLY
   over ~12 named monadic defs (literals for macro chains, direct
   `by omega` bounds, sharing instead of the artifact's 8-fold
   inlining) — kernel-defeq to the generated goal, so the rfl drift
   check (~1 s) licenses it. A 4001-line goal discharges in a
   ~640-line outline. Supersedes numerals-first where used: a
   literal-native outline needs no macro normalization at all.
2. omega hazards (all reproduced): share partial sums as variables
   (fully-inlined carry chains time out); pre-chain divisions by 256
   (`x/65536` and `x/256/256` are unlinked atoms); GENERALIZE all
   toNat atoms to fresh variables immediately before the closing
   omega (its preprocessing defeq-compares large atoms otherwise).
3. Nat precedence trap: `x % 256 <<< 8` parses as `x % (256 <<< 8)` —
   parenthesize shifted-masked terms (produced a true-but-useless
   hypothesis silently).
4. bvSShr needed no signed-shift theory: core
   `BitVec.sshiftRight_eq_of_msb_false` + `msb_and` under an 0xFFFF
   mask suffice.
5. Slice bodies via if-guarded `atWithDefault` (total) rather than
   dependent getElem dodge dite-motive friction throughout.

## W2 record: eq_u128 discharged (2026-07-17) — drift-scaling finding binding

`proofs/llvm_eq_u128` graduates (~9-18 s wall; axioms = trio + both
round-trips). Phase G: `vecToBitVec_zeroPadWindow` generalized to
arbitrary width (32-corollary preserved; bytePack kept at 32 by
recorded scoping decision — equality decomposition needs no pack).
Crux lemma landed: `bvEq128_eq_foldr_byteEq` (foldr-AND of 16
per-byte compares = whole-width equality), via the new bidirectional
`foldr_and_gen_eq_true_iff` (seed-generalized induction — this
toolchain's `Vector.foldr_push` folds into the ACCUMULATOR) +
getMsbD extensionality with bit p ↦ byte 15−p/8 offset p%8.

**Drift-check scaling wall (new, binding on large goals):** the pure
clean-restatement move (byte_add) hits a wall at 128-bit — the rfl
reconciliation of a clean outline against the emitted macro/coerce/
re-gen tower exceeds recursion then heartbeat budgets, even though
both sides are genuinely defeq. Resolution — the HYBRID outline:
keep `def goal` byte-identical stripped-verbatim (drift instant),
then inside `goal_holds` do numerals-first simp + a `show` bridge to
the named clean defs (a cheap local defeq) + the standard `_ok`
characterization discharge. Clean restatement for goals the kernel
can whole-tower-reconcile; hybrid above that. The GAP's historical
full-tree-simp timeouts are confirmed as wrong-plan, not
wrong-budget: the same goal discharges in seconds under the
characterization route.
