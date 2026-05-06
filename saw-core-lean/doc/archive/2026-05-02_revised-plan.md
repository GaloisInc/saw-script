# Revised long-term plan

*2026-05-02 (evening) — supersedes `2026-05-02_post-audit-plan.md`.
Incorporates today's mid-Phase-5 audit findings and the Rocq parity
reframing.*

## What changed since the morning plan

Two surveys ran this afternoon:

1. **An honest project-wide audit**, asking the question "where is
   this *really*?" The audit found two material gaps where the
   project's own discipline isn't being met:
   - Phase 1a's exit criteria committed to a residual-trust catalog
     (`doc/2026-05-XX_residual-trust.md`) — the file does not exist.
     The Cryptol productivity assumption, `scNormalizeForLean`
     preservation, and SAWCore Prelude axioms-transported all live
     scattered across narrative.
   - Phase 5 Slices A and A.5 shipped today without the end-to-end
     semantic-discharge proofs the design doc explicitly named as
     "the strongest pin." `otherTests/saw-core-lean/proofs/recursion_*/`
     directories don't exist; pins are textual subset assertions in
     smoketest plus `lake build` typing — exactly the L-16-lesson
     standard.

2. **A Rocq parity framing.** Measuring the prototype against
   `saw-core-rocq` (the explicit bar) clarifies what's left:
   - We **exceed** Rocq on stream corecursion (Slices A and A.5
     translate; Rocq rejects all `fix` outright) and on
     specialization architecture.
   - We are **comparable** on refusal discipline (both reject what
     can't soundly translate; ours has more catalog rigor, theirs
     has years of maturation).
   - We are **behind** on a substantial, previously-unscoped axis:
     **Rocq's support library is *defined*; ours is mostly
     *axiomatized*.** Rocq's `gen`, `atWithDefault`, `foldr`,
     `foldl` are structural `Fixpoint`s with equivalence theorems
     to SAWCore semantics. Ours are `axiom gen : ...` etc. — they
     typecheck but don't reduce. Concrete consequence: a Lean
     downstream proof of `streamIdx allTrue 5 = true` would compute
     to `true` against Rocq's library; against ours, the user has
     to invoke `atWithDefault_gen` axiom by hand. This is a quality
     gap, not a soundness gap, but it makes our output strictly
     less useful.

The strategic implication: **the discipline plan landed, the
architecture is sound, but matching Rocq quality wasn't on the
roadmap — and it's a multi-week chunk of work that should be.**

## Cross-cutting findings

The morning plan's three findings still hold: translator core is
solid, output is hard to use, test coverage is thinner than the
status doc claimed. Today's findings refine this:

- **Translator core remains solid** — L-1..L-16 lockdown is mostly
  real and pinned (audit spot-checked five items, all verified at
  cited test paths). What was *not* closed is the discipline meta-
  layer: the residual-trust catalog and Phase 5's semantic pins.
- **The "hard to use" finding is more concrete now.** Slice A.5's
  `streamFibs.module.lean.good` is ~180 lines of nine-deep
  `@Stream.rec` chains. The output type-checks; it's
  not human-tractable as a proof goal. The design doc's
  "iota-reduction takes care of the chains" is optimistic.
- **The Rocq comparison adds a fourth finding:** axiom-only support
  library vs Rocq's defined-with-equivalence support library is the
  single biggest quality lift remaining.

## Soundness as the bar (unchanged)

The driving principle from the morning plan stays:

1. No comment-grade guarantees.
2. Every soundness claim pins a regression test.
3. Hand-maintained safety lists are last resorts.
4. Loud failure beats silent containment.

Today's findings don't weaken this — they reveal where the
discipline wasn't actually applied (Phase 1a's residual-trust doc,
Phase 5's semantic pins). The new phase 5b below closes those.

A fifth principle, surfaced by the Rocq comparison:

5. **Prefer defined functions over axioms in the support library.**
   An axiom that "matches SAW semantics" is faithful but
   computationally inert. A structural definition that's
   semantically equivalent — provably or via narrow match — gives
   downstream users a goal that *evaluates*. Axioms are reserved
   for SAW primitives whose Lean realisation must explicitly
   diverge from Lean's natives (BitVec ops on edge cases) or for
   genuinely-axiomatic SAW primitives (`unsafeAssert`, `error`,
   `coerce`).

## Phased plan

### Phase 5b — Discipline cleanup *(1-2 days, GATING)*

The reopened-Phase-1a + Phase-5-close-out work. **Nothing
downstream should claim "complete" status until this is done.**

- **L-discipline-1: Residual-trust catalog.** Write
  `doc/2026-05-XX_residual-trust.md`. Enumerate every inherited-
  trust item: SAWCore Prelude axioms transported (`unsafeAssert`,
  `error`, `coerce`), Cryptol frontend productivity (Phase 5's Link
  1), `scNormalizeForLean` semantics-preservation (Phase 5's Link
  2), `Bool#rec` direct-emission gap (currently comment-grade,
  see L-discipline-3). Cite each via file:line to where the trust
  is actually exercised. Mark items as "intentional residual" vs
  "pending gate" (the latter motivates further lockdown work).

- **L-discipline-2: Phase 5 semantic-discharge pins.** Land at
  least two end-to-end proofs:
  - `otherTests/saw-core-lean/proofs/recursion_stream_corec/` —
    discharge a property of `RecOnes`-shape output (e.g.
    `streamIdx allTrue n = true` for some concrete n, or the
    structural lemma the design doc cites).
  - TODO (audit H-2, 2026-05-06): `recursion_stream_fibs_proof/` —
    discharge a Fibonacci-recurrence property of `StreamFibs` output.
    No new home yet; H-2 tracks landing the proof.
  
  These are the L-16-lesson pins the design doc promised. If
  proofs require new helper lemmas (which they will — the existing
  axiomatic `gen_atWithDefault` etc. need to fire), record those
  needs in Phase 8's queue.

- **L-discipline-3: `Bool#rec` direct-emission gate.** L-16's fix
  only protects shapes routed through `ite`/`iteDep`. A
  `parse_core` user emitting `Bool#rec` directly silently swaps
  branches with no diagnostic. Either:
  - Reject `Bool#rec` outright at SpecialTreatment (route to a
    diagnostic explaining the user must use `ite`/`iteDep`), or
  - Implement an emission-time permutation that detects bare
    `Bool#rec` and inserts the wrapper.
  
  Pin with a smoketest constructing a synthetic SAWCore term that
  uses `Bool#rec` directly and verifying the output is correct
  (or refused).

- **L-discipline-4: Doc accuracy sweep.**
  - `README.md`: "Recursive SAWCore terms are rejected" → updated
    to reflect Slices A/A.5.
  - `2026-05-02_recursion-design.md`: `mkStreamFix` description
    matches the implementation (the design's
    `where mkStreamFixLookup` sketch is non-structural; the
    implementation uses `mkStreamFixPrefix` with `getD` indexing).
  - Phase 1a marked complete only after L-discipline-1 lands.

- **L-discipline-5: L-1 scope clarification.** The
  `polymorphismResidual` gate checks Pi binders, not Lambda
  binders (`Exporter.hs:1007-1016`). Document the invariant
  (post-`scTypeOf`, lambdas don't have sort-1 binders that survive
  unguarded). Either add a Lambda-side check or document the
  inductive argument that the existing check is sufficient.

**Exit criteria.** Every closed-completed phase actually meets its
written exit criteria. The residual-trust doc exists and is cited
from `soundness-boundaries.md` and `recursion-design.md`. Two
end-to-end recursion-discharge proofs land. README and
recursion-design.md don't lie about the current state.

### Phase 5c — Slice C: Prelude fix-users *(1-2 days)*

Mirror Rocq's `SAWCorePreludeExtra.v` hand-rewrites. Audit
`Prelude.sawcore` for `Prelude.fix` users (`streamScanl` is the
known one); mirror each in our `SAWCorePreludeExtra.lean` using
structural Lean recursion; route via SpecialTreatment. Equivalence
lemmas where Rocq has them.

Pure mechanical mirror work; not blocked on anything; can run in
parallel with 5b.

### Phase 5d — Slice B unblock *(closed by Phase 6)*

The "Cryptol-pair encoding bridge" turned out to be self-inflicted.
Phase 5 Slice B's `zip` axiom in our Lean support library declared
the return type as `Vec _ (PairType a b)` (flat). SAW's actual
`#(a, b)` syntax in primitive declarations expands via the
typechecker to `PairType a (PairType b UnitType)` (nested-with-Unit;
see `saw-core/src/SAWCore/Typechecker.hs:414-418`). Our axiom was
strictly NARROWER than SAW's primitive — a soundness gap caught
by Lean's elaborator at popcount.

Phase 6 fix: corrected the axiom signature; re-enabled the
BoundedVecFold recognizer. End-to-end test:
`otherTests/saw-core-lean/test_cryptol_module_popcount`.

(Entry preserved for the audit trail; no further action.)

### Phase 8 — Support library: axioms → defined *(NEW, multi-week)*

The single biggest quality lift relative to Rocq. Replace
support-library axioms with structural definitions where Lean's
stdlib supports it. Reserve axioms for principled cases.

**To replace with defined:**
- `gen : (n : Nat) → (α : Type) → (Nat → α) → Vec n α` →
  `Vector.ofFn`-based structural def
- `atWithDefault : (n : Nat) → (α : Type) → α → Vec n α → Nat → α`
  → structural def using `Vector.get`
- `foldr` / `foldl` → structural def using `Vector.foldr`/`foldl`
- `head`, `tail`, `EmptyVec` (from
  `leanIntentionallyUnmappedPrimitives`) → defined
- `shiftL` / `shiftR` (currently axioms; structural definition is
  feasible)

**To stay axiomatic, with documented reasons:**
- `bvAdd`, `bvSub`, `bvMul`, `bvUDiv`, `bvURem`, `bvSDiv`, `bvSRem`,
  `bvNot`, `bvAnd`, `bvOr`, `bvXor`, `bvNeg`, `bvShl`, `bvShr`,
  `bvSShr`, `bvUExt`, `bvSExt`, `bvEq`, `bvult`, `bvule`, etc.
  Reason: Lean's `BitVec` semantics differ from SAW's on signed
  div/rem and edge cases (per `SAWCorePrimitives.lean:143-162`).
  Could be revisited as a separate "native `Lean.BitVec` binding"
  arc; deferred.
- `unsafeAssert`, `error`, `coerce`. Reason: SAWCore primitives
  with no body. Inherent residual trust.
- `Pair_fst`, `Pair_snd`, `Integer`, `bvPopcount`,
  `bvCountLeading/TrailingZeros`, `bvLg2`. Reason: SAWCore
  primitives or simple SAW Prelude lookups.

**Per replacement, three artifacts:**
1. The new defined Lean function.
2. An equivalence theorem (or set of `simp` lemmas) showing it
   matches the SAWCore semantics.
3. An updated `SAWCorePrelude_proofs.lean` where the corresponding
   axiomatic round-trip lemma (e.g. `gen_atWithDefault`,
   `atWithDefault_gen`) becomes a `theorem` instead of an `axiom`.

**Exit criteria.** Every `axiom` in `SAWCorePrimitives.lean` is
either (a) a SAW primitive whose Lean realisation must axiomatize
SAW semantics that diverge from Lean's natives, or (b) a SAW
primitive with no useful Lean realisation. Documented per-axiom in
the file. The
`SAWCorePrelude_proofs.lean` round-trip axioms turn into proven
theorems where they're now inferable from the defined functions.

This is a substantial chunk — I'd estimate 2-3 weeks for
intelligent execution, with the BitVec axioms staying intact as
the residual.

### Phase 6 — Cryptol surface expansion *(organic, concrete primitive list)*

Now informed by the audit's coverage assessment. Demos that
currently fail and the primitives they need:

- **Class dictionaries** (`PRing`, `PCmp`, `PEq`, …) — needed for
  any non-trivial polymorphic Cryptol code. Each lowers to a
  SAWCore record-of-functions. Add the records to support library;
  route the dictionary-construction primitives.
- **Record updates** (test_records t8-t15 backfilled) — already
  scoped in audit B.
- **Comprehension/transpose** (test_sequences gaps) — `ecTranspose`,
  `ecFromTo`-family enumeration primitives.
- **IntMod / Rational / Float** — separate domains, each adds a
  type + ops. SHA-512's full instantiation needs none of these,
  but ECC code paths do.
- **SHA-512** — currently fails on polymorphic `Num#rec1`
  dispatch. Either upstream Cryptol changes to specialise the
  message length at the SAW boundary, or polymorphism-residual
  relaxation that's hard to do soundly. Defer.
- **Popcount** — closed (Phase 5d). The blocker was a wrong zip
  axiom signature; corrected and the recognizer is enabled.

Each addition under lockdown discipline:
- Matched-shape Lean realisation.
- Pinned routing test.
- Smoketest verifying `auditPreludePrimitivesForLean` still passes.

`dump_lean_residual_primitives` should emit empty on a target demo
set (TBD per arc — start with the audit's "exercises/" survey).

### Phase 7 — Proof-side tooling *(unchanged from morning plan)*

Decision: own the proof side or punt to downstream.

After Phase 8's axiom→defined conversion, much of this becomes
easier — defined functions reduce, so basic semantic goals close
without an explicit lemma library. The "build a proof library"
question changes character once support is computed.

`getting-started.md` should be re-validated after Phase 8 (its
walkthrough relies on current axiom shapes; switching to defined
functions changes the proof-discharge experience).

## Open strategic questions *(unchanged)*

- `translateSAWModule` — defer until concrete user materialises.
- Native `Lean.BitVec` binding — Phase 8's bv axioms are the
  natural successor; cost/benefit re-evaluable after Phase 8 lands.
- Upstream destination — TBD until the project hits "useful for
  someone."

## Suggested ordering

**Phase 5b is gating.** No other phase claims "complete" until
discipline is cleaned up.

After 5b:
- 5c (parallelizable, days)
- 8 (multi-week, single biggest quality lift) → this is now the
  main sequence work
- 6 (organic, can run in parallel with 8 once Phase 5b's
  residual-trust catalog gives 6's primitives a home)
- 7 (after 8 makes proofs reduce; possibly merges with 8 in
  practice)

5d remains blocked on Phase 6 / Cryptol surface work.

## Honest verdict on where this plan leaves us

After 5b: discipline-clean. The lockdown principle actually
applies to claimed-complete work.

After 5c + 8: roughly Rocq-parity in support-library quality, with
remaining gaps being primitive coverage (Phase 6) and BitVec
axioms.

After 6: actual production-ready for the demo set we care about.

After 7: ergonomic for downstream proof users.

Total honest estimate from today: 4-8 weeks of focused work to
clear Rocq's bar, with the spread depending on Phase 6 demo
selection. The architectural advantages we have (Slice A/A.5
stream coverage, lockdown discipline) survive intact through this
arc.

## Note on the morning plan

`2026-05-02_post-audit-plan.md` is preserved as the as-of-morning
snapshot. Its Phase 1a should be re-marked as not-quite-complete
in light of L-discipline-1 above. Its Phase 5 is partially
delivered (Slices A and A.5) but didn't meet its own pin
criteria, addressed by L-discipline-2.

The morning plan was correct as a discipline statement; this
revision adds the work the morning plan didn't see (axioms →
defined) and operationalizes the cleanup the morning plan didn't
finish (residual-trust catalog, semantic-discharge pins).
