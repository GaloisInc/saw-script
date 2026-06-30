# Obligation-Shape Testing Plan

**Date**: 2026-06-30

## Goal

The conformance suite now covers many executable SAW-vs-Lean value cases. This
plan builds the parallel testing corpus for proof-carrying boundary coverage:
when the Lean backend cannot soundly emit a plain value, the test suite must say
whether the backend emits the exact Lean precondition or proof obligation that
makes the lowering sound.

This is a testing plan, not a backend implementation plan. The work should not
fix backend bugs, change semantic Lean support-library behavior, or add Haskell
special cases to make tests pass. If a required obligation shape is missing
today, the corpus should contain a small fixture that exposes that fact. Missing
backend support is a test result, not a reason to omit the surface.

An obligation-shape test answers:

1. Did SAW-Lean emit a visible Lean contract for the soundness condition?
2. Is the contract the right one for the SAWCore surface?
3. Does the generated term depend on evidence for that contract?
4. Did the backend avoid silently using a totalized primitive, hidden axiom,
   Haskell classifier result, or obsolete helper instead?

These tests are not proof-discharge tests. They may accept an emit-stage
outline with a placeholder proof, as long as the placeholder is visibly attached
to the right proposition and the test is classified as "obligation emitted",
not "proof checked". They must fail when the expected emitted obligation is
absent, weakened, hidden behind a totalized primitive, or replaced by an
unchecked semantic claim.

## Scope And Rules

This work should follow the same discipline as the differential conformance
suite:

- Only the test harness, test corpus, and documentation are in scope.
- Do not change the SAW-Lean backend to make obligation tests pass.
- Do not change semantic Lean support-library definitions to make obligation
  tests pass.
- Do not remove a surface from the corpus because the current backend cannot
  handle it.
- Do not count Lean elaboration alone as success.
- Do not reconstruct equivalent hand-written Lean terms in observers.
- Do not silently skip missing tools, missing emissions, unsupported primitives,
  or malformed obligations.

Each soundness-sensitive surface should be represented in the corpus in one of
three ways:

- `obligation`: the backend emits the expected contract and the test verifies
  its shape.
- `known gap`: the backend currently fails to emit the required contract, and
  the test pins the exact failure stage and diagnostic.
- `final boundary`: rejection is the intended final behavior, and the test pins
  the exact rejection stage and diagnostic.

There should be no fourth state where a known missing obligation is recorded
only in prose.

## Coverage Matrix

The required artifact is a live obligation matrix, either as a dedicated
`otherTests/saw-core-lean/OBLIGATIONS.md` file or as a clearly separated
section of `otherTests/saw-core-lean/CONFORMANCE.md`. The matrix is the measure
of completeness.

Each row should record:

- SAWCore surface or Cryptol.sawcore entry point;
- source authority, such as `Prelude.sawcore`, `Cryptol.sawcore`, or a Haskell
  emitter function;
- expected contract family;
- test path;
- observation method;
- status: `obligation`, `known gap`, `final boundary`, or `not yet tested`;
- current failure stage and diagnostic for known gaps;
- TODO needed to promote the row.

The matrix should include every soundness-sensitive surface listed below, even
when the current backend cannot emit a useful artifact. A missing row is a test
suite bug.

## Boundary Versus Known Gap

These must stay separate.

- `final boundary`: rejection is the intended behavior. The test pins the exact
  rejecting component and diagnostic. This should be rare for SAWCore surfaces
  that the backend aims to support.
- `known gap`: the source term is in backend scope, but the current backend
  cannot yet emit the required obligation or checked realization. A passing
  known-gap fixture means the gap is pinned, not solved.
- `obligation`: the backend emits the expected contract and the test verifies
  that the generated term consumes evidence for it.

For example, under-applied `unsafeAssert` is a final boundary unless we design a
first-class higher-order assertion encoding. Fully applied `unsafeAssert` is not
a final boundary: it must be an obligation. Direct zero-divisor emissions are
known gaps until they either use SAW-exact total semantics or emit nonzero
preconditions.

## Ground Truth

The plan is grounded in the current backend and support-library interfaces:

- `saw-core-lean/src/SAWCoreLean/Term.hs`
  - `withLocalProofObligationUsing`;
  - `withLocalProofObligation`;
  - `translateUnsafeAssertObligation`;
  - `translateRawErrorObligation`;
  - `lowerFixProofObligation`.
- `saw-core-lean/src/SAWCoreLean/SpecialTreatment.hs`
  - rejection table for residual proof-carrying or unsupported primitives;
  - mapped support-library primitives that may need contracts in partial
    positions.
- `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean`
  - current checked contracts;
  - current plain total-looking primitive definitions;
  - support-library axioms and tactics.
- `saw-core/prelude/Prelude.sawcore`
  - authoritative SAWCore primitive and axiom surface.
- `cryptol-saw-core/saw/Cryptol.sawcore`
  - Cryptol wrapper entry points that lower to proof-carrying or partial
    SAWCore surfaces.

The corpus should be built from these sources, not from the subset of examples
that happen to pass today.

## Interfaces Reviewed

### Haskell emission

The current local-obligation constructor is:

- `withLocalProofObligationUsing`
- `withLocalProofObligation`
- `proofObligationPlaceholder`

These create:

```lean
let h_name_obligation_ : Prop := <contract>
let h_name_ : h_name_obligation_ := by
  sorry
<body using h_name_>
```

The soundness-sensitive entry points that already use this pattern are:

- `translateUnsafeAssertObligation`
  - emits the literal `Eq` proposition for fully applied
    `Prelude.unsafeAssert`;
  - rejects residual under-applied `unsafeAssert` through `SpecialTreatment`.
- `translateRawErrorObligation`
  - emits `False` for raw-position `Prelude.error`, then uses
    `False.elim`.
- `lowerFixProofObligation`
  - emits `saw_fix_unique_exists_raw` for raw `fix` results;
  - emits `saw_fix_unique_exists` for wrapped value-domain `fix`.

The rejection table in `SpecialTreatment.hs` is also part of the obligation
surface. It currently rejects:

- residual `fix` and `fix_unfold`;
- with-proof vector primitives (`atWithProof`, `genWithProof`,
  `updWithProof`, `sliceWithProof`, `updSliceWithProof`);
- proof primitives and SAW-side lemma axioms;
- size assertions such as `unsafeAssertBVULt` and `unsafeAssertBVULe`;
- unsupported arrays and other primitive families.

These rejections are acceptable only until a proof-carrying contract exists.
They should be pinned as known gaps, not treated as final conformance unless we
make an explicit out-of-scope decision.

### Lean support-library contracts

The current proof-carrying definitions are:

- `saw_fix_unique_exists`
- `saw_fix_choose`
- `saw_fix_unique_exists_raw`
- `saw_fix_choose_raw`
- `saw_mkStream_total_exists`
- `saw_mkStream_choose`
- `saw_unsafeAssert`

The current partial arithmetic primitives are still plain definitions:

- `divNat`
- `divModNat`
- `intDiv`
- `intMod`
- `ratio`
- `rationalRecip`
- `bvUDiv`
- `bvURem`
- `bvSDiv`
- `bvSRem`

Those definitions are convenient support-library functions, but zero-divisor or
zero-denominator SAWCore emissions cannot soundly call them directly without a
checked precondition or SAW-exact total semantics. The conformance suite already
pins direct zero cases as known gaps.

### Existing harnesses

- `differential/*` compares SAW-observed values with Lean observations of the
  emitted artifact. It rejects `sorry`, so it is correct for green executable
  conformance, but not for open proof obligations.
- `saw-boundary/*` currently runs SAW, compares logs/goldens, and elaborates
  emitted Lean. It is useful for rejection and emitted-outline tests, but a
  golden diff alone is too weak for a principled obligation-shape suite.
- `proofs/*` checks completed proof replay. It rejects unresolved obligations
  and audits theorem axioms. This is the right model for checked discharge, but
  not for testing that an emitter produced the right open obligation.
- `shape/*` contains hand-written adversarial Lean probes. These are useful
  soundness guards, but they do not inspect generator output.

## Proposed Test Category

Add a dedicated category:

```text
otherTests/saw-core-lean/obligations/<name>/
```

This keeps proof-carrying boundary tests separate from:

- true value differential tests;
- rejection-only boundary tests;
- completed proof-discharge tests;
- hand-written adversarial shape tests.

The top-level conformance command should run this category after
`differential/*` and before `saw-boundary/*`. A passing obligation-shape test
counts as conformance only for the claim "the backend exposes the required
contract". It does not mean the obligation is automatically discharged.

Known gaps must remain visibly distinct in the final summary. A green run with
known gaps means "the gaps are pinned", not "obligation parity is complete".

## Harness Contract

Each `obligations/<name>` directory should contain:

```text
test.saw
source.txt
expected.txt
```

Optional files:

```text
obligation-observe.lean
.known-gap
.known-gap.expected
forbidden.txt
```

The harness should:

1. Run the real SAW producer in `test.saw`.
2. Require the emitted Lean artifact named by `source.txt`.
3. Compile the emitted artifact as an outline. `sorry` is allowed only in local
   proof placeholders that are part of the emitted obligation shape.
4. Inspect the emitted artifact for normalized obligation facts.
5. Compare normalized `OBLIGATION_OBSERVED:` lines with `expected.txt`.
6. Fail if any listed `forbidden.txt` substring or Lean constant appears.
7. For `.known-gap` tests, require the real run to fail with the diagnostics in
   `.known-gap.expected`, exactly like differential known gaps.

The observer may initially be a source checker in the shell harness, and should
eventually become a Lean meta observer. In either form, it must inspect the
emitted artifact. It must not reconstruct an equivalent term by hand.

Positive obligation tests must fail on failure: if the contract is missing, if
the wrong contract head appears, if the generated term does not consume the
evidence, if a forbidden bypass appears, or if the emitted artifact no longer
elaborates as an outline, the test must fail. Known-gap fixtures are allowed
only when they pin a current missing obligation with a specific expected
diagnostic; if the backend starts passing, the known-gap fixture must fail so it
can be promoted to a positive obligation test.

## Observation Strategy

The first implementation can be pragmatic, but it should be honest about what
it observes.

### Phase 1: emitted-source checks plus Lean elaboration

For local-let obligation outlines, the simplest useful checks are source-level
facts extracted from the emitted artifact:

- required contract head appears:
  - `saw_fix_unique_exists`;
  - `saw_fix_unique_exists_raw`;
  - `saw_mkStream_total_exists`;
  - `Eq`;
  - `False`;
- required consumer appears:
  - `saw_fix_choose`;
  - `saw_fix_choose_raw`;
  - `saw_mkStream_choose`;
  - `False.elim`;
- forbidden totalized or obsolete paths do not appear:
  - direct zero-divisor calls without an obligation;
  - old fix helper names;
  - `error_unrestricted`;
  - direct unsafe proof axioms;
  - obsolete stream/vector helper names.

This is text-level, so it is not ideal. It is still useful as a short-term
guard because it checks the actual generated file and is much better than only
checking that Lean elaborates.

The Phase 1 harness should still emit normalized `OBLIGATION_OBSERVED:` facts.
That keeps the test directory format compatible with the later Lean meta
observer.

### Phase 2: Lean meta observer

The principled observer should be a small Lean meta program that imports the
emitted artifact and inspects the generated declaration body from the
environment. It should print normalized facts such as:

```text
OBLIGATION_OBSERVED: obligation saw_fix_unique_exists
OBLIGATION_OBSERVED: consumer saw_fix_choose
OBLIGATION_OBSERVED: placeholder sorryAx present
OBLIGATION_OBSERVED: forbidden bvUDiv absent
```

For exact propositions, the observer can pretty-print the subexpression headed
by the contract constant. This avoids reconstructing the term while giving a
stable enough comparison for small litmus tests.

This phase is preferable before we add many tests. It reduces churn from
pretty-printer changes and avoids relying on incidental whitespace in generated
Lean.

### Out of scope: emitter redesign

This plan should not redesign obligation emission. If local-let obligations are
hard to observe, that is a test-harness problem for this phase, not permission
to change the backend under test. The corpus should still contain the relevant
small fixture and classify the current result as `obligation`, `known gap`, or
`final boundary`.

Future backend work may decide to lift obligations into top-level declarations
with stable names, but that must be driven by the corpus findings. It is not
part of this testing-only plan.

## Surfaces To Cover

### P0: partial arithmetic and partial construction

These are highest priority because direct totalized emission can change SAW
semantics.

Required rows:

- `divNat x 0`
- `modNat x 0`
- `divModNat x 0`
- `intDiv x 0`
- `intMod x 0`
- `ratio n 0`
- `rationalRecip 0`
- `bvUDiv x 0`
- `bvURem x 0`
- `bvSDiv x 0`
- `bvSRem x 0`
- Cryptol wrappers that lower to those operations:
  - `ecDiv`;
  - `ecMod`;
  - `ecFieldDiv`;
  - `ecRecip`;
  - `ecSDiv`;
  - `ecSMod`.

Corpus expectation:

- either SAW-exact total semantics in Lean, if SAW defines a total result for
  the zero case, or
- an explicit precondition obligation such as nonzero divisor or nonzero
  denominator, if the backend treats the surface as proof-carrying.

Every row should exist immediately. Rows whose current emission silently calls
the current Lean primitive on a zero argument with no evidence should be
recorded as known gaps until fixed.

### P0: `unsafeAssert`

Required rows:

- fully applied definitional equality, e.g. `unsafeAssert Bool True True`;
- fully applied non-definitional Nat/Num equality that `saw_unsafeAssert` can
  prove;
- fully applied impossible equality that remains an open obligation;
- under-applied residual `unsafeAssert` rejection.

Corpus expectation:

- emitted proposition is the literal `Eq α x y`;
- generated value is exactly the proof of that equality;
- optional tactic is checked by Lean;
- no hidden `unsafeAssert` axiom is trusted.

### P0: `fix`

Required rows:

- wrapped value-domain `fix`;
- raw function/index/proof-position `fix`;
- weak success-only fixed-point contract negative probe;
- `fix_unfold` rejection or future proof-carrying replacement.

Corpus expectation:

- wrapped values use `saw_fix_unique_exists` and `saw_fix_choose`;
- raw values use `saw_fix_unique_exists_raw` and `saw_fix_choose_raw`;
- uniqueness quantifies over all wrapped fixed points, including errors;
- obsolete direct fix helpers must not appear.

### P1: raw `Prelude.error`

Required rows:

- raw Nat/index error branch;
- raw proof/Prop error branch;
- raw function-result error branch;
- value-domain error branch that remains `Except.error`.

Corpus expectation:

- raw positions emit an unreachability obligation, currently `False`;
- value-domain positions use `saw_throw_error`;
- no `error_unrestricted` axiom or fabricated default appears.

### P1: `MkStream` and stream totality

Required rows:

- stream constructor from a total raw function;
- stream constructor from an `Except`-valued function requiring
  `saw_mkStream_total_exists`;
- stream helpers that currently emit unresolved totality stubs:
  - `streamGet`;
  - `streamMap`;
  - stream shifts;
  - `streamScanl`.

Corpus expectation:

- totality obligations are explicit;
- stream construction consumes only checked totality evidence;
- no default element is fabricated for failing indices.

### P1: vector proof-carrying operations

Required rows:

- `atWithProof`;
- `genWithProof`;
- `updWithProof`;
- `sliceWithProof`;
- `updSliceWithProof`;
- `ecAt` and other Cryptol indexing wrappers that need bounds evidence.

Corpus expectation:

- index/bounds propositions are visible Lean obligations;
- generated vector operation consumes that proof;
- current rejection fixtures remain known gaps until this exists.

### P2: proof primitives and lemma axioms

Required rows:

- representative `Eq` / `EqDep` proof combinators;
- `bvForall`;
- Nat proof/order primitives;
- bitvector lemma primitives;
- `unsafeAssertBVULt`;
- `unsafeAssertBVULe`.

Corpus expectation:

- either a Lean theorem realization with axiom audit, or
- a generated proof obligation;
- never a trusted Haskell rewrite or hidden axiom.

### P2: recursors and datatype/list encodings

Required rows:

- direct `Bool#rec`;
- direct `Nat#rec`;
- direct `Z#rec`;
- `AccessibleNat` / `AccessiblePos` recursors;
- user datatypes;
- `List`, `ListSort`, `FunsTo`.

Corpus expectation:

- constructor-order differences are handled by a checked Lean realization;
- unsupported recursors remain known gaps;
- no Haskell-side case-order classifier is trusted unless it emits checked Lean
  evidence.

### P2: imported declarations and injected code

Required rows:

- imported-name realization contract;
- injected Lean code declarations;
- primitive/axiom declarations from loaded SAWCore modules.

Corpus expectation:

- imported names elaborate at the translated SAWCore type;
- injected declarations are either explicitly trusted and documented, or paired
  with realization obligations;
- no bare name is emitted without a visible contract.

## Relationship To Existing Tests

The current tests should be reclassified as follows:

- `saw-boundary/fix_obligation`
  - migrate to `obligations/fix_wrapped_unique` and add a raw variant;
  - keep the existing golden until the new harness covers it.
- `saw-boundary/partial_operation_obligations`
  - keep as known gaps until the backend emits checked preconditions;
  - migrate each case to positive obligation-shape rows as they are fixed.
- `saw-boundary/unsafe_assert_rejection`
  - keep under-applied rejection;
  - add separate positive fully-applied obligation-shape rows.
- `saw-boundary/vector_with_proof_rejection`
  - keep as known gaps;
  - replace with positive vector proof-obligation rows when implemented.
- `shape/fix_contract`
  - keep as an adversarial contract-strength probe.
- `shape/unsafe_assert_prop` and `shape/coerce_unsafeassert_combo`
  - keep as support-library shape guards.
- `proofs/*`
  - continue to test completed proof replay;
  - do not use proof tests as evidence that the emitter exposed the right
    obligation unless the source obligation is also covered by
    `obligations/*`.

## Success Criteria

The obligation-shape suite is good enough for the next backend phase when:

1. Every soundness-sensitive row in `CONFORMANCE.md` has either:
   - a passing `obligations/*` fixture;
   - a passing value differential fixture;
   - a rejection fixture marked as final boundary; or
   - an explicit `.known-gap` fixture.
2. Every passing obligation fixture observes the emitted artifact itself.
3. Every fixture checks both required contract heads and forbidden bypasses.
4. Known gaps remain visible in the conformance summary.
5. No completed proof-discharge test accepts `sorry`, hidden axioms, or a proof
   of a different proposition.
6. The matrix, not the test count, is the coverage measure.
7. There are no unrepresented known missing obligation surfaces.

## Implementation Roadmap

1. Add `obligations/*` harness support.
   - Start with text/source checks plus Lean elaboration.
   - Design the file contract so it can be upgraded to a Lean meta observer
     without changing each test directory.
2. Build the initial corpus before fixing backend behavior.
   - Add every P0 row as either a positive obligation test or a known-gap
     fixture.
   - Add P1/P2 rows as known gaps where the current backend lacks an
     obligation interface.
   - Update `CONFORMANCE.md` so every surface has a path and status.
3. Add the Lean meta observer utility, if source-level checks become too weak
   for precise testing.
   - Import `Emitted`.
   - Inspect generated declaration bodies from the environment.
   - Print normalized `OBLIGATION_OBSERVED:` facts.
4. Migrate existing obligation-like fixtures.
   - `fix_obligation`;
   - fully applied `unsafeAssert`;
   - raw `Prelude.error`;
   - stream totality;
   - current partial-operation known gaps.
5. Extend to P1/P2 surfaces until the matrix is complete.
   - vector with-proof operations;
   - proof primitives;
   - recursors;
   - imported/injected declarations.

Backend fixes happen after this testing work has made the current state visible.
As fixes land, individual `.known-gap` fixtures should fail, then be promoted to
positive obligation tests with the same small source case.

## Non-Goals

- Do not prove every obligation automatically.
- Do not turn large examples into obligation-shape tests.
- Do not count Lean elaboration of a file with `sorry` as proof discharge.
- Do not add Haskell semantic recognizers to make a test pass.
- Do not replace real emitted artifacts with hand-written Lean analogues.
