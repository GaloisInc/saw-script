# Position/Callee Convention Implementation Goal

**Date**: 2026-07-02

**Status**: Execution plan for the first implementation slice of
`doc/2026-07-02_position-callee-calculus.md` and
`doc/2026-07-02_position-callee-conventions-design.md`. This document is the
operative goal for the next build phase. Do not edit it during execution to
make the work easier; if the plan is wrong or incomplete, stop and report the
decision point.

**Revision 2026-07-03** (pre-execution design review; no design intent
changed): added the Subject Representation Determination Order, recorded why
motive result positions are forced by the calculus, fixed the verification
commands in execution step 10 (`make conformance` does not run `drivers/*` or
`proofs/*`), restricted slice-1 behavior changes explicitly to the raw logical
callees, and added a required runtime-subject equality regression row. This
revision was made by the document owner before execution started; the "do not
edit during execution" rule still applies to executors. Its baseline statement
was superseded by the correction below.

**Revision 2026-07-03 baseline correction** (requested after executor
baseline check): the earlier baseline was stale. Focused harness re-runs with
the existing built SAW binary confirm that all five Nat proof-transport rows
fail with the same wrapped-motive shape:
`proof_add_nat_assoc`, `proof_eq_nat_add_0`, `proof_eq_nat_add_s`,
`proof_eq_nat_add_comm`, and `proof_equal_nat_to_eq_nat`. This does not change
the design target. It broadens the first positive proof-transport checkpoint
from one failing row plus four preserved rows to five failing rows that must
all be fixed by the same declared raw logical convention.

**Revision 2026-07-03 resume clarification** (requested after the corrected
baseline was checked against the partially executed worktree): the
baseline layers below are historical. They record the states before
and at the start of the raw-logical convention slice. A resumed executor may
find that the worktree has already moved past that baseline: the five Nat
proof-transport rows may now elaborate, the runtime-subject equality row may
already exist, and the recursor/dictionary rows may already be promoted from
known gaps. Do not revert or recreate the failing baseline. Instead use the
"Resume Checkpoint" section below to decide whether the slice is complete, and
classify remaining full-suite failures against this goal's scope.

**Revision 2026-07-03 second baseline correction** (requested after checking
the goal document against `HEAD` and the dirty worktree): the earlier
historical baseline conflated two different states. A clean checkout of the
current committed `HEAD` still has some recursor/dictionary rows tracked as
known gaps; the raw-logical slice was intended to start after the uncommitted
recursor/dictionary checkpoint had already promoted those rows. This document
now distinguishes the committed baseline from the slice-start baseline. Do not
use the clean `HEAD` known-gap state as evidence that the raw-logical slice
should re-pin those rows.

**Revision 2026-07-03 third baseline correction** (double-check after the
second correction): the raw-logical slice-start baseline must not be described
as a globally green `make test` baseline. The focused recursor/dictionary rows
are the prerequisite positive rows for this slice. The broader `drivers/*` and
`proofs/*` rows remain valuable regression surfaces, but stale golden or proof
ergonomics failures there are not evidence that the raw-logical slice-start
baseline was wrong unless artifact review ties them to the convention being
changed here. Run them, report them, and classify them; do not treat them as
the baseline that this slice must recreate.

## Just Woke Up: Start Here

This is the next backend-completion task after the raw/wrapped recursor and
dictionary checkpoint.

The previous checkpoint made real progress: the local `RecursorConvention`
abstraction fixes the wrapped dictionary/record recursor gap without
special-casing dictionaries or generated Lean syntax. However, full conformance
then exposed proof-transport failures such as `obligations/proof_add_nat_assoc`.
Those failures show that the backend still lacks a first-class
position/callee convention for raw logical infrastructure.

Do not start by changing code. First read:

1. this document;
2. `doc/2026-07-02_position-callee-calculus.md`;
3. `doc/2026-07-02_position-callee-conventions-design.md`;
4. `doc/2026-06-26_phase-beta-expected-shape.md`;
5. `doc/2026-07-02_raw-wrapped-recursor-dictionary-plan.md`;
6. the current-state position/callee checkpoint and current execution-order
   item 1 in `TODO.md` (the historical "Priority 0: Test Harness Integrity"
   section is complete and is not this task);
7. `src/SAWCoreLean/Term.hs`, especially:
   - `BindingShape`;
   - `TranslatedTerm`;
   - `shouldWrapBinder`;
   - `natValueResult`;
   - `argumentBindPlan`;
   - `originalDispatchWithShape`;
   - `translateIdentWithArgsWithShape`;
   - `translateRecursorAppWithShape`;
8. `src/SAWCoreLean/SpecialTreatment.hs`, especially:
   - `DefSiteTreatment`;
   - `UseSiteTreatment`;
   - `UseArgShape`;
   - `UseMapsToWrapped`;
   - `autoEmitRaw`;
9. the Rocq analogues:
   - `saw-core-rocq/src/SAWCoreRocq/Term.hs`;
   - `saw-core-rocq/src/SAWCoreRocq/SpecialTreatment.hs`;
   - `saw-core-rocq/rocq/handwritten/CryptolToRocq/SAWCoreScaffolding.v`.

The task is not "make proof rows pass". The task is:

> Introduce the first explicit position/callee convention slice so runtime
> value computation, raw logical/type/proof infrastructure, wrapped helpers,
> proof obligations, and recursors are not routed through one accidental
> application policy.

If an example needs a broader theory than this first slice, preserve the
failure and report the decision point. Do not keep patching.

The implementation target is a small, reviewable convention table plus
adapter path. It is acceptable for some existing code to remain transitional
plumbing if every surviving branch is classified and no unclassified branch can
silently rawify, wrap, default, or fall back.

This sprint is gated. Do not try to solve every convention surface in one run.
The first checkpoint is only:

1. representation/convention vocabulary plus dispatch classification;
2. raw logical convention for `Eq`, `Refl`, and `Eq.rec`/`Eq__rec`;
3. Lean elaboration of all five Nat proof-transport rows as positive
   obligation rows, with artifact review confirming that their raw motives
   route through the declared convention rather than the old heuristic (see
   "Historical Baseline Layers");
4. focused regression confirmation for runtime equality — including the new
   runtime-subject equality row required below — and the existing
   recursor/dictionary rows.

Stop at that checkpoint for assessment before broad migration.

## Execution Goal

At the end of this phase, the backend should have an explicit convention path
for at least these use-site classes:

1. ordinary Phase-beta value computation;
2. raw Lean/support-library targets;
3. raw logical/type/proof callees such as `Eq__rec`;
4. wrapped helpers with declared argument/result conventions;
5. proof-obligation emitters and checked helper contracts;
6. recursors through the existing `RecursorConvention`.

This does not require a full rewrite of `Term.hs`. It does require a real
abstraction boundary so future work does not keep adding local shape patches.

The minimal successful slice must:

- keep existing recursor/dictionary focused rows passing;
- make all five Nat proof-transport rows positive obligation rows through a
  raw logical callee convention (see "Historical Baseline Layers");
- confirm by emitted-artifact review that their raw motives now come from the
  declared raw logical convention rather than the previous accidental
  heuristic;
- classify any row that still fails only after artifact review shows that
  the raw logical convention was applied and the remaining failure is
  outside this phase;
- preserve equality over runtime values, where the proposition is raw but the
  compared terms may have wrapped runtime representation;
- avoid using `DefPreserveRaw` as a hidden proxy for use-site semantics;
- avoid adding fixture-specific or callee-name-specific patches outside the
  declared convention table.

## Central Invariant

Every translation site must be explainable as:

```text
source term + expected position + callee convention -> emitted Lean shape
```

The expected position, not just the syntactic source type, determines whether
the Lean representation is raw, wrapped, or function-shaped.

Runtime value computations use:

```lean
Except String T
```

Type, index, proposition, proof, motive, and raw logical positions stay raw.

This means `Nat` is not semantically special:

- a width/index `Nat` is raw;
- a proof/logical `Nat` is raw;
- a runtime computed `Nat` is wrapped;
- a raw support formal expecting `Nat` may receive a wrapped actual only inside
  an error-preserving `Bind.bind` continuation.

## Non-Negotiable Rules

- Haskell stays dumb. It may translate source syntax, carry explicit position
  and shape metadata, build declared Lean applications, emit proof obligations,
  and reject unsupported conventions. It must not prove semantic equivalences.
- Do not inspect emitted Lean syntax to decide whether a term is pure, total,
  raw, wrapped, logical, or safe to adapt.
- Do not special-case fixture names such as `proof_add_nat_assoc`,
  `cryptol_vector_eq_dictionary`, `cryptol_module_simple`, or `sequences.t18`.
- Do not special-case `Eq__rec`, `RecordType.rec`, `PEqSeq`, `Stream.rec`,
  or `Nat` as isolated fixes. They may appear in a declarative convention table
  only if the table entry states the general position/callee contract.
- Do not convert an arbitrary wrapped function to a raw function.
- Do not extract a raw value from `Except` except inside a `Bind.bind`
  continuation whose final result keeps errors observable or whose precondition
  is Lean-checked.
- Do not wrap proofs, propositions, motives, type expressions, or index
  positions just because their syntax mentions a value type.
- Do not add Lean automation, proof scripts, broad simp bundles, or tactic work
  in this phase. Generated obligations may remain open. "Open" means a visible
  local `sorry` placeholder (or an explicitly named open goal) in the emitted
  file: a positive obligation row counts as elaborating with such
  placeholders present, but nothing in this phase may treat a `sorry`-closed
  obligation as discharged evidence, and the final replay gate (out of scope
  here) must reject it.
- Do not hide failures by weakening observers, deleting known gaps, refreshing
  goldens without artifact review, or changing expected diagnostics to match a
  bad emission.
- Do not edit this goal document during execution to make the goal easier. If
  the design is wrong or incomplete, stop and report the decision point.

## In Scope

This phase is a first slice of the position/callee convention design.

In-scope work:

- introduce explicit internal data/types/functions for use-site callee
  conventions, or refactor existing `UseSiteTreatment` machinery to carry the
  same information clearly;
- introduce enough expected-position metadata to distinguish raw value, raw
  type, raw index, raw proposition, raw proof, raw motive, raw logical, runtime
  value, and function convention positions;
- introduce explicit equality subject representation metadata for every
  equality proposition producer/consumer in the first slice;
- route ordinary application dispatch through the explicit convention rather
  than through one implicit Phase-beta path;
- account for every pre-existing `translateIdentWithArgsWithShape` branch as a
  convention instance, a documented transitional path, or an explicit rejection;
- add a raw logical callee convention sufficient for equality/proof transport
  infrastructure;
- preserve the existing `UseMapsToWrapped` path as the wrapped-helper
  convention, improving names or result-shape metadata only if needed for the
  first slice;
- preserve `ProofPrimitiveContract`, `CheckedApplicationContract`, and
  `PartialOpContract` as proof-obligation/checked-helper convention instances;
- treat `RecursorConvention` as the recursor instance of the larger design,
  without rewriting it unless the shared convention machinery naturally absorbs
  part of it;
- add local-let and top-level-definition guardrails from the calculus:
  no shared binding may be reused at incompatible representations, and a
  def-site raw/preserve choice must not imply use-site behavior;
- classify atomic term forms explicitly: variables, constants, sorts/sort
  flags, recursor atoms, string literals, and array values;
- add focused regression tests for raw logical proof transport before broad
  conformance promotion.

## Out Of Scope

The following are not part of this phase:

- proving the emitted obligations;
- adding Lean automation or proof-library ergonomics;
- direct support for unsupported recursors such as raw `Bool#rec`, `Nat#rec`,
  `Z#rec`, `Accessible`, or user datatypes;
- stream productivity/totality design beyond preserving existing explicit
  obligations and failures;
- higher-order proof-carrying wrappers at non-exact arity;
- direct vector fallback/defaulting cleanup, unless it is required to avoid
  breaking this convention slice;
- implementing higher-order proof-carrying residual function wrappers beyond
  conservative rejection/classification;
- completing array, float, loaded primitive, loaded axiom, injected Lean code,
  list/function-sort, or user-datatype realization policies;
- final `offline_lean` replay UX;
- large crypto proof discharge or SHA512.

If one of these surfaces appears while testing, classify it. Do not pull it
into this goal.

## Historical Baseline Layers (verified 2026-07-03, corrected twice)

Do not skip this section. It states what actually passes and fails before
this phase begins, and which baseline is relevant, so a later agent cannot
misread the goal as "make one failing row pass" or stall because reality
differs from an assumed baseline. If this document is being used to resume an
already-started implementation, this section is evidence about previous states,
not an instruction to make the current worktree fail again.

There are two distinct baselines:

1. **Committed repository baseline (`HEAD`).** Before the uncommitted
   recursor/dictionary checkpoint, several rows named below are still tracked
   as `.known-gap` fixtures in the committed tree, including
   `differential/cryptol_vector_eq_dictionary`,
   `differential/unit_recursor_raw_scrutinee`,
   `obligations/recursor_raw_scrutinee_effectful_value`, and
   `obligations/recursor_wrapped_scrutinee_error_propagates`. This is not the
   intended starting point for the raw-logical slice.
2. **Raw-logical slice-start baseline.** The intended starting point for this
   goal is after the recursor/dictionary checkpoint has been applied in the
   worktree: the focused recursor/dictionary rows are positive rows or explicit
   boundaries, not silently re-pinned known gaps. From that state, the five Nat
   proof-transport rows below are the raw-logical failure class for this goal.

If resuming from a clean `HEAD` checkout without the recursor/dictionary
checkpoint, do not pretend those known gaps already pass. Either restore/finish
that checkpoint first, or stop and ask whether the goal should be restarted
from the committed baseline.

- These five positive obligation rows were failing and had no `.known-gap`
  files at the raw-logical slice-start baseline:
  - `obligations/proof_add_nat_assoc`;
  - `obligations/proof_eq_nat_add_0`;
  - `obligations/proof_eq_nat_add_s`;
  - `obligations/proof_eq_nat_add_comm`;
  - `obligations/proof_equal_nat_to_eq_nat`.
- At that slice-start baseline, each row showed the exact bad shape this
  phase exists to fix: a probe `def ... : Nat` whose `@Eq.rec` motive returns
  `Except String Nat` and whose zero branch is
  `Pure.pure ... : Except String Nat`. Lean rejected the mismatch, so each row
  failed at the mandatory elaboration step before any `expected.txt` check.
- Treat the five rows as one failure class. The correction is not five local
  patches, nor a `Nat` patch, nor a fixture-specific patch. Success means all
  five rows elaborate as positive obligation rows, and emitted-artifact review
  confirms their raw motives are produced by the declared raw logical
  convention rather than the previous accidental Phase-beta result
  classification.
- At the raw-logical slice-start baseline, the focused recursor/dictionary
  rows named under "Required Regression Rows" are expected to pass as positive
  rows or retain their explicit intended boundary. The broader `drivers/*` and
  `proofs/*` rows named there are regression surfaces to run after the slice:
  classify any failures by artifact review, but do not use stale broad golden
  failures to redefine this slice's baseline. The only intentionally pinned
  named boundary row is `saw-boundary/proof_primitive_rejection`.
- Transient `known-gap.actual` files, if present after a failed harness run,
  are not pins. A row is pinned only by a checked-in `.known-gap` file plus its
  expected diagnostic. Do not create `.known-gap` files merely to match
  transient `known-gap.actual` leftovers.

If the observed slice-start baseline at execution time differs from this
section before any convention implementation has begun, stop and report before
changing code.
If the current worktree already contains convention implementation work, use
the resume checkpoint below instead of treating either historical baseline
layer as the current expected result.

## Resume Checkpoint

Use this section when resuming from a dirty worktree that already contains
some or all of the raw-logical convention implementation. This is a checkpoint
for assessment, not permission to widen the goal.

The current slice is on track only if all of the following are true:

- the five Nat proof-transport rows named in the baseline layers now
  elaborate as positive obligation rows, not known gaps;
- emitted-artifact review confirms their `Eq.rec` motives return raw proof
  results such as `Nat`, not `Except String Nat`, and the branch is not
  repaired by a fixture-specific patch;
- `obligations/proof_transport_runtime_subject` exists as a positive row and
  pins equality over a runtime carrier such as `Except String Bool`;
- the focused recursor/dictionary rows listed under "Required Regression Rows"
  still pass as positive rows, not re-pinned known gaps;
- `cabal build exe:saw`, `cabal test saw-core-lean-smoketest`, and
  `git diff --check` pass.

If those checks hold, remaining broad-suite failures should be classified, not
folded into this slice. In particular, these are outside the first raw-logical
convention checkpoint unless artifact review proves otherwise:

- function-shaped equality subjects, for example auto-emitted Prelude rows
  that would require equality over function carriers;
- higher-order wrapped-function convention gaps exposed by residual
  `foldl`/`foldr`/scan helpers;
- stream productivity or stream-recursion totality gaps;
- stale goldens from explicit-universe or obligation-shape churn that have
  not yet received artifact review;
- final proof replay or proof automation failures.

Do not change this goal to make any of those pass. Record them in the roadmap
or TODO backlog and stop for assessment if choosing the next design slice
requires user input.

## Required Model

The implementation should move toward this conceptual split.

### Translated Terms

A translated term has a Lean term plus a representation shape.

The current:

```haskell
data BindingShape = BindingRaw | BindingWrapped | BindingFunction
```

is acceptable as an interim representation, but the implementation must stop
treating `BindingRaw` as if all raw things are semantically the same. Raw value,
index, proof, proposition, motive, and type positions differ.

### Expected Positions

Introduce an explicit concept equivalent to:

```haskell
data ExpectedShape
  = ExpectRuntimeValue
  | ExpectRaw RawReason
  | ExpectRawProposition PropositionConvention
  | ExpectFunction FunctionConvention

data RawReason
  = RawValuePosition
  | TypePosition
  | IndexPosition
  | ProofPosition
  | PropositionPosition
  | MotivePosition
  | RawLeanFormal
  | RawLogicalEliminator
  | StructuralRecursorField

data PropositionConvention
  = NonEqualityProposition
  | EqualitySubject ExpectedShape
```

The exact type names and payloads may differ. The required property is that the
code can say why a term is expected raw or wrapped at each boundary. Equality
propositions must carry an explicit subject representation; do not infer
`Eq Nat` as raw or wrapped from `Nat`.

Position/type pairs must be well formed:

- `ExpectRuntimeValue` is for non-function runtime value computations;
- function-typed terms use an explicit `FunctionConvention`;
- proof, proposition, motive, type, and index terms remain raw;
- raw successful values are distinct from raw proofs, raw propositions, raw
  indices, and raw motives even when the Lean outer type is the same;
- if the expected position cannot be justified, reject.

### Function Conventions

Represent function-shaped terms structurally. Do not translate a function value
as `Except String (A -> B)` unless a declared checked helper explicitly uses
that type. A function convention must state:

- each binder's expected position;
- the result position;
- how partial application leaves a residual convention;
- whether a wrapped prefix argument may be sequenced immediately;
- when a residual function must reject because prefix errors would be hidden.

The common value-function convention is morally:

```text
Except String A -> Except String B
```

but dependent, proof, type, index, and higher-order binders must be stated
explicitly.

### Callee Conventions

Introduce or make explicit a convention equivalent to:

```haskell
data CalleeConvention
  = CalleePhaseBetaDefinition
  | CalleeRawLeanTarget
  | CalleeRawLogical
  | CalleeWrappedHelper
  | CalleeProofObligation
  | CalleeMacro
  | CalleeReject
```

The convention tells application dispatch:

- what shape each argument position expects;
- what shape the result naturally provides;
- what adaptations are allowed;
- strict sequencing order for wrapped prefix arguments;
- exact/partial/reject arity policy;
- when unsupported shapes must reject.

Every existing use-site branch must be classified under one of these entries
or marked as a transitional branch with the same information. `UsePreserve` or
`DefPreserveRaw` is not a use-site convention by itself.

### Definition And Let Conventions

Top-level definitions and local shared `let`s are part of this phase as
guardrails, not as a broad rewrite goal.

Add or document a definition convention that determines the expected position
of a definition body from the declaration type and def-site treatment. A
closed value may be lifted with `Pure.pure` only because the definition
convention says it denotes a runtime value computation.

For local/shared lets:

- choose the right-hand side expected position before translating the RHS;
- record exact Lean type and representation in the environment;
- share one Lean binding only when all uses agree on representation;
- translate separate bindings or reject mixed raw/runtime uses;
- do not translate in one shape and repair later by raw/wrapped guessing.

### Atomic Terms

Classify atomic terms explicitly:

- variables: lookup exact environment representation, then adapt if allowed;
- constants: def-site convention plus use-site convention;
- sorts/sort flags: raw type/universe positions only;
- recursor atoms: recursor convention, not ordinary function fallback;
- string literals: raw values or `Pure.pure` runtime values;
- array values: explicit rejection/known gap until an array realization exists.

### Adaptation

Allowed:

- raw value to runtime value: `Pure.pure`;
- runtime value to raw successful value only via `Bind.bind` in a continuation
  whose final result remains runtime-valued and error-preserving;
- raw proof/type/index/proposition/motive to raw: identity;
- raw function to wrapped-function formal by eta-expanding and adapting each
  slot according to an explicit function convention;
- proof obligation emission where the required precondition is visible in Lean.
- named checked adapters that expose a Lean-checked fact tied to the exact
  computation, for example `e = Except.ok a`.

Forbidden:

- arbitrary wrapped value to raw value;
- any generic raw final result extracted from `Except`;
- arbitrary wrapped function to raw function;
- proof/type/proposition/motive wrapping;
- generated Lean syntax inspection;
- Haskell-side semantic rewriting.

## Raw Logical Callees

Raw logical callees are the load-bearing new slice.

Examples:

- `Eq__rec`;
- `sym`;
- `trans`;
- `eq_cong`;
- `coerce__def`;
- related SAW Prelude proof/type infrastructure currently marked
  `autoEmitRaw`.

Two different def-site families are involved, and both need explicit
use-site conventions in this slice:

- `Eq` and `Refl` are Lean-core mappings (`DefSkip` def-site plus
  `UseRenameUniv` use-site in `SpecialTreatment.hs`); they are not
  auto-emitted. Today a dedicated branch in
  `translateIdentWithArgsWithShape` decides `Eq`'s carrier by calling
  `shouldWrapBinder` on the type argument — that is the forbidden type-name
  inference, and it must be replaced by the Subject Representation
  Determination Order below.
- `Eq__rec`, `sym`, `trans`, `eq_cong`, `coerce__def`, and the related
  Prelude proof infrastructure are `autoEmitRaw` (`DefPreserveRaw` def-site
  plus `UsePreserve` use-site). Their def-site treatment stays as it is; the
  missing piece is the use-site raw logical convention.

The convention is **not** "translate all arguments raw". That would break
propositions about runtime values. Instead:

- the callee itself lives in the logical/type/proof layer;
- its proof, proposition, motive, and equality-eliminator structure is raw;
- if a proposition compares runtime values, the compared terms may use runtime
  representation;
- the callee result is raw unless an explicit value-boundary convention says
  otherwise.

Soundness direction for runtime-subject equality: a Lean proof of
`Eq (Except String (T a)) x y` establishes that the two computations are
equal in the error-tracking model, which refines SAW's semantics — anything
Lean can prove about the wrapped carriers is true of the SAW terms. The cost
runs in the safe direction only: Lean equality distinguishes error messages,
so some SAW-true equalities become unprovable, but nothing false becomes
provable. Incompleteness here is acceptable; unsoundness is not. If a proof
should compare successful raw values instead, its convention must use a raw
subject and separately expose the required no-error fact (see the calculus).

This is the precise bug exposed by `proof_add_nat_assoc`:

- `Eq__rec` is a raw logical eliminator;
- its motive result in that fixture is raw proof-transported `Nat`;
- generic Phase-beta application wrapped the zero branch as `Except String Nat`;
- Lean rejected the mismatch.

The fix must be a raw logical convention, not a fixture patch.

### Required First-Slice Logical Table

The first implementation slice must be operational enough that reviewers can
audit argument modes. It is not sufficient to add a broad "raw mode" around
proof transport.

At minimum, the convention table, data constructors, or local documentation
next to the convention implementation must state these contracts:

- `Eq`: the type/proposition layer is raw, but the equality carrier is
  convention-indexed. Every producer/consumer of an equality proposition must
  declare `SubjectRep(a, rho_eq)`. Propositions about runtime values may
  compare runtime representations; propositions about type/index/proof/logical
  values stay raw.
- `Refl`: the proof result is raw. The reflected value is translated at
  `SubjectRep(a, rho_eq)`, matching the corresponding `Eq` contract.
- `Eq__rec`/`Eq.rec`: the type, motive, proof, and eliminator structure are
  raw logical positions. Equality operands follow the corresponding `Eq`
  subject-representation contract. The branch and final result are translated
  according to the motive result position; they are not blindly wrapped or
  blindly rawified. The convention must record operand position, carrier,
  motive binder positions, motive result position, branch position, proof
  position, final result position, and sort/universe class.
- Raw proof combinators such as `sym`, `trans`, `eq_cong`, and `coerce__def`
  are raw logical callees whose proof/proposition infrastructure stays raw;
  any embedded runtime-value comparison follows the `Eq` operand contract.

If the implementation cannot express one of these rows without a special-case
patch, stop and report the missing abstraction.

### Subject Representation Determination Order

"Declare the subject representation" is only executable if the translator has
a deterministic procedure for producing the declaration at every equality
occurrence. This is that procedure. Apply the first rule that matches; do not
reorder the rules, and do not add new inference sources.

1. **Surrounding convention.** If the convention governing the occurrence
   already declares the expected position of the equality — an obligation
   emitter contract, a `ProofPrimitiveContract`/`CheckedApplicationContract`
   argument mode, a callee-convention argument slot, or a definition
   convention for a top-level proposition — use that declared `rho_eq`.
2. **Equality-proof argument.** For `Eq__rec`/`Eq.rec` and the raw proof
   combinators, the exact Lean proposition type of the equality-proof
   argument fixes `rho_eq`: read it from the environment entry (proof
   variables must record their exact Lean proposition type) or from the
   producing convention (`Refl`, a proof primitive contract, or another
   combinator). The equality operands are then translated to match that
   carrier.
3. **Operand natural shapes.** For a standalone `Eq a x y` with no
   declaration from rules 1-2, translate each operand once in its natural
   Phase-beta form (the form the translator produces before any adaptation)
   and read its representation shape from the carried translation metadata
   (`TranslatedTerm`/`BindingShape`). This translation is not a discarded
   probe: reuse the translated term selected by this rule when building the
   emitted equality, so fresh names, sharing, obligations, and effects cannot
   diverge between "classification" and "emission":
   - if either operand is runtime-valued, `rho_eq = RuntimeValue`; lift a
     raw operand with `Pure.pure` (an allowed adaptation);
   - if both operands are raw, `rho_eq` is the corresponding raw position;
   - if either operand is function-shaped, reject in this slice and classify
     the surface (function-carrier equality is out of scope here).
4. **Refl.** `Refl a x` takes `rho_eq` from its consumer's expected position
   when rule 1 or 2 supplies one; a standalone `Refl` uses rule 3 on `x`.
5. **Otherwise reject**, with a diagnostic naming the occurrence and the
   candidate representations. Do not guess.

Rule 3 is legitimate under this document's rules and must not be confused
with the two forbidden inferences: it reads the shape metadata carried by
the translation, which Haskell is explicitly allowed to carry; it does not
inspect generated Lean syntax, and it does not test type names such as
`Nat`. Replacing rule 3 with a type-name test (`shouldWrapBinder`-style) or
an emitted-syntax scan is a stop condition.

### Why Motive Results Cannot Be Wrapped

This subsection records the theoretical justification so a later agent does
not treat the raw-motive fix as one of two acceptable emissions.

A source motive body is a SAWCore type expression, and SAWCore has no
`Except`: no source term can demand the runtime representation inside a
motive result. Therefore any `Except String T` appearing in an emitted
motive result was invented by the translator, and inventing it is exactly
the forbidden "wrap proofs, propositions, motives, type expressions"
adaptation. The motive body must be translated at a raw type position
(`T(tau)`), the branch at the raw position the motive result determines, and
the equality operands per the determination order above.

Consequences:

- The correct emission for `proof_add_nat_assoc` is forced, not chosen: raw
  motive `=> Nat`, raw zero branch, raw transported result. If the overall
  expected position of the eliminator application is `RuntimeValue`, the
  adaptation is `Pure.pure` applied outside the whole eliminator, never a
  wrapped motive inside it. A coherent all-wrapped emission (wrapped def
  type, wrapped motive, `Pure.pure` branch) would also elaborate, but it is
  ruled out by the no-invented-`Except`-in-motives argument above; do not
  choose it.
- An `Eq__rec` whose branch term is inherently runtime-valued (its natural
  shape is a runtime computation, so no allowed adaptation applies at the
  raw branch position) rejects in this slice. A future declared convention
  extension may instead sequence the wrapped branch outside the eliminator
  with `Bind.bind` when the application's expected position is
  `RuntimeValue` — that is sound under the calculus — but it is not part of
  this slice; reject and classify. This is the answer to the design note's
  open question about runtime uses of `Eq__rec`: the value boundary lives
  outside the eliminator, or the translation rejects.

## Relationship To RecursorConvention

`RecursorConvention` is good local architecture and should not be discarded.
It is the recursor instance of the larger expected-position model:

- raw Lean recursors consume raw scrutinees;
- wrapped scrutinees are opened only in value-result `Bind.bind` continuations;
- raw/type/proof/proposition recursor results reject rather than extracting
  from `Except`;
- dictionaries are ordinary values.

Do not broaden `RecursorConvention` to solve `Eq__rec` or proof primitive
transport. That would mix two separate abstractions.

## Execution Order

1. Review current diff and ensure no exploratory patch remains that does not
   match this goal. Keep the principled recursor changes; remove local
   proof-row patches if any were added.

2. Confirm the focused baseline rows if starting from the raw-logical
   slice-start baseline:
   - `obligations/proof_add_nat_assoc`;
   - `obligations/proof_eq_nat_add_0`;
   - `obligations/proof_eq_nat_add_s`;
   - `obligations/proof_eq_nat_add_comm`;
   - `obligations/proof_equal_nat_to_eq_nat`;
   - the existing recursor/dictionary focused rows listed below.
   The expected baseline is stated in "Historical Baseline Layers":
   all five Nat proof-transport rows fail with the wrapped-motive shape (a raw
   `Eq.rec`/proof-transport context receiving a
   `Pure.pure ... : Except String ...` branch), while the recursor/dictionary
   rows pass from the slice-start baseline, even though a clean `HEAD` checkout
   still pins some of them as known gaps. If the observed slice-start baseline
   differs, stop and report before changing any code. Do not change fixtures to
   make them easier. The bad emitted shape was observed in the focused baseline
   run and may also be present in
   transient harness artifacts such as `emitted.lean`/`test.log` if they have
   not been cleaned, but those artifacts are not checked-in fixtures. Re-run
   the rows to confirm they still reproduce before implementation; if the
   current worktree has already moved past the baseline, use the corrected
   baseline layers and the "Resume Checkpoint" section above rather than
   treating current generated artifacts as authoritative.

3. Add the representation vocabulary from the calculus:
   - expected positions for runtime value, raw value, raw type, raw index,
     raw proposition, raw proof, raw motive, raw logical, and function
     convention;
   - proposition conventions, including explicit equality subject
     representation;
   - callee conventions with argument modes, result mode, strict sequencing
     order, arity policy, allowed adaptations, and rejection cases;
   - minimal definition/local-let metadata needed to prevent def-site raw
     treatment or shared lets from becoming hidden use-site conventions.

4. Classify existing dispatch before changing behavior. Produce code or local
   comments that account for every branch in `translateIdentWithArgsWithShape`,
   every `UseSiteTreatment`, and every relevant `DefSiteTreatment` as one of:
   - declared convention instance;
   - documented transitional branch with the same convention fields;
   - explicit rejection/known-gap path.

5. Route application dispatch through the convention path. In this slice,
   "route" means classification and metadata: every branch is wrapped in, or
   annotated as, a declared convention instance without changing its emitted
   output. The ONLY behavior-changing surfaces in this slice are the raw
   logical callees of step 6. The branches to account for are
   `originalDispatchWithShape` and every earlier identifier-specific branch
   in `translateIdentWithArgsWithShape`: proof primitives, checked
   applications, the checked-application and partial-operation wrong-arity
   rejection branches, partial operations, `unsafeAssert`, `error`, `fix`,
   `MkStream`, `if0Nat`, `natCase`, `coerce`, `Eq`, and the generic
   catch-all. A branch may remain transitional only if it is explicitly
   documented as the convention instance for that surface. Do not add new
   pre-dispatch identifier guards unless they are documented as convention
   instances.

6. Implement the raw logical convention for equality/proof transport:
   - `Eq` and `Refl` use an explicit `SubjectRep`, produced by the Subject
     Representation Determination Order;
   - `Eq__rec`/`Eq.rec` records operand position, carrier, motive binder
     positions, motive result position, branch position, proof position, final
     result position, and sort/universe class;
   - proof variables preserve exact Lean proposition/proof types in the
     environment;
   - ambiguity rejects.
   Limit the first behavior-changing implementation to these raw logical
   callees unless a prerequisite classification refactor requires touching an
   adjacent convention.

7. Add the conservative guardrails required by the calculus:
   - no runtime value may become a raw value except through error-preserving
     `Bind.bind` in a runtime-valued result, or through a named checked adapter
     tied to the exact computation;
   - partial applications reject if wrapped prefix errors would be hidden by a
     raw residual function;
   - shared lets may only share one Lean binding when all uses agree on exact
     representation; otherwise translate separately or reject;
   - top-level body wrapping remains allowed only through a declared definition
     convention, not through an unclassified repair.

8. Check that equality over runtime values still compares runtime
   representations, and that raw proof/index/logical equality stays raw. This
   is the regression guard against replacing the bug with an "all raw Eq"
   shortcut.

9. Re-run focused proof rows and recursor/dictionary rows. Inspect emitted
   artifacts before changing expected status. Positive obligation rows must
   elaborate in Lean with visible obligations; textual source/contains checks
   alone are not enough to count as promotion.

10. Run `cabal build exe:saw`, `cabal test saw-core-lean-smoketest`,
   `git diff --check`, and then `make -C otherTests/saw-core-lean test`.
   The `test` verb is required, not optional: `make -C otherTests/saw-core-lean
   conformance` runs only `differential/*`, `obligations/*`, and
   `saw-boundary/*`, so it never executes the required `drivers/*` and
   `proofs/*` regression rows; the `test` verb runs every category. For
   known-gap accounting, also run `make -C otherTests/saw-core-lean
   conformance` and report the pinned known-gap list against the
   Historical Baseline Layers (`bash test.sh conformance-strict`
   with `SAW` set is the hard-gate form).

11. Classify remaining failures. Do not refresh broad goldens unless the
   emitted artifacts have been reviewed against this convention.

## Required Regression Rows

These rows are the load-bearing evidence for the raw logical convention:

- the five Nat proof-transport rows named in the baseline section must change
  from failing rows to Lean-elaborating positive obligation rows — not pinned
  known gaps and not text-only observations. Emitted-artifact review must
  confirm their raw motives now come from the declared raw logical convention
  rather than the previous heuristic;
- one NEW positive obligation row exercising runtime-subject equality (next
  subsection).

A row may be reclassified only after emitted-artifact review shows that the
raw logical convention has been applied and the remaining failure belongs to
a named out-of-scope boundary.

### Required New Row: Runtime-Subject Equality

The regression guard against an "all raw Eq" shortcut currently rests only
on two smoke-test string assertions (`Eq.rec proof supplied to coerce stays
raw`, `coerce wrapped result keeps wrapped shape at Eq`), and this phase
rewrites exactly the code those assertions pin. Add one focused positive
obligation row (suggested name:
`obligations/proof_transport_runtime_subject`) in which:

- the source term contains an equality proposition whose operands are
  runtime-valued computations (for example, `coerce` results or another
  value-domain computation), so that rule 3 of the Subject Representation
  Determination Order selects `rho_eq = RuntimeValue`;
- `expected.txt` pins that the emitted equality carrier is the wrapped
  representation (a `contains:` directive on the `Except String` carrier at
  the `Eq`) and that no operand was extracted from `Except` (`absent:`
  directives for the extraction shapes);
- the emitted file elaborates.

The exact fixture term may be adjusted to what the front end can express;
the pinned property may not: after this phase, equality over runtime values
must compare runtime representations, verified by a conformance-level row,
not only by smoke tests.

These focused recursor/dictionary rows must keep passing or retain their
existing explicit boundary at the raw-logical slice-start baseline:

- `obligations/recursor_wrapped_scrutinee_error_propagates`;
- `obligations/recursor_wrapped_scrutinee_function_result_error_propagates`;
- `obligations/recursor_raw_scrutinee_effectful_value`;
- `differential/unit_recursor_raw_scrutinee`;
- `differential/cryptol_vector_eq_dictionary`;
- `differential/record_projection_binder`;

These broader driver/proof rows must still be run as regression surfaces. A
failure here is a required finding to classify, but it is not automatically a
failure of this slice unless artifact review ties it to the position/callee
convention changed here:

- `drivers/cryptol_module_simple`;
- `drivers/cryptol_polymorphic_class_dict`;
- `drivers/cryptol_module_record_update`;
- `drivers/cryptol_module_point`;
- `proofs/point_shift_property`.

Also keep the proof-primitive boundary and smoke-test intent covered by:

- `saw-boundary/proof_primitive_rejection`;
- `Eq.rec proof supplied to coerce stays raw`;
- `coerce wrapped result keeps wrapped shape at Eq`.

A green `test`/`conformance` run is not sufficient if one of the required
positive rows is still passing only as a pinned known gap, and a green
`conformance` run alone is never sufficient because it does not execute the
`drivers/*` and `proofs/*` rows. Report the known-gap delta against the
Historical Baseline Layers and name any required positive row that
remains pinned.

## Artifact Review Checklist

For proof-transport rows, inspect emitted Lean and confirm:

- `Eq__rec`/`Eq.rec` motive structure is raw logical where appropriate;
- each equality proposition has an explicit subject representation, and no
  equality carrier was inferred from a type name such as `Nat`;
- raw proof/type/motive components are not wrapped in `Except`;
- runtime value propositions still compare runtime representations;
- proof variables in the environment carry exact Lean proposition/proof types;
- proof primitive obligations remain visible as local propositions;
- no raw proof primitive name leaks through as an unchecked axiom;
- no `Except.error` path is defaulted or erased.
- bare or under-applied proof primitive names still reject unless there is a
  checked obligation/theorem path for that exact use.

For local lets/top-level definitions, confirm:

- definition bodies are translated according to a declared definition
  convention, not repaired by an unclassified closed-value wrapping pass;
- shared lets are not reused across incompatible raw/runtime representations;
- constants emitted raw at def-site still have explicit use-site conventions.

For recursor rows, confirm the previous checklist still holds:

- wrapped value scrutinees are sequenced with `Bind.bind`;
- raw recursor calls receive raw scrutinees;
- value-producing motives return `Except String T`;
- raw/proof/type result recursors reject on wrapped scrutinees;
- dictionary projection is not special-cased.

## Stop Conditions

Stop and ask for design review if:

- the implementation wants to add a one-off `Eq__rec`/`Nat`/fixture patch;
- a raw logical convention would translate every argument raw and thereby break
  equality over runtime values;
- a convention cannot explain whether a position is runtime or logical;
- a convention cannot state the equality subject representation for an `Eq`,
  `Refl`, `coerce`, proof primitive, or `Eq.rec` use;
- the Subject Representation Determination Order cannot produce a unique
  answer for a real occurrence, or implementing its rule 3 would require a
  type-name test, an emitted-Lean scan, or a discard-and-retranslate
  classification probe;
- fixing a proof row would require wrapping proof/type/motive terms;
- an emitted term would need a raw value/function from `Except` without an
  error-preserving continuation or checked precondition;
- a partial application would hide a wrapped prefix argument's error inside a
  raw residual function;
- a shared let would need one Lean binding to serve incompatible raw/runtime
  positions;
- the patch starts rewriting SAWCore expressions into semantically equivalent
  Lean expressions without emitting a checked proof;
- fixing `Eq__rec` requires a broad top-level/local-let rewrite beyond the
  declared definition and let guardrails in this goal;
- a failing row can only be hidden by changing an observer, weakening a known
  gap, or refreshing a golden without artifact review.

The AI may declare the goal done, rather than continue, if further progress
would require violating these rules or choosing among incompatible designs that
need user input.

## Done Criteria

This phase is complete when:

- the position/callee convention exists as an explicit abstraction, not only as
  comments or scattered booleans;
- raw logical callees are no longer routed through accidental Phase-beta value
  application;
- all five Nat proof-transport rows elaborate as positive obligation rows
  through the raw logical convention, with emitted-artifact review confirming
  their raw motives come from the declared convention rather than the old
  heuristic;
- the new runtime-subject equality row exists, elaborates, and pins the
  wrapped carrier;
- any row that still fails has a documented out-of-scope boundary after
  emitted-artifact review;
- existing recursor/dictionary rows remain protected;
- equality over runtime values remains wrapped where semantically required;
- equality over raw proof/index/logical values remains raw with explicit
  subject representation;
- top-level definitions, local lets, and atomic term forms are classified
  under the calculus or explicitly documented as transitional/rejected;
- no fixture-specific or generated-Lean syntax classifier was added;
- the full sweep (`make -C otherTests/saw-core-lean test`, which includes the
  conformance categories plus `drivers/*` and `proofs/*`) has no unexpected
  failures from this convention family, or remaining failures are documented
  as outside this phase.
