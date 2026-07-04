# Complete Wrapping/Adaptation Migration Goal

**Date**: 2026-07-01

**2026-07-03 status note**: this document remains useful background, but it is
no longer the operative next-sprint goal. Tuple update helper coverage is now
classified as conforming, and the next live value-level wrapping target is the
fold-family higher-order function convention described in
`doc/2026-07-03_higher-order-function-conventions-goal.md`. Prefer that newer
goal document for execution.

## Just Woke Up: Start Here

The task is to finish the value-level raw/wrapped adaptation migration for the
SAW-Lean backend.

Do this task only after reading:

1. this document;
2. `doc/2026-06-26_phase-beta-expected-shape.md`;
3. `doc/2026-06-28_clever-legacy-path-audit.md`;
4. the wrapping-related rows in `otherTests/saw-core-lean/CONFORMANCE.md`;
5. the current implementation of `BindingShape`, `UseArgShape`, and
   `UseMapsToWrapped` in `src/SAWCoreLean/Term.hs` and
   `src/SAWCoreLean/SpecialTreatment.hs`.

The next implementation phase is not "make examples pass". It is:

> Complete the remaining value-level wrapping/adaptation migration using a
> small, explicit, auditable convention system.

If a failure is caused by proof primitives, proof-valued terms, direct
recursors, user datatypes, `ListSort`/`FunsTo`, imported realizations, raw Lean
injection, or proof automation, it is outside this phase. Keep it pinned as a
known gap or boundary and record it. Do not patch around it.

## Execution Goal

At the end of this phase, every in-scope value-level term should be translated
according to the Phase beta `Except String` convention without relying on local
syntactic hacks:

- translate each source term in its natural shape;
- carry shape metadata through the translation;
- adapt once at the use site according to an explicit expected convention;
- reject clearly when no sound adaptation exists.

The success criterion is not that all conformance known gaps disappear. The
success criterion is that remaining raw/wrapped failures are either fixed by
the shared shape/convention machinery or explicitly reclassified as non-wrapping
work.

This phase should move the backend closer to Rocq parity by removing a real
example blocker, but it must preserve the Lean backend's stricter soundness
rule: Haskell emits simple syntax and checked contracts; Lean, not Haskell,
does the proof work.

## Current State

The backend already has most of the right abstraction:

- `BindingShape` distinguishes raw, wrapped, and function-shaped local terms.
- `TranslatedTerm` carries the emitted Lean term plus its shape.
- `translatedTermAsWrapped` is the central raw-to-wrapped lift.
- `UseMapsToWrapped` routes selected SAWCore identifiers to Lean helpers whose
  result is already `Except String`.
- `UseArgShape` currently records explicit helper-formal conventions:
  `UseArgRaw`, `UseArgWrapped`, `UseArgFunction`, and
  `UseArgFunctionWithNatLt`.
- under-applied wrapped helpers return `BindingFunction` rather than escaping
  the raw/wrapped convention silently.
- unsupported function-shaped situations reject instead of rawifying an
  arbitrary `Except` computation.

Several earlier special cases have already been removed or migrated:

- the old emitted-Lean result-shape classifier is gone;
- broad `rawifyExceptToRaw`-style semantic rawification is no longer the
  migration direction;
- ordinary applications, shared `let`s, recursor case fields, and many wrapped
  helper calls now use shape metadata;
- finite generators receive checked index evidence through the
  `UseArgFunctionWithNatLt` convention;
- fully applied bounds/index operations now expose checked Lean obligations
  rather than trusting SAW proof arguments.

The remaining known wrapping-adjacent failures are focused:

| Surface | Current fixture | Current failure shape | In-scope? |
| --- | --- | --- | --- |
| Tuple update helpers | `differential/tuple_update_helpers` | updater lambda receives/returns the wrong raw-vs-wrapped shape; emitted Lean has `Except String Nat` where raw `Nat` is expected | yes, if solved by function argument conventions |
| Vector folds | `differential/vector_fold` | raw functions such as `addNat : Nat -> Nat -> Nat` are passed where `foldrM`/`foldlM` require wrapped functions | yes |
| Cryptol fold wrappers | `differential/cryptol_ec_fold_scan` | `ecFoldl`/`ecFoldlPrime` expose the same raw-function-to-wrapped-function mismatch for Nat/Int functions | yes |
| Stream helpers | `differential/stream_helpers` | `Stream.rec` has a raw/wrapped result mismatch; current artifact expects `Except String ...` where the recursor gives raw `Nat` | maybe; solve only if it fits the same expected-shape abstraction |
| Derived sequence/vector rows | multiple known gaps | direct or derived bounds obligations and proof stubs | no, unless a separate raw/wrapped mismatch remains after obligations are exposed |

Do not infer from this list that fixture-specific code is acceptable. These
fixtures are representatives of missing convention shapes. A fix is valid only
if it explains the source/target convention generally.

## Non-Negotiable Rules

- Haskell must stay dumb. It may translate terms, carry shapes, build declared
  helper applications, emit explicit proof obligations, and reject unsupported
  shapes. It must not prove semantic equivalences.
- Do not inspect generated Lean syntax to decide whether a term is pure,
  total, in bounds, equal to another term, or safe to rawify.
- Do not add a classifier that recognizes the current conformance fixture and
  emits a hand-shaped alternative.
- Do not add Haskell rewrites that turn one SAWCore expression into a
  semantically equivalent but structurally different Lean expression unless the
  equivalence is carried by a checked Lean theorem or visible obligation.
- Do not convert an arbitrary wrapped function into a raw function. There is no
  sound general function of shape `(A -> Except String B) -> (A -> B)`.
- Do not hide failures by changing observers, weakening known gaps, deleting
  failing rows, or broadening expected diagnostics.
- Do not add Lean automation in this phase. No convenience tactics, generated
  proof scripts, broad simp bundles, `omega`/BV automation, or proof-library
  work whose purpose is to make obligations discharge.
- Do not preserve fallback, backup, or legacy paths for erroneous behavior.
  Old paths that bypass the explicit convention system are targets for removal,
  not compatibility requirements.

## In Scope

This phase covers value-level raw/wrapped adaptation where the source semantics
are already understood and the missing piece is the calling convention.

### Function arguments to wrapped helpers

The main in-scope family is higher-order value arguments passed to helpers that
operate in the `Except String` convention.

Representative cases:

- `foldr` / `foldl` routed to `foldrM` / `foldlM`;
- `Cryptol.ecFoldl` and `Cryptol.ecFoldlPrime` after they lower to finite
  folds;
- any other fully applied value-level helper that has a raw source function
  argument but a wrapped Lean helper formal.

The correct abstraction may be an extension of `UseArgShape`, for example a
mode that explicitly says:

```text
this source argument is a function;
its source binders are raw values of these shapes;
its Lean helper formal expects wrapped arguments/results of these shapes;
translate the body once and adapt by wrapping raw results or binding wrapped
arguments as required.
```

The exact Haskell type is not prescribed. The important property is that the
convention is declared at the callee boundary, not discovered by inspecting the
generated Lean AST.

### Tuple update helper functions

`Cryptol.sawcore` defines:

```saw
updFst : (a b : sort 0) -> (a -> a) -> PairType a b -> PairType a b
updSnd : (a b : sort 0) -> (b -> b) -> PairType a b -> PairType a b
```

The updater function is value-level. Under Phase beta, the body may produce an
`Except String` value, while the pair-field plumbing may expose raw constructor
fields. This should be solved by the same function-shaped expected convention
used for folds, or by a narrowly named wrapped helper with an explicit
function-formal convention.

Do not special-case `updFst`, `updSnd`, or the fixture's `addNat`/`mulNat`
bodies in Haskell.

### Stream helper recursor adaptation

`differential/stream_helpers` currently exposes a `Stream.rec` raw/wrapped
mismatch. This row is in scope only if the failure is caused by the same missing
expected-shape propagation for value-level recursor case bodies.

If fixing it requires a new semantic realization of stream recursion,
productivity, totality, `MkStream`, `streamScanl`, or `Prelude.fix`, stop and
classify it as a recursor/proof-carrying stream design issue. Do not build a
stream-specific Haskell rewrite.

### Under-applied value-level helpers

Under-applied wrapped helpers are in scope only insofar as the existing
convention system can represent their partial application soundly as
`BindingFunction`.

If an under-applied helper would require hiding `Except` errors, fabricating a
raw function from a wrapped computation, or carrying a proof-producing function
without an explicit contract, reject with a pinned diagnostic and record the
higher-order wrapper design as future work.

## Out Of Scope

The following are not part of this phase, even if a focused conformance run
mentions them:

- proof primitives and proof-valued terms such as `coerce__eq`,
  `equalNatToEqNat`, `proveLeNat`, `bvEqToEq`, `bvEqToEqNat`,
  `bvultToIsLtNat`, `uip`, `unsafeAssert*`, and vector/fold proof lemmas;
- proof datatype encodings such as `IsLeNat` and `IsLtNat`, except when a
  previously designed checked helper already consumes Lean evidence;
- direct recursor realization for `Bool`, `Nat`, `Z`, `Accessible`, user
  datatypes, or raw datatype eliminators;
- `ListSort`, `FunsTo`, algebraic enum encodings, and user datatype/module
  translation;
- `scLiteralFold`, opaque-builtin discovery, imported realization semantics,
  raw Lean injection, and loaded custom primitive/axiom declarations;
- broad proof ergonomics for bounds, nonzero arithmetic, BV facts, or generated
  index arithmetic;
- final SAW-side proof replay UX or offline checker integration.

If one of these surfaces blocks a wrapping fixture, preserve the fixture as a
known gap and update the classification. Do not expand this phase.

## Required Abstraction

The implementation should converge on an explicit shape/convention abstraction.
It must answer these questions without looking at generated Lean syntax:

- What shape does this translated source term naturally provide?
- What shape does this callee formal expect?
- Is raw-to-wrapped lifting sufficient?
- Is wrapped-to-raw sequencing possible because the use site has a continuation
  that keeps errors observable?
- Is the term function-shaped, and if so what shapes do the function's binders
  and result use?
- Is there a named checked helper that consumes exactly this convention?
- If no sound adaptation exists, what diagnostic should be emitted?

The current `UseArgShape` values may be enough with a small extension, or they
may need to become a richer function-shape description. Acceptable designs
include a sibling type such as:

```haskell
data FunctionArgConvention
  = FunctionRawToWrapped
      { binderModes :: [FunctionBinderMode]
      , resultMode  :: FunctionResultMode
      }
  | FunctionWithNatLtEvidence Int
```

This is illustrative, not required. The actual design should fit the existing
code. The required property is that the convention is explicit and reusable.

### Allowed Adaptations

These adaptations are allowed:

- raw value to wrapped value: `Pure.pure raw`;
- wrapped value to wrapped value: identity;
- wrapped value to raw value only inside a `Bind.bind` continuation whose final
  result remains wrapped and therefore preserves the error path;
- raw type/index/proof to raw type/index/proof: identity;
- raw function to wrapped-function formal by eta-expanding the function and
  wrapping/sequencing its arguments and result according to the declared
  function convention;
- wrapped function to wrapped-function formal: identity when the shape matches;
- proof-carrying finite generator function to
  `(i : Nat) -> i < n -> Except String alpha` through the existing checked
  evidence convention.

These adaptations are forbidden:

- arbitrary wrapped function to raw function;
- wrapped proof/type to raw proof/type;
- proof/type to wrapped value;
- dropping an `Except.error` branch because a fixture happens not to reach it;
- replacing a source function body with a computed Lean shortcut;
- using a Lean axiom or unchecked helper as an adapter.

## Haskell Architecture

Haskell may choose behavior based on declared source identifiers, arity, and an
explicit convention table. That is a calling convention, not semantic proof.

Acceptable Haskell responsibilities:

- translate ordinary SAWCore arguments;
- record each translated argument's `BindingShape`;
- declare helper formal conventions in one place;
- eta-expand function arguments when the convention says how to translate the
  binders and body;
- insert `Pure.pure` and `Bind.bind` according to shape metadata;
- emit exact local obligations for already-designed proof-carrying helpers;
- reject unsupported or under-specified shapes with clear diagnostics.

Forbidden Haskell responsibilities:

- recognizing `addNat`, `mulNat`, `intAdd`, or any other function body as
  "safe" by semantic inspection;
- proving that a wrapped function is total;
- proving that an index is in bounds;
- simplifying arithmetic or bitvector expressions to avoid an obligation;
- detecting that a generated Lean term is syntactically `Pure.pure`;
- rewriting `Stream.rec`, `foldr`, `foldl`, tuple updates, or Cryptol wrappers
  into an alternative semantic form unless a checked Lean contract justifies
  that exact rewrite;
- adding a fallback path when the convention table does not fit.

## Lean Support Library Policy

This phase may add or adjust thin wrapped helper definitions only when their
types directly encode the Phase beta convention and their bodies preserve
errors visibly.

Allowed:

- small helper definitions such as `foldrM`/`foldlM`-style wrappers that take
  wrapped values/functions and return `Except String ...`;
- simple checked adapters that preserve the `Except` error path;
- documentation comments explaining the helper's source convention;
- axiom audits for any existing helper that is treated as trusted support.

Forbidden:

- Lean automation intended to prove current examples;
- new axioms;
- helper definitions that duplicate nontrivial SAW semantics without a
  realization theorem or exact source correspondence;
- a helper that rawifies an arbitrary `Except` computation;
- adding a theorem solely so the conformance fixture turns green in this phase.

If a helper requires a substantial semantic proof, leave the row as a known gap
and move that proof-library work to a later phase.

## Testing Plan

All tests must remain under the `make -C otherTests/saw-core-lean conformance`
infrastructure.

Before changing code, run or inspect the focused known-gap rows:

- `differential/tuple_update_helpers`
- `differential/vector_fold`
- `differential/cryptol_ec_fold_scan`
- `differential/stream_helpers`

After each implementation checkpoint:

1. run the focused conformance rows you touched;
2. update `.known-gap.expected` only when the failure stage or diagnostic has
   legitimately changed;
3. promote a `.known-gap` row only when it performs a true SAW-vs-Lean
   differential comparison of the backend-emitted artifact;
4. update `otherTests/saw-core-lean/CONFORMANCE.md` with the new status;
5. update `TODO.md` if a row is reclassified outside this phase;
6. run the full conformance target before committing.

Do not weaken the harness. Do not hand-write a Lean observer that reconstructs
the expected value. Do not mark a case green because the artifact elaborates
with unrelated proof stubs. For differential rows, SAW and Lean must compare
the same backend-emitted observation.

## Acceptance Criteria

This phase is complete when all of the following are true:

1. All focused value-level wrapping rows are either promoted to conforming
   differential tests or explicitly reclassified as non-wrapping known gaps.
2. `foldr`/`foldl` and representative Cryptol fold wrappers no longer require
   raw functions where wrapped helper function formals are expected.
3. Tuple update helper updater lambdas are handled by the shared function-shape
   convention or remain pinned with a precise reason that is not fixture
   specific.
4. Stream helper failures are either fixed by general expected-shape propagation
   or classified as a separate recursor/proof-carrying stream design issue.
5. No new Haskell semantic classifier, Lean-AST recognizer, fallback path, or
   fixture-specific patch has been added.
6. No new Lean automation has been added.
7. Unsupported higher-order cases reject clearly rather than silently rawifying
   wrapped computations.
8. The conformance matrix and TODO backlog distinguish:
   - conforming differential rows;
   - expected proof obligations;
   - known gaps we intend to close later;
   - final boundaries, if any have been explicitly decided.
9. Full `make -C otherTests/saw-core-lean conformance` passes with known gaps
   visibly reported as known gaps, not hidden as conformance.

## Stop Conditions

Stop and reassess before coding further if any of these happen:

- a proposed fix requires converting `(A -> Except String B)` into `A -> B`;
- a fixture passes only after recognizing a particular generated Lean term;
- a helper would need to assume totality, purity, productivity, or bounds
  without a visible Lean obligation;
- a stream helper fix turns into a `Prelude.fix`/`MkStream` semantic rewrite;
- a fold helper fix depends on knowing that `addNat`, `mulNat`, or `intAdd`
  cannot fail;
- a tuple update fix depends on the current fixture's literal pair shape;
- a solution adds a second path that preserves old behavior "just in case";
- a change requires broad proof-library work or proof automation;
- more than one new special-case convention is needed and no common abstraction
  explains them.

At a stop condition, keep the relevant fixture pinned, write the precise design
question in `TODO.md`, and ask for a design decision. Do not continue by
patching around the problem.

If continuing would require user input and the only alternative is to break one
of this document's rules, the agent may declare this goal complete for the
current run at that stopping point. That is not a claim that the backend work is
finished; it means the safe execution of this goal has reached a design
decision boundary. The user can then respond with the needed decision and
restart or revise the goal.

## Expected Work Order

1. Survey the focused known gaps and confirm each root cause:
   tuple updater function shape, vector fold function shape, Cryptol fold
   wrapper function shape, and stream recursor expected shape.
2. Decide whether the existing `UseArgFunction` is sufficient. If not, design
   the smallest reusable extension to describe function argument conventions.
3. Implement the convention once in the wrapped-helper application path.
4. Apply it first to `foldr`/`foldl`, because these have a clear helper formal
   shape and no proof/datatype side issue.
5. Re-run `differential/vector_fold` and
   `differential/cryptol_ec_fold_scan`.
6. Apply the same abstraction to tuple update helpers only if it fits without a
   tuple-specific semantic rewrite.
7. Investigate `stream_helpers` last. Promote it only if the fix is ordinary
   expected-shape propagation; otherwise reclassify it as recursor/stream
   design work.
8. Update conformance documentation and TODO classifications.
9. Run the full conformance suite.
10. Commit the checkpoint only after the code, docs, and tests tell a coherent
    story.

## Anti-Cheat Rules

The following are explicitly forbidden even if they make tests pass:

- special-case the names `tuple_update_helpers`, `vector_fold`,
  `cryptol_ec_fold_scan`, or `stream_helpers`;
- special-case `addNat`, `mulNat`, `intAdd`, or literal Nat/Int fold bodies as
  pure functions;
- rewrite a failing source term into a hand-authored equivalent Lean term;
- add a support-library theorem as an axiom;
- add `by sorry`, `admit`, `unsafe`, native-evaluation trust, or `bv_decide` to
  discharge a wrapping fixture;
- change a differential observer so it reconstructs the expected value instead
  of importing and inspecting the emitted artifact;
- delete `.known-gap` rows without promoting them to true differential tests or
  replacing them with a sharper pinned failure;
- loosen expected diagnostics so a different failure is accepted silently;
- add a fallback branch that tries the old emission when the new convention
  rejects;
- mark a proof-support failure as wrapping-complete without recording the
  reclassification in the conformance matrix or TODO backlog.

If tempted to do one of these, the right action is to stop and write down the
missing abstraction or separate design problem.
