# Higher-Order Value Function Conventions Goal

**Date**: 2026-07-03

**Status**: Goal document for the next backend-completion sprint after the
position/callee raw-logical checkpoint. This document is the execution
contract for the phase. Do not edit it during execution to make the work
easier; if it is wrong, incomplete, or unsafe, stop and report the decision
point.

## Just Woke Up: Start Here

The task is to finish the next narrow slice of value-level wrapping
conventions for higher-order helper calls.

The previous checkpoints established three important facts:

1. runtime value computations use `Except String`;
2. raw logical/type/proof infrastructure must stay raw;
3. adaptations must be declared by position and callee convention, not inferred
   by inspecting emitted Lean syntax.

The next live example-facing blocker is not proof automation and not a broad
example refresh. It is:

> Some SAW value-level function arguments are passed to Lean helpers whose
> formals expect `Except String`-aware functions.

This phase makes that convention explicit for ordinary value functions. The
first targets are folds:

- `Prelude.foldr` / `Prelude.foldl` routed to `foldrM` / `foldlM`;
- `Cryptol.ecFoldl` and `Cryptol.ecFoldlPrime` when they lower to those finite
  folds;
- the `drivers/sequences.t18` `foldl (+)` example once the same focused
  convention is validated.

Do not start by changing code. First read:

1. this document;
2. `doc/2026-07-02_position-callee-calculus.md`;
3. `doc/2026-07-02_position-callee-conventions-design.md`;
4. `doc/2026-07-01_complete-wrapping-migration-goal.md`;
5. `doc/2026-07-01_example-refresh-inventory.md`;
6. the current execution-order section of `TODO.md`;
7. the vector/fold rows in `otherTests/saw-core-lean/CONFORMANCE.md`;
8. `src/SAWCoreLean/SpecialTreatment.hs`, especially `UseArgShape` and
   `UseMapsToWrapped`;
9. `src/SAWCoreLean/Term.hs`, especially
   `translateFunctionToWrappedFormal`,
   `translateFunctionConventionBinders`, `functionConventionValueSlot`,
   `functionConventionResultIsValue`, `buildLifted`, and the
   `UseMapsToWrapped` branch in `originalDispatchWithShape`.

## Execution Goal

At the end of this phase, the backend should have a small, auditable
higher-order value-function convention for wrapped helper formals.

The goal is not that every fold proof becomes automatic. The goal is that SAW
terms using ordinary value-level fold functions emit sound Lean code or reject
with a principled diagnostic. If the emitted artifact contains visible proof
obligations, that is acceptable. Proving them is later proof-ergonomics work.

The minimal successful slice is:

1. focused fold rows no longer reject merely because the helper formal expects
   a wrapped value function;
2. the emitted Lean function adapter is explained by a declared convention,
   not by recognizing `+`, `addNat`, `intAdd`, or any generated Lean term;
3. `differential/vector_fold` is either promoted to true differential
   conformance or reclassified with a sharper non-function-convention blocker;
4. `differential/cryptol_ec_fold_scan` is either promoted similarly or
   reclassified with a sharper non-function-convention blocker;
5. `drivers/sequences.t18` is reduced against the focused rows and refreshed
   only if artifact review shows the fold-function convention is the remaining
   blocker.

## Central Invariant

Every higher-order value argument must be translated according to:

```text
source function + helper formal convention + expected position
  -> emitted Lean function shape
```

The convention may:

- eta-expand a source function;
- give value binders wrapped Lean types when the helper formal expects
  wrapped values;
- translate the source body once;
- lift a raw body result with `Pure.pure`;
- sequence wrapped arguments/results through `Bind.bind` when the final result
  remains wrapped and errors stay observable;
- reject when the function's source type or result position is not a
  value-level computation.

The convention must not:

- turn an arbitrary `(A -> Except String B)` into `A -> B`;
- prove that a function is pure, total, terminating, in-bounds, or non-erroring;
- inspect generated Lean syntax to discover that a term is `Pure.pure`;
- special-case the concrete function body used by a fixture.

## Non-Negotiable Rules

- Haskell stays dumb. It may translate syntax, carry explicit shape metadata,
  apply declared helper conventions, insert error-preserving binds, emit proof
  obligations, and reject unsupported shapes. It must not prove semantic
  equivalences.
- Do not add Haskell semantic classifiers, simplifiers, normalizers, or
  generated-Lean recognizers.
- Do not special-case fixture names such as `vector_fold`,
  `cryptol_ec_fold_scan`, `sequences.t18`, or any driver path.
- Do not special-case function bodies such as `+`, `addNat`, `mulNat`,
  `intAdd`, boolean operators, literals, or Cryptol overload wrappers.
- Do not add a fallback branch that tries old emission when the convention
  rejects.
- Do not preserve obsolete fallback/defaulting behavior to keep broad examples
  green.
- Do not add Lean automation, convenience tactics, simp bundles, BV automation,
  proof scripts, or proof-library work whose purpose is to discharge current
  examples.
- Do not weaken differential observers, delete known gaps without promotion, or
  refresh broad driver goldens before artifact review.
- Do not count elaboration with `sorry` as proof discharge.

## In Scope

### Ordinary Value-Function Arguments

This phase covers higher-order arguments whose source role is an ordinary
value-level function and whose callee formal expects a wrapped value function.

Representative source shapes:

- lambdas;
- named local functions;
- primitive or Prelude function values with enough source type information to
  eta-expand;
- partial applications only when the existing translation can determine a
  value-level function type without semantic guessing.

Representative targets:

- `foldrM`;
- `foldlM`;
- finite Cryptol wrappers that lower to those folds.

The implementation should either use the existing `UseArgFunction` convention
or replace it with a richer explicit convention if the current representation
is too implicit. The important property is that the convention is declared at
the helper formal, not discovered from the actual function body.

### Focused Test Rows

Use the focused rows as the primary guardrails:

- `otherTests/saw-core-lean/differential/vector_fold`;
- `otherTests/saw-core-lean/differential/cryptol_ec_fold_scan`;
- the `drivers/sequences.t18` row only after the focused fold rows explain the
  same failure.

If a broad driver still fails because of unrelated bounds, stream, or proof
support gaps, preserve that failure and classify it. Do not turn this phase
into a broad driver refresh.

## Out Of Scope

The following are not part of this phase:

- higher-order proof-carrying/indexing contracts such as the `implRev4`
  under-applied `at` surface;
- function-carrier equality, except to record a blocker if it directly appears
  while validating the focused fold rows;
- stream/productivity/`Stream.rec` design;
- direct recursor realization;
- user datatypes, `ListSort`, `FunsTo`, loaded primitive declarations, loaded
  axiom declarations, or injected Lean code policy;
- direct or derived bounds proof discharge;
- BV/nonzero/arithmetic proof ergonomics;
- final SAW-side proof replay UX;
- large crypto/LLVM stress examples.

If one of these surfaces appears while working on a fold row, stop and
reclassify the row with the sharper blocker. Do not broaden this sprint.

## Design Questions To Resolve Before Editing

Before making implementation changes, answer these locally in notes or in the
first commit message:

1. Why does the current `UseArgFunction` path reject the focused fold rows?
2. Is the rejection because the actual function lacks a recoverable source
   function type, because the result-position predicate is too weak, because
   overloaded wrappers obscure the value function, or because the helper formal
   convention is under-specified?
3. Can the existing `translateFunctionToWrappedFormal` be made explicit enough
   without adding semantic classification?
4. If a richer convention is needed, what exact metadata does it carry?
5. What cases must remain rejected to avoid rawifying errors?

Acceptable answers are operational and syntactic. They should refer to source
types, binder positions, result positions, declared helper formal conventions,
and translated shapes. They must not refer to semantic purity of the function
body.

## Allowed Implementation Moves

Allowed:

- extend `UseArgShape` or add a sibling convention type if it makes function
  formals more explicit;
- eta-expand a source function when its source type exposes value binders and a
  value result;
- translate lambda bodies under the declared binder shapes;
- adapt raw body results to wrapped results with `Pure.pure`;
- bind wrapped value arguments/results with `Bind.bind` when errors remain
  observable;
- reject type-producing, proof-producing, logical, or unsupported function
  results with a specific diagnostic;
- add narrow conformance rows only if they capture a distinct higher-order
  function convention not already covered.

Forbidden:

- broadening `shouldWrapBinder` or `functionConventionResultIsValue` until a
  current fixture passes without explaining why the predicate is correct;
- recognizing particular primitive names as "safe functions";
- rebuilding a different Lean expression that is merely equivalent to the
  source fold;
- adding a helper that assumes a wrapped computation succeeds;
- adding a compatibility path for old `atWithDefaultM`/fallback behavior;
- moving failing rows out of the harness instead of pinning the real result.

## Testing Plan

Use focused tests first. Do not start with the full broad driver suite.

1. Inspect or run the focused known-gap rows to capture the baseline
   diagnostic:
   - `differential/vector_fold`;
   - `differential/cryptol_ec_fold_scan`.
2. After each implementation checkpoint, run the touched focused rows through
   the conformance infrastructure.
3. Promote a `.known-gap` row only when it performs a true SAW-vs-Lean
   comparison of the backend-emitted artifact.
4. If a row remains failing, update the expected gap only when the failure
   stage or diagnostic legitimately changed and the new reason is sharper.
5. Validate `drivers/sequences.t18` only after the focused fold rows show that
   the convention is correct.
6. Run full `make -C otherTests/saw-core-lean conformance` before committing.
7. Run `cabal test saw-core-lean-smoketest` if the implementation touches
   shared dispatch, shape, or helper-convention code.
8. Run `git diff --check` before every commit.

The broad `make -C otherTests/saw-core-lean test` sweep is useful before a
major checkpoint, but failures there are not automatically in scope. Classify
them against this document.

## Acceptance Criteria

This phase is complete when all are true:

1. Higher-order value-function helper formals have an explicit convention in
   the Haskell code.
2. The focused fold rows are promoted to conforming differential tests or
   pinned with sharper non-function-convention blockers.
3. `sequences.t18` has been checked against the new convention and either
   refreshed as current emission or recorded with a precise remaining blocker.
4. No new semantic classifier, generated-Lean recognizer, fixture special case,
   fallback path, or proof automation has been added.
5. Unsupported higher-order cases reject clearly.
6. `TODO.md` and `CONFORMANCE.md` distinguish closed fold-function convention
   work from remaining proof-carrying, stream, bounds, and stress gaps.
7. Focused validation and full conformance validation have been run and their
   results are recorded.

## Stop Conditions

Stop and ask for a design decision if any of these happen:

- the only apparent fix requires converting `(A -> Except String B)` into
  `A -> B`;
- the solution depends on knowing that a particular function body cannot fail;
- the implementation needs generated Lean syntax inspection;
- more than one new local convention is needed and no common abstraction
  explains them;
- a fold row exposes proof-carrying bounds/index contracts rather than an
  ordinary value-function convention;
- `sequences.t18` cannot be reduced to the focused fold rows;
- a broad driver refresh would be needed before the focused rows tell a
  coherent story;
- continuing would require Lean automation or proof-library development.

If continuing would require user input and the only alternative is to break one
of this document's rules, the agent may declare the goal done for the current
run at that stopping point. That means the safe execution path has reached a
decision boundary, not that the backend is complete.

## Expected Work Order

1. Confirm the current focused diagnostics for `vector_fold` and
   `cryptol_ec_fold_scan`.
2. Inspect the source terms and the current `UseArgFunction` path to identify
   the exact missing metadata or predicate.
3. Decide whether to keep `UseArgFunction` or replace/extend it with a richer
   function-formal convention.
4. Implement the convention once in the wrapped-helper application path.
5. Validate `foldr`/`foldl` first.
6. Validate `Cryptol.ecFoldl`/`ecFoldlPrime` through the same path.
7. Check `drivers/sequences.t18` and classify any remaining failures.
8. Update `CONFORMANCE.md`, `TODO.md`, and, if needed,
   `doc/2026-07-01_example-refresh-inventory.md`.
9. Run focused validation, full conformance, and smoke tests as required.
10. Commit only when the code, docs, and tests tell one coherent story.

## Anti-Cheat Rules

The following are explicitly forbidden even if they make the tests green:

- special-case the directory or test names;
- special-case addition, multiplication, comparisons, or Cryptol overloaded
  wrapper names;
- silently treat a wrapped function as raw;
- rewrite a fold into a hand-authored equivalent expression;
- insert a Lean axiom, `sorry`-based proof, tactic script, or native-eval proof
  shortcut as part of the backend feature;
- change an observer so it reconstructs the expected value rather than
  inspecting the emitted artifact;
- update broad `.lean.good` files without reviewing whether the emitted
  artifact is the correct current emission;
- delete or hide a known gap instead of promoting it or replacing it with a
  sharper pinned finding.

If tempted to do any of these, stop and record the missing abstraction.
