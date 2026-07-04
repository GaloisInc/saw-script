# Higher-Order Proof-Carrying Wrappers Goal

**Date**: 2026-07-03

**Status**: Goal document for the next backend-completion sprint after the
higher-order value-function convention checkpoint. This is the execution
contract for this phase. Do not edit it during execution to make the work
easier; if it is wrong, incomplete, or unsafe, stop and report the decision
point.

## Just Woke Up: Start Here

The next backend blocker is higher-order proof-carrying wrappers for
bounds/index-sensitive operations.

The current witness is:

- `otherTests/saw-core-lean/drivers/implRev4`

Current baseline diagnostic:

```text
Error translating: Refusing to translate primitive at.

Reason: checked bounds/index contracts require exactly 4 argument(s);
under-applied or over-applied proof-carrying operations must use a
higher-order proof-wrapper design before they can be emitted soundly
```

This rejection is good. It prevents the backend from silently discarding a
bounds proof obligation when a checked/indexing operation is used as a function
value or reaches the emitter at a non-exact arity.

The task is to decide and implement the smallest principled extension that
carries the required Lean proof obligation through higher-order function
values. If that cannot be done cleanly, preserve the rejection and record the
sharper blocker. Do not make `implRev4` pass by restoring raw/defaulting
fallbacks or by trusting Haskell-side reasoning.

Before changing code, read:

1. this document;
2. `doc/2026-07-02_position-callee-calculus.md`;
3. `doc/2026-07-02_position-callee-conventions-design.md`;
4. `doc/2026-06-30_bounds-index-obligations-plan.md`;
5. `doc/2026-07-03_higher-order-function-conventions-goal.md`;
6. `doc/2026-07-01_example-refresh-inventory.md`;
7. the execution-order section of `TODO.md`;
8. the bounds/index rows in `otherTests/saw-core-lean/CONFORMANCE.md`;
9. `src/SAWCoreLean/SpecialTreatment.hs`, especially checked application and
   argument-shape declarations;
10. `src/SAWCoreLean/Term.hs`, especially application dispatch, residual
    primitive handling, and higher-order function adaptation.

## Execution Goal

At the end of this phase, the backend should have a clear answer for
higher-order checked bounds/index operations:

1. emit a sound Lean term whose function value carries the required proof
   contract to the point where the index operation occurs; or
2. reject with a precise diagnostic that names the unsupported proof-carrying
   higher-order shape.

The successful implementation target is not proof automation. Generated Lean
may contain visible local obligations with `by sorry` placeholders in emitted
outlines. The goal is sound emission shape: the obligation must be present,
must mention the real translated bounds/index terms, and must be consumed by a
checked helper. Proving those obligations belongs to a later proof-ergonomics
phase.

The minimal useful slice is:

1. reduce `implRev4` to the exact non-exact-arity checked/indexing shape it
   exposes;
2. add or identify a focused conformance/obligation litmus for that shape;
3. implement one general convention for proof-carrying function values, or
   decide that the shape should remain rejected for now;
4. validate that no checked bounds/index operation falls back to
   `atWithDefaultM`, unchecked raw `at`, or proof-erasing function emission.

## Central Invariant

For any source operation that requires a proof-side condition, the emitted Lean
must follow this discipline:

```text
source checked operation + source arguments + use-site function convention
  -> visible Lean proposition + Lean-checked evidence slot + checked helper
```

When the operation is higher-order, the proof contract moves with the function
value. It must not disappear merely because the operation is partially applied,
eta-expanded, passed as an argument, returned from a branch, or applied later.

Acceptable function shapes may include:

- eta-expanded functions that introduce the missing runtime/index arguments;
- functions that emit a local obligation when the final checked operation is
  reached;
- functions whose formal convention explicitly includes a proof/evidence slot;
- wrapper records/structures only if they make the proof-carrying contract
  more explicit and remain thin, auditable syntax carriers.

The convention must not:

- turn a partial checked operation into an unchecked total function;
- invent a default value for out-of-bounds cases;
- trust a SAW proof object as Lean evidence;
- prove or simplify bounds in Haskell;
- inspect generated Lean syntax to decide whether a proof obligation is
  satisfied;
- rely on a fixture-specific residual primitive path.

## Non-Negotiable Rules

- Haskell stays dumb. It may translate syntax, follow declared conventions,
  construct proposition syntax, wire proof variables into checked helpers, emit
  obligations, and reject unsupported shapes. It must not prove semantic
  equivalences.
- Do not add Haskell classifiers that determine an index is in bounds, a branch
  is unreachable, a vector length arithmetic fact is true, or a function is
  total.
- Do not special-case `implRev4`, a driver path, a generated Lean name, or a
  particular Cryptol residual shape.
- Do not special-case primitive bodies such as `at`, `ecAt`, `Prelude.at`, or
  generated helper names except through a declared checked-application
  contract table.
- Do not add old fallback, backup, compatibility, or defaulting behavior.
- Do not emit unchecked `at`, `atWithDefaultM`, or a raw vector lookup as the
  realization of a proof-carrying access unless a Lean-checked proof makes the
  default branch unreachable.
- Do not add Lean automation, convenience tactics, simp bundles, generated
  proof scripts, BV automation, or proof-library work for this phase.
- Do not hide failures by moving rows out of the harness or weakening
  observers.
- Do not call Lean elaboration with unresolved local obligations proof
  discharge.

## In Scope

### Higher-Order Checked Bounds/Index Operations

This phase covers checked/indexing operations whose fully applied form is
already handled by the proof-carrying bounds/index infrastructure, but whose
non-exact-arity use is currently rejected.

Representative source families:

- residual `Prelude.at`/Cryptol `at` shapes that require an index bound;
- checked `atWithProof`-style function values if they arise in the same
  convention path;
- helper calls whose missing arguments are ordinary value/index arguments and
  whose final application can expose the same checked proposition used by the
  fully applied operation.

The first concrete witness is `drivers/implRev4`. Add a smaller focused row if
`implRev4` is too large to serve as the primary design guardrail.

### Focused Guardrails

Use or add minimal tests in these categories:

- `otherTests/saw-core-lean/obligations/*` for emitted obligation shape;
- `otherTests/saw-core-lean/differential/*` only if the row performs a true
  SAW-vs-Lean observed outcome comparison without relying on proof stubs;
- `otherTests/saw-core-lean/saw-boundary/*` for shapes that must remain
  rejected;
- `drivers/implRev4` only after a focused row explains the same failure.

Any new test must be a small litmus. Do not add large examples to conformance.

## Out Of Scope

The following are not part of this phase:

- proving generated bounds obligations;
- derived arithmetic proof support for reverse/split/update/transpose;
- broad Lean proof automation;
- stream productivity or `Stream.rec` design;
- direct recursor realization;
- user datatypes, `ListSort`, `FunsTo`, loaded primitive/axiom declarations,
  injected Lean code policy, or SMT arrays;
- remaining proof-primitive theorem realization work;
- large crypto/LLVM proof discharge;
- final SAW-side proof replay UX.

If one of these surfaces is the real blocker for `implRev4`, stop and record
that sharper classification instead of broadening this sprint.

## Design Questions To Resolve Before Editing

Answer these before implementation:

1. What exact SAWCore residual term in `implRev4` reaches primitive `at` at
   non-exact arity?
2. Is the operation under-applied, over-applied, passed as an argument, returned
   as a value, or hidden inside a branch/fold/recursor convention?
3. What is the fully applied checked contract for the same operation?
4. Which missing arguments are ordinary values or indices, and where should the
   Lean proposition be emitted?
5. Does the existing checked-application contract table have enough metadata to
   describe the function value, or is a separate proof-carrying function
   convention needed?
6. How will the emitted Lean type prevent using the function without supplying
   or creating checked evidence?
7. Which cases must remain rejected to avoid proof erasure?

Acceptable answers are syntactic and representational: source arity, argument
modes, expected positions, binder conventions, proposition construction, and
checked helper application. Do not answer by appealing to semantic facts about
the current example's indices.

## Allowed Implementation Moves

Allowed:

- extend the checked-application contract metadata so a source primitive can
  describe both exact-arity and higher-order proof-carrying use;
- introduce a separate explicit convention for proof-carrying function values
  if that is cleaner than overloading ordinary value-function conventions;
- eta-expand a checked operation when its source type exposes the missing
  binders and their positions;
- emit a local proof obligation at the final checked operation site;
- pass Lean-checked evidence into existing checked helpers;
- reject unsupported non-exact-arity forms with a diagnostic that identifies
  the missing convention;
- add narrow litmus tests for each distinct shape.

Forbidden:

- adding a function wrapper that throws away the source proof argument and also
  omits the replacement Lean obligation;
- mapping partial checked access to `atWithDefaultM` with an arbitrary default;
- accepting source proof terms as Lean proofs without rechecking;
- normalizing arithmetic to avoid emitting the obligation;
- adding a second "try old emission" path;
- changing broad goldens before the focused shape is understood;
- modifying Lean support libraries solely to automate the proof.

## Testing Plan

Use focused tests first. Do not start with the full broad driver suite.

1. Capture the current `drivers/implRev4` diagnostic.
2. Reduce the failing shape into a minimal obligation or boundary row if no
   focused row already covers it.
3. Run the focused row before implementation and record whether it is a known
   gap or boundary.
4. Implement the convention or sharpen the rejection.
5. Promote an obligation row only when the emitted artifact exposes the exact
   proof contract and forbidden bypasses are absent.
6. Promote a differential row only when it compares actual SAW and Lean
   observations and does not depend on proof stubs.
7. Re-run `drivers/implRev4` after focused validation.
8. Run `make -C otherTests/saw-core-lean conformance`.
9. Run `cabal test saw-core-lean-smoketest` if shared dispatch, residual
   primitive handling, or contract-table code changes.
10. Run `git diff --check` before every commit.

The broad `make -C otherTests/saw-core-lean test` sweep is useful before a
major checkpoint, but failures there are not automatically in scope. Preserve
unrelated known gaps.

## Acceptance Criteria

This phase is complete when all are true:

1. The higher-order proof-carrying checked/indexing surface has an explicit
   design in code or an explicit reason it remains rejected.
2. A small focused row pins the behavior.
3. `drivers/implRev4` is either current emission under the new convention or is
   classified with a sharper blocker than the generic non-exact-arity checked
   contract rejection.
4. No old fallback/defaulting/raw lookup behavior has been restored.
5. No Haskell semantic classifier, generated-Lean recognizer, fixture special
   case, proof automation, or proof-erasing function adapter has been added.
6. `TODO.md`, `CONFORMANCE.md`, and the example inventory reflect the result.
7. Focused validation and full conformance validation have been run and their
   results are recorded.

## Stop Conditions

Stop and ask for a design decision if any of these happen:

- the only apparent fix requires using a checked/indexing operation as a raw
  function without carrying a proof contract;
- the solution depends on proving or simplifying bounds in Haskell;
- the solution needs generated Lean syntax inspection;
- the shape requires a dependent function convention not covered by the
  position/callee calculus;
- the implementation would need Lean automation or proof-library work;
- `implRev4` reduces to stream, recursor, datatype, or proof-primitive gaps
  rather than a higher-order checked/index wrapper gap;
- more than one new local convention appears and no common abstraction explains
  them;
- completing the task would require changing this goal document during
  execution.

If continuing would require user input and the only alternative is to break one
of this document's rules, the agent may declare the goal done for the current
run at that stopping point. That means the safe execution path has reached a
decision boundary, not that the backend is complete.

## Expected Work Order

1. Confirm the current `implRev4` diagnostic.
2. Inspect the residual SAWCore shape and identify the exact primitive
   application structure.
3. Add or locate a small focused litmus for the same shape.
4. Decide whether the existing checked-application contract can express the
   required function convention.
5. Implement the smallest explicit convention, or preserve rejection with a
   sharper diagnostic.
6. Validate the focused litmus.
7. Validate `drivers/implRev4`.
8. Update `TODO.md`, `CONFORMANCE.md`, and the example inventory.
9. Run focused validation, full conformance, and smoke tests as required.
10. Commit only when code, docs, and tests tell one coherent story.

## Anti-Cheat Rules

The following are explicitly forbidden even if they make tests green:

- special-case `implRev4`;
- special-case a generated Lean helper name or fixture path;
- treat checked access as total because the current example happens to be
  in-bounds;
- emit `atWithDefaultM` as a proof-carrying checked access without a
  Lean-checked unreachable-default proof;
- trust a SAW proof argument as a Lean proof;
- rewrite the source term into a hand-authored equivalent Lean expression;
- insert Lean axioms, `sorry`-based accepted proofs, tactic scripts, or
  native-eval proof shortcuts;
- weaken differential observers or obligation shape checks;
- delete, skip, or hide known gaps instead of promoting them or replacing them
  with sharper pinned findings.

If tempted to do any of these, stop and record the missing abstraction.
