# SAWCore Lean Backend Roadmap

This is the working roadmap for bringing the SAW Lean backend to a sound,
usable state. Detailed design notes live in `doc/`; this file tracks the
current execution order and decision points.

## Goal

Use Lean as a SAW proof backend for discharging proof obligations, similar in
role to an SMT backend, while preserving the SAWCore semantics exactly.

Hard requirements:

- Never erase or reinterpret `Except.error`.
- Reject unsupported SAWCore shapes before emitting semantically different
  Lean.
- Do not add unjustified Lean axioms or widen the trusted base.
- Prefer deterministic wrapping decisions over emitted-Lean pattern matching.
- Keep tests and goldens aligned with Lean elaboration, not just textual output.

## Current State

The Phase-beta expected-shape migration is partially complete and moving in
the right direction:

- `BindingShape` now tracks raw, wrapped, and function-shaped local bindings.
- Result shapes are carried by translation paths instead of rediscovered from
  emitted Lean syntax.
- The old general Lean result-shape classifier has been removed.
- Ordinary applications, shared `let`s, recursor case fields, and many wrapped
  helper calls now use explicit shape information.
- The old broadly defaulting stream helpers have been removed from the support
  library.
- Driver and boundary tests pass except for the intentionally unresolved
  `sawcore_prelude_auto_emit` path.

The backend is not yet sound for arbitrary accepted SAWCore. The main remaining
soundness surface is accepted `fix` shapes whose productivity is not checked
locally.

## Priority 0: Soundness Blockers

- [ ] Close the `fix` productivity surface with a proof-carrying contract.
  - Current risk: `classifyFix` recognizes outer stream/vector shapes, but does
    not prove recursive lookups are productive.
  - Current lowering still passes `saw_unreachable_default` into
    `mkStreamFix`, `mkStreamFixPair`, and `genFixM`.
  - Required outcome: every accepted lowering must either supply Lean-checked
    evidence of productivity or emit an explicit proof obligation. A completed
    proof artifact must not rely on a hidden Haskell-side assumption.
  - Preferred direction: add Lean-level productivity contracts, teach the
    translator to discharge the common cases automatically, and support a mode
    that emits obligations for cases automation cannot prove.
  - Negative tests to add:
    - `fix (Stream a) (\rec -> MkStream a (\i -> rec[i]))`
    - pair-stream variants where either component reads the current/future
      index
    - `fix (Vec n a) (\rec -> gen n a (\i -> rec[i]))`
    - any accepted shape where `saw_unreachable_default` becomes observable
  - Design reference: `doc/2026-06-26_proof-carrying-soundness-contracts.md`.

- [ ] Ensure rawification never hides residual per-index effects.
  - Keep `rawifyExceptToRaw` as a gate, not a convenience rewrite.
  - Add tests where `Prelude.error` remains under an index-dependent stream,
    iterate, or fix body and must reject.
  - Add tests asserting obsolete helpers do not appear in emitted output:
    `mkStreamM`, `mkStreamFixM`, `mkStreamFixPairM`, `cryptolIterateM`.

- [ ] Reject unsupported raw/proof/type/function uses of `Prelude.error`.
  - Current behavior may emit an `Except` expression and rely on Lean
    elaboration failure in some raw contexts.
  - Required outcome: unsupported error positions should fail at SAW
    translation with a direct diagnostic.

## Priority 1: Prelude Auto-Emit

- [ ] Decide the contract for `write_lean_sawcore_prelude`.
  - Current state: `sawcore_prelude_auto_emit` fails Lean elaboration.
  - This is not a golden-refresh issue. The auto-emit path walks SAWCore
    Prelude declarations directly through `SAWModule.translateDef`, not through
    the normalized Cryptol-user-term path.
  - Current generated shapes include invalid or suspicious Phase-beta forms
    around `Sort u`, equality recursors, and already-wrapped binders.

- [ ] Choose one principled implementation path:
  - Option A: quarantine auto-emitted Prelude as experimental and emit only a
    small allowlist whose Lean elaboration is proven by tests.
  - Option B: add a declaration-level expected-shape mode for SAWCore Prelude
    declarations, distinct from normalized user terms.
  - Option C: stop auto-emitting most Prelude definitions and route them to
    hand-written Lean support definitions/theorems.

- [ ] Make the test status unambiguous.
  - `sawcore_prelude_auto_emit` must not have a refreshed `.lean.good` while
    elaboration fails.
  - If quarantined, the test should assert the explicit unsupported status
    rather than silently preserving invalid Lean.

## Priority 2: First-Class Expected Shapes

- [ ] Promote the design from scattered policy to explicit data types.
  - Add first-class equivalents of:
    - `ExpectedShape`
    - `RawReason`
    - `CalleeConvention`
    - richer `BindingShape` carrying relevant type/function information
  - Keep `BindingShape` as the binding environment, but stop using it as the
    only shape abstraction.

- [ ] Centralize adaptation.
  - Target operation:
    - translate naturally and return a shape
    - adapt exactly once to an expected shape
  - Allowed adaptations:
    - raw value to wrapped value with `Pure.pure`
    - wrapped value to raw value only by binding in a continuation
    - raw type/index/proof to raw type/index/proof
    - function rawification only through named, precondition-checked adapters
  - Forbidden adaptations:
    - wrapped proof/type to raw proof/type
    - arbitrary `(a -> Except String b) -> (a -> b)`
    - defaulting on `Except.error`

- [ ] Replace transitional local policy.
  - Audit and migrate uses of:
    - `skipBinderWrap`
    - `inRecursorCaseBinder`
    - `shouldWrapBinder`
    - `typeArgPositions`
    - `natValueResult`
    - ad hoc special cases for `Eq`, `coerce`, `MkStream`, and `fix`
  - The target is not zero local cases; it is named conventions with explicit
    preconditions and regression tests.

- [ ] Make `UseMapsToWrapped` more explicit.
  - Current form records only arity and target name.
  - Add per-formal shape information and result shape so helper calls do not
    need local reconstruction from SAW binder syntax.

## Priority 3: Proof Backend Usability

- [ ] Add Lean simp support for Phase-beta generated goals.
  - Normalize common `Except.ok` / `Pure.pure` / `Bind.bind` patterns.
  - Add lemmas for generated helpers such as `iteM`, `genM`,
    `atWithDefaultM`, `vecSequenceM`, stream/fix helpers, and bitvector
    operations.
  - Avoid lemmas that erase `Except.error` or hide unsupported cases.

- [ ] Update proof examples for wrapped generated goals.
  - Cookbook examples should show the current generated theorem shape, not the
    old raw-era shape.
  - Add small stable proof scripts that users can copy.
  - Keep proof scripts narrow enough that regressions identify a real backend
    or ergonomics issue.

- [ ] Improve generated Lean readability where it does not affect semantics.
  - Reduce unnecessary-looking `Pure.pure` around already-wrapped values.
  - Prefer stable helper names and local names in generated goals.
  - Keep readability changes behind elaboration and proof-regression tests.

## Priority 4: Regression Coverage

- [ ] Add focused shape tests.
  - Datatype-parameter recursor fields where the actual parameter is
    function-shaped.
  - Partial applications through `ite`, wrapped helpers, and higher-order
    arguments.
  - `Nat` as raw index versus wrapped value result, especially `bvToNat` and
    related conversions.
  - Shared `let` RHS dependencies where later RHSs reuse earlier wrapped
    bindings.

- [ ] Add soundness boundary tests.
  - Nonproductive fix rejection.
  - Residual per-index error rejection.
  - Raw/proof/type-position error rejection.
  - Unsupported higher-order rawification rejection.

- [ ] Keep broad validation gates green.
  - `git diff --check`
  - `cabal build exe:saw`
  - `cabal test saw-core-lean-smoketest`
  - Driver and boundary sweep under `otherTests/saw-core-lean`
  - Lean support library build
  - Focused proof examples once Phase-beta proof ergonomics are updated

## Decision Log

- [x] Treat Lean as a proof backend, not just an emitter.
- [x] Preserve SAWCore errors with `Except String`.
- [x] Reject unsupported primitives by default.
- [x] Remove the old emitted-Lean result-shape classifier.
- [x] Remove broadly defaulting stream helpers from the Lean support library.
- [ ] Decide whether arbitrary SAWCore `Prelude.fix` is in scope.
- [ ] Decide the supported contract for auto-emitted SAWCore Prelude
  declarations.
- [ ] Decide how much of the expected-shape design to encode in data types
  before migrating proof ergonomics.

## References

- `doc/2026-06-26_phase-beta-expected-shape.md`
- `doc/2026-06-26_expected-shape-todo.md`
- `doc/2026-05-14_wrap-invariant-audit.md`
- `doc/2026-05-02_residual-trust.md`
- `doc/proof-cookbook.md`
