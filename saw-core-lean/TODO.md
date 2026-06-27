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

## Proof Discharge Workflow

The target backend workflow is two-phase. Lean proof construction does not need
to be fully automated:

1. SAW emits an exact Lean proof obligation for the current verification goal.
   The emitted file may contain a proof stub and should be stable enough for a
   human, tactic, or AI assistant to work against.
2. A user or automation writes/repairs a Lean proof in a separate proof file.
3. SAW later checks the completed proof by invoking the pinned Lean toolchain
   on the exact emitted obligation and proof file. SAW may accept the original
   goal only if Lean kernel-checks a theorem whose type is that obligation, with
   no forbidden escape hatches such as `sorry`, unchecked user axioms, import
   shadowing, or a proof of an unrelated proposition.

This is still proof discharge, even when step 2 is manual or AI-assisted. The
critical soundness boundary is the check step, not automatic proof search.

## Current State

The Phase-beta expected-shape migration has reached a useful checkpoint:

- `BindingShape` now tracks raw, wrapped, and function-shaped local bindings.
- Result shapes are carried by translation paths instead of rediscovered from
  emitted Lean syntax.
- The old general Lean result-shape classifier has been removed.
- Ordinary applications, shared `let`s, recursor case fields, and many wrapped
  helper calls now use explicit shape information.
- The old broadly defaulting stream helpers have been removed from the support
  library.
- `fix` lowerings now use checked helpers with emitted productivity obligations
  rather than hidden Haskell-side productivity assumptions.
- Driver and boundary tests pass except for the intentionally unresolved
  `sawcore_prelude_auto_emit` path.

The backend is not yet complete for arbitrary accepted SAWCore. The next
priority is emission quality: every emitted Lean file should either elaborate
with explicit proof obligations or fail at SAW translation with a clear,
principled diagnostic.

## Priority 0: Emission Soundness

- [x] Close the `fix` productivity surface for emit-stage soundness.
  - Current lowering emits checked helpers (`mkStreamFixChecked`,
    `mkStreamFixPairChecked`, `genFixMChecked`) and split local Lean productivity
    obligations: one local `Prop` binding for the contract and one local proof
    placeholder.
  - The Haskell backend does not need to prove productivity. It emits the exact
    Lean contract and makes the lowering depend on checked evidence.
  - Completed proof artifacts must not rely on a hidden Haskell-side assumption
    or an unresolved generated placeholder.
  - Later proof ergonomics question: decide whether local obligations should be
    lifted into top-level declarations with explicit dependency binders, or
    whether edit-in-place obligation files are acceptable for generated code that
    depends on surrounding locals.
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

## Priority 1: Emission Architecture

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

- [ ] Improve generated Lean readability where it does not affect semantics.
  - Reduce unnecessary-looking `Pure.pure` around already-wrapped values.
  - Prefer stable helper names and local names in generated goals.
  - Keep readability changes behind elaboration and proof-regression tests.

## Priority 2: Regression Coverage

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

## Priority 3: Proof Ergonomics

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

- [ ] Decide the external proof-obligation format.
  - Current productivity obligations are split local lets in emitted Lean.
  - Later ergonomics work can decide whether to lift local obligations into
    top-level declarations with explicit dependency binders, or keep
    edit-in-place generated proof files.

## Priority 4: SAW-Side Proof Checking

- [ ] Add an integrated SAW-side proof-check command.
  - Emit-only mode should produce obligations for offline work without
    claiming success.
  - Check mode should take a completed Lean proof file, rebuild the exact
    obligation context, invoke Lean, reject forbidden proof escapes, and only
    then discharge the SAW goal.
  - The current `otherTests/saw-core-lean/proofs/*` harness validates this
    shape outside SAW; the backend needs the same acceptance rule in SAWScript.
  - This is important for final UX and end-to-end trust, but it comes after the
    emitted Lean shape is stable.

## Decision Log

- [x] Treat Lean as a proof backend, not just an emitter.
- [x] Preserve SAWCore errors with `Except String`.
- [x] Reject unsupported primitives by default.
- [x] Remove the old emitted-Lean result-shape classifier.
- [x] Remove broadly defaulting stream helpers from the Lean support library.
- [x] Treat soundness-side conditions as emitted Lean obligations, not Haskell
  automation requirements.
- [x] Prioritize emission correctness and stable generated Lean before adding
  integrated SAW-side proof-check UX.
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
