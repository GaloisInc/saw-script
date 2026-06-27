# SAWCore Lean Backend Roadmap

This is the working roadmap for bringing the SAW Lean backend to a sound,
usable state. Detailed design notes live in `doc/`; this file tracks the
current execution order and decision points.

## Goal

Mirror the Rocq backend's user-visible feature surface in Lean while preserving
the SAWCore semantics exactly. This includes Lean proof-obligation discharge
analogous to `offline_rocq`, direct term emission analogous to
`write_rocq_term`, support-library regeneration analogous to the Rocq prelude
emitters, and whole-Cryptol-module extraction analogous to
`write_rocq_cryptol_module`.

Hard requirements:

- Never erase or reinterpret `Except.error`.
- Reject unsupported SAWCore shapes before emitting semantically different
  Lean.
- Do not add unjustified Lean axioms or widen the trusted base.
- Prefer deterministic wrapping decisions over emitted-Lean pattern matching.
- Keep tests and goldens aligned with Lean elaboration, not just textual output.
- Do not treat Rocq feature parity as permission to emit unsound Lean; parity
  gaps must reject cleanly until they can be implemented with a defensible
  contract.

## Rocq Parity Surface

The intended public surface mirrors the Rocq backend commands, modulo legacy
`coq` aliases:

- `write_lean_term` mirrors `write_rocq_term`.
- `write_lean_cryptol_module` mirrors `write_rocq_cryptol_module`; this is an
  in-scope feature, not a legacy path to disable.
- `write_lean_sawcore_prelude` mirrors `write_rocq_sawcore_prelude`.
- `write_lean_cryptol_primitives_for_sawcore` mirrors
  `write_rocq_cryptol_primitives_for_sawcore`.
- `offline_lean` mirrors `offline_rocq`.

Proof discharge is the primary verification workflow, but the whole backend goal
is Rocq feature parity with Lean's kernel as the checker.

Working matrix: `doc/2026-06-26_rocq-parity-matrix.md`.

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
- The auto-emitted SAWCore Prelude path now has an explicit raw-vs-wrapped
  declaration convention and elaborates under the focused driver test.

The backend is not yet complete for arbitrary accepted SAWCore or for the full
Rocq feature surface. The next priority is emission quality: every emitted Lean
file should either elaborate with explicit proof obligations or fail at SAW
translation with a clear, principled diagnostic.

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
  - Added smoke coverage where `Prelude.error` remains under an
    index-dependent direct stream, stream-corecursive `fix`, or Cryptol
    `iterate` step and must reject.
  - Added driver-harness checks asserting obsolete helpers do not appear in
    emitted output:
    `mkStreamM`, `mkStreamFixM`, `mkStreamFixPairM`, `cryptolIterateM`.
  - Remaining work: add end-to-end Cryptol driver coverage for representative
    source programs on both `offline_lean` and `write_lean_cryptol_module`
    paths once the exact user-facing rejection wording is stable.

- [x] Reject unsupported raw/proof/type/function uses of `Prelude.error`.
  - `Prelude.error` is now gated by the same wrapped-value-domain predicate
    used for binder/result shape decisions.
  - Raw Nat/Num indices, types, propositions/proofs, and function results fail
    at SAW translation with a direct diagnostic instead of emitting an
    ill-shaped `Except` term and relying on Lean elaboration failure.

- [x] Design and implement initial proof obligations for raw-position Cryptol
  partiality.
  - Raw `Prelude.error` at Nat/index, type, proof, or function results now emits
    a local `False` obligation and produces the raw result through
    `False.elim`, rather than manufacturing a default or trying to use
    `Except.error` at a raw type.
  - Polynomial literals now elaborate as an explicit obligation-emission case.
  - Full SHA512 moves past the raw-error blocker and now exposes the next
    blocker: unsupported SHA-style `Prelude.fix`.
  - Remaining ergonomics work: replace generic `False` obligations with more
    specific bounds/unreachable-branch propositions when the translator can
    state them cleanly.

- [ ] Extend proof-carrying recursion coverage for SHA-style recurrences.
  - The SHA512 residual probe confirms `sha`, `SHA_2_Common'`,
    `processBlock_Common`, and `SHAUpdate` all now fail first on unsupported
    `Prelude.fix`; raw `Prelude.error` is no longer the first translation
    blocker.
  - Existing checked helpers cover several stream/vector shapes but not the
    SHA message-schedule/compression recurrences in this module.
  - Any extension should be a Lean contract/proof-obligation path, not another
    hidden Haskell-side productivity classifier.

- [x] Decide and implement the contract for `write_lean_sawcore_prelude`.
  - The auto-emit path walks SAWCore Prelude declarations directly through
    `SAWModule.translateDef`, not through the normalized Cryptol-user-term path.
  - The chosen convention is explicit:
    raw proof/type infrastructure auto-emits in `RawValueMode` over `Sort u`;
    wrapped value-domain facades auto-emit or replace into `Except String`
    definitions whose carrier binders live in `Type u`.
  - `sawLet`, `xor`, and `boolEq` use small hand-shaped wrapped facades where
    direct SAWCore-body emission would mix raw callback arguments with wrapped
    value conventions.
  - Some proof-equation conveniences (`not__eq`, `and__eq`,
    `ite_eq_iteDep`) remain skipped until the proof-ergonomics phase decides
    whether they should be raw theorems, wrapped theorems, or hand-library
    lemmas.

- [x] Make the test status unambiguous.
  - `sawcore_prelude_auto_emit` now elaborates and has a refreshed golden for
    the generated `.prelude.lean` file.
  - The Lean elaboration harness now preserves diagnostics from failing
    `lake env lean` probes instead of exiting early under `set -e`.

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

- [x] Build and maintain an explicit Rocq parity matrix.
  - Map every `otherTests/saw-core-rocq/*.saw` driver to a Lean analogue or a
    documented, principled rejection.
  - Include `write_lean_cryptol_module` drivers in the required parity set.
  - Track whether each driver only emits text, elaborates under Lean, or has a
    corresponding human/automation proof.
  - Do not count a test as parity if it elaborates only by erasing an error,
    widening an axiom, or relying on unchecked Haskell-side reasoning.
  - Current reference: `doc/2026-06-26_rocq-parity-matrix.md`.

- [x] Close command-level Rocq parity gaps.
  - Added `write_lean_cryptol_primitives_for_sawcore`, mirroring Rocq's
    regeneration command.
  - Added focused driver coverage that emits and elaborates the generated
    Cryptol primitives module.
  - Keep `write_lean_cryptol_module` in the required validation set.

- [ ] Close small direct-driver Rocq parity gaps.
  - Added arithmetic divide-by-zero case; focused driver test elaborates and
    passes with refreshed goldens.
  - Added missing boolean `t2`/`t10` and offline reverse/implication cases;
    focused driver tests elaborate and pass with refreshed goldens.
  - Added missing sequence update-first/update-last/update-multiple,
    comprehension, and transpose cases;
    focused driver test elaborates and passes with refreshed goldens.
  - Added direct record update, tuple update, relative update, and nested-field
    update cases; focused driver test elaborates and passes with refreshed
    goldens.
  - Added octal literal coverage; polynomial literals now emit an explicit
    raw-error unreachable-branch obligation and elaborate.

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
- [x] Treat Rocq feature parity as the top-level feature goal; proof discharge
  is required but not exclusive.
- [x] Preserve SAWCore errors with `Except String`.
- [x] Reject unsupported primitives by default.
- [x] Remove the old emitted-Lean result-shape classifier.
- [x] Remove broadly defaulting stream helpers from the Lean support library.
- [x] Treat soundness-side conditions as emitted Lean obligations, not Haskell
  automation requirements.
- [x] Prioritize emission correctness and stable generated Lean before adding
  integrated SAW-side proof-check UX.
- [x] Split auto-emitted Prelude declarations into raw logical definitions and
  wrapped value-domain facades.
- [ ] Decide whether arbitrary SAWCore `Prelude.fix` is in scope.
- [ ] Decide how much of the expected-shape design to encode in data types
  before migrating proof ergonomics.

## References

- `doc/2026-06-26_phase-beta-expected-shape.md`
- `doc/2026-06-26_expected-shape-todo.md`
- `doc/2026-05-14_wrap-invariant-audit.md`
- `doc/2026-05-02_residual-trust.md`
- `doc/proof-cookbook.md`
