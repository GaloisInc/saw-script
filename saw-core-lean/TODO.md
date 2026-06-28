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
- Treat every Haskell-side "clever equivalence" recognizer or rewrite as
  removal-target code. The acceptable replacement is proof-carrying emission:
  emit the literal obligation plus optional Lean-side checked helpers/lemmas.
- Do not add unjustified Lean axioms or widen the trusted base.
- Do not accept proofs that depend on proof-local native-evaluation axioms.
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
critical soundness boundary for the final backend is the check step, not
automatic proof search.

Lean automation policy for the current prototype:

- `grind`, `simp`, `omega`/`bv_omega`, `cbv`, and hand-written helper lemmas are
  acceptable when the checked theorem's axiom report contains only the allowed
  standard axioms plus the explicitly cataloged support-library assumptions.
- Plain `bv_decide` and `bv_check` are not acceptable in completed backend
  proofs today. Although they use an LRAT certificate and a verified checker,
  the current Lean frontend validates the certificate through native evaluation
  and inserts a proof-local native axiom for substantial goals. This widens the
  trusted base to Lean code generation, which is outside the backend's current
  soundness policy.
- Hard BV-heavy crypto obligations should remain explicit proof obligations,
  manual/checked proof-library work, or expected gaps. Lack of automated BV
  discharge is not a reason to weaken the emitted obligation.
- `bv_decide?` may still be useful as research input, but any cached proof path
  must be audited with `#print axioms` before it can become an accepted
  regression mechanism.

Near-term prototype priority is slightly different: we first need emitted Lean
obligations that are semantically correct, elaboration-stable, and realistically
provable. Several audit findings are "good-faith use of Lean" issues: a user can
edit a generated file to prove a different theorem, import extra axioms, or ask
the current `offline_lean` command to act like an admitting exporter. Those are
real product soundness issues, but they are not the deepest technical blocker for
the prototype unless they let our regression tests falsely validate a broken
emission strategy. Therefore:

- Prototype-critical harness checks should prevent stale artifacts, unrelated
  proofs, generated `sorry` dependencies, and unchecked axioms from making a
  regression look green.
- Full SAW-side proof replay, import isolation, provenance manifests, and final
  user-facing ergonomics remain required before the backend can be called sound,
  but they come after the emitted obligations and Lean proof libraries settle.

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
- Unsupported `fix` shapes now fall back to a generic Lean obligation requiring
  existence and uniqueness of a fixed point, instead of being silently lowered
  or rejected solely because Haskell lacks a shape-specific productivity proof.
- The long-term direction is to retire most or all semantic Haskell classifiers
  for recursion/productivity/totality. Haskell should emit the ordinary
  translated term plus an explicit Lean contract; Lean theorems and tactics
  should recognize and discharge common patterns.
- A Haskell classifier can still be useful as an optional proof producer: if it
  recognizes a shape, it may emit a Lean lemma/proof script intended to
  discharge the regular obligation. The classifier result is not trusted unless
  the emitted Lean evidence kernel-checks.
- Direct `MkStream` construction with residual per-index effects now emits a
  pointwise-totality obligation rather than defaulting those effects.
- The auto-emitted SAWCore Prelude path now has an explicit raw-vs-wrapped
  declaration convention and elaborates under the focused driver test.

The backend is not yet complete for arbitrary accepted SAWCore or for the full
Rocq feature surface. The next priority is emission quality: every emitted Lean
file should either elaborate with explicit proof obligations or fail at SAW
translation with a clear, principled diagnostic.

## Priority 0: Emission Soundness

- [x] Close the `fix` productivity surface for emit-stage soundness.
  - Current lowering emits generic fixed-point obligations
    (`saw_fix_unique_exists` / `saw_fix_unique_exists_raw`) plus local proof
    placeholders; nested constructors such as `MkStream` emit their own
    pointwise contracts.
  - The Haskell backend does not need to prove productivity. It emits the exact
    Lean contract and makes the lowering depend on checked evidence.
  - Completed proof artifacts must not rely on a hidden Haskell-side assumption,
    a shape-specific Haskell recognizer, or an unresolved generated placeholder.
  - Later proof ergonomics question: decide whether local obligations should be
    lifted into top-level declarations with explicit dependency binders, or
    whether edit-in-place obligation files are acceptable for generated code that
    depends on surrounding locals.
  - Design reference: `doc/2026-06-26_proof-carrying-soundness-contracts.md`.

- [x] Ensure rawification never hides residual per-index effects.
  - The old `rawifyExceptToRaw` Lean-AST rewrite engine has been removed from
    Haskell rather than kept as a trusted gate.
  - Added smoke coverage where `Prelude.error` remains under an
    index-dependent direct stream or stream-corecursive `fix`; these now emit
    explicit Lean contracts (`saw_mkStream_total_exists` or
    `saw_fix_unique_exists`) rather than defaulting.
  - Cryptol `iterate` still rejects input-dependent step errors on its
    shape-specific lowering path; migrating it to the generic obligation path is
    a follow-up ergonomics/scope decision.
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
  - Full SHA512 is no longer the acceptance criterion for this surface. It is a
    large stress probe for the same raw-error and proof-carrying-recursion
    contracts, and is tracked below as stretch scalability work.
  - Remaining ergonomics work: replace generic `False` obligations with more
    specific bounds/unreachable-branch propositions when the translator can
    state them cleanly.

- [ ] Track full SHA512 as a stretch/performance goal, not a Rocq-parity blocker.
  - Generic `Prelude.fix` fallback now emits `saw_fix_unique_exists`
    obligations for shapes outside the audited stream/vector lowerings.
  - Focused SHA residual probes can now emit large Lean files with explicit
    recursion/stream-totality obligations instead of failing at the first
    unsupported `fix`.
  - Full `write_lean_cryptol_module` for SHA512 is a very large stress test,
    not a feature required to match Rocq. Rocq rejects the analogous full-module
    path; Lean accepting focused proof-carrying terms is already beyond parity.
  - Optimization work such as sharing/top-level obligation factoring remains
    valuable, but it should be scheduled after the parity baseline is green and
    should be tracked as stretch scalability work.

- [x] Decide and implement the contract for `write_lean_sawcore_prelude`.
  - The auto-emit path walks SAWCore Prelude declarations directly through
    `SAWModule.translateDef`, not through the normalized Cryptol-user-term path.
  - The chosen convention is explicit:
    raw proof/type infrastructure auto-emits in `RawValueMode` over `Sort u`;
    wrapped value-domain facades either auto-emit into `Except String` or map
    to checked support-library declarations whose carrier binders live in
    `Type u`.
  - `sawLet`, `xor`, and `boolEq` map to small Lean support-library facades
    where direct SAWCore-body emission would mix raw callback arguments with
    wrapped value conventions.
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

- [ ] Complete the audit-driven removal of clever/legacy emission paths.
  - 2026-06-28 audit reference:
    `doc/2026-06-28_clever-legacy-path-audit.md`.
  - 2026-06-28 checkpoint: finished the `fix` migration cleanup. Deleted
    `FixShapes`, removed the dead `rawifyExceptToRaw` rewrite engine and
    dormant `MkStream` deferral switch, updated smoke tests to assert generic
    fixed-point and stream-totality obligations, and refreshed affected driver
    goldens.
  - Remaining audit targets are live or design-relevant clever paths:
    imported-name realization, numeric macro collapse/fallbacks, and residual
    raw/wrapped inference heuristics.
  - Continue removing backup or deferral switches that preserve old behavior
    whenever the proof-carrying path has become the only intended path.
  - Treat Haskell-side classifiers as valid only when they emit optional
    Lean-checked proof artifacts over the ordinary literal obligation. They
    must not erase, weaken, or replace the obligation.

- [ ] Close semantics-injection paths in prelude/module emission.
  - 2026-06-28 checkpoint: removed generic `DefReplace` and moved the remaining
    `sawLet` / `xor` / `boolEq` facades into the Lean support library. Haskell
    now maps the SAW names to checked declarations instead of injecting
    verbatim Lean source.
  - 2026-06-28 checkpoint: generic `AxiomQualifier` / `PrimQualifier` emission
    now rejects by default in the module walker. Any remaining trust assumption
    must be an explicit support-library TCB entry, not reachable through
    ordinary preservation machinery.
  - 2026-06-28 checkpoint: imported constants no longer fall back to accidental
    bare Lean names. The translator emits an imported constant only when the
    user explicitly supplies a renaming or skip-list entry. Remaining work:
    make those explicit realizations carry audit-visible contracts connecting
    the Lean name to the SAW source meaning.

- [ ] Remove or justify Haskell-side representation rewrites.
  - 2026-06-28 checkpoint: `NatPos` / `Bit0` / `Bit1` no longer collapse
    closed constructor chains in Haskell. They now emit one-to-one Lean helper
    calls (`natPos_macro`, `bit0_macro`, `bit1_macro`) and rely on Lean
    reduction when a concrete numeral is needed. Keep removing any remaining
    `UseMacro` uses that compute semantic equivalences rather than emitting
    syntax or wrapper plumbing.
  - 2026-06-28 checkpoint: removed the global `liftRawValue` Lean-AST
    recognizer. All wrapped-formal adaptation now uses translated shape
    metadata or explicit `UseMapsToWrapped` conventions.
  - 2026-06-28 checkpoint: several wrapped-formal adaptation sites now use
    `TranslatedTerm` shape metadata instead of `liftRawValue` AST recognition
    (`if0Nat`, value-domain `Eq`, wrapped-helper conventions, array
    sequencing, top-level def wrapping, and Cryptol-module top-level
    wrapping). This also exposed and fixed a `Prelude.coerce` shape
    propagation gap.
  - 2026-06-28 checkpoint: `buildLifted` now consumes shaped translated
    arguments and wraps bind inputs from `BindingShape` metadata rather than
    inspecting Lean syntax.
  - Raw/wrapped inference remains transitional machinery. Continue migrating it
    toward explicit conventions and checked adapters; avoid adding new
    free-variable or Lean-AST heuristics.

- [ ] Promote the design from scattered policy to explicit data types.
  - Add first-class equivalents of:
    - `ExpectedShape`
    - `RawReason`
    - `CalleeConvention`
    - richer `BindingShape` carrying relevant type/function information
  - Keep `BindingShape` as the binding environment, but stop using it as the
    only shape abstraction.
  - 2026-06-28 audit finding: the remaining shape gaps are no longer just
    readability issues. Non-application translations such as non-empty
    `ArrayValue` can produce wrapped Lean terms (`vecSequenceM`) while fallback
    shape inference classifies the term as raw. Under-applied wrapped helpers
    also bypass their explicit `UseArgRaw`/`UseArgWrapped`/`UseArgFunction`
    conventions. These are the next migration targets because they can make
    later adaptation reason from the wrong shape.
  - 2026-06-28 checkpoint: fixed these concrete migration gaps. Non-empty
    `ArrayValue` bindings keep wrapped shape, under-applied wrapped helpers
    adapt their supplied prefix through the explicit convention table, variable
    applications adapt from the translated Lean Pi shape, and recursor motives
    now use raw binders with wrapped value-producing results.

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
  - The removed `FixShapes` classifier is the model for this migration: the
    preferred end state is generic proof-carrying emission plus Lean-side
    automation that proves the emitted contract for stream, vector, SHA-style,
    and other recurring patterns, not a better Haskell recognizer.
  - Shape recognition in Haskell is acceptable when it only emits additional
    Lean proof artifacts, such as a local lemma specialized to the generated
    body. The regular obligation must still be present, and final acceptance
    must depend on Lean checking the emitted lemma/proof.
  - Preferred proof-obligation shape: Haskell emits the literal/dumb contract
    needed by the checked helper, plus an optional Lean-side proof attempt that
    rewrites it into an ergonomic proof-library lemma. Failure of that proof
    attempt leaves the original obligation visible; it must not cause Haskell
    to erase, weaken, or reinterpret the contract.
  - 2026-06-28 audit finding: `classifyPolyStreamIterate` violates this rule.
    It recognizes only a broad polymorphic-stream outer shape, discards the
    actual `fix` body, and emits `cryptolIterate α f x`. That is not obviously
    correct Haskell emission. It should be removed or demoted to optional
    Lean-proof generation over a regular emitted obligation; until then, the
    conservative behavior is to reject/fall back rather than rewrite.
  - 2026-06-28 checkpoint: removed `classifyPolyStreamIterate` and the
    `lowerPolyStreamIterate` Haskell rewrite. Higher-arity `Prelude.fix`
    applications now emit the generic fixed-point obligation for `fix type body`
    and apply the extra arguments normally, so Cryptol `iterate` coverage is
    retained without a Haskell-side semantic shortcut.
  - 2026-06-28 checkpoint: removed `rawifyExceptToRaw`, the broad Haskell-side
    Lean AST rewrite engine for `Except`-to-raw adaptation. Future adaptation
    work should use named adapters/contracts whose semantic preservation is
    checked in Lean.
  - 2026-06-27 checkpoint: added the first generic wrapped-fix bridge on the
    Lean side. If Lean proves that every bounded-vector body element actually
    built by `genFixM` succeeds, then the wrapped `genFixM`/`genFixVecChecked`
    result rewrites to the pure structural `genFix` target used by the
    existing recurrence library. This is exactly the "dumb obligation plus
    checked bridge" pattern: Haskell can emit the success/productivity proof
    attempt, but Lean must verify it.

- [x] Make `UseMapsToWrapped` more explicit.
  - `UseMapsToWrapped` now records per-formal conventions
    (`UseArgRaw`, `UseArgWrapped`, `UseArgFunction`) instead of only arity and
    target name.
  - Wrapped helper calls no longer reconstruct which arguments to lift from
    SAW binder syntax. The use-site table declares that policy directly for
    `genM`, `atWithDefaultM`, `foldrM`, and `foldlM`.
  - Result shape is explicit in the use-site constructor: these helpers return
    wrapped values. If a future helper needs a different result shape, it should
    use a different convention rather than reintroducing syntactic inference.
  - 2026-06-28 audit finding: the fully-applied path uses this table, but the
    under-applied path still applies supplied arguments directly. Fix this by
    adapting every supplied prefix with the same convention before returning a
    function-shaped partial application.

- [ ] Improve generated Lean readability where it does not affect semantics.
  - Reduce unnecessary-looking `Pure.pure` around already-wrapped values.
  - Prefer stable helper names and local names in generated goals.
  - Keep readability changes behind elaboration and proof-regression tests.

- [ ] Consider renaming the Lean support namespace/package.
  - Current names such as `CryptolToLean` reflect the original prototype, but
    the backend is translating SAWCore proof obligations to Lean. A later
    cleanup should evaluate a rename toward `SAWCoreToLean` or similar.
  - Defer until the proof-discharge core is stable; this will be broad
    artifact/import churn rather than a semantic milestone.

## Priority 2: Regression Coverage

- [ ] Pin audit findings with focused regression tests as code is removed.
  - Assert obsolete direct fix helpers do not appear in generated output unless
    the output also contains the checked proof-carrying contract that justifies
    the helper.
  - Add negative/diagnostic coverage for generic primitive or axiom emission
    once those paths become reject-by-default.
  - Maintain small closed-numeral and imported-name tests around macro or
    realization behavior, so replacements preserve the user-visible cases
    without trusting Haskell-side equivalence.

- [x] Build and maintain an explicit Rocq parity matrix.
  - Map every `otherTests/saw-core-rocq/*.saw` driver to a Lean analogue or a
    documented, principled rejection.
  - Include `write_lean_cryptol_module` drivers in the required parity set.
  - Track whether each driver only emits text, elaborates under Lean, or has a
    corresponding human/automation proof.
  - Do not count a test as parity if it elaborates only by erasing an error,
    widening an axiom, or relying on unchecked Haskell-side reasoning.
  - Current reference: `doc/2026-06-26_rocq-parity-matrix.md`.
  - Full SHA512 is not required to close this matrix. Treat it as a future
    scalability/stress test unless a smaller focused term exposes a general
    parity bug.

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
  - Generic `Prelude.fix` obligation emission.
  - `fix_unfold` rejection.
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

- [x] Harden only the proof-harness checks needed to trust prototype
  regressions.
  - This is not the full SAW-side proof-check feature. It is the minimum
    discipline needed so tests cannot accidentally validate bad emission.
  - Require proof tests to expose a specific checked theorem of the expected
    goal type, rather than accepting any elaborating `proof.lean`.
  - Reject proofs whose checked theorem depends on `sorryAx`, including the
    generated `goal_holds := by sorry` stub. Use Lean's axiom reporting rather
    than text-only `sorry` scans.
  - Reject new unchecked proof-test axioms except for an explicit allowlist of
    support-library TCB axioms.
  - Ensure proof tests depend on freshly generated or tracked emitted artifacts;
    avoid ignored stale `.lean` files as the only source of truth.
  - Defer stronger provenance/skeleton matching for `completed.lean` unless
    tests start relying on completed outlines broadly enough that mutation risk
    can mask emission bugs.
  - 2026-06-27 checkpoint: `lean-proof-test.sh` now stages tracked
    `.lean.good` artifacts, requires `goal_closed : goal` for offline-goal
    outputs, and runs `#print axioms` on checked proof theorems. The allowlist is
    Lean's standard kernel axioms plus the two current support-library
    Vec/BitVec round-trip axioms.

## Priority 3: Proof Ergonomics

- [ ] Refresh generated goldens and proof examples after proof-carrying
  emission changes.
  - The default `otherTests/saw-core-lean` sweep no longer treats full SHA512 as
    required, but many checked-in `.lean.good` files still reflect the earlier
    generated naming/proof-obligation shape.
  - Several proof harness examples still target raw-era or pre-obligation terms
    and now fail because generated goals contain wrapped binds or unresolved
    productivity/fixed-point obligations.
  - This is proof ergonomics/regression-maintenance work, not a reason to
    weaken the proof-carrying soundness interface.
  - 2026-06-27 checkpoint: the small non-recursive proof examples now validate
    the current wrapped emission style (`E1`, `E2`, `E3`, `E7`, `offline_t1`,
    `offline_t3`, `offline_t4`, `tuple_fst`, `point_shift_property`,
    `cookbook`, and `walkthrough`). Remaining failures are informative:
    monadic vector helper goals need checked `genM`/`atWithDefaultM`/`foldrM`
    proof lemmas; large crypto goals still time out under direct unfolding; and
    recursive examples cannot be discharged externally while emitted files
    contain local productivity witnesses as `by sorry`.
  - 2026-06-27 checkpoint: bounded-vector driver goldens that still showed the
    old `genFixMChecked` path (`cryptol_running_sum_verify`,
    `llvm_popcount_verify`, and `cryptol_module_popcount`) now pin the
    `genFixVecChecked` / `GenFixVecBodySound` contract. The driver harness treats
    `genFixMChecked` as an obsolete emitted helper.

- [ ] Redesign emitted proof-obligation placement for recursive/productivity
  contracts.
  - Current emitted definitions put local placeholders such as
    `let h_productivity_ : h_productivity_obligation_ := by sorry` directly
    inside `Emitted.lean`.
  - That was adequate as a temporary elaboration marker, but it is not the
    proof-discharge architecture: an external `proof.lean` cannot fill a local
    `by sorry` embedded in an imported definition, and the proof harness is
    right to reject it.
  - Target shape: obligations must be surfaced as proof-file-fillable
    assumptions/declarations whose evidence is provided by the completed Lean
    proof and kernel-checked before SAW accepts the goal. Do not replace these
    placeholders with axioms.
  - 2026-06-27 checkpoint: the proof harness now supports a
    `completed.lean` artifact alongside `source.txt` and `proof.lean`.
    This models the immediate sound workflow for generated outlines with
    embedded side-condition placeholders: SAW emits the outline, the user edits
    that outline until every placeholder is gone, and the harness replays the
    completed file with a zero-`sorry` policy. This is intentionally separate
    from the later ergonomics question of whether the translator should lift
    local side conditions to top-level declarations; naive top-level lifting
    would over-generalize local body functions unless the closure dependencies
    are represented explicitly.
  - The first recursive completed-outline regression is
    `proofs/recursion_stream_corec/`: its generated `StreamBodyProductive`
    side condition is proved in `completed.lean`, then the separate replay
    proof checks concrete stream observations against that completed artifact.
  - 2026-06-27 blocker found in `proofs/E6_popcount`: the emitted
    `GenFixBodyProductive` obligation appears to be for the wrong Lean shape.
    The generated body computes `atWithDefaultM ... (genM ... body) i`; because
    `genM` sequences the whole vector before indexing, the body can depend on
    future recursive values even when the source-level selected element is
    productive. This is a soundness-relevant emission issue, not a proof
    ergonomics issue. The fix should preserve the dumb Haskell principle by
    emitting a Lean-side contract/rewrite that relates the eager monadic vector
    form to the selected-element productive form, or by emitting a checked
    helper whose precondition matches the actual monadic semantics.
  - Chosen direction: emit both the literal vector body and a mechanically
    selected element view, then require Lean proofs of
    `GenFixVecBodySound n α bodyVec bodyAt` and
    `GenFixBodyProductive α bodyAt`. The checked helper computes with
    `bodyAt`; the soundness bridge to `bodyVec` is a Lean obligation, not a
    trusted Haskell classifier result.
  - Initial implementation note: the mechanically selected view removes the
    outer eager vector body, but examples such as `E6_popcount` can still
    contain nested eager `genM`/`atWithDefaultM` pairs inside the selected
    element. Completed outlines may refine `bodyAt` further, but must then
    prove `GenFixVecBodySound`; reusable Lean lemmas for selected indexing
    through `genM` should be added before trying to close the larger recursive
    examples.
  - 2026-06-27 checkpoint: added Lean lemmas `genM_eq_ok_gen` and
    `atWithDefaultM_genM_ok_lt`. These deliberately require an explicit
    all-elements-success premise, preserving the fact that `genM` is eager
    rather than pretending selected indexing is lazy.
  - 2026-06-27 checkpoint: bounded-vector `fix` emission now fills
    `GenFixVecBodySound` with a Lean proof script
    `unfold ... GenFixVecBodySound; intro lookup_; rfl`. This is generated by
    Haskell, but remains kernel-checked Lean evidence. The remaining
    `GenFixBodyProductive` obligation is intentionally still explicit.
  - 2026-06-27 checkpoint: added generic Lean bridges from wrapped
    `genFixM`/`genFixVecChecked` to pure `genFix`, under an explicit bounded
    all-elements-success premise. This gives proof outlines a checked way to
    rewrite dumb wrapped obligations into the ergonomic recurrence lemmas.
  - 2026-06-27 scratch result: a direct `E6_popcount` productivity proof closes
    the seed case by reduction, but the step cases do not close by `rfl`. This
    is expected and confirms the next missing abstraction: a nested eager
    `genM` proof skeleton must prove success of every generated inner element
    while using `lookup₁ k = lookup₂ k` only at the selected predecessor index.
  - Next design step: add a reusable Lean-side proof skeleton for nested eager
    `genM` selected indexing that proves "all eager elements succeed" and uses
    lookup equality only at the selected prior index. That bridge should be
    emitted as a partial proof attempt for common bounded-vector recurrence
    shapes, not as a trusted Haskell classifier result or an unsound
    selected-index rewrite.
  - 2026-06-27 checkpoint: started that bridge on the Lean side by proving the
    popcount-style wrapped body succeeds pointwise when the input vector is
    successful. `vecSequenceM` now uses `Vector.ofFnM`, an equivalent eager
    sequencing definition that exposes existing `Vector.ofFnM_pure` reasoning
    instead of Lean's private `Vector.mapM` worker. Remaining work is the outer
    theorem that rewrites `atWithDefaultM (genM (... genFixVecChecked ...)) 0`
    to the pure `genFixIdx`/`Nat.rec` recurrence under the checked success
    premises.
  - 2026-06-27 checkpoint: added the outer checked rewrite theorems for both
    input-first and self-first self-referential comprehensions. These theorems
    rewrite the literal wrapped `genM`/`genFixVecChecked` shape to a pure
    `Nat.rec` recurrence only after Lean has checked the body-soundness,
    productivity, default-success, and all-elements-success premises. Next step
    is to apply these theorems in completed proof outlines and then decide
    whether the translator should emit them as optional proof-script hints.
  - 2026-06-27 checkpoint: applied the checked wrapped recurrence bridge to
    `proofs/E6_popcount` and `proofs/cryptol_running_sum_eq`. Both now replay
    through `completed.lean` artifacts with no `sorry`: the generated local
    productivity obligations are filled by Lean-checked proof attempts, and the
    external proofs rewrite the wrapped `genFixVecChecked` results to
    `Nat.rec` before discharging the concrete postconditions.
  - 2026-06-27 checkpoint: repaired `proofs/stream_fibs_corec` by factoring
    the mutual-stream bodies into named `bodyA`/`bodyB` definitions in the
    completed outline, then proving the two `PairStreamComponentProductive`
    contracts over those names. This deliberately avoids heartbeat increases:
    the idiomatic path is to name large generated subterms and prove contracts
    over stable definitions, not force the elaborator to repeatedly normalize
    huge inline expressions.
  - 2026-06-27 checkpoint: migrated `proofs/popcount32_via_bridge` to the
    checked wrapped recurrence path and restored its tracked generated
    `.lean.good` artifact. The external proof now uses a Lean-checked
    `foldlM_pure_eq_foldl` bridge to prove that the emitted literal
    `Except`-wrapped fold succeeds before rewriting to the pure recurrence.
    This keeps the Haskell side dumb: success of the monadic fold is evidence
    supplied and checked in Lean, not a trusted classifier decision.
  - 2026-06-27 checkpoint: repaired `proofs/llvm_point_eq` against wrapped
    emitted output by using checked simplification of `iteM`, `Bind.bind`, and
    singleton `vecSequenceM`. This is a proof-library ergonomics fix, not a
    semantic shortcut: the emitted `Except` structure is still present and
    reduced only by Lean-checked equations.
  - 2026-06-27 checkpoint: moved the BV-heavy Salsa/ChaCha proof attempts that
    depend on `bv_decide` or currently time out into
    `otherTests/saw-core-lean/proof-gaps/`. They remain useful stress artifacts,
    but they are not counted as accepted proof regressions under the current
    no-native-axiom trust policy.

- [ ] Add Lean simp support for Phase-beta generated goals.
  - Normalize common `Except.ok` / `Pure.pure` / `Bind.bind` patterns.
  - Add lemmas for generated helpers such as `iteM`, `genM`,
    `atWithDefaultM`, `vecSequenceM`, stream/fix helpers, and bitvector
    operations.
  - Avoid lemmas that erase `Except.error` or hide unsupported cases.
  - Prefer `grind` and targeted simp lemmas as checked proof automation. Do not
    solve proof-library gaps by adding accepted `bv_decide`/`bv_check` proofs;
    BV-heavy cases can stay as explicit obligations until there is an
    axiom-clean proof route.
  - 2026-06-27 checkpoint: replaced the width-4 `vecSequenceM` probe with the
    general theorem `vecSequenceM_ok_of_get`, which states the principled eager
    sequencing contract: if every wrapped vector element is `Except.ok`, the
    whole `vecSequenceM` is `Except.ok` of the pure vector. Literal-vector
    conveniences should be corollaries of this all-width theorem, not new
    width-specific proof rules.
  - 2026-06-27 checkpoint: added `atWithDefaultM_vecSequenceM_ok_lt`/`_ge`
    and `foldrM_pure_eq_foldr`. These extend the same pattern to selected
    indexing through eager sequencing and to right folds: the proof script must
    provide all-elements or all-steps success evidence before Lean rewrites to
    the pure helper.

- [ ] Update proof examples for wrapped generated goals.
  - Cookbook examples should show the current generated theorem shape, not the
    old raw-era shape.
  - Add small stable proof scripts that users can copy.
  - Keep proof scripts narrow enough that regressions identify a real backend
    or ergonomics issue.
  - Quarantine or mark BV-heavy crypto examples that currently need
    `bv_decide`; they are useful stress cases, but they should not be counted as
    green proof regressions under the current trust policy.
  - 2026-06-27 checkpoint: `proofs/cookbook` now pins small wrapped-helper
    examples for `vecSequenceM`/`atWithDefaultM` and `foldrM`, giving users a
    copyable proof shape that preserves eager `Except` semantics.

- [ ] Decide the external proof-obligation format.
  - Current productivity obligations are split local lets in emitted Lean.
  - The current checked path is edit-in-place generated proof files:
    proof tests may provide `completed.lean`, which is treated as the
    user-completed generated outline and must elaborate without any `sorry`.
  - Later ergonomics work can decide whether to lift local obligations into
    top-level declarations with explicit dependency binders.
  - 2026-06-28 audit finding: `completed.lean` can currently redefine the
    emitted `goal` and still satisfy the harness check. This can falsely
    validate prototype regressions. Harden the harness with a skeleton/hash or
    generated-goal comparison before relying more heavily on completed outline
    tests.

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
    emitted Lean shape is stable and after the prototype harness is strong enough
    to keep regression results honest.
  - Audit triage: `offline_lean` currently behaves like Rocq's offline exporter
    and marks the SAW goal solved after writing the file. For final proof
    discharge this must become either emit-only or be paired with a real Lean
    replay command. For the current prototype, treat this as a known UX/trust
    gap, not as the next blocker ahead of emission correctness.
  - 2026-06-28 audit finding: driver tests that pin `Proof succeeded!` plus
    generated `by sorry` are emission/elaboration tests only. They must not be
    counted as checked proof-discharge regressions.

## Audit Findings: 2026-06-28

Immediate priority from the comprehensive adversarial audit:

- Remove or demote Haskell semantic shortcuts. The first target was
  `classifyPolyStreamIterate`, which has now been removed; the next targets are
  the remaining dead or live clever paths cataloged in
  `doc/2026-06-28_clever-legacy-path-audit.md`.
- Finish deleting backup/legacy paths. The `FixShapes`/`rawifyExceptToRaw`
  cleanup is complete; continue applying the same rule to the remaining
  cataloged paths.
- Continue the expected-shape migration. Fix known wrong-shape cases before
  investing further in proof automation.
- Keep rawification under scrutiny. Where Haskell rewrites `Except` structure
  into raw terms, either the rewrite must be syntactically trivial and
  obviously correct or the semantic preservation proof must move to Lean.
- Rework generic axiom/primitive emission, imported-name realization, numeric
  macro collapse, and global raw-value lifting so that they either become
  literal syntactic emission or proof-carrying Lean-checked contracts.
- Fix prototype false-validation risks: `completed.lean` goal drift and
  driver-level `sorry` acceptance should not be able to make a broken emission
  strategy look green.
- Revisit the generic wrapped `fix` contract. The current successful-value
  uniqueness contract may be too weak if `Except.error` can also be a fixed
  point.
- Later cleanup: prove or further isolate the two Vec/BitVec round-trip axioms,
  update stale README/STATUS/examples, and implement SAW-side proof replay.

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
- [x] Treat Haskell semantic classifiers as migration scaffolding, not the
  trusted long-term design. When a classifier justifies recursion,
  productivity, totality, or rawification, prefer moving that justification into
  Lean as a named theorem, checked helper, or tactic-proved obligation.
- [x] Permit classifiers as untrusted proof emitters: they may recognize a
  generated shape and emit helpful Lean lemmas/scripts, provided the backend
  still emits the regular contract and trusts only the kernel-checked evidence.
- [x] Treat arbitrary SAWCore `Prelude.fix` as in scope for emit-stage
  proof-carrying translation via an explicit unique-fixed-point obligation.
  This does not mean arbitrary fix is automatically discharged.
- [x] Prioritize emission correctness and stable generated Lean before adding
  integrated SAW-side proof-check UX.
- [x] Split auto-emitted Prelude declarations into raw logical definitions and
  wrapped value-domain facades.
- [x] Reject `bv_decide`/`bv_check` as accepted proof-discharge mechanisms under
  the current no-extra-trust policy, because substantial uses introduce
  proof-local native-evaluation axioms. Use checked Lean proof automation
  (`grind`, `simp`, `omega`/`bv_omega`, `cbv`, helper lemmas) where it works,
  and leave hard BV obligations open rather than widening the trusted base.
- [ ] Decide how much of the expected-shape design to encode in data types
  before migrating proof ergonomics.

## References

- `doc/2026-06-26_phase-beta-expected-shape.md`
- `doc/2026-06-26_expected-shape-todo.md`
- `doc/2026-05-14_wrap-invariant-audit.md`
- `doc/2026-05-02_residual-trust.md`
- `doc/2026-06-28_clever-legacy-path-audit.md`
- `doc/proof-cookbook.md`
