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

Current implementation priority:

1. Close partial-operation obligations in principle:
   `doc/2026-06-30_partial-operation-obligations-plan.md`.
   Direct scalar operations, direct bitvector operations, and the Cryptol
   signed-BV wrapper surface (`ecSDiv`, `ecSMod`) now use checked
   proof-carrying helpers. The wrapper slice is fixed at the
   wrapper/recursor contract layer rather than by width-specific Haskell
   normalization.
2. Execute the Priority #1 principled-emission plan:
   `doc/2026-06-30_priority-1-principled-emission-plan.md`.
   The first driver, `ecSDiv`/`ecSMod`, is complete. The next step is to test
   whether the same checked-contract abstraction cleanly covers bounds/index
   obligations (`ecAt` and with-proof vector primitives) before coding another
   local case.
3. Then move to bounds/index obligations (`ecAt` and with-proof vector
   primitives), followed by smaller wrapper-shape gaps.

## Priority 0: Emission Soundness

- [x] Implement proof-carrying partial-operation contracts.
  - Design reference:
    `doc/2026-06-30_partial-operation-obligations-plan.md`.
  - This is the current top backend priority. Direct partial operations must
    not emit unchecked total-looking Lean calls at zero divisors or zero
    denominators. They must emit visible preconditions and consume Lean-checked
    evidence.
  - Scope, in order:
    1. [x] Direct scalar Prelude operations:
       `divNat`, `modNat`, `divModNat`, `intDiv`, `intMod`, `ratio`,
       `rationalRecip`.
       2026-06-30 checkpoint: these now route through a shared
       `PartialOpContract` table, emit local `h_nonzero_obligation_` /
       `h_nonzero_` bindings, and call checked Lean helpers. Nat operations
       use raw preconditions; Int/Rational value-domain operations use
       wrapped `Except` preconditions so proof automation can reason about the
       emitted computation before monadic bind erases its expression shape. The
       seven corresponding obligation fixtures have been promoted from known
       gaps. `ecDiv`, `ecMod`, `ecFieldDiv`, and `ecRecip` also promote through
       the same scalar path after normalization.
       Remaining proof-ergonomics gap: rational executable differential cases
       are pinned known gaps where the emitted obligations are correct but the
       starter tactic does not yet prove all rational nonzero facts.
    2. [x] Direct bitvector Prelude operations:
       `bvUDiv`, `bvURem`, `bvSDiv`, `bvSRem`.
       2026-06-30 checkpoint: these now use the same `PartialOpContract`
       table with explicit helper argument modes: raw width argument, wrapped
       vector operands, named `bvNonzeroM` precondition, and checked Lean
       helpers. The four direct BV zero-divisor obligation fixtures have been
       promoted from known gaps. Nonzero executable BV division is pinned as a
       proof-ergonomics known gap because the emitted obligations are sound but
       the starter tactic does not yet prove concrete vector nonzero facts.
    3. [x] Cryptol.sawcore wrappers:
       `ecDiv`, `ecMod`, `ecFieldDiv`, and `ecRecip` are covered by scalar
       normalization. `ecSDiv` and `ecSMod` now stay opaque across
       normalization and route through a checked wrapper contract over
       `Cryptol.Num`; the Lean helper case-splits on `Num` and requires
       `ecSignedBVNonzeroM` evidence for the finite positive case. This avoids
       any Haskell rewrite from `ecSDiv (TCNum (Succ n))` to `bvSDiv n`.
       Planning reference:
       `doc/2026-06-30_priority-1-principled-emission-plan.md`.
  - Implementation rule: add a small data-driven partial-operation contract
    interface. Haskell may construct the operation-specific proposition and
    call a checked helper, but it must not inspect generated Lean syntax to
    prove nonzero-ness, erase the obligation, or choose a total fallback value.
  - Lean support-library helpers should be thin proof-taking wrappers around
    the existing operations. The proof argument may be computationally unused;
    its purpose is to put the soundness precondition into the checked type of
    the emitted result.
  - 2026-06-30 checkpoint: all direct `obligations/partial_*` and
    `obligations/cryptol_ec_*_zero` zero-divisor/zero-denominator fixtures are
    positive obligation-shape tests. Remaining gaps in this area are proof
    ergonomics for executable replay of nonzero Rational/BV examples, not
    missing emission contracts.

- [ ] Close the bitvector primitive conformance surface found in the
  2026-06-29 audit.
  - `bvLg2` now uses SAW's ceiling-log convention for nonzero inputs. Added
    paired SAW-vs-Lean conformance coverage for `bvLg2 0`, `1`, powers of two,
    and non-powers of two.
  - Added the first differential conformance driver/proof pair:
    `drivers/conformance_bitvector` proves defined concrete SAWCore bitvector
    facts with SAW's `w4` backend and emits the same term for Lean elaboration;
    `proofs/conformance_bitvector` checks the corresponding Lean support
    realizations.
  - Division/remainder/modulus by zero is not a green conformance case today.
    Although some `Prelude.sawcore` comments describe concrete results, SAW's
    active concrete and What4 paths treat those cases as undefined. The Lean
    backend must therefore emit explicit nonzero-divisor preconditions/proof
    obligations, or reject until it can do so; it must not silently pick total
    Lean values.
  - 2026-06-29 checkpoint: `drivers/conformance_zero_divisor_obligations` was
    added to the unified conformance suite as a regression probe for the
    missing zero-divisor contract, but the first Haskell implementation was
    stripped because it was an ad hoc per-primitive dispatch block. The backend
    is intentionally back in the broken state here: the test documents the
    required behavior, not a completed fix.
  - 2026-06-29 checkpoint: `divModNat`'s support-library result type now uses
    SAW's nested `PairType ... UnitType` tuple representation instead of Lean's
    native `Nat × Nat`.
  - Remaining work: follow the dedicated partial-operation plan above, then
    audit higher-level Cryptol operations that may hide these primitives.
  - Audit reference: `doc/2026-06-29_comprehensive-audit.md`.

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
  - 2026-06-28 checkpoint: strengthened the wrapped-value generic `fix`
    contract so uniqueness ranges over all `Except String α` fixed points, not
    just successful `Pure.pure` fixed points. This rules out a successful
    witness coexisting with an `Except.error` fixed point.
  - Design reference: `doc/2026-06-26_proof-carrying-soundness-contracts.md`.

- [x] Ensure rawification never hides residual per-index effects.
  - The old `rawifyExceptToRaw` Lean-AST rewrite engine has been removed from
    Haskell rather than kept as a trusted gate.
  - Added smoke coverage where `Prelude.error` remains under an
    index-dependent direct stream or stream-corecursive `fix`; these now emit
    explicit Lean contracts (`saw_mkStream_total_exists` or
    `saw_fix_unique_exists`) rather than defaulting.
  - Cryptol `iterate` should stay on the generic obligation path; any
    recurrence-specific ergonomics belong in Lean-checked proof scripts.
  - Added driver-harness checks asserting obsolete helpers do not appear in
    emitted output:
    `mkStreamM`, `mkStreamFix*`, `mkStreamFixPair*`, `cryptolIterateM`,
    `genFix*`, `GenFix*`, `StreamBodyProductive`, `PairStream*`, and
    `saw_unreachable_default`.
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
  - 2026-06-28 checkpoint: explicit imported realizations now emit an auxiliary
    `__saw_realizes_*` Lean alias at the translated SAW type, and generated
    terms use that alias instead of the raw external target. This makes the
    contract Lean-checked and audit-visible. Imported value/function constants
    also carry deterministic shape metadata so applications go through the same
    wrapper adaptation as local variables and ordinary translated globals.
    Remaining work: decide whether external realization declarations need a
    richer semantic proof obligation beyond type-correctness for the parity
    milestone, or whether that belongs in the later ergonomics/TCB phase.

- [ ] Remove or justify Haskell-side representation rewrites.
  - 2026-06-28 checkpoint: `NatPos` / `Bit0` / `Bit1` no longer collapse
    closed constructor chains in Haskell. They now emit one-to-one Lean helper
    calls (`natPos_macro`, `bit0_macro`, `bit1_macro`) and rely on Lean
    reduction when a concrete numeral is needed. Keep removing any remaining
    `UseMacro` uses that compute semantic equivalences rather than emitting
    syntax or wrapper plumbing.
  - 2026-06-28 checkpoint: `Zero` / `One` now follow the same helper pattern
    (`zero_macro`, `one_macro`) instead of emitting Lean numeric literals
    directly. The helpers are reducible and simp-normalizing, so proofs still
    reduce concrete lengths on the Lean side while Haskell stays syntactic.
  - 2026-06-29 checkpoint: `Succ` also routes through a reducible Lean helper
    (`succ_macro`) rather than a direct Haskell rewrite to Lean `Nat.succ`.
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
  - 2026-06-29 audit finding: `scNormalizeForLean` still applies
    `scLiteralFold` in Haskell before Lean emission. Either remove this from
    trusted emission or make it proof-carrying by emitting the literal term plus
    a Lean-checked equality/obligation for the folded form.
  - 2026-06-29 experiment: a direct removal of `scLiteralFold` compiles after
    deleting dead code, but the Lean driver suite then emits many non-elaborating
    dependent vector terms. The breakage is not merely golden churn: unevaluated
    Nat/Int size arithmetic reaches casts, `coerce`, and vector helper lengths
    where Lean needs explicit equality evidence. Therefore this path needs a
    principled replacement, not a one-line deletion: emit literal arithmetic
    plus Lean-checked normalization/cast obligations, or make the relevant
    size-equality evidence explicit at each dependent use site.
  - 2026-06-29 checkpoint: moved `Prelude.Bit` from a direct Haskell replacement
    with Lean `Bool` into the Lean support library as a reducible `Bit` alias.
    Haskell now routes to that checked support declaration. This is a small
    instance of the general rule: representation choices belong in Lean-side
    realizations or proof-carrying contracts, not ad hoc Haskell rewrites.

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
  - 2026-06-28 checkpoint: `UseRenameUniv` no longer has a backup path that
    silently drops explicit universes and asks Lean to infer them. The
    translator now derives levels from bound sort variables or from the
    argument's SAWCore sort (`Bool`/`Vec n Bool` -> level 1, `sort k` literals
    -> their next Lean sort), and rejects if a required level is still unknown.

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
  - 2026-06-29 audit finding: ordinary sort-literal translation may still use
    binder-position universe generalization where a value-position concrete
    sort literal is intended. Add focused tests before changing this path.

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
  - 2026-06-28 checkpoint: `unsafeAssert` now follows this obligation-first
    rule. Fully-applied uses emit the asserted `Eq` proposition as a named local
    proof obligation; Haskell no longer drops the SAW arguments and replaces the
    call with a hidden tactic-only proof. The `saw_unsafeAssert` tactic remains
    available as Lean-side automation a user/proof script can apply to that
    visible obligation.
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
  - 2026-06-28 checkpoint: deleted the old direct fix-shape Lean helper
    surface. Future recurrence ergonomics must prove facts about the generic
    emitted obligation rather than rewriting through a structural helper API.

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

- [ ] Build a comprehensive differential conformance suite.
  - Current planning note:
    `doc/2026-06-29_differential-conformance-plan.md`. This is the
    authoritative roadmap for treating conformance as complete SAWCore
    coverage: cover the actual SAWCore constructors (`App`, `Lambda`, `Pi`,
    `Constant`, `Variable`, `Recursor`, `Sort`, `ArrayValue`, `StringLit`),
    module/parser constructs, every Prelude/Cryptol-SAWCore family, and every
    known gap. Current Lean `noncomputable` markings or backend rejections are
    test targets, not scope exclusions.
  - Use `make test-saw-core-lean-conformance` from the `deps/saw-script`
    repository root for the focused backend conformance sweep. From
    `otherTests/saw-core-lean`, the local-development equivalent is
    `make conformance`. It intentionally runs only true conformance categories:
    - `differential/*`: positive executable litmus tests where SAW observes an
      outcome, Lean observes an outcome from the SAW-Lean emitted artifact, and
      the harness mechanically compares those observations.
    - `differential/*/.known-gap`: the real differential run fails at a pinned
      SAW producer, emitted-Lean, or Lean observer diagnostic. This records
      missing parity or an observation-path blocker; it is not a passing
      conformance case.
    - `saw-boundary/*`: expected rejection or obligation-boundary litmus tests.
    Broad examples, whole-module extraction examples, crypto/stress drivers,
    proof-discharge demos, emitted-shape goldens, and Lean support-library-only
    proofs do not belong in this gate.
  - WARNING: `drivers/conformance_*` and `proofs/conformance_*` are legacy
    litmus candidates/regression checks, not true differential conformance.
    Most of them do "SAW proves" + "Lean elaborates" + "separate Lean theorem";
    that is useful, but it is not a compared SAW-vs-Lean observation. Migrate
    useful cases into `differential/*` one feature family at a time.
  - Every concrete support-library realization that stands in for a SAWCore
    primitive should ultimately have true differential coverage: a SAW-side
    observed result and a Lean-side observed result from the emitted artifact.
  - Prefer small, named, cheap cases over large examples: bitvectors, Nat/Int,
    rationals, IntMod, vector helpers, records/tuples, error propagation,
    raw/wrapped adaptation, and fix/precondition obligation emission.
  - Classify each case explicitly as:
    - true SAW-vs-Lean differential conformance,
    - expected obligation/rejection for partial or undefined behavior, or
    - non-conformance regression/support/integration coverage.
  - Do not count a Lean-only proof, golden diff, or elaboration-only check as
    semantic conformance.
  - 2026-06-29 correction: added `differential/*` and changed `make
    conformance` to exclude legacy `drivers/conformance_*` and
    `proofs/conformance_*`. Added the first tiny true-differential Boolean
    litmus. Next work is to migrate existing small legacy litmus candidates
    into this shape without adding large examples.
  - 2026-06-29 checkpoint: the active true differential suite now includes
    focused litmus tests for Boolean primitives, closed lambda/application,
    `id`/`sawLet`, unreachable `error` branches, algebraic/control recursors,
    Nat/Int/IntMod/Rational scalars, string primitives including
    `bytesToString`, tuple and record projection/update, bitvector literals,
    bitvector conversions, bitvector arithmetic, bitwise/shift operations,
    order/extension/counting operations, and finite vector literals. All
    positive cases compare SAW-observed output against Lean-observed output
    from the emitted artifact.
  - 2026-06-29 checkpoint: expanded true differential coverage for SAWCore
    parser `let` and type ascription, string empty/escape cases, vector
    empty/singleton/nested literals, Cryptol sequence take/drop/update/map/zip,
    and Cryptol bitvector rotates. These all passed as real SAW-vs-emitted-Lean
    observations.
  - 2026-06-29 checkpoint: expanded scalar/algebraic coverage with defined Nat
    arithmetic, Int division/modulus, IntMod add/neg, and Maybe
    constructors/recursor. Added pinned differential known gaps for SAW-side
    evaluator panics on Pos-backed observations (`pos_values` and
    `nat_pos_recursor_eval`); these fail before Lean can observe an emitted
    artifact, so they are conformance-harness/backend-input findings rather
    than Lean backend fixes.
  - 2026-06-29 checkpoint: `differential/*/.known-gap` support now pins real
    differential failures with required diagnostic substrings. The first such
    cases are `vector_gen_at`, `vector_shift_rotate`, and `vector_fold`, which
    expose raw-`Nat` bodies/functions being emitted where wrapped
    `Except String Nat` vector helpers are expected.
  - 2026-06-29 checkpoint: added the first bitvector conformance pair for
    defined division/remainder, signed division/remainder, arithmetic shift,
    and `bvLg2`. Added a scalar conformance pair for Nat, Int, IntMod, and a
    small rational smoke case. A generated-output proof of whole emitted
    conjunctions was too expensive in the current literal-vector/normalization
    shape; keep that as a harness improvement target, not a reason to drop
    differential coverage.
  - 2026-06-29 checkpoint: expanded bitvector conformance to cover arithmetic
    wraparound, shifts, bitwise operations, unsigned/signed comparisons,
    extension, popcount, leading/trailing zeros, and the existing defined
    division/log cases. Added defined `divModNat` quotient/remainder coverage
    to the scalar pair. These are support-library conformance checks, not new
    Haskell-side recognizers.
  - 2026-06-29 checkpoint: added vector-helper conformance for `gen`,
    `atWithDefault`, `shiftL`, `shiftR`, `rotateL`, `rotateR`, `foldr`, and
    `foldl`. This exposes a higher-order wrapper adaptation gap. The first
    attempted Haskell adapter was stripped because it was too clever; keep the
    regression coverage and solve this with a principled convention/certificate
    design.
  - 2026-06-29 checkpoint: added tuple conformance for concrete pair
    construction/projection and nested tuple projection. This pins the
    `PairType ... UnitType` representation used by emitted SAW tuples and by
    helper results such as `divModNat`.
  - 2026-06-29 checkpoint: added record and string conformance pairs. Record
    coverage checks concrete construction, projection, nested projection, and
    update semantics against the Lean `RecordType` realization. String coverage
    checks `appendString` / `equalString` behavior used by Cryptol error-message
    plumbing.
  - 2026-06-29 checkpoint: added algebraic/control conformance for concrete
    `Either`, `UnitType`, `EmptyType`, and `ite` behavior. The driver proves
    the source facts in SAW; the paired Lean proof pins the support-library
    constructors, recursor behavior, and `iteM` branch order.
  - 2026-06-29 checkpoint: drafted stream conformance for `Stream#rec`,
    `MkStream`, `streamIdx`, and `streamScanl`. This exposed a recursor
    result-shape convention gap: a wrapped scrutinee can feed a recursor whose
    motive returns a raw value such as `Nat`, while the surrounding value-domain
    flow expects `Except String Nat`. Do not patch this with local
    "already-wrapped" predicates; resolve it through an explicit recursor
    convention/adaptation design.
  - 2026-06-29 checkpoint: added focused true-differential coverage for a
    finite `MkStream`/`Stream#rec` projection. This small projection now
    compares SAW and emitted-Lean observations directly; the larger legacy
    `streamScanl`/helper surface still needs focused litmus migration.
  - 2026-06-29 checkpoint: added Boolean conformance for `not`, `and`, `or`,
    `xor`, and `boolEq`. The paired Lean proof pins the checked `xor`/`boolEq`
    facades without adding any Haskell-side special reasoning.
  - 2026-06-29 checkpoint: added bitvector conversion conformance for
    `bvToNat`, `bvToInt`, `sbvToInt`, `bvNat`, and `intToBv`.
  - 2026-06-29 checkpoint: added core control conformance for `id` and
    `sawLet`.
  - 2026-06-29 checkpoint: added unreachable-error conformance. SAW proves
    closed Cryptol facts where the `error "boom"` branch is unreachable, while
    the paired Lean proof pins `saw_throw_error` and `iteM` branch selection.
  - 2026-06-29 checkpoint: added scalar-extra conformance for defined Nat
    arithmetic (`addNat`, `mulNat`, `minNat`, `maxNat`, `expNat`,
    `doubleNat`, `pred`, `ltNat`), Int arithmetic/comparison/conversion,
    `fromIntMod`, `intModSub`, `intModMul`, and nonzero Rational arithmetic.
    `leNat` is not in this differential fixture because SAW's current `w4`
    path panics while evaluating the closed source term `leNat 4 4`; track it
    as a SAW-side conformance-harness blocker, not a Lean backend fix.
  - 2026-06-29 checkpoint: added `bytesToString` conformance for a concrete
    ASCII byte vector.
  - 2026-06-29 checkpoint: added direct SAWCore `zip` conformance for unequal
    input lengths, truncation to `minNat`, pair projection, and defaulted
    out-of-bounds access. This exposes the same raw function-result adaptation
    gap as the existing `genM` vector fixture.
  - 2026-06-29 checkpoint: added parser/module differential coverage for
    explicit `Pi`/`sort 0` binders and a loaded `.sawcore` module with local
    and qualified ordinary-definition references. Added Cryptol.sawcore
    differential coverage for `const`, `compose`, finite append, reverse, join,
    and split.
  - 2026-06-29 checkpoint: expanded the parser/module coverage with a
    cross-module import/qualified-name litmus and explicit `isort`/`qsort`
    parser-surface coverage. Added a small Cryptol.sawcore `Num` litmus for
    `TCNum`, `TCInf`, `tcFin`, and `getFinNat`.
  - 2026-06-29 checkpoint: added a positive import-hiding litmus for loaded
    `.sawcore` modules. It checks that a non-hidden import resolves
    unqualified while a hidden declaration is still available by qualified
    name. A stricter local-shadowing probe exposed SAW-side ambiguity, so that
    should be treated separately if we decide it is an input-language boundary
    worth pinning.
  - 2026-06-29 checkpoint: added a direct user-defined SAWCore datatype
    boundary fixture. A closed datatype computation can reduce away before
    Lean emission, which is not enough to prove datatype emission support; the
    new fixture forces the datatype to remain in the term and pins the current
    rejection as a known gap.
  - 2026-06-29 checkpoint: added focused direct-result partial-operation
    boundary fixtures for `divNat`, `divModNat`, `intDiv`, `bvUDiv`,
    `bvSDiv`, `ratio`, and `rationalRecip` at zero divisors/denominators.
    2026-06-30 update: scalar Nat/Int/Rational, direct bitvector, and Cryptol
    zero-divisor wrapper fixtures now emit proof-carrying obligations and
    checked helpers. Remaining work is proof ergonomics for executable replay
    of nonzero examples.
  - 2026-06-29 checkpoint: added a focused finite-observation stream-helper
    differential known gap for `streamGet`, `streamMap`, shifts, and
    `streamScanl`. SAW evaluates the closed Boolean, but the emitted Lean
    contains unresolved `MkStream` totality proof stubs, so this cannot count
    as executable differential coverage until those obligations are checked or
    moved into an explicit obligation-shape boundary fixture.
  - 2026-06-29 checkpoint: expanded Cryptol.sawcore dictionary and entry-point
    coverage. Positive true-differential rows now cover type-level `tc*`
    arithmetic, Bool/Integer/word/pair equality and comparison dictionaries,
    signed word comparison, zero/logic/ring dictionaries, and defined
    integral/field entry points (`ecDiv`, `ecMod`, `ecRecip`, `ecFieldDiv`).
    Two focused known gaps are pinned: `updFst`/`updSnd` updater lambdas
    currently hit raw/wrapped `Except String Nat` adaptation failures in emitted
    Lean, and `ecAt` currently emits an unresolved index proof stub. Keep both as
    conformance failures until the backend emits checked evidence or a clean
    obligation shape.
  - 2026-06-29 checkpoint: added true-differential coverage for ordinary
    literal dictionaries and rounding entry points (`ecNumber`, `ecFraction`,
    `ecFromInteger`, Rational floor/ceiling/truncate/rounding), plus
    deterministic effect-like Cryptol entry points (`ecTrace`, `ecDeepseq`) and
    finite `ecParmap`. Added a focused float known gap: `TCFloat` and its
    dictionaries are in the backend surface, but Cryptol.sawcore currently routes
    representative operations through runtime `error`.
  - 2026-06-29 checkpoint: added higher-universe sort binder coverage,
    sort-1 `PairType1` coverage, safe `coerce`/`rcoerce` coverage, direct
    `Num_rec` coverage, additional finite/infinite `tc*` arithmetic coverage,
    finite observations of infinite sequences, finite Cryptol sequence
    generator wrappers, additional Rational/IntMod/Unit/sequence dictionaries,
    and more BV `ec*` wrappers. New pinned gaps: residual `ZtoNat`, reachable
    `Prelude.error`/`ecRandom` runtime errors pending an error-outcome observer,
    Suite-B crypto primitives implemented as runtime `error`, and residual
    `natCase` in `ecSShiftR`/`ecSExt` wrappers.
  - 2026-06-29 checkpoint: added record and empty-tuple/empty-record dictionary
    coverage, a message-specific `ecError` runtime-error known gap, a
    representative projective-helper runtime-error known gap, and a direct
    Cryptol.sawcore sequence-helper known gap. The direct sequence fixture shows
    the same principled wrapper-adaptation problem as the vector helper gaps:
    raw Nat bodies are emitted where the Lean vector helpers expect
    `Except String Nat`.
  - 2026-06-29 checkpoint: added positive true-differential coverage for
    `tcWidth`, function dictionaries, stream dictionaries, and additional
    deterministic `ec*` comparison/logic/ring wrappers. Added focused known gaps
    for `ecFoldl`/`ecFoldlPrime` wrapper adaptation and `ecScanl` reaching the
    deliberately rejected bounded-vector `Prelude.scanl` primitive.
  - 2026-06-29 checkpoint: expanded direct Cryptol.sawcore `ec*` coverage with
    positive true-differential tests for finite `ecCat`/`ecTake`/`ecDrop`/
    `ecJoin`/`ecSplit`, `ecTranspose`, `ecAtBack`, `ecUpdate`, `ecUpdateEnd`,
    `ecShiftL`/`ecShiftR`, and `toSignedInteger`. Added focused known gaps for
    `ecSDiv`/`ecSMod` leaving residual `Nat__rec`, `ecExp` leaving residual
    `expByNat`, and GF2 polynomial operations leaving residual proof lemmas
    such as `eqNatAddS`.
  - 2026-06-29 checkpoint: added positive direct coverage for the remaining
    finite range producers `ecFromToByLessThan` and
    `ecFromToDownByGreaterThan`, plus direct finite `ecReverse`.
  - 2026-06-29 checkpoint: added direct Cryptol.sawcore entry coverage for
    IntMod literal dictionaries, `ecArray*`, `ecFp*`, and SHA2 primitives.
    IntMod and IntModNum literals are true SAW-vs-emitted-Lean differential
    conformance. The array, FP, and SHA rows are pinned known gaps with real
    diagnostics from the SAW producer path: unsupported SMT-array translation
    and Cryptol.sawcore runtime `error` implementations.
  - 2026-06-29 checkpoint: added a true differential litmus for an
    under-applied/function-valued SAWCore term. SAW observes the same lambda
    application after applying it to a concrete argument; Lean imports the
    emitted function artifact and applies that artifact. This closes the main
    `App`/`Lambda` function-valued coverage hole without reconstructing the
    term by hand in the observer.
  - 2026-06-29 checkpoint: tightened existing positive coverage by adding a
    non-`Nat` Bool type-ascription observation and `zipWith` to the small
    sequence litmus. These are still tiny differential tests, not broad
    examples.
  - 2026-06-29 checkpoint: added a direct `List`/`ListSort`/`FunsTo`
    differential known gap. SAW evaluates the closed observation to true, but
    Lean emission deliberately rejects residual `ListSort` because the
    algebraic-enum support encoding has no checked Lean realization yet.

- [x] Add obligation-shape tests for proof-carrying boundaries.
  - Current planning note:
    `doc/2026-06-30_obligation-shape-testing-plan.md`.
  - These tests should inspect the actual emitted Lean artifact and check that
    soundness-sensitive surfaces expose the right contract while avoiding
    hidden totalization, obsolete helpers, unchecked axioms, or Haskell-side
    semantic shortcuts.
  - Planning rule: this phase is testing-only, like the differential
    conformance plan. Do not change backend semantics or Lean support-library
    semantics to make these pass. Missing obligation support must appear as a
    small corpus fixture, usually `.known-gap`, with a pinned failure
    diagnostic. Positive obligation fixtures must fail when the emitted
    contract is absent or bypassed; known-gap fixtures must fail when the pinned
    failure disappears so the case can be promoted.
  - First targets: partial-operation preconditions, fully applied
    `unsafeAssert`, generic `fix`, raw-position `Prelude.error`, and
    `MkStream`/stream totality.
  - 2026-06-30 checkpoint: added the dedicated `obligations/*` harness and
    expanded the corpus beyond the initial P0 rows. Positive obligation-shape
    fixtures now cover wrapped and raw-function `fix`, definitional and open
    fully-applied `unsafeAssert`, raw `Prelude.error` in Nat/function/proof
    positions, and `MkStream` totality. Known-gap obligation fixtures now pin
    direct partial-operation preconditions, representative proof primitives,
    all with-proof vector primitives, and direct recursor families.
  - 2026-06-30 checkpoint: expanded the obligation corpus for stream helpers
    and Cryptol wrappers without changing backend semantics. Positive
    obligation-shape fixtures now cover `streamMap`, `streamShiftL`, and
    `streamScanl` as stream-producing helper lowerings. Known-gap obligation
    fixtures pin `streamShiftR`'s current Nat-vs-`Except` emitted-outline
    mismatch, Cryptol zero-divisor/zero-denominator wrappers
    (`ecDiv`, `ecMod`, `ecFieldDiv`, `ecRecip`, `ecSDiv`, `ecSMod`), and
    `ecAt`'s current indexing emission gap. `streamGet` finite projection is
    intentionally kept as value/differential coverage, not a fake standalone
    obligation test.
  - 2026-06-30 checkpoint: promoted `ecSDiv` and `ecSMod` from known-gap
    rows to positive obligation-shape tests. Their emitted artifacts expose
    `ecSignedBVNonzeroM` and checked `ecSDiv_checkedM` / `ecSMod_checkedM`
    helpers, and assert absence of residual `Nat__rec` and unchecked direct
    signed-BV bypasses.
  - 2026-06-30 checkpoint: added obligation known-gap fixtures for P2 datatype
    and list surfaces: direct `List`/`ListSort`/`FunsTo`, direct user-defined
    SAWCore datatype recursors, and Cryptol algebraic enum lowering. These are
    not backend fixes; they pin the current rejection/realization gaps as
    corpus entries so they cannot remain prose-only.
  - 2026-06-30 checkpoint: expanded proof-primitive obligation known gaps to
    include `uip`, `bvEqToEq`, `foldr_nil`, and `head_gen`, and added loaded
    SAWCore primitive/axiom declaration fixtures plus an injected-Lean-code
    fixture. The injected-code fixture documents the current public API gap:
    term emission ignores module-level `injectCode`, and there is no public
    generic SAWCore-module Lean writer for the obligation corpus yet.
    Also added the remaining explicit positive rows from the obligation plan:
    non-definitional/provable `unsafeAssert` equality and raw index/proof
    `fix` alongside the existing raw function-position `fix`.
  - 2026-06-30 checkpoint: completed the obligation-shape testing plan as a
    testing corpus. The current conformance target reports all remaining
    missing proof-carrying surfaces as explicit known gaps; this is the
    guardrail for the next backend implementation phase, not proof that those
    surfaces are implemented.
  - 2026-06-29 checkpoint: expanded `saw-boundary` expected-rejection coverage
    for mapped-but-unsupported primitives. The new fixtures pin explicit
    diagnostics for unsupported Int primitives (`intAbs`, `intMin`, `intMax`),
    vector primitives (`head`, `tail`, `EmptyVec`, `scanl`), with-proof vector
    variants, SMT-array primitives, and under-applied `unsafeAssert`. These are
    not backend fixes; they make sure unsupported surfaces fail loudly until a
    proof-carrying implementation exists.
  - 2026-06-29 checkpoint: added proof-carrying surface coverage. A focused
    conformance driver pins fully-applied `unsafeAssert` as a visible Lean
    equality obligation consumed by `coerce`. A boundary fixture pins explicit
    rejection for representative SAW-internal proof primitives and lemma axioms
    (`uip`, `coerce__eq`, Nat/vector/bv lemmas, and size-bound assertions)
    until each has a Lean-checked realization.
  - 2026-06-29 correction: removed broad legacy/example buckets from
    `make conformance`. The conformance suite is a tight litmus boundary, not
    a place to jam large examples. Existing command-level parity drivers,
    Cryptol-source feature buckets, whole-module extraction examples, E-series
    proofs, LLVM examples, and crypto/stress examples remain available under
    the full `test` sweep or manual runs, but conformance work should extract
    focused `differential/*` or `saw-boundary/*` cases from them instead of
    promoting them wholesale.
  - Existing large examples that have exposed real gaps should be mined into
    focused litmus tests:
    - legacy `arithmetic` and `cryptol_chacha20_core_iterate` expose missing
      checked divisor/precondition obligations;
    - `cryptol_module_rational` exposes missing nonzero denominator obligations
      for rational literals;
    - `cryptol_module_error_string` exposes missing divisor obligations on a
      whole-module path.
    These gaps are already represented in `conformance_zero_divisor_obligations`
    or should be split into smaller conformance drivers before entering the
    gate.
  - Remaining conformance backlog from the mapped support surface:
    - Injected-code declarations: no public generic SAWCore-module Lean writer
      path currently exposes `InjectCodeDecl` to the conformance harness. Add a
      small scoped fixture as soon as injected declarations can reach the Lean
      module emitter without using hand-written Lean.
    - Direct `Void`: `Void` has no closed value source. Keep `EmptyType` and
      eliminator coverage, and add a direct `Void` boundary only if a genuine
      source term can reach the backend.
    - Checked Lean proof-library coverage for nontrivial Rational arithmetic.
      The SAW driver proves the source facts and the emitted Lean elaborates,
      but the local Lean environment has no lightweight checked Rat arithmetic
      tactic; do not use `native_decide`, because that introduces proof-local
      native-evaluation axioms.
    - `leNat` differential coverage once the SAW-side closed-term panic is
      avoided or a different clean SAW proof path is available.
    - `Float`, `Double`, `mkFloat`, and `mkDouble`: SAW currently exposes no
      equality or eliminator surface that makes these bindings observable in a
      clean differential test. A direct probe showed the Lean backend emits
      these primitive terms rather than rejecting them, but elaboration-only
      checks do not count as conformance. Keep documented until there is an
      observable source-level property to compare.

- [ ] Pin audit findings with focused regression tests as code is removed.
  - Assert obsolete direct fix helpers do not appear in generated output unless
    the output also contains the checked proof-carrying contract that justifies
    the helper.
  - Add negative/diagnostic coverage for generic primitive or axiom emission
    once those paths become reject-by-default.
  - Maintain small closed-numeral and imported-name tests around macro or
    realization behavior, so replacements preserve the user-visible cases
    without trusting Haskell-side equivalence.
  - 2026-06-29 audit priority: keep expanding the conformance suite.
    `bvLg2` is now pinned; zero-divisor paths must be tested as explicit
    obligation/rejection surfaces rather than as total operations.

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
  - 2026-06-29 checkpoint: fixed `otherTests/saw-core-lean/Makefile` to export
    an absolute `SAW` path; the orchestrator `cd`s into test subdirectories, so
    a relative binary path made local full-suite runs fail before exercising the
    backend.

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
  - 2026-06-28 checkpoint: driver goldens and the driver harness now reject the
    deleted direct fix-helper surface. The harness was tightened to elaborate
    and scan all emitted `.lean` files in a driver directory, including names
    that do not begin with the `.saw` basename.

- [ ] Keep recursive/fix emission on the generic proof-carrying path.
  - Direct fix-shape helper surfaces (`mkStreamFix*`, `genFix*`,
    `GenFix*`, `StreamBodyProductive`, `PairStream*`,
    `saw_unreachable_default`, and `saw_productivity`) have been deleted from
    the Lean support library. They represented a false-start architecture where
    Haskell selected semantic lowerings and Lean merely checked side conditions.
  - Current rule: Haskell emits the literal SAWCore fixed-point body and the
    Lean propositions required to justify using it. Any ergonomic rewrite from
    the literal obligation to a cleaner recurrence must be a Lean theorem or
    proof-script hint, not a trusted Haskell classifier.
  - Obsolete proof examples built around the deleted helpers were removed
    (`E6_popcount`, `cryptol_running_sum_eq`, `popcount32_via_bridge`,
    `recursion_stream_corec`, `stream_fibs_corec`, and the
    `shape/productivity_contract` probes). Replacement examples should be
    rebuilt against the generic obligation surface once that emitted shape is
    stable.
  - Remaining work: harden completed-outline validation so proof examples
    cannot drift from the generated obligation, then add small recurrence
    examples that prove explicit generic fix contracts without reintroducing
    special-purpose helper APIs.

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
  - 2026-06-28 checkpoint: `completed.lean` is now checked against the tracked
    generated `.lean.good` artifact. The harness imports the generated artifact
    under a private namespace and requires `GeneratedHarness.goal = goal` by
    `rfl`, so completed outlines may simplify only by Lean definitional
    equality. Any non-definitional rewrite must be exposed as a separate
    Lean-checked proof artifact, not hidden in the edited outline.
  - 2026-06-29 audit finding: this harness is strong enough for trusted
    regression fixtures, but not for product replay. The final checker should
    generate a separate file that refers to fully qualified fresh obligation
    names, rather than appending unqualified checks inside the user's proof-file
    namespace.

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
- Keep the generic wrapped `fix` contract pinned with regression probes: it now
  rejects bodies where a successful fixed point coexists with an `Except.error`
  fixed point.
- Later cleanup: prove or further isolate the two Vec/BitVec round-trip axioms,
  update stale README/STATUS/examples, and implement SAW-side proof replay.

## Audit Findings: 2026-06-29

Fresh adversarial audit reference:
`doc/2026-06-29_comprehensive-audit.md`.

Validated immediate blockers:

- Fix SAW-vs-Lean bitvector semantic mismatches for division by zero and
  `bvLg2`.
- Prove or remove the two Vec/BitVec round-trip axioms.
- Keep generated files with local `by sorry` obligations classified as
  incomplete outlines. They may elaborate, but they are not checked discharges.
- Treat `offline_lean` as emit-stage behavior until a real Lean replay command
  exists.

Architecture follow-ups:

- Decide whether raw `InjectCodeDecl "Lean"` is rejected in sound mode or only
  allowed as an explicitly trusted support-library mechanism.
- Decide whether imported realizations need semantic realization theorems for
  the parity milestone, or remain explicit trusted assumptions.
- Replace or make proof-carrying the remaining Haskell semantic routing:
  `scLiteralFold`, opaque-builtin discovery, and transitional raw/wrapped
  classifiers.
- Classify tests as emission/golden, elaborates-with-open-obligations, or
  checked discharge.
- Scrub docs after the immediate semantic fixes so current behavior is not
  confused with the intended final proof-discharge workflow.

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
- `doc/2026-06-29_comprehensive-audit.md`
- `doc/proof-cookbook.md`
