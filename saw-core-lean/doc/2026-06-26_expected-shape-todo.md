# Expected-shape stabilization TODO

**Date**: 2026-06-26
**Goal**: converge the Phase beta backend on the expected-shape design in
`2026-06-26_phase-beta-expected-shape.md`, preserving the hard soundness
requirement: reject rather than emit semantically different Lean.

## Current slice

- [x] Replace recursor case-handler raw-arity splitting with per-binder
  roles derived from constructor metadata and actual datatype parameters.
- [x] Make `cryptol_module_simple` generated Lean elaborate directly,
  without refreshing `.lean.good` first.
- [x] Keep proof/type-producing recursors raw while adapting only value
  computations.
- [ ] Add regression coverage for datatype-parameter case fields, e.g.
  `RecordType.rec` instantiated with a Phase-beta function parameter.
  Current coverage: focused `cryptol_module_simple` direct Lean check
  exercises this path; smoke coverage now pins the corresponding
  `RecordValue` function-field constructor shape.
- [x] Make recursor constructor-field shadowing demand-driven and extend
  it to non-function datatype-parameter fields. This preserves the
  function-field shape already used by records while letting
  parameter-instantiated fields such as `Stream α` be viewed through the
  wrapped Phase-beta body interface.

## Expected-shape migration

- [x] Replace `wrappedVars :: Set Lean.Ident` with a `BindingShape`
  environment that distinguishes raw, wrapped, and function-shaped
  bindings. This is the first environment slice; full function
  conventions are still tracked by the callee-convention item below.
- [x] Move application lifting behind an explicit callee convention:
  raw Lean target, Phase-beta emitted definition, wrapped helper, macro.
  Progress: global and special-treated application dispatch now has a
  `TranslatedTerm` path. Macro-style `SpecialTreatment` entries carry
  explicit result shapes, and `UseMapsToWrapped` records per-formal
  conventions for raw, wrapped, and function-shaped helper arguments.
- [x] Replace transitional Lean helper result-shape recognition with
  result shapes carried by translation.
  Progress: application argument planning and shared `let` bindings now
  consume `TranslatedTerm` result shapes instead of immediately
  reclassifying emitted Lean syntax. Recursor applications and wrapped
  helper mappings now also return explicit shapes. The transitional
  `leanTermResultShape` classifier has been removed.
- [x] Convert constructor application to use the same adaptation path as
  raw Lean function application.
- [x] Classify every rawifying adapter. If it can erase `Except.error`
  for translator-emitted inputs, replace it, prove/enforce its
  preconditions, or reject the shape.
  Progress: direct `Prelude.MkStream` no longer emits monadic stream
  adapters; residual per-index effects become explicit totality
  obligations. Shape-specific stream/vector `fix` helpers have been
  removed rather than preserved as alternate lowering targets. Statically
  in-bounds raw vector indexing now emits `atInBounds` with an explicit
  `(by decide)` proof rather than a dummy default.
- [x] Decide and close the fix-productivity fallback surface. This is
  separate from `Except.error` erasure: there is no unreachable-default
  fallback in the live Lean library. The backend emits explicit Lean
  obligations for `Prelude.fix` (`saw_fix_unique_exists` or its raw
  variant), and unsupported recurrence reasoning remains a proof
  obligation until Lean kernel-checks evidence.

## Validation gates

- [x] `cabal test saw-core-lean-smoketest`
- [x] `cabal build exe:saw`
- [x] Focused driver: regenerate and direct-check
  `drivers/cryptol_module_simple/test_cryptol_module_simple.module.lean`
- [x] Focused driver: regenerate and direct-check
  `drivers/cryptol_polymorphic_class_dict/test_poly_eq.module.lean`
- [x] Focused driver: regenerate and direct-check
  `drivers/cryptol_module_rec_ones/test_cryptol_module_rec_ones.module.lean`
- [x] Focused driver: regenerate and direct-check
  `drivers/cryptol_module_stream_fibs/test_cryptol_module_stream_fibs.module.lean`
- [x] Focused driver: regenerate and direct-check
  `drivers/cryptol_chacha20_iround_zero/test_cryptol_chacha20_iround_zero.eq_prove0.lean`
- [x] Focused driver: regenerate and direct-check
  `drivers/cryptol_chacha20_core_iterate/test_cryptol_chacha20_core_iterate.eq_prove0.lean`
- [x] Direct Lean sweep over generated driver `.lean` files
  - 2026-06-27: full `otherTests/saw-core-lean/test.sh test` found no driver
    `*.lean.elaboration.fail` files and no obsolete-helper failures. Remaining
    driver failures were stale `.lean.good` diffs; proof directories remain
    intentionally stale until the proof-ergonomics stage.
- [x] Refresh focused `.lean.good` files after direct Lean checks pass
