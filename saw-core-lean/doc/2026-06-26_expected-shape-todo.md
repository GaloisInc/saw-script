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

## Expected-shape migration

- [x] Replace `wrappedVars :: Set Lean.Ident` with a `BindingShape`
  environment that distinguishes raw, wrapped, and function-shaped
  bindings. This is the first environment slice; full function
  conventions are still tracked by the callee-convention item below.
- [ ] Move application lifting behind an explicit callee convention:
  raw Lean target, Phase-beta emitted definition, wrapped helper, macro.
- [ ] Replace `isLikelyWrappedTerm` helper-name recognition with result
  shapes carried by translation.
  Progress: application argument planning and shared `let` bindings now
  consume `TranslatedTerm` result shapes instead of immediately
  reclassifying emitted Lean syntax. Compound helper applications still
  use `isLikelyWrappedTerm` as a fallback until callee conventions carry
  their result shapes explicitly.
- [ ] Convert constructor application to use the same adaptation path as
  raw Lean function application.
- [ ] Classify every rawifying adapter. If it can erase `Except.error`
  for translator-emitted inputs, replace it, prove/enforce its
  preconditions, or reject the shape.

## Validation gates

- [x] `cabal test saw-core-lean-smoketest`
- [x] `cabal build exe:saw`
- [x] Focused driver: regenerate and direct-check
  `drivers/cryptol_module_simple/test_cryptol_module_simple.module.lean`
- [ ] Direct Lean sweep over generated driver `.lean` files
- [ ] Only after direct Lean checks pass: refresh `.lean.good` files in a
  separate mechanical commit
