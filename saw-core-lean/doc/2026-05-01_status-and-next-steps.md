# Status survey and next-steps plan

*Draft — 2026-05-01*

A snapshot of the `saw-core-lean` Lean 4 backend after Stage 5.1
(integration-test infrastructure, commit `00c056efd`), with a
prioritised list of what to do next. Picks up where the dated
`2026-04-23_*` and `2026-04-24_*` docs left off.

## 1. Where we are

### Architecture: stable

The pivot from "translate the whole Prelude as a universe-polymorphic
Lean library" to "specialization via `scNormalize`" landed cleanly
across:

- `27f9136ff` — Phase 3 Stage 4: specialization-mode backend
- `c1f319ea5` — Stage 4.1: iterate `scNormalize` to a fixed point
- `77f66e9c2` — Stage 4.2: shore up soundness boundaries
- `00c056efd` — Stage 5.1: integration-test infrastructure

Two earlier failed attempts (P4 v2, P6) live on the parked branches
`saw-core-lean-p4-wip` and `saw-core-lean-p6-wip` as institutional
memory. Reading the docs in chronological order tells a coherent
story: misplaced ambition → diagnosis → reframe → execution. The
docs from 2026-04-22 onward are accurate as historical record.

### Translator: ~1700 LoC

```
saw-core-lean/src/SAWCoreLean/CryptolModule.hs    106
saw-core-lean/src/SAWCoreLean/Lean.hs             119
saw-core-lean/src/SAWCoreLean/Monad.hs            128
saw-core-lean/src/SAWCoreLean/SpecialTreatment.hs 360
saw-core-lean/src/SAWCoreLean/Term.hs             690
saw-core-lean/lean/CryptolToLean/*.lean           277  (5 files)
                                                 ----
                                                 1680
```

Comparable in shape to the Rocq backend, smaller because the support
library is much leaner under specialization (one
`SAWCorePrimitives.lean` of 157 lines vs Rocq's 10 handwritten `.v`
files plus 2 generated).

### Tests: 16 smoketests + 4 intTests dirs, all green

- `saw-core-lean-smoketest` (Tasty): 12 pretty-printer cases, 3
  translator cases, 1 goal-emission case.
- `intTests/test_lean_basic/`: idBit, eqBit, literalNat, monomorphic
  implRev4. Pins both saw stdout and emitted `.lean`. Optional Lean
  elaboration via `lake env lean` when available.
- `intTests/test_lean_soundness_natrec/`: pinned `UnsoundRecursor`
  diagnostic via a hand-built `Nat#rec` term.
- `intTests/test_lean_soundness_polymorphic/`: pinned
  `polymorphismResidual` diagnostic for a `sort 1` binder.
- `intTests/test_lean_soundness_error_prop/`: pure-Lean test that
  the `error : Sort (u+1)` axiom rejects the Prop attack and accepts
  legitimate uses.

### Demo working end-to-end

`saw-lean-example/demo.saw` produces 5 outputs from `rev.cry`
(idBool, implRev, Rev, invol_prove0, eq_spec_prove0). All elaborate
under `lake env lean`. The polymorphic `Rev.lean` is 4109 lines —
the full Cryptol module specialization-unfolded.

### Soundness audited

Two independent agents audited the design on 2026-04-24:

- `2026-04-24_audit-nat-mapping.md` — SAW-Nat-to-Lean-Nat mapping
- `2026-04-24_audit-primitives-fidelity.md` — handwritten
  declarations vs SAWCore primitives

Both flagged real but bounded issues; all of them addressed in
Stage 4.2.

## 2. Stale or missing

### Hygiene

- `saw-core-lean/README.md` still says "Phase 0".
- Smoketest case `"polymorphic \\(a : Type) (x : a) -> x injects
  Inhabited"` (`smoketest/SmokeTest.hs`) has a misleading name; the
  assertion is still correct but the comment refers to the
  now-removed `Inh_a` auto-injection.
- `intTests/test_lean_basic/idBool.saw` hardcodes `Bit` rather than
  `Bool` (legacy demo naming).
- The two 2026-04-24 audit docs are good as-is, but the project
  doesn't yet have a single user-facing "soundness boundaries"
  summary that consolidates their findings into actionable rules
  (don't import outside SAW-emitted contexts, etc.).
- The original `2026-04-22_soundness.md` predates the specialization
  pivot; some statements ("the prelude is the unit of trust") are
  no longer load-bearing. Needs a short reconciliation note.
- `saw-core-lean-p4-wip` and `saw-core-lean-p6-wip` are
  unannotated branches. Adding a one-paragraph `NOTE.md` to the
  HEAD of each — what it is, why it's parked, when to revisit —
  would save future readers (or future-us) an hour of forensics.

### Coverage gaps

The Rocq backend has 13 test files in `otherTests/saw-core-rocq/`.
We mirror 4 (under different names). Unmirrored (in approximate
priority order):

| Rocq test                       | Lean equivalent | Notes |
|---------------------------------|-----------------|-------|
| `test_arithmetic`               | missing         | Concrete Nat/Int ops; should hit `addNat`/`subNat`/`intLe`/etc. |
| `test_boolean`                  | partial (`eqBool`) | Should also cover `if`, `&&`, `\|\|`, `xor`, negation. |
| `test_lambda`                   | partial (`idBit`) | Higher-order, currying, shadowing. |
| `test_literals`                 | partial (`literalNat`) | Numeric literals across Nat/Int/Bit ranges; vector literals. |
| `test_records`                  | missing         | Exercises `RecordType`/`RecordValue` we just added. |
| `test_tuples`                   | missing         | `PairType`/`PairValue`. |
| `test_sequences`                | missing         | Vec, take, drop, ++, reverse — bigger Cryptol surface. |
| `test_typelevel`                | missing         | Type-level Cryptol arithmetic; the verbose `bit0_macro` chains live here. |
| `test_cryptol_primitives`       | missing         | Cryptol prelude functions (`ecAdd`, `ecMul`, …) on small inputs. |
| `test_prelude`                  | missing         | SAWCore Prelude defs not unfolded by specialization; smaller surface than Rocq because we don't generate the prelude. |
| `test_offline_rocq`             | partial (demo only) | The two `*_prove0.lean` files exist as generated artefacts in the demo but aren't pinned as a test dir. |
| `test_cryptol_module_simple`    | partial (demo) | We have `rev.cry` end-to-end; not pinned at intTests. |
| `test_cryptol_module_sha512`    | far future      | Real-world Cryptol. Needs at minimum the missing `bit0_macro`-collapse and a wider Cryptol-primitive set. |

Smoketest gaps:

- No coverage for the `TranslationError` constructors. Each one
  should have a synthetic Term that triggers it (probe-style).
- No `polymorphismResidual` battery (positive: `Type`, `Nat`, `Num`;
  negative: `Sort 1`, `Sort 2`).
- No `UnsoundRecursor` guard test (the intTests version uses
  `parse_core`; a smoketest version using direct `scTerm` would
  exercise the same path without the SAW-script surface).

### Output verbosity (cosmetic, not soundness)

- Type-level Nats appear as `id (bit0_macro (bit0_macro 1))`
  instead of `4`. Pervasive — every Cryptol type-level numeric
  literal goes through it. The `replace` entries for
  `Bit0`/`Bit1`/`NatPos` in `SpecialTreatment.hs` lose
  the literal-collapse opportunity that was present in the
  earlier (deleted) `UseMacro` form.
- Cosmetic fix: pattern-match `NatPos` applied to a fully-collapsed
  Bit-chain and emit `Lean.NatLit`. Where the chain is symbolic,
  fall back to the wrapper functions. The Stage 4.2 commit
  abandoned the literal-collapse path because it complicated the
  Stage-4-time fix; under specialization, with `leanOpaqueBuiltins`
  in place, the literal-collapse is straightforwardly safe.
- Long qualifier prefixes everywhere (`CryptolToLean.\
  SAWCorePrimitives.foo`). Output readability would improve a lot
  with `open CryptolToLean.SAWCorePrimitives` at the top of each
  emitted file. The translator's preamble emitter already exists
  (`Lean.preamble`); this is a one-line addition.

### Backend feature gaps

- **No native `BitVec` binding.** The original design doc called
  this "the biggest Lean win" (`2026-04-22_lean-backend-design.md`
  §5.3); currently `bitvector n := Vec n Bool`. Faithful but loses
  Lean's `BitVec` ergonomics for downstream proofs. The tradeoff
  is a non-trivial coherence story — every Cryptol bv operation
  needs a proven equivalence between the `Vec n Bool` definition
  and the `BitVec n` shadow. Cost: weeks. Reward: Lean-side
  proofs about Cryptol bv code become tractable without manual
  `Vec`-rewriting.
- **No recursive Cryptol support.** `Prelude.fix` is rejected by
  the translator. Common in Cryptol idioms beyond `rev.cry`. Lean
  has `termination_by`; the translator path is non-trivial because
  SAW doesn't carry termination measures.
- **Cryptol primitive surface is thin.** ~25 primitives in
  `SAWCorePrimitives.lean`. Cryptol's prelude has hundreds. We
  cover what `rev.cry` plus `sum_example` exercises. Each gap
  fails loudly (unknown identifier or `UnsoundRecursor`), not
  silently — but every demo we want to add will surface a few.
- **`leanOpaqueBuiltins` is hand-curated.** It will keep growing as
  new programs surface Prelude defs that internally use `Nat#rec`
  / `Pos#rec`. A simple auto-detection pass (walk the Prelude
  module map, mark anything whose body transitively reaches
  `Nat#rec` or `Pos#rec` as opaque) would convert this from a
  manual chore to a translator-build-time computation.

### Operational

- No CI integration. The smoketest runs via `cabal test`, the
  intTests run via `cabal test integration-tests` — both work, but
  no `.github/workflows/*.yml` change has been made to actually
  run them on the saw-script repo. (Whether that's something
  upstream wants is part of the upstreaming story below.)
- No upstreaming story. The 2026-04-22 design doc Q4 asked "where
  to upstream"; still TBD. Options: (a) PR into
  `GaloisInc/saw-script` as a sibling of `saw-core-rocq`; (b)
  keep out-of-tree until the test surface is wide enough that
  upstream review is straightforward; (c) explicitly fork and
  rebase periodically.
- `build.log` is checked-out in the repo root and gets touched
  occasionally; should be in `.gitignore`.

## 3. Recommended arcs, in priority order

### Arc 1: Close out Stage 4/5 properly (≈half day)

After this, the project is *coherent and presentable*.

- Update `saw-core-lean/README.md` to reflect specialization-mode
  status, link to the planning docs in chronological order, mention
  the demo and the test suite.
- Consolidate the two 2026-04-24 audit docs into a single
  user-facing "soundness boundaries" doc. Bullet list of don'ts
  for Lean-side consumers (don't apply `error` outside non-Prop
  sorts even though the type permits it; instance the support
  library by import-then-open, etc.).
- Reconcile or supersede `2026-04-22_soundness.md` — short addendum
  noting which claims survived the specialization pivot.
- Fix the stale smoketest test name (`"polymorphic ... injects
  Inhabited"`).
- Rename `intTests/test_lean_basic/idBool.saw`'s Cryptol type from
  `Bit` to `Bool` (or document why Bit, kept for legacy reasons).
- Add `NOTE.md` at the HEAD of `saw-core-lean-p4-wip` and
  `saw-core-lean-p6-wip` describing what each branch is and the
  conditions under which to revisit.
- Add `build.log` to `.gitignore`.
- Implement the `NatPos`/`Bit0`/`Bit1` literal-collapse macro so
  emitted output reads like the design intended.

### Arc 2: Test coverage to Rocq-parity (≈1 day)

After this, regressions are caught automatically.

- Mirror the 9 unmirrored `otherTests/saw-core-rocq/` test files as
  `intTests/test_lean_*/` directories using the Stage-5.1
  infrastructure. Mostly mechanical: the SAW driver scripts can be
  copied with `write_rocq_term` → `write_lean_term`, then
  references regenerated and pinned via `make good`.
- Add a `test_lean_cryptol_module/` pinning the full polymorphic
  `Rev.lean` output (4109 lines today) so any future translator
  change is visible.
- Expand the smoketest with: each `TranslationError` constructor's
  trigger, a `polymorphismResidual` battery, and the
  `UnsoundRecursor` guard exercised via a synthetic Term.

### Arc 3: Output quality and ergonomics (≈1 day)

After this, the output is what the original design promised.

- Optionally bring `CryptolToLean.SAWCorePrimitives` into scope at
  the top of emitted files. Decision point: bare unqualified names
  read better but lose disambiguation; namespace-`open` is the
  middle path.
- Bind SAW's `bitvector` to Lean's native `BitVec n` with a
  documented coherence theorem set. Or: explicitly document why
  we're keeping `Vec n Bool` and what the user-side cost is.
  *(Done as the "document why" branch — see
  `2026-05-01_bitvec-binding-decision.md`.)*
- Auto-derive `leanOpaqueBuiltins` by walking the Prelude
  ModuleMap looking for `Nat#rec` / `Pos#rec` references.
- A `--dump-residual-primitives` flag on `write_lean_*` that
  reports which SAW names survived normalization — useful for
  growing the SAWCorePrimitives table when adding new demos.

### Arc 4: Real Cryptol coverage (multi-week)

Where the project becomes *useful*, vs *correct on the demo*.

- Recursion via `termination_by`. Needs a translator path that
  emits `def f` with a termination measure inferred or annotated.
- Wider Cryptol primitive set in `SAWCorePrimitives.lean`. SHA-256
  is a useful target — small enough to handcraft missing primitives
  for, big enough that the missing set will be visible.
- Real-world programs (SHA, AES, etc.) end-to-end. The
  Rocq-backend test `test_cryptol_module_sha512.saw` is an existing
  reference target.
- Proof-side tooling: `offline_lean` emits stubs today; the natural
  next question is "what does discharging one of these in Lean look
  like?" That's a separate doc — possibly a separate project — but
  worth scoping now so the emit format anticipates the proof flow.

## 4. Recommendation

**Do Arc 1 next.** It's small, finishes the loop on what's already
shipped, and the remaining work then has a clean baseline to build
on. Arc 2 is the natural follow-up — mirroring Rocq's tests is
mostly mechanical and the infrastructure is already in place.

Arc 3 is the right point to revisit BitVec — once the test suite is
broad enough that BitVec's cost (a wider proven-coherence set) can
be balanced against its ergonomic win on actual user code rather
than a single demo.

Arc 4 is open-ended but well-defined: each item is a concrete
unblocker for a specific class of Cryptol program. Pick by demand.
