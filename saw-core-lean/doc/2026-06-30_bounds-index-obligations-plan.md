# Bounds/Index Obligation Plan

**Date**: 2026-06-30

## Execution Goal

Implement proof-carrying emission for bounds/index-sensitive vector and Cryptol
indexing operations in the SAW-Lean backend.

This is the next backend-completion target after partial-operation obligations.
At the end of this phase, every in-scope fully applied bounds/index operation
must either:

1. emit a visible Lean proof obligation for the exact bounds/index condition
   and consume checked evidence for that condition; or
2. reject at SAW translation time with a pinned final-boundary diagnostic when
   no sound proof-carrying function shape has been designed.

The target is not proof automation. Generated obligations may remain open in
emit-stage artifacts. The target is sound emission: no unchecked default, no
hidden Haskell proof, no trusted SAW proof argument, and no fallback to a
total-looking helper when the source operation is partial or proof-carrying.

Strict phase boundary: do not build Lean automation while executing this plan.
Do not add convenience tactics, proof-search macros, simp bundles, generated
proof-search scripts, or proof-library lemmas whose purpose is to make emitted
obligations discharge automatically. The existing local obligation placeholder
skeleton is allowed only as emit-stage scaffolding and must not count as proof
discharge. Proof search is a later proof-ergonomics phase. For this phase,
success means the emitted Lean states the right obligation and the helper
types require the right evidence, not that Lean can automatically prove the
evidence.

## Why This Is Next

The conformance matrix now shows the partial-operation family as closed for
fully applied emissions. The largest remaining soundness-sensitive surface of
the same kind is bounds/index evidence:

- `Cryptol.ecAt` currently has a known-gap obligation fixture because finite
  indexing can reach an emitted Lean type mismatch before exposing the desired
  bound obligation.
- Prelude with-proof vector primitives are currently rejected:
  `atWithProof`, `genWithProof`, `updWithProof`, `sliceWithProof`, and
  `updSliceWithProof`.

These are not mere ergonomic gaps. Incorrect handling can silently choose an
out-of-bounds default, trust a SAW proof object that Lean has not checked, or
reconstruct a vector operation with the wrong precondition. Fixing this moves
the backend toward Rocq parity while preserving the project rule that Haskell
stays dumb.

## Non-Negotiable Rules

- Haskell must not prove bounds, classify an index as in-bounds, normalize
  arithmetic to erase an obligation, or trust source proof terms.
- Haskell may construct the Lean syntax for the contract proposition and wire
  a checked proof term into a helper.
- Source proof arguments such as `IsLtNat i n` and `IsLeNat (addNat off len) n`
  are not themselves accepted as Lean evidence. If the emitted Lean result
  depends on such evidence, the backend must emit a Lean proof obligation and
  consume the Lean-checked proof.
- Lean support helpers must be thin proof-taking wrappers around faithful vector
  operations. If a helper is not definitionally tied to the existing raw helper,
  prove the realization theorem in Lean before treating the helper as trusted.
  If that theorem is not available yet, the corresponding surface remains a
  known gap rather than a completed implementation.
- Do not use `atWithDefault` with an arbitrary default as the final realization
  of a proof-carrying in-bounds access unless the emitted contract proves that
  the default branch is unreachable and Lean checks that proof.
- Do not add Haskell pattern recognizers for the current examples. Tests should
  pass because the backend has a general checked-application contract.
- Do not add Lean automation for generated bounds proofs in this phase. No new
  tactics, tactic macros, generated proof-search scripts, broad `simp`/`omega`
  proof search, or proof-support lemmas should be introduced to make current
  rows pass. Leave obligations open and pin known gaps when evidence is not
  already available through the checked helper interface.
- Under-applied proof-carrying operations remain boundary rejections unless
  they are covered by an explicit proof-carrying higher-order wrapper
  convention, such as the checked prefix-partial access convention.

## In-Scope Surfaces

### Cryptol wrapper

Authoritative source: `cryptol-saw-core/saw/Cryptol.sawcore`.

- `ecAt : (n : Num) -> (a : isort 0) -> (ix : sort 0) ->
  PIntegral ix -> seq n a -> ix -> a`

The implementation must survey and account for all behaviorally distinct
branches before claiming `ecAt` complete:

- finite `TCNum n` sequence, nonnegative index: requires bound evidence
  for the selected `Nat` index;
- finite `TCNum n` sequence, negative index: follow `Cryptol.sawcore`
  semantics exactly. Today the negative branch indexes at zero rather than
  raising the commented-out error; do not invent a stricter boundary unless the
  source changes. Pin the emitted zero-index branch specifically; a generic
  proof-stub known gap is not enough branch coverage.
- infinite `TCInf` stream: no finite bound exists; indexing should route
  through the stream lookup semantics after the same source index conversion.
- unsupported or malformed residual shapes: reject with a clear diagnostic,
  and pin a boundary or known-gap row.

The first implementation driver is the existing focused finite fixture:
`otherTests/saw-core-lean/obligations/cryptol_ec_at_bounds`.

### Prelude with-proof vector primitives

Authoritative source: `saw-core/prelude/Prelude.sawcore`.

- `atWithProof : (n : Nat) -> (a : sort 0) -> Vec n a ->
  (i : Nat) -> IsLtNat i n -> a`
- `genWithProof : (n : Nat) -> (a : sort 0) ->
  ((i : Nat) -> IsLtNat i n -> a) -> Vec n a`
- `updWithProof : (n : Nat) -> (a : sort 0) -> Vec n a ->
  (i : Nat) -> a -> IsLtNat i n -> Vec n a`
- `sliceWithProof : (a : sort 0) -> (n off len : Nat) ->
  IsLeNat (addNat off len) n -> Vec n a -> Vec len a`
- `updSliceWithProof : (a : sort 0) -> (n off len : Nat) ->
  IsLeNat (addNat off len) n -> Vec n a -> Vec len a -> Vec n a`

The existing obligation fixtures for these operations are known gaps that only
exercise the under-applied primitive name. They must be rewritten into minimal
fully applied litmus tests for the proof-carrying path. Separate saw-boundary
rows should continue to pin under-applied rejection.

## Correct Contract Shapes

The exact emitted names may vary, but each positive target must have this
shape:

```lean
let h_bounds_obligation_ : Prop := <operation-specific bound proposition>
let h_bounds_ : h_bounds_obligation_ := by
  sorry
<checked helper> ... h_bounds_
```

The proposition must mention the actual translated index/offset/length/width
terms used by the result. It must not be a generic, disconnected fact.

Candidate propositions:

| Source surface | Required Lean proposition |
| --- | --- |
| `ecAt (TCNum n) ... xs ix` after source index conversion to `i : Nat` | `i < n` for the finite nonnegative branch |
| `atWithProof n a xs i p` | `i < n` |
| `genWithProof n a f` | for every generated `i`, the element call receives Lean evidence of `i < n`; either the helper carries the `Fin n` proof directly or the emitted contract supplies a proof function `(i : Nat) -> i < n -> ...` |
| `updWithProof n a xs i x p` | `i < n` |
| `sliceWithProof a n off len p xs` | `off + len <= n` |
| `updSliceWithProof a n off len p xs ys` | `off + len <= n` |

For `genWithProof`, do not fake a global proposition such as `True`. The source
function consumes an index proof at every generated position. A sound Lean
helper should make that evidence available from the `Fin n` index or require a
visible proof-producing function. If this shape exposes a new function-binder
translation issue, stop and update this plan instead of adding an ad hoc
translation branch.

## Haskell Architecture

Add a general checked-application contract for proof-carrying operations. It may
reuse and generalize `PartialOpContract`, but it should not become another
collection of local pattern branches.

The contract table should specify:

- source module and source identifier;
- exact arity required for the proof-carrying lowering;
- how each source argument is used by the checked helper:
  - raw type/index argument;
  - wrapped value argument;
  - function argument with proof/evidence binder;
  - source proof argument that is ignored and replaced by a Lean obligation;
- how to build the Lean proposition from already translated terms;
- the checked Lean helper name;
- forbidden fallback names for tests.

Acceptable Haskell responsibilities:

- translate ordinary data/value arguments according to the declared modes;
- construct `i < n` or `off + len <= n` syntax from translated terms;
- emit the local obligation binding;
- call the checked helper with the generated proof variable;
- reject non-exact-arity forms until a higher-order wrapper exists.

Forbidden Haskell responsibilities:

- deciding that an index is in bounds;
- simplifying `off + len <= n` to remove the obligation;
- inspecting generated Lean syntax to prove arithmetic;
- trusting the SAW proof argument;
- choosing `atWithDefault` defaults for out-of-bounds behavior;
- pattern-matching the current litmus examples.

If `PartialOpContract` remains specific to nonzero partial operations, introduce
a sibling type such as `CheckedApplicationContract`. The important abstraction
is not the name; it is that all proof-carrying applications share one
declarative path.

## Lean Support Library

Add checked helpers to `CryptolToLean.SAWCorePrimitives` or a small adjacent
support module.

Expected helper families:

```lean
def atWithProof_checkedM
  (n : Nat) (α : Type) (xs : Except String (Vec n α))
  (i : Nat) (h : i < n) : Except String α := ...

def updWithProof_checkedM
  (n : Nat) (α : Type) (xs : Except String (Vec n α))
  (i : Nat) (x : Except String α) (h : i < n) :
  Except String (Vec n α) := ...

def sliceWithProof_checkedM
  (α : Type) (n off len : Nat)
  (h : off + len <= n) (xs : Except String (Vec n α)) :
  Except String (Vec len α) := ...

def updSliceWithProof_checkedM
  (α : Type) (n off len : Nat)
  (h : off + len <= n) (xs : Except String (Vec n α))
  (ys : Except String (Vec len α)) :
  Except String (Vec n α) := ...
```

For `genWithProof`, prefer a helper that uses `Fin n` evidence internally:

```lean
def genWithProof_checkedM
  (n : Nat) (α : Type)
  (f : (i : Nat) -> i < n -> Except String α) :
  Except String (Vec n α) := ...
```

If the existing translator cannot yet translate the source function into this
shape, do not work around it with Haskell body rewriting and do not add Lean
automation to force the example through. Emit a known-gap fixture describing the
required function-binder adaptation, then design that adapter explicitly.

For `ecAt`, the chosen implementation is more general than a Cryptol-specific
classifier: keep the underlying `Prelude.at` definition opaque during
normalization and route fully applied `Prelude.at` through the same
checked-application contract table as the with-proof vector operations. This
exposes the source precondition documented in `Prelude.sawcore`:

```lean
def at_checkedM
  (n : Nat) (α : Type) (xs : Except String (Vec n α))
  (i : Nat) (h : i < n) : Except String α := ...
```

The current helper reuses `atWithProof_checkedM`, because the checked Lean
realization is exactly vector lookup with kernel-checked `i < n` evidence.
Haskell does not inspect `ecAt`, classify positive/negative branches, or prove
the bound; it only preserves `Prelude.at` and emits the `i < n` contract when
that source primitive is fully applied.

An `ecAt_checkedM` wrapper remains a possible future proof-ergonomics layer if
we need branch-local theorems, but it is not the soundness boundary for this
phase:

```lean
def ecAt_checkedM ... (h : <finite index bound>) : Except String α := ...
```

The helper must match `Cryptol.sawcore` branch behavior. During this phase,
prefer helpers that are definitionally tied to existing checked primitives. If
that definitional tie is not available, do not build a proof library or tactic
layer to force completion. Record the missing realization theorem as a
proof-library gap and keep the corresponding row pinned until the proof phase.

## Testing Plan

All tests must live under the existing `make test-saw-core-lean-conformance`
infrastructure.

### Promote known-gap obligation fixtures

Promote these only after they emit the expected proof-carrying shape:

- `obligations/cryptol_ec_at_bounds`
- `obligations/cryptol_ec_at_negative_bounds`
- `obligations/vector_at_with_proof`
- `obligations/vector_gen_with_proof`
- `obligations/vector_upd_with_proof`
- `obligations/vector_slice_with_proof`
- `obligations/vector_upd_slice_with_proof`

Each positive `expected.txt` must require:

- a local bounds/index obligation name, such as `h_bounds_obligation_`;
- a local evidence name, such as `h_bounds_`;
- the exact proposition family (`<`, `<=`, or a named reducible predicate);
- the checked helper name;
- absence of forbidden unchecked bypasses such as `atWithDefault` with an
  arbitrary error default, direct rejected with-proof primitive names, raw
  proof-primitive reliance, or obsolete helper names.

### Preserve boundary coverage

Under-applied with-proof primitives remain boundary cases until a
proof-carrying higher-order wrapper is designed. Keep or add saw-boundary rows
that pin rejection of:

- bare `atWithProof`;
- bare `genWithProof`;
- bare `updWithProof`;
- bare `sliceWithProof`;
- bare `updSliceWithProof`.

These rows are not evidence that the fully applied proof-carrying surface is
complete; they only prevent unsafe function-valued fallthrough.

### Add branch coverage for `ecAt`

Before claiming `ecAt` complete, add or classify focused rows for:

- finite nonnegative in-bounds index: positive obligation shape;
- finite nonnegative out-of-bounds index: visible obligation that cannot be
  discharged, or a pinned known gap if the emit-stage cannot represent it yet;
- finite negative index: source-semantics row matching `Cryptol.sawcore`'s
  current zero-index branch, with checks specific enough to fail if the emitted
  access no longer uses index zero;
- infinite stream index: value differential or obligation row, depending on
  whether any source-side precondition remains visible.

Do not use a large Cryptol example as the acceptance test. Each row should be a
minimal litmus.

### Preserve newly exposed generated-sequence failures

Keeping `Prelude.at` opaque and checked is intentionally broader than the
original `ecAt` fixture. Existing finite sequence differential rows may now
fail because their emitted Lean contains bounds obligations inside `genM` or
derived sequence helper functions. Those are real failures, not regressions to
paper over:

- do not reintroduce `atWithDefault` as an unchecked fallback;
- do not add Haskell index arithmetic recognizers to prove these cases;
- pin affected executable rows as known gaps if the true differential harness
  rejects them for `sorry`-backed generated bounds;
- route ordinary generators through Lean-side generated-index evidence
  threading, so element functions can consume `Fin n`/`i < n` evidence checked
  by the kernel;
- after direct `i < n` obligations are discharged, preserve any remaining
  derived-index failures as known gaps until Lean-side proof support handles
  transformed indices such as offsets, subtraction, reverse, split/update
  branches, and nested transpose indices. Getting emitted Lean to pass
  automatically is not the objective; broad proof search must not be part of
  this goal. If we add proof automation later, it should be explicit Lean-side
  proof-library work in a separate phase, and failures should remain visible
  until that checked proof support exists.

## Acceptance Criteria

This phase is complete only when all of the following are true:

1. The six target known-gap fixtures above are either promoted to positive
   obligation-shape tests or split into a positive fully applied row plus a
   justified pinned known gap for a newly discovered sub-surface.
2. Fully applied bounds/index operations do not emit unchecked total-looking
   indexing, arbitrary defaults, or trusted source proof arguments.
3. Under-applied proof-carrying vector primitives reject with pinned
   diagnostics unless a proof-carrying higher-order wrapper has been designed
   and implemented.
4. Haskell implements a declarative checked-application contract path rather
   than operation-specific semantic branches.
5. Lean helpers consume proof evidence in their types and are either thin
   wrappers around faithful vector operations or explicitly recorded as pending
   proof-library realization gaps.
6. `otherTests/saw-core-lean/CONFORMANCE.md` records the final status of every
   target row as `obligation`, `known gap`, or `boundary`.
7. `saw-core-lean/TODO.md` points to the completed checkpoint and lists any
   residual proof-ergonomics or function-wrapper work separately from emission
   soundness.
8. No new Lean automation was added for this feature: no convenience tactics,
   tactic macros, generated proof-search scripts, or proof-support lemmas whose
   purpose is to discharge these bounds/index obligations automatically.
9. Validation passes:
   - `lake build` in `saw-core-lean/lean`;
   - `cabal build exe:saw`;
   - focused obligation/boundary tests for each changed row;
   - `make test-saw-core-lean-conformance`;
   - `git diff --check`.

## Stop Conditions

Stop and reassess rather than patching locally if any of these occur:

- `genWithProof` requires a new proof-binder translation convention that is not
  covered by the checked-application abstraction.
- `ecAt` exposes a source branch whose behavior is unclear from
  `Cryptol.sawcore`.
- a helper would need to duplicate substantial vector semantics instead of
  delegating to existing definitions or proving an equivalence in Lean.
- a passing test would require weakening the obligation, trusting a source proof
  term, or hiding a condition in Haskell.
- adding the next operation requires a second bespoke lowering path rather than
  another table entry.
- progress appears to require Lean automation, proof-search tactics, or helper
  lemmas whose purpose is proof discharge rather than defining the checked
  emission interface.

These are design points, not permission to add a special case.

## Expected Next Work Order

1. Rewrite the with-proof obligation fixtures so positive tests use fully
   applied minimal terms; keep under-applied rejection as boundary coverage.
2. Add only thin Lean checked helpers needed as the emission interface. Do not
   add proof automation or proof-support theorems to discharge generated
   obligations.
3. Add the checked-application contract abstraction in Haskell and route one
   direct operation, starting with `atWithProof`.
4. Promote `vector_at_with_proof`; then route and promote `updWithProof`,
   `sliceWithProof`, and `updSliceWithProof`.
5. Design and route `genWithProof`, stopping if proof-binder adaptation needs a
   separate abstraction.
6. Route finite `ecAt` through the same contract discipline; then add branch
   coverage for negative and stream cases.
7. Run the full validation gate and update the conformance matrix/TODO.
