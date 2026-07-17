# Priority #1 Principled Emission Plan

Date: 2026-06-30

This note turns the current gap list into an implementation plan for Priority
#1: remove clever or legacy Haskell emission paths by replacing them with
explicit proof-carrying contracts checked by Lean.

The immediate driver is the remaining partial-operation gap for Cryptol signed
bitvector wrappers, `ecSDiv` and `ecSMod`. Those fixtures currently fail before
the direct `bvSDiv` / `bvSRem` contract path because the Cryptol wrapper leaves
a residual `Prelude.Nat__rec`. The fix must be principled; it must not be a
Haskell classifier that recognizes one width pattern and rewrites the term to a
convenient direct primitive call.

Implementation checkpoint: the immediate `ecSDiv` / `ecSMod` driver is now
implemented. The wrappers stay opaque under Lean normalization and route
through checked Lean helpers over `Cryptol.Num`; Haskell passes the raw `Num`
argument and wrapped operands to the contract table but does not compute a
finite predecessor width or erase the wrapper's recursor structure.
Audit follow-up: the finite positive helper branches now call
`bvSDiv_checkedM` / `bvSRem_checkedM` rather than reimplementing signed-BV
semantics, `rfl` equations pin those finite-successor branches, and
non-exact-arity partial-operation uses reject until a proof-carrying
higher-order wrapper is designed.

## Goal

For every soundness-sensitive emission surface:

1. Haskell emits the source-shaped Lean term, or a named checked helper with an
   explicit contract.
2. Any non-obvious semantic equivalence is represented as a Lean proposition,
   theorem, or local proof obligation.
3. The emitted result can only use the helper if Lean receives evidence for the
   required contract.
4. Unsupported surfaces reject or remain pinned known gaps until such a
   contract exists.

The end state is not "more special cases"; it is a small family of explicit
emission contracts that make the translator's behavior auditable.

## Non-Goals

- Do not add Haskell width arithmetic such as recognizing
  `ecSDiv (TCNum (Succ n))` and emitting `bvSDiv n`.
- Do not add another `scNormalizeForLean` escape hatch whose correctness relies
  on Haskell computing a semantic equivalence.
- Do not hide the zero-width, infinite-stream, or zero-divisor cases behind a
  total Lean default.
- Do not promote known-gap tests by weakening the expected obligation shape.

## Core Abstraction

Generalize the current `PartialOpContract` idea into a reusable checked
application contract. The direct partial-operation implementation is the first
instance of this design, but the abstraction should also cover wrapper,
recursor, and bounds/index helper surfaces.

A checked application contract should record:

- source identity and full arity;
- accepted application shape, including what happens to under-applied uses;
- per-argument convention: raw, wrapped, function-shaped, or dependent/raw
  binder;
- result convention: raw, wrapped, function-shaped, or continuation-bound;
- one or more named obligations, each with a deterministic proposition builder;
- checked Lean helper name;
- optional starter proof script, whose failure leaves a visible obligation
  rather than changing the emitted term;
- optional realization theorem name when the helper is not definitionally just
  a thin wrapper around the emitted source shape.

The contract table may construct propositions from the source arguments. It may
not inspect generated Lean syntax to decide that an obligation is unnecessary,
prove a precondition, erase `Except.error`, or pick a fallback value.

## Immediate Driver: `ecSDiv` / `ecSMod`

`Cryptol.sawcore` defines signed word division/modulus by eliminating the
Cryptol `Num` width:

- finite zero width goes to a runtime error function;
- finite successor width delegates to `bvSDiv n` / `bvSRem n`;
- infinite stream width goes to a runtime error function.

Before the checkpoint, a focused zero-divisor fixture such as
`ecSDiv (TCNum 8) 0xf9 0x00` failed because `Nat__rec` survived normalization
and the translator rejected the residual recursor before the direct BV
partial-operation contract could fire.

The principled fix is:

1. Add a checked wrapper/recursor contract for the Cryptol signed-BV entry
   points, not a closed-width Haskell rewrite.
2. State the required facts explicitly in Lean:
   - the width argument is the finite successor case needed by signed BV
     primitives;
   - the divisor is not the zero vector at that width;
   - zero-width and infinite-stream cases either remain error-producing or are
     impossible under the emitted finite-successor contract.
3. Route the wrapper through a Lean helper that consumes that evidence and then
   calls `bvSDiv_checkedM` / `bvSRem_checkedM`.
4. If the helper is not a literal definitional realization of the
   `Cryptol.sawcore` body, add or plan a Lean-checked realization theorem tying
   the helper contract back to the source wrapper semantics.
5. Promote `obligations/cryptol_ec_sdiv_zero` and
   `obligations/cryptol_ec_smod_zero` only when the emitted artifact exposes
   the expected finite-successor/nonzero obligations and cannot circumvent the
   checked BV helper.

This still keeps Haskell dumb: it wires a declared source operation to a
declared checked contract. Lean owns the width/recursor reasoning.

## Recursor Policy

Residual recursors are not all the same problem. The plan is:

- Keep rejecting raw dangerous recursors until there is a checked contract.
- For narrow wrapper surfaces where the recursor is part of a support-library
  realization, use a named checked helper plus a realization theorem or local
  obligation.
- Do not globally map `Nat#rec`, `Bool#rec`, or other recursors to Lean's native
  recursors without an argument-order and motive-convention proof. Bool is
  especially dangerous because SAW and Lean use different constructor orders.
- Treat future generic `Nat__rec` support as a checked recursor contract, not as
  a normalization rule. It must specify motive/result conventions and test
  constructor-order behavior directly.

## Extension Targets

After `ecSDiv` / `ecSMod`, use the same contract style for:

- `ecAt` and indexing wrappers: emit visible bounds/index obligations consumed
  by checked vector-access helpers.
- With-proof vector primitives: replace rejection with checked helpers whose
  types consume the supplied or generated bounds evidence.
- Stream helper totality: move unresolved totality stubs into explicit
  obligations or checked helper contracts.
- Imported realizations: keep the audit-visible alias, but add richer
  realization obligations where type-correctness alone is not enough.
- `scLiteralFold`: replace trusted Haskell literal folding with either literal
  emission plus Lean-side normalization evidence or explicit dependent
  cast/equality obligations at the use sites that need normalized sizes.

## Acceptance Criteria

For the immediate signed-BV wrapper slice:

- done: `obligations/cryptol_ec_sdiv_zero` and
  `obligations/cryptol_ec_smod_zero` are positive shape tests rather than
  known gaps;
- done: the positive shape tests require `ecSignedBVNonzeroM`, checked
  `ecSDiv_checkedM` / `ecSMod_checkedM`, and absence of residual `Nat__rec` or
  unchecked direct signed-BV circumventes;
- done: the checked wrapper helpers delegate to `bvSDiv_checkedM` /
  `bvSRem_checkedM` in the finite positive case;
- done: non-exact-arity partial-operation identifiers reject before falling
  through to unchecked direct mappings;
- done: Haskell does not compute the predecessor width or recognize a closed
  `TCNum` pattern to decide the semantic translation;
- validation remains the normal full conformance gate:
  `make test-saw-core-lean-conformance`.

For the broader Priority #1 architecture:

- each remaining clever path in
  `doc/2026-06-28_clever-legacy-path-audit.md` is either removed, converted to
  a checked contract, or explicitly justified as syntactic plumbing;
- no backup or legacy branch preserves obsolete behavior after the checked path
  exists;
- the conformance and obligation matrices distinguish conforming cases,
  obligations, known gaps, and final boundaries.

## Work Breakdown

1. Done: extended `PartialOpContract` to cover this wrapper-shaped case
   directly; a separate wrapper-contract type was not needed for the current
   arity and argument-convention shape.
2. Done: added the Lean support carrier, predicate, and helpers needed for
   finite-successor signed-BV wrapper contracts.
3. Done: routed fully applied `ecSDiv` and `ecSMod` through that contract
   table.
4. Done: refreshed the two obligation fixtures from known gaps to positive
   shape tests.
5. Next validation gate: run `lake build`, `cabal build exe:saw`, and
   `make test-saw-core-lean-conformance`.
6. Reassess whether the same abstraction cleanly covers `ecAt`; if yes, move
   directly to bounds/index obligations. If not, update this plan before
   coding another local case.
