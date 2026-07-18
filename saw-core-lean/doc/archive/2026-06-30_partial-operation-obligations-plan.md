# Partial-Operation Obligation Plan

**Date**: 2026-06-30

## Goal

Close the highest-priority known-gap family in the SAW-Lean backend:
partial operations whose Lean support-library definitions currently look total
at zero divisors or zero denominators.

The required end state is proof-carrying emission, not a larger collection of
Haskell special cases. When SAW-Lean emits a term whose soundness depends on a
nonzero divisor, nonzero denominator, or nonzero reciprocal argument, the
generated Lean must expose that precondition as a visible proof obligation and
make the emitted result depend on checked evidence for it.

This follows the general rule in
`2026-06-26_proof-carrying-soundness-contracts.md`: Haskell constructs syntax
and contracts; Lean checks the mathematical evidence.

## Surfaces

Priority order:

1. Direct Prelude scalar operations:
   - `divNat`, `modNat`, `divModNat`;
   - `intDiv`, `intMod`;
   - `ratio`, `rationalRecip`.
2. Direct Prelude bitvector operations:
   - `bvUDiv`, `bvURem`;
   - `bvSDiv`, `bvSRem`.
3. Cryptol.sawcore wrappers that lower to the same partial surfaces:
   - `ecDiv`, `ecMod`;
   - `ecFieldDiv`, `ecRecip`;
   - `ecSDiv`, `ecSMod`.

The existing corpus entries under `otherTests/saw-core-lean/obligations/*`
are the acceptance tests for this work. They must be promoted from
`.known-gap` to positive obligation-shape tests as each family is implemented.

## Implementation Checkpoints

2026-06-30 scalar checkpoint:

- implemented a shared direct-primitive `PartialOpContract` lowering path for
  `divNat`, `modNat`, `divModNat`, `intDiv`, `intMod`, `ratio`, and
  `rationalRecip`;
- added thin checked Lean helpers for those operations in
  `CryptolToLean.SAWCorePrimitives`;
- promoted the seven direct scalar zero-divisor / zero-denominator obligation
  fixtures from known gaps to positive shape tests.
- represented Int and Rational value-domain contracts over wrapped
  `Except String` expressions, not over post-bind variables. This keeps the
  proposition connected to the emitted computation and lets Lean prove simple
  closed nonzero cases before the monadic bind erases the expression.
- promoted `ecDiv`, `ecMod`, `ecFieldDiv`, and `ecRecip` obligation fixtures
  where Cryptol normalization reaches the scalar contract path.

2026-06-30 bitvector checkpoint:

- extended `PartialOpContract` with explicit helper argument modes and a
  data-driven proposition builder. This handles operations whose checked helper
  takes a raw width argument plus wrapped value arguments without adding a
  bitvector-specific semantic classifier.
- added named Lean predicates `bvNonzero` / `bvNonzeroM` and thin checked
  helpers for `bvUDiv`, `bvURem`, `bvSDiv`, and `bvSRem`.
- promoted the four direct bitvector zero-divisor obligation fixtures from
  known gaps to positive shape tests.
- split nonzero executable bitvector division into a pinned differential known
  gap. The emitted obligations are the intended sound shape, but the starter
  proof does not yet discharge concrete vector nonzero facts.

2026-06-30 signed-wrapper checkpoint:

- kept `ecSDiv` and `ecSMod` opaque across Lean normalization so their
  wrapper boundary remains visible to the translator instead of exposing a
  residual `Nat__rec`;
- added Lean-side `seq` / `seqBool` carriers for Cryptol `Num` sequence types;
- added `ecSignedBVNonzeroM` and checked `ecSDiv_checkedM` /
  `ecSMod_checkedM` helpers. These helpers case-split on `Num` in Lean and
  require nonzero evidence only in the finite positive branch. The zero-width
  and infinite branches are impossible under the contract, so they cannot be
  silently totalized. Audit follow-up: the finite positive branches delegate
  to `bvSDiv_checkedM` / `bvSRem_checkedM` instead of reimplementing signed-BV
  semantics, with `rfl` equations pinning those finite-successor branches.
- routed fully applied `ecSDiv` / `ecSMod` through the same data-driven
  `PartialOpContract` table using raw `Num` plus wrapped value arguments.
  Haskell does not compute a predecessor width or rewrite to `bvSDiv` /
  `bvSRem`.
- promoted `obligations/cryptol_ec_sdiv_zero` and
  `obligations/cryptol_ec_smod_zero` from known gaps to positive
  obligation-shape tests.
- rejected under-applied or over-applied partial-operation identifiers before
  they can fall through to unchecked function-shaped mappings. Higher-order
  partial operations need a separate proof-carrying function-wrapper design.

The partial-operation obligation family is now closed at the emitted-contract
level for fully applied operations. Remaining work in this area is proof
ergonomics for executable replay of nonzero Rational and bitvector examples,
plus a future higher-order wrapper design if under-applied partial operations
become required.

## Correctness Contract

For each partial operation, generated Lean should have this shape:

```lean
let h_nonzero_obligation_ : Prop := <operation-specific precondition>
let h_nonzero_ : h_nonzero_obligation_ := by
  sorry
<checked helper> ... h_nonzero_
```

The exact helper names are a design detail, but the contract requirements are
not:

- the proposition must be visible in the emitted artifact;
- the proposition must mention the actual emitted divisor, denominator, or
  reciprocal argument;
- the result term must consume the evidence;
- if proof automation is generated, it must be ordinary Lean code checked
  against that proposition;
- failure to prove the condition leaves an explicit obligation rather than
  choosing an arbitrary total value.

Candidate propositions:

| SAWCore surface | Contract |
| --- | --- |
| `divNat x y`, `modNat x y`, `divModNat x y` | `Not (y = 0)` |
| `intDiv x y`, `intMod x y` | `Not (y = 0)` |
| `ratio n d` | `Not (d = 0)` |
| `rationalRecip x` | `Not (x = 0)` |
| `bvUDiv w x y`, `bvURem w x y` | `Not (y = zero_vector w)` or a named support-library `bv_nonzero w y` predicate |
| `bvSDiv w x y`, `bvSRem w x y` | `Not (y = zero_vector (w + 1))` or a named support-library `bv_nonzero (w + 1) y` predicate |

For bitvectors, prefer a named support-library predicate if it gives stable
generated text and reusable lemmas. The predicate must be transparent enough
for proofs to connect it to SAW's zero-vector semantics.

## Haskell Architecture

Implement a small data-driven contract interface, not bespoke lowering code for
each primitive.

Suggested shape:

```haskell
data PartialOpContract = PartialOpContract
  { pocName              :: Text
  , pocArity             :: Int
  , pocEvidenceName      :: Lean.Ident
  , pocPrecondition      :: [Lean.Term] -> TermTranslation Lean.Term
  , pocCheckedTarget     :: Lean.Ident
  , pocForbiddenBypasses :: [Text]
  }
```

This table should live near the existing use-site special-treatment
infrastructure, but the lowering itself belongs in `Term.hs` next to the other
proof-obligation emitters. The table should only specify:

- which fully-applied primitive needs a contract;
- which argument is the divisor/denominator/reciprocal;
- how to build the Lean proposition from the already-translated argument terms;
- which checked Lean helper consumes the proof.

It must not inspect Lean syntax to decide whether the divisor is zero, nor
should it erase the obligation when the divisor is syntactically nonzero. If we
want better ergonomics for obvious cases, emit a starter proof script or call a
Lean tactic that proves the visible proposition. The Haskell result is trusted
only because Lean checks the proof term.

Under-applied forms need careful handling. A partially-applied division
function cannot consume evidence until the divisor argument exists. The
conservative first implementation:

- emits obligations only for fully-applied direct calls; and
- rejects under-applied or over-applied partial-operation identifiers before
  they can fall through to unchecked function-shaped mappings.

If higher-order uses become important, add a proof-carrying function wrapper
whose returned function requires evidence at application time. Do not infer or
cache a hidden precondition in Haskell.

## Lean Support Library

Add checked helpers in `CryptolToLean.SAWCorePrimitives`.

The helpers should be thin wrappers around the existing operation definitions,
with an extra proof argument:

```lean
def divNat_checked (x y : Nat) (h : Not (y = 0)) : Nat := divNat x y
def modNat_checked (x y : Nat) (h : Not (y = 0)) : Nat := modNat x y
```

For `divModNat`, preserve SAW's tuple representation:

```lean
def divModNat_checked
  (x y : Nat) (h : Not (y = 0)) :
  PairType Nat (PairType Nat UnitType) :=
  divModNat x y
```

The proof argument may be unused computationally. Its purpose is to make the
precondition part of the emitted term's checked type. That is still meaningful:
a completed proof artifact cannot construct the result without Lean evidence
for the precondition.

For Rational and bitvector operations, add analogous checked helpers. Avoid
changing the existing plain definitions until we have audited all callers; the
first migration should route proof-carrying emissions to checked helper names
while leaving ordinary defined nonzero differential tests stable.

Optional Lean proof automation:

- a small tactic such as `saw_nonzero` may prove closed numeral nonzero goals;
- BV nonzero automation can start with simple `simp` lemmas for literal
  zero/nonzero vectors;
- lack of automation is acceptable as long as the obligation is visible.

Do not use `bv_decide` or native-evaluation proof shortcuts in completed
regression proofs under the current trusted-base policy.

## Testing Plan

For each implemented family:

1. Convert the existing `.known-gap` obligation fixture to a positive
   obligation-shape fixture.
2. Check that `expected.txt` requires:
   - the precondition proposition or named predicate;
   - the local obligation/evidence names;
   - the checked helper call;
   - absence of the unchecked primitive circumvent when called in the partial
     zero-divisor position.
3. Add or update differential tests for defined nonzero cases only if the
   helper routing changes emitted value behavior.
4. Keep zero-divisor cases out of green value-differential coverage unless SAW
   defines an executable total result and the Lean helper is proved to match
   that exact SAW result.
5. Run `make test-saw-core-lean-conformance`.

Promotion order:

1. Nat direct operations, because they exercise the contract path with the
   simplest proposition and tuple result.
2. Int and Rational direct operations.
3. Bitvector direct operations, after deciding the stable nonzero predicate.
4. Cryptol wrappers, once direct operations have a reusable contract interface.

## Soundness Argument

This design is sound because Haskell no longer chooses a partial-operation
result unconditionally. It emits a term that is type-correct only when the Lean
artifact contains evidence for the operation-specific precondition. Haskell may
construct the proposition, but it does not prove it, normalize it away, or
replace the operation with a different semantic value.

The trusted boundary is therefore:

- the Lean support-library helper's type;
- the proof term supplied for the precondition;
- Lean's kernel checking that proof term.

If the precondition is false or cannot be proved, the backend has not
discharged the operation. That is the intended behavior.

## Non-Goals

- Do not solve every generated precondition automatically.
- Do not change SAW semantics by selecting arbitrary total zero-divisor values.
- Do not add a Haskell syntactic nonzero classifier as a trusted gate.
- Do not collapse Cryptol wrapper cases by recognizing wrapper bodies in
  Haskell. The wrapper path should reuse the same contract interface or emit
  its own visible obligation.
- Do not use large examples such as SHA as acceptance criteria for this phase.
