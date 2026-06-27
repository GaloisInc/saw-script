# Proof-Carrying Soundness Contracts

**Date**: 2026-06-26

This note refines the Phase-beta expected-shape plan with a general rule for
soundness-sensitive backend lowerings:

> If a lowering is sound only under a precondition, encode that precondition in
> Lean and make the generated file provide evidence for it.

The translator may include a starter proof script for common cases, but proof
search is not the translator's job. The required interface is to emit the
contract as a Lean proof obligation. It must not silently assume the
precondition in Haskell, hide it in a comment, or add an axiom that weakens the
Lean trusted base.

## Motivation

The immediate trigger is `Prelude.fix` lowering.

The current stream and vector fix helpers use structurally recursive Lean
definitions with a dummy default value:

```lean
mkStreamFix      : (d : α) -> ((Nat -> α) -> Nat -> α) -> Stream α
mkStreamFixPair  : ...
genFixM          : ...
```

These helpers are sound only when recursive lookup is productive: the value at
index `i` may depend on earlier indices, but not on index `i` or later. If this
condition is false, the helper's default can become observable.

A Haskell recognizer that accepts only patterns such as `subNat i 1` can block
some bad cases, but it is not the right abstraction. It arbitrarily forbids
valid cases it cannot recognize and keeps the semantic contract outside Lean.

The more principled design is proof-carrying lowering.

## Contract Shape

Each soundness-sensitive adapter or lowering should have:

1. a Lean-level contract proposition;
2. a Lean helper whose type requires evidence of that proposition, or whose
   result includes an explicit obligation theorem;
3. an emitted obligation for the exact evidence required at the use site;
4. optional Lean-side automation that can try to fill the obligation, without
   changing the trusted contract.

The contract must be meaningful in Lean. It cannot be:

- `axiom productive : ...`
- `by sorry`
- an unsafe tactic that can prove arbitrary propositions
- an erased Haskell-side boolean whose result is not visible in the generated
  Lean

## Fix Productivity

There are two plausible Lean contracts for fix productivity.

### Option A: Type-Enforced Previous-Index Lookup

Represent recursive lookup with an index proof:

```lean
body : (i : Nat) -> ((j : Nat) -> j < i -> α) -> α
```

The helper only permits previous-index access. A recursive read at `j` must
come with a proof `j < i`.

For example, a productive stream body:

```lean
fun i lookup => lookup (i - 1) h
```

where `h : i - 1 < i` is provable under the relevant branch condition.

Strengths:

- The helper type makes current/future lookup impossible.
- The default value disappears from the public contract.
- Proof obligations are local: each recursive access needs an inequality.

Weaknesses:

- Existing generated bodies use `Nat -> α`, so this requires a larger lowering
  rewrite.
- Base cases need explicit handling, because `i - 1 < i` is false at `i = 0`.
  Cryptol stream definitions such as `[base] # rest` naturally provide that
  branch, but the translator must preserve it in a proof-friendly shape.

### Option B: Noninterference From Future Values

Keep the existing body shape but require a semantic proof that future/default
entries cannot affect the result at the current index:

```lean
ProductiveBody (body : (Nat -> α) -> Nat -> α) : Prop :=
  forall i lookup1 lookup2,
    (forall j, j < i -> lookup1 j = lookup2 j) ->
    body lookup1 i = body lookup2 i
```

Then `mkStreamFix` may use any default internally, because the proof says the
result is independent of values at `j >= i`.

Strengths:

- Smaller change to existing helper signatures.
- Good fit for current rawified generated bodies.
- Automatically discharged cases can be proved by simplification plus
  arithmetic obligations.

Weaknesses:

- The proof can be harder to synthesize for complex bodies.
- The helper still computes with a default internally, so the theorem tying the
  helper to SAW semantics must use the noninterference proof carefully.

## Obligation Emission Modes

The backend should support two workflow stages:

- **Emit stage**: SAW writes the translated Lean plus every required contract
  obligation. The file may contain obvious placeholders or starter tactic
  scripts. This stage does not discharge the SAW proof obligation.
- **Check stage**: SAW invokes the pinned Lean toolchain on the exact emitted
  obligations plus the user's completed proof artifact. SAW may accept the
  original goal only when Lean checks all required evidence and the artifact
  contains no forbidden escapes.

Automation lives inside the check stage as ordinary Lean proof search. It is
useful for ergonomics, but it is not part of the trusted Haskell backend. A
failed tactic is not a backend failure if the obligation remains available for a
human, AI assistant, or later prover script to discharge.

The generated Lean must not use `sorry` in completed artifacts. An emitted
work-in-progress file may contain obvious placeholders only if the test harness
or command mode treats the file as incomplete and does not count it as a
discharged proof.

The current `fix` migration uses local obligation bindings at checked-helper
call sites, for example:

```lean
let h_productivity_obligation : Prop :=
  StreamBodyProductive α body
let h_productivity : h_productivity_obligation := by
  sorry
mkStreamFixChecked α d body h_productivity
```

This is sound as an emit-stage artifact only because unresolved placeholders are
not accepted by the check-stage harness. This is a deliberate checkpoint: the
contract is separate from the proof placeholder, but it is still local when it
depends on surrounding generated variables. A later proof ergonomics stage can
decide whether to lift these local obligations into top-level declarations with
explicit dependency binders, or keep the edit-in-place workflow for this class of
generated code.

## Automation Boundary

The Haskell backend should be boring at every soundness interface:

- construct the Lean syntax for the program and the exact contract proposition;
- maintain syntactic hygiene, such as avoiding accidental variable capture;
- decide whether a command is in emit mode or check mode;
- reject completed artifacts that still contain `sorry`, unchecked axioms,
  import shadowing, or proofs of unrelated propositions.

It should not perform semantic reasoning about generated Lean terms. In
particular, it should not normalize generated Lean ASTs to make a contract
appear provable, classify a recursive body as productive by semantic pattern
matching, or silently erase a precondition because a heuristic recognizes a
common case.

When reasoning is needed, it belongs in Lean:

- as a named theorem;
- as a proof term supplied to a checked helper;
- as a tactic script whose result is kernel checked;
- or as a visible proof obligation left for the user/prover.

This keeps the trusted Haskell surface small. Bugs in optional automation can
make a proof fail or become inconvenient, but they cannot justify an invalid
lowering unless Lean accepts invalid evidence, which is outside the backend's
trusted code.

## General Adapter Rule

This approach applies beyond `fix`.

Any backend feature that would otherwise rely on a hidden invariant should be
converted into a contract:

- rawifying a wrapped function;
- proving a vector index is in bounds;
- proving a stream/corecursive lookup is productive;
- using a hand-written helper whose semantics assumes normalized Cryptol input;
- transporting through equality or unsafe assertions supplied by SAW.

For each case:

1. name the precondition;
2. encode it in Lean;
3. make generated code depend on evidence;
4. optionally include a Lean-side proof attempt;
5. otherwise leave the obligation explicit or reject when the command requires a
   completed proof.

## Immediate Plan

For the current `fix` productivity surface:

1. Keep the nonproductive boundary tests. They define the cases that must not be
   silently lowered.
2. Add a Lean contract for stream-body productivity. Start with the
   noninterference contract because it fits the existing helper shape.
3. Add proof-taking variants of the stream helpers.
4. Teach the translator to emit proof obligations for the required evidence.
   The common `saw_productivity` tactic may remain as a convenience script, but
   the design must not require Haskell to solve productivity automatically.
5. Move pair-stream and bounded-vector fix lowerings onto the same pattern.
6. Remove or quarantine helper forms whose soundness still relies on hidden
   residual trust.

This gives a clean migration path: coverage grows as the automatic proof
producer improves, but unsupported cases are not arbitrarily forbidden. They
become explicit obligations.
