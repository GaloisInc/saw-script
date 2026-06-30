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

The immediate trigger is `Prelude.fix` lowering. Earlier prototypes used
shape-specific Lean helpers for stream and vector recurrences, with Haskell
classifiers selecting helper calls and Lean side conditions justifying the
selection. That design has been retired. It made Haskell responsible for too
much semantic recognition, and it left obsolete backup paths in the support
library.

The live rule is simpler: every soundness-sensitive lowering emits a literal
SAWCore-shaped term plus the Lean proposition needed to justify using it. For
`Prelude.fix`, the generic contract is a unique-fixed-point obligation over the
translated body. For stream construction, the contract is pointwise totality of
the translated index function. For raw-position partiality, the contract is an
explicit proof obligation rather than a fabricated default.

Haskell may still generate a starter proof script when it recognizes a common
shape, but the recognized fact is not trusted. The generated proof must check in
Lean against the exact emitted obligation. If it does not check, the obligation
remains visible for a human, AI assistant, or later proof script.

This gives one uniform soundness pattern:

1. Haskell emits syntax for the literal translated program and the required
   contract proposition.
2. Haskell may emit a proof attempt, but the main term depends only on the
   resulting Lean-checked evidence.
3. Lean theorems and tactics perform recurrence, productivity, totality, or
   normalization reasoning.
4. Failed automation is acceptable; accepting an unchecked semantic claim is
   not.

Under this discipline, semantic classifier code in Haskell is a target for
removal unless it only produces optional Lean proof artifacts. Haskell remains
responsible for syntactic construction, naming, hygiene, command mode, and clear
diagnostics. The mathematical content belongs on the Lean side.

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

Accepted automation must also respect the backend's trusted-base policy. Tactics
such as `simp`, `grind`, `omega`/`bv_omega`, `cbv`, and hand-written bridge
lemmas are appropriate when the resulting theorem's axiom report contains only
the allowed standard axioms and explicitly cataloged support-library
assumptions. Plain `bv_decide` and `bv_check` are not accepted proof-discharge
mechanisms under the current policy: in the pinned Lean frontend, substantial
uses validate the LRAT certificate through native evaluation and add a
proof-local native axiom for that result. The certificate may be useful research
data, but the completed backend proof must not rely on Lean code generation
unless the project deliberately widens its trusted computing base.

Consequently, bitvector-heavy crypto obligations may remain as manual proof
work or expected proof gaps. This is a proof-automation limitation, not an
emission soundness problem, as long as the generated Lean states the exact
obligation and the harness does not count an unchecked or native-axiom proof as
green.

The generated Lean must not use `sorry` in completed artifacts. An emitted
work-in-progress file may contain obvious placeholders only if the test harness
or command mode treats the file as incomplete and does not count it as a
discharged proof.

The current `fix` migration emits local obligation bindings for the generic
contract, for example:

```lean
let h_fix_obligation : Prop :=
  saw_fix_unique_exists α body
let h_fix : h_fix_obligation := by
  sorry
saw_fix_choose α body h_fix
```

This is sound as an emit-stage artifact only because unresolved placeholders are
not accepted by the check-stage harness. The contract is separate from the proof
placeholder, but it may still be local when it depends on surrounding generated
variables. A later proof ergonomics stage can decide whether to lift local
obligations into top-level declarations with explicit dependency binders, or
keep the edit-in-place workflow for generated code with local context.

The emitted contract for `Prelude.fix` is:

```lean
saw_fix_unique_exists α body
```

where `saw_fix_unique_exists` states that there is a value `x : α` such that
`body (Pure.pure x) = Pure.pure x`, and that every wrapped fixed point of
`body` is exactly `Pure.pure x`. The universal uniqueness check ranges over
`Except String α`, not just over successful values, so a successful fixed point
cannot coexist with an `Except.error` fixed point. The generated term is
obtained with `Classical.choose` from that existence proof. This does not
automate recursion, but it is sound as a proof-carrying interface: if Lean
proves uniqueness, then SAW's `fix_unfold` principle forces the chosen Lean
value to coincide with the SAW fixed point. If uniqueness is not true or cannot
be proved, the obligation remains open.

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

Existing Haskell classifiers for `fix`, stream construction, rawification, and
similar surfaces should therefore be treated as temporary bridges. The
replacement is not a larger collection of special cases; it is a small set of
uniform contracts plus Lean-side proof procedures. A tactic may pattern match
aggressively on generated terms, because its output is checked by Lean's kernel.
A Haskell recognizer doing the same work changes the trusted base and should be
phased out unless it is only selecting which explicit obligation to emit.

Equivalently: Haskell may classify to improve proof ergonomics, not to remove a
proof obligation. A classifier can emit a specialized lemma, choose a tactic
script, or name a known theorem that should solve the obligation. It cannot make
the lowering sound by fiat.

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
- using a partial operation such as division, modulus, rational construction,
  rational reciprocal, or bitvector division/remainder;
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

The current next application of this rule is partial operations. The dedicated
implementation plan is
`2026-06-30_partial-operation-obligations-plan.md`: direct zero-divisor and
zero-denominator surfaces should be converted from pinned known gaps into
proof-carrying emissions with visible nonzero preconditions and checked helper
calls.

## Raw `Prelude.error` and Partiality

The same rule applies to `Prelude.error` that survives in raw positions. A value
result can preserve Cryptol partiality as `Except String α`, but a raw index,
type, proof, or function result cannot be represented by `Except.error` without
changing the surrounding Lean type. Emitting a dummy raw value would be an
unsound reinterpretation of SAW's error semantics.

The correct shape is therefore contract-dependent:

- if the error branch is unreachable, emit a Lean obligation proving that
  unreachability and use a helper whose type requires that proof;
- if the term is a vector/index operation, emit the concrete bounds/proof
  condition the helper needs;
- if the translator cannot state a replacement contract, reject at SAW
  translation time.

Full SHA512 is a useful stress test for this surface, but it is not a Rocq
parity blocker. `write_lean_cryptol_module` for the full SHA512 functor reaches
large proof-carrying `fix` and stream-totality obligations after raw-position
`Prelude.error` has been converted into explicit obligations. That is evidence
that the proof-carrying approach is exposing the right contracts, not evidence
that the parity milestone must solve full-module SHA512 emission now.

A focused polynomial-literal regression now emits:

```lean
let h_raw_error_obligation_ : Prop := False
let h_raw_error_ : h_raw_error_obligation_ := by
  sorry
False.elim h_raw_error_
```

This is deliberately conservative. It states only the contract the backend can
always state soundly: the raw error branch is unreachable. Later ergonomics can
replace this generic `False` with more specific bounds or branch-condition
propositions where the translator can construct them without semantic
guesswork. Raw partiality and productivity remain separate proof-carrying
contracts, not a broad SHA-specific special case.

The same rule applies to `MkStream`. A translated index function may have type
`Nat -> Except String α`, but SAW's stream constructor requires a raw
`Nat -> α`. The backend therefore either syntactically rawifies the function
through `rawifyExceptToRaw`, or emits:

```lean
saw_mkStream_total_exists α f
```

which states that there is a raw function `g : Nat -> α` whose values exactly
match the successful results of `f`. The stream is built from `Classical.choose`
on that proof. This replaces the old rejection/defaulting surface with a
visible totality contract.

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
7. Migrate shape-specific Haskell classifiers toward generic proof-carrying
   emission. The Lean library should own the recognizers/proofs for common
   stream, vector, SHA-style, and helper-specific recurrence patterns.
8. Where Haskell classifiers remain useful, demote them to proof emitters:
   they may generate specialized Lean lemmas or tactic scripts, but the regular
   obligation stays in the emitted file and final trust comes only from the
   checked proof.

This gives a clean migration path: coverage grows as the automatic proof
producer improves, but unsupported cases are not arbitrarily forbidden. They
become explicit obligations.
