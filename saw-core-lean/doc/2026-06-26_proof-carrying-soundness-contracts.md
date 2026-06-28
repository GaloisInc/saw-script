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

This also changes the role of Haskell classifiers. A classifier such as
`FixShapes` may be useful migration scaffolding, but it should not be the place
where the backend ultimately establishes semantic facts like productivity,
totality, or equivalence between a SAWCore recurrence and a Lean helper. The
preferred end state is:

1. Haskell emits the regular translated SAWCore shape, or a small uniform
   proof-carrying wrapper around it.
2. Haskell emits the exact Lean contract required for the wrapper to be sound.
3. Lean theorems and tactics inspect that contract/body and prove it for known
   patterns.
4. If Lean-side automation fails, the obligation remains visible for a human,
   AI assistant, or later proof script.

Under this discipline, most or all semantic classifier code in Haskell should
move toward Lean-side proof automation. Haskell may still make syntactic
decisions needed for well-formed emission, naming, hygiene, command mode, and
clear diagnostics, but it should not be trusted to recognize the mathematical
cases that make an otherwise-dangerous lowering sound.

There is one legitimate role for classifiers: untrusted proof generation. If
Haskell recognizes a particular generated shape, it may emit both:

1. the regular translated `fix`/adapter term with its ordinary proof
   obligation; and
2. a helpful Lean lemma or proof script specialized to that shape, intended to
   discharge the obligation.

This is sound because the classifier's conclusion is not accepted directly.
The generated lemma/proof must still be checked by Lean's kernel, and the main
lowering must depend on that checked evidence. If the classifier is wrong, the
generated proof fails, leaving the original obligation rather than accepting an
unsound lowering.

The preferred generated shape is therefore "dumb obligation plus partial
Lean-side bridge": Haskell states the literal contract required by the checked
helper, then may include a proof attempt that rewrites the literal emission into
a named ergonomic theorem from the Lean proof library. This keeps Haskell's role
syntactic. The clever part, including any recurrence/productivity recognition or
normalization, is a Lean proof term or tactic result and is trusted only after
kernel checking.

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

### Bounded Vectors: Literal Body Plus Selected-Element View

The bounded-vector `fix` shape has an additional Phase-beta wrinkle. The
literal wrapped translation of

```lean
fun rec => gen n α (fun i => elem rec i)
```

is an eager monadic vector body:

```lean
bodyVec : (Nat -> α) -> Except String (Vec n α)
```

where the generated `genM` sequences every element before returning the vector.
The productive recurrence, however, is about the selected element:

```lean
bodyAt : (Nat -> α) -> Nat -> Except String α
```

Requiring `GenFixBodyProductive α (fun lookup i =>
atWithDefaultM n α err (bodyVec lookup) i)` is too strong: indexing after an
eager `genM` can depend on future elements that the selected source expression
does not need.

The chosen contract is therefore proof-carrying and two-part:

```lean
GenFixVecBodySound n α bodyVec bodyAt :=
  forall lookup, bodyVec lookup = genM n α (bodyAt lookup)

GenFixBodyProductive α bodyAt
```

The first proof ties the selected-element view back to the literal vector body
that Haskell emitted from SAWCore. The second proof is the actual productivity
condition used by `genFixM`. Haskell may build `bodyAt` by selecting the
generator function from the already-recognized `gen` shape, but it does not get
to assume that this selection is semantics-preserving: the generated Lean file
contains the `GenFixVecBodySound` obligation, and completed artifacts must
kernel-check it.

The mechanically emitted `bodyAt` is a starter view, not trusted evidence. If
the selected expression still contains eager subterms such as
`atWithDefaultM ... (genM ... inner) k`, a completed outline may refine
`bodyAt` to a more selective expression. That refinement is sound only because
the same completed outline must also prove `GenFixVecBodySound`. This is the
intended pressure valve: Haskell does not need a growing classifier for every
nested recurrence idiom, while Lean still checks the bridge from the literal
body to the view used for structural computation.

This preserves the project rule for soundness boundaries:

- Haskell performs syntactic construction and hygiene only.
- Lean proves that the mechanically emitted selected view corresponds to the
  literal vector body.
- Lean proves productivity of the selected view.
- No eager `Except.error` path is erased by Haskell.

The wrapped-to-ergonomic bridge now has a generic first layer in the Lean
library. For a bounded vector body, Lean can prove:

```lean
genFixM n α dM bodyM = Except.ok (genFix n α d body)
```

provided it also proves that `dM = Except.ok d` and that every
`bodyM lookup i` with `i < n` succeeds as `Except.ok (body lookup i)`. The
checked `genFixVecChecked` helper has the same bridge. This is the intended
partial proof shape for generated outlines: the emitted term remains the
literal wrapped SAWCore model, while the proof tries to justify a rewrite into
the pure recurrence library. If the success proof or productivity proof is
wrong, Lean rejects the artifact and the original obligation remains.

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

For bounded-vector recurrences, the emitted starter proof may try named Lean
library bridges before falling back to the same visible placeholder:

```lean
let h_productivity_obligation : Prop :=
  GenFixBodyProductive α bodyAt
let h_productivity : h_productivity_obligation := by
  unfold h_productivity_obligation
  first
  | exact SAWCorePreludeProofs.sawSelfRefCompBodyM_productive ...
  | exact SAWCorePreludeProofs.sawSelfRefCompBodySelfFirstM_productive ...
  | sorry
genFixVecChecked n α dM bodyVec bodyAt h_sound h_productivity
```

This is still proof-carrying emission, not a trusted classifier. The Haskell
side only chooses a starter script for the exact obligation it has already
emitted. If the selected theorem does not apply, the obligation remains in the
file. If the theorem does apply, Lean checks the proof against the local
generated terms before the helper can use it. The soundness surface is therefore
the checked helper contract (`GenFixVecBodySound` plus
`GenFixBodyProductive`), not the Haskell pattern that selected the tactic
attempt.

There is now a second, more conservative fallback for `Prelude.fix` shapes that
Haskell does not structurally lower. The emitted contract is:

```lean
saw_fix_unique_exists α body
```

where `saw_fix_unique_exists` states that there is a value `x : α` such that
`body (Pure.pure x) = Pure.pure x`, and that every other successful fixed point
of `body` is equal to `x`. The generated term is obtained with
`Classical.choose` from that existence proof. This does not automate recursion,
but it is sound as a proof-carrying interface: if Lean proves uniqueness, then
SAW's `fix_unfold` principle forces the chosen Lean value to coincide with the
SAW fixed point. If uniqueness is not true or cannot be proved, the obligation
remains open.

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
