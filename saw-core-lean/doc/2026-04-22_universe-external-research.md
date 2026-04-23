# External research: Coq→Lean universe translation patterns

*Agent summary — 2026-04-22*

Summary of external evidence, compiled from mathport source, Lean
4.30.0-rc2 installed toolchain, Lean docs, and GitHub issues.
Complements `2026-04-22_universe-problem.md`'s Q1–Q5 with answers
from outside our codebase.

## Key findings

### 1. Lean 4 is non-cumulative by kernel design

From `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Lean/Meta/ExprDefEq.lean:152`:

> "eta-reduction is not a good alternative even in a system without
> universe cumulativity like Lean."

Non-cumulativity is baked into the kernel, not a policy setting. **No
`set_option` or pragma restores it.** The Lean 4 Reference manual
§4.3 (https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/)
is the authoritative statement.

### 2. No Coq↔Lean4 structural translator exists

Full search yielded only:

- `atlas-computing-org/CoqLeanTranslation` — ChatGPT-assisted on a
  ~400-LOC ISA model. Not a tool.
- `LLM4Rocq/babel-formal` — LLM-based experiment.
- `zengyuzhi/HOL-Light-to-Lean4` — LLM-based informalise/reformalise.

**There is no "mathport for Coq".** SAWCore→Lean4 is new ground.

### 3. Mathport is the closest precedent but doesn't cross cumulativity

Both Lean 3 and Lean 4 are non-cumulative, so mathport sidesteps the
gap entirely. What mathport *does* give us is the correct *emission*
pattern: every `mkConst name [explicit-level-list]` carries the
source's universe-parameter list explicitly. Translator does no
universe unification of its own; the kernel checks.

**Implication for saw-core-lean:** at call sites of
universe-polymorphic defs, the translator must emit
`@Foo.{u₀, u₁, …}` with *explicit* levels, not bare `@Foo` (which
leaves Lean inferring level metavariables — see finding 5).

Reference: `leanprover-community/mathport/Mathport/Binary/TranslateExpr.lean`,
`Apply.lean`, `Heterogenize.lean`.

### 4. The three lifting operators

All three in `Init/Prelude.lean` of any Lean 4 distribution.

| Name | Location | Signature | Use |
|---|---|---|---|
| `PLift α` | ~L872 | `Sort u → Type u` | Lift +1 level, works from Prop |
| `ULift.{r,s} α` | ~L921 | `Type s → Type (max s r)` | Lift within Type; can't escape Prop |
| `PULift.{r,s} α` | ~L947 | `Sort s → Sort (max s r 1)` | Most general; subsumes PLift |

All are plain single-field structures with `up`/`down` as the
isomorphism, proved by `rfl`. **These are escape valves for when
universe polymorphism alone can't bridge a fixed gap.**

### 5. Lean issue #2297 is likely the specific unblocker

https://github.com/leanprover/lean4/issues/2297 documents:

> "Currently universe unification will not solve `max u v =?= max u ?v`
> or `max u v =?= max u ?v`. (Lean 3 would do this.) This is causing
> some problems in mathlib4."

Quoted workaround:

```lean
abbrev TypeMax := Type max u v
instance (priority := high) HLOS_max' : HLOS.{a} (TypeMax.{a, b}) := sorry
```

An `abbrev` that freezes the `max` so the elaborator doesn't have to
solve it.

**The failure mode in my P4 attempt almost certainly involves this.**
When my emitted `@Eq__rec` invocation expected Lean to solve universe
constraints across cross-def call sites, the `max` arithmetic
triggered by function type composition is exactly what this issue is
about. The `abbrev` trick unblocks.

### 6. Mathlib's escape-hatch patterns

When explicit-level emission isn't enough, mathlib uses:

- **`Small.{w} α`** (`Mathlib/Logic/Small/Defs.lean`): asserts `α` is
  equivalent to some type in universe `w`.
- **`UnivLE.{u,v}`** (`Mathlib/Logic/UnivLE.lean`): asserts universe
  inequality `u ≤ v` as a typeclass.
- **`Shrink α`**: noncomputable `def` giving a canonical model in
  target universe.

Comment directly from `UnivLE.lean`:

> "in Lean's type theory, while `max u v` is at least as big as `u`
> and `v`, it could be bigger than both!"

This is mathlib *encoding a universe inequality as a typeclass* when
the elaborator can't solve it directly. Last-resort pattern; we
should only reach for this if explicit-level emission (pattern 3)
fails on some specific SAWCore construct.

### 7. Lean 4.29+ `@[univ_out_params]`

From v4.29.0 release notes and PR #12423 — any universe level not
appearing in input parameters is treated as an output parameter.

Relevant to our scaffolding: `class Inhabited.{u} (α : Sort u) :
Type u` has `u` in both input and output, so it's not affected. But
any future class we add whose universe levels appear only in the
result needs this annotation for correct instance-cache behavior. On
toolchain 4.29.1 (our pin) we're fine.

## Three community-validated translation patterns

Ranked by how much our translator should lean on each:

### Pattern A: Explicit levels at every call site (mathport default)

Always emit `@Foo.{u₀, u₁}` with named levels drawn from the caller's
declared universe list. Never emit bare `@Foo` for a
universe-polymorphic target.

**This is the correction to my P4 first attempt.** I emitted bare
`@Foo` at call sites and hoped Lean would infer; the inference gets
stuck on `max` constraints.

### Pattern B: Explicit `PLift`/`ULift`/`PULift` wrapping

When a specific call site must cross a fixed universe (e.g., we
declare `Eq.{u} (t : Sort u+1) …` and a caller passes `Sort 0`), an
explicit `PULift.{…}` wrap preserves semantics.

Cost: adds a structural lifting wrapper that changes the Lean
surface form. Users' proofs about our output may need to unfold the
lift. Acceptable, but emit only when Pattern A isn't enough.

### Pattern C: `UnivLE` / `Small` / `TypeMax` escape hatches

For cases where Lean 4's unification is *provably* stuck (as in issue
#2297), introduce the mathlib-style abbreviation to unblock.

Only reach here as a last resort.

## Actionable implications

1. **Reject the premise of my P4 attempt.** Emitting bare `@Foo`
   and hoping for inference is the wrong pattern. Fix: thread
   explicit levels through every call site (Pattern A).

2. **`scTypeOf` at emission time.** SAWCore's type-checker tells us
   the exact sort of every subterm. Emit the *actual* level —
   `Sort (u+1)` with named `u` where SAWCore has `sort 1` under a
   polymorphic binder, or `Type 0` where it's concrete — rather than
   hoping Lean guesses right. This is pattern-A done faithfully.

3. **The `abbrev TypeMax` pattern may be needed** for constructs
   where we genuinely emit `max u v` in types. Worth testing
   whether the Prelude's `Eq__rec` or `coerce__def` would benefit.

4. **`PULift` wrapping** is the legitimate way to handle places
   where SAWCore's cumulativity genuinely needs to be simulated.
   SAWCore's `(t : sort 1) → t → t → Prop` called with `t := Bool`
   (a `sort 0` value) can be translated soundly via
   `(t : Sort (u+1)) → PULift t → PULift t → Prop` or similar, at
   the cost of ergonomics.

## What we still don't know

- Whether the Lean Zulip has a long-running design discussion about
  this (sandbox couldn't reach `leanprover.zulipchat.com`). Worth a
  manual lookup.
- Whether any academic paper formally describes the
  cumulativity-gap translation strategy. The agent couldn't confirm
  or rule this out without arXiv access.

## Local pointers

- Our scaffolding `Inhabited.{u}` already uses the right idiom:
  `saw-core-lean/lean/CryptolToLean/SAWCoreScaffolding.lean:26`.
- First P4 attempt parked at branch `saw-core-lean-p4-wip` commit
  `14d6c96`. The AST infrastructure there (universe lists on
  Definition/Axiom/Inductive) is the correct substrate for
  Pattern A; what's missing is threading the levels through
  *call sites*, not just declarations.
