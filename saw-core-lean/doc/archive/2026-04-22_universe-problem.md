# The universe translation problem

*Draft — 2026-04-22*

## Problem statement

SAWCore has a cumulative universe hierarchy:
- `Prop` (impredicative)
- `Type 0, Type 1, Type 2, …` (predicative)
- With `Prop <= Type 0 <= Type 1 <= …` as subtyping (see
  `saw-core/src/SAWCore/Term/Functor.hs`'s `Ord Sort` instance).

Lean 4 has the same hierarchy — `Prop`, `Type 0`, `Type 1`, … — but
is **not cumulative**. `Nat : Type 0` does not imply `Nat : Type 1`
in Lean; instead, `Sort u` with a free universe variable must be
used for polymorphism, and the elaborator picks `u` at each call
site.

The translator's job: produce Lean output that preserves SAWCore's
semantics *for arbitrary SAWCore input*, including input that
exercises the cumulativity. This is the core design problem for P4.

## What we know doesn't work

### Option A: collapse every `sort k` to Lean `Type` (pre-P4 behavior)

Unsound when SAWCore genuinely distinguishes sorts. `Prelude.Eq`'s
type is `(t : sort 1) -> t -> t -> Prop` — calling `Eq Type Bool True`
requires the first argument at `sort 1`, not `sort 0`. Collapsing
loses the distinction. In practice, the generated `SAWCorePrelude.lean`
showed ~60 elaboration errors with this approach, confirming
Lean's elaborator can't guess the right level.

### Option B: emit fresh universe variable per `sort k` per def (my first attempt)

Each `def Foo.{u0 u1}` declared its own universe variables. At
call sites in other defs' bodies, Lean was supposed to unify the
caller's universes with the callee's via metavariables.

**What went wrong:** Lean's universe inference *should* handle this,
but in practice it often couldn't because the enclosing term has
enough ambiguity that multiple universe solutions exist. The
errors shifted but count stayed at ~100.

Open question: is my understanding of Lean's universe unification
wrong, or did I emit output that legitimately confuses it? I didn't
dig into individual failures.

### Option C: Rocq-style unadorned `Type`

Coq is cumulative; Lean isn't. We cannot simply copy Rocq's approach.
Fails the same way as Option A.

## What we don't yet know

1. **When my option-B output fails, is it because Lean genuinely
   can't infer the universe, or because our emitted term has
   structural issues I'm conflating with universe issues?** I
   haven't carefully read the errors one at a time with Lean's
   `set_option pp.universes true`.

2. **How does Rocq handle SAWCore's `Eq` at `sort 1`?** If Rocq's
   output elaborates even though Coq's universe system is different,
   there's a pattern we can learn from.

3. **Are there Lean mechanisms (`@[reducible]`, `Sort u`,
   universe-polymorphic instances, type-class resolution, Lean's
   native `Eq.rec`) that SAWCore's emitted references can route
   through to avoid the problem?**

4. **Is there a pre-emission pass on the SAWCore `Term` that would
   compute the required universe relationships and make the Lean
   emission straightforwardly correct?** (E.g., SAWCore's
   `scTypeOf` at each `Sort` occurrence tells us which level it's
   actually used at.)

## Draft questions for investigation

Before designing a solution, we should answer:

**Q1.** For each of the ~100 elaboration errors in the
P4-WIP-generated `SAWCorePrelude.lean`, what is the exact root
cause? A shared root cause or ~6 distinct ones?

**Q2.** Does Lean have any mechanism (imports, pragmas, option
settings) that restores limited cumulativity, e.g. between
`Type 0` and `Type 1`? (There's `Sort.liftInfer` or similar in
mathlib; worth checking.)

**Q3.** Does emitting `@Foo.{_, _, _}` (let Lean infer each
universe) work when `Foo` is universe-polymorphic? My attempt
emitted `@Foo` without `.{…}` — which makes Lean think Foo is
non-universe-polymorphic.

**Q4.** How does SAW's `scTypeOf` on a `Sort k` subterm behave?
Can we use it to emit the correct concrete universe level
(e.g. `Sort 1`) at each use site rather than a polymorphic `u`?

**Q5.** What does the Lean 4 community do when translating from a
cumulative type theory (Coq, Agda+cumulativity) to Lean? There's
likely prior art.

## Proposed plan

1. **Spawn a research agent** to investigate Q1–Q5 systematically.
   Read Lean source, mathlib code, Lean community discussions,
   papers on universe translation. Come back with a concrete
   recommendation.
2. **Based on the recommendation, design option B' or option D** —
   a concrete approach that handles arbitrary SAWCore input
   soundly.
3. **Implement, with tests** that cover the Prelude's universe-
   polymorphic slice (Eq family, coerce family, inductive
   recursors).
4. **No scope-dodge** — the translator must handle arbitrary
   SAWCore, not just what the current demo touches.

## Non-negotiables

- **Soundness.** Every SAWCore term must translate to Lean with
  matching SAW semantics, or the translator refuses (loud
  failure).
- **No scope restriction to the demo.** The rev.cry example is a
  driving instance for validation, not a boundary on the
  translator's input language.
- **No `skip` entries without handwritten Lean realisation paired
  in the support library.**

## Current state

- Main `saw-core-lean` branch: clean, at commit `e4bd622` with
  P1+P2+P3 landed (Nat unmap, Bool order, UnitType revert).
- Branch `saw-core-lean-p4-wip` (commit `14d6c96`): first P4
  attempt parked with WIP universe plumbing (AST changes,
  per-def universe lists, `translateSort` recording). Reusable
  infrastructure but incomplete approach.
