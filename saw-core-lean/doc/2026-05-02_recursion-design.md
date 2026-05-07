# Recursion design — Phase 5

*2026-05-02. Synthesis of three surveys (`.tmp-phase5/s1-shapes.md` and
the S2/S3 reports captured in conversation), framing Phase 5's
implementation. Supersedes the placeholder in
`2026-05-02_post-audit-plan.md` §"Phase 5 — Recursion design".*

## Goal and scope

Translate the SAWCore `Prelude.fix` shapes that Cryptol actually
produces, soundly, without introducing logical escape hatches
(`partial def`, `partial_fixpoint`, kernel axioms beyond what we
already inherit). Where a shape can't be soundly translated within
that bar, continue to reject loudly via the L-5 gate.

Out of scope: handling user-written recursion that genuinely lacks a
total Lean target (factorial-on-bitvectors, SHA-512's polymorphic
Merkle-Damgård chain). These stay rejected; they're at parity with
Rocq, which rejects all `fix` outright.

## Findings recap

**S1 (empirical shapes).** Four shapes survive `scNormalizeForLean`:

| # | Shape | Example | Type at fix | Outer body |
|---|-------|---------|-------------|------------|
| 1 | Bounded Vec fold | popcount on `[32]` | `Vec n A` (concrete `n`) | `\rec -> gen n _ (\i -> e[rec, i])` |
| 2 | Stream corecursion | `streamFibs` | `Stream A` (or `PairType` of streams) | `\rec -> MkStream A (\i -> e[rec, i])` |
| 3 | Bitvector-gated partial | factorial on `[8]` | `Vec w Bool -> Vec w Bool` | `\rec -> \n -> ite (bvEq w n 0) base (op (rec (bvSub w n 1)))` |
| 4 | Polymorphic `Num#rec1` dispatch | SHA-512 functor | `Cryptol::Num#rec1 _ (\n -> Vec n A) (Stream A) L` (`L` free) | `\rec -> Num#rec1 _ _ _ L _seed _step` |

The discriminator is the head of the type argument plus the body's
outer producer; all four are syntactically distinguishable.

**S2 (Rocq baseline).** Rocq rejects `Prelude.fix` outright (BadTerm
at `saw-core-rocq/src/SAWCoreRocq/Term.hs:653`, mirroring our L-5).
SAWCore Prelude defs that internally use `fix` (e.g. `streamScanl`)
are hand-rewritten on the Rocq side in `SAWCorePreludeExtra.v` using
structural `Fixpoint`/local `fix`, with equivalence lemmas. Going
beyond Rocq for shapes 1 and 2 (which Rocq punts on) is the option
this design chooses; it's strictly additive.

**S3 (Lean mechanisms).** `partial def` is *logically vacuous* —
becomes `opaque f`, no equation provable. `partial_fixpoint`
(Lean 4.21+) gives a sound CCPO-based fix with `eq_def` lemma but
adds `propext`/`Classical.choice`/`Quot.sound` to trusted axioms.
**Manual structural recursion / `Nat.rec`** is the gold standard:
fully kernel-reducing, no axioms. Lean's `WellFounded.fix` with
constructive WF proofs preserves `rfl` reduction; `termination_by` is
`@[irreducible]` so `rfl` doesn't, but `simp [f]` does.

The implication: shapes 1 and 2 can be lowered using *only* manual
structural constructions — no axiom additions, no `partial`
machinery. Shapes 3 and 4 would require either `partial_fixpoint`
(adds axioms, weaker reasoning) or upstream specialisation. We
defer them.

## Strategy: shape-recognize-and-lower

The translator gets a new pass between `scNormalizeForLean` and the
existing Lean emit:

```
scNormalizeForLean
  -> classifyFix : Term -> FixShape    -- new
  -> lowerFix   : FixShape -> Term     -- new; rewrites the term tree
  -> existing Lean emit
```

`classifyFix` syntactically matches one of {BoundedVecFold,
StreamCorec, Other}. `lowerFix` rewrites BoundedVecFold and
StreamCorec into total SAWCore terms that reference new support-
library entries (`genFix` and `mkStreamFix`, see below); Other falls
through to the existing L-5 reject path with the existing diagnostic.

Shapes 3 and 4 fall under Other:

- **Shape 3** (bv-gated): rejected with a tightened diagnostic
  pointing the user at the bvSub-decreasing argument as the
  obstruction; mention that providing an explicit Nat bound would
  let translation succeed.
- **Shape 4** (Num#rec1): already caught upstream by
  `polymorphismResidual`. No new work needed; verify the diagnostic
  fires at `writeLeanCryptolModule` time before Phase 5 ships.

## Soundness argument

The soundness chain has three links. Each is either
**inherited from SAWCore/Cryptol** (i.e., a residual trust we
document) or **translator-internal** (i.e., we pin it with a test).

### Link 1 — Cryptol produces only *productive* fix shapes (residual trust)

Cryptol's type checker rejects non-productive recursive definitions
at source level. A Cryptol stream `xs = [seed] # f xs` is accepted
only if `f xs[i]` depends on `xs[j]` for `j < i`. This guarantees
that every `Prelude.fix` SAW receives from Cryptol has a
well-defined LFP equal to the bottom-up index-by-index computation.

**This is a trust assumption inherited from Cryptol — we don't
introduce it.** It belongs in the residual-trust catalog
(`doc/2026-05-XX_residual-trust.md`) alongside SAWCore's `unsafeAssert`
and the SAWCore Prelude axioms we transport. Concretely:

> *Cryptol's frontend enforces productivity for all recursive
> definitions. Our `fix` lowering for shapes 1 and 2 trusts this:
> if Cryptol's type checker ever admitted a non-productive recursion
> and let it survive `scNormalize`, our Lean lowering would diverge
> from SAW's denotational `fix` semantics. We have no test that
> fires if Cryptol's productivity check stops being true.*

This is the same character of trust as "Lean's `Quot.sound` is
consistent" — a system we depend on, documented in the residual-trust
doc, not tested locally.

### Link 2 — `scNormalizeForLean` doesn't introduce non-productive fix (residual trust)

Normalization steps (β, ι, η, defined-name unfolding, recursor
reduction) preserve the productivity of fix bodies — they don't
re-bind recursive variables, only reduce around them. The L-6 gate
catches non-convergent normalization. **No non-productive fix
emerges from a productive one through `scNormalizeForLean`.**

This is asserted by the SAWCore meta-theory and not separately
tested. Documented alongside Link 1.

### Link 3 — Our recognizer + lowering preserves SAWCore semantics (translator-internal, **pinned by tests**)

This is the link we control. The claim:

> *For every term `fix T body` matched by `classifyFix` as
> `BoundedVecFold` or `StreamCorec`, the lowered Lean term is
> definitionally equal to the SAWCore-denotational value of the
> original term.*

The argument:

**For BoundedVecFold (`fix (Vec n A) body` where `body = \rec -> gen n _ (\i -> e[rec, i])`):**

SAWCore's `fix` denotes the LFP. Productive bodies (Link 1) have a
unique LFP equal to the index-by-index bottom-up build. Our Lean
target is `genFix n A d (\lookup i => e'[lookup, i])` where:

```lean
def genFix : (n : Nat) → (A : Type) → A → ((Nat → A) → Nat → A) → Vec n A
  | 0,     _, _, _ => Vector.nil
  | n + 1, A, d, f =>
      let prev := genFix n A d f
      Vector.snoc prev (f (atWithDefault n A d prev) n)
```

(Structural recursion on `n`. No axioms.)

`e'` is `e` with every `atWithDefault n α d' rec j` rewritten to
`lookup j`, propagating through any other `rec` use sites. The
rewrite is purely syntactic and doesn't depend on the
well-foundedness of `j` — by Link 1, every `j` is `< i` at runtime,
so `lookup j` returns the right value; if (per Link 1's failure mode)
any `j ≥ i` survived, our `genFix` would return `d` and SAWCore's
fix would denote `⊥`, which is the documented divergence we trust
Link 1 to prevent.

**For StreamCorec (`fix (Stream A) body` where `body = \rec -> MkStream A (\i -> e[rec, i])`):**

Lean's `Stream A := MkStream : (Nat → A) → Stream A` is *already*
the corecursive encoding (the index function is stored
verbatim — see `SAWCorePrimitives.lean:67`). The fix is unfolded
once and then resolved structurally:

```lean
def mkStreamFix : (A : Type) → A → ((Nat → A) → Nat → A) → Stream A :=
  fun A d f => Stream.MkStream (fun i => f (mkStreamLookup A d f) i)

-- where mkStreamLookup is structurally recursive over i, walking
-- the Stream by applying f i' for each i' < i, memoization is
-- implicit in the index-function representation.
```

The `Stream#rec _ _ (\s -> s (subNat i 1))` access pattern in
SAWCore (which retrieves the (i-1)-th element of the stream)
becomes a recursive call to `f` at `i - 1`. Productivity (Link 1)
guarantees this terminates by the time we hit `i = 0`.

For mutually-recursive stream pairs (`PairType (Stream A) (Stream B)`,
as in streamFibs), the lowering produces a Lean `Prod` of `Stream`s
with the index functions of each component referencing both via
the standard pair projections.

**Pinning.** Each shape gets a regression test under `intTests/`:

- `test_lean_recursion_bounded_vec_fold/` — popcount-shape,
  emits → elaborates → proves a popcount property end-to-end. The
  end-to-end proof is the *strongest* pin; if our lowering produced
  a Lean term semantically different from SAWCore's, the proof
  would either fail or close an off-by-one (and the latter would
  be caught by the property's specificity).
- `test_lean_recursion_stream_corec/` — streamFibs-shape, similar
  proof: the i-th Fibonacci equals the standard recurrence.
- `test_lean_recursion_classifier_smoketest/` — Haskell-side
  smoketest that constructs synthetic terms matching each shape,
  asserts `classifyFix` returns the right `FixShape`, and asserts
  unmatchable shapes fall through to L-5.
- Negative pins for shapes 3 and 4: factorial.cry and SHA-512
  continue to fail at translation time with the new diagnostics.

Together, the recognizer-test pins Link 3a (correct
classification) and the end-to-end proof pins Link 3b (correct
lowering).

### Why this clears the bar

The only soundness gap that's *introduced* by this design is the
shape recognizer. If `classifyFix` ever returned the wrong
classification (matching a shape we can't soundly lower), we'd emit
a wrong Lean term. The recognizer test is the gate; widening it
without widening the test is forbidden by the lockdown discipline.

Everything else is either translator-faithful by construction
(structural Lean defs are total and reduction is kernel-decidable)
or trust inherited from upstream (Cryptol productivity, SAWCore
meta-theory).

## Translator implementation sketch

### Module: `saw-core-lean/src/SAWCoreLean/FixShapes.hs` (new)

```haskell
data FixShape
  = BoundedVecFold
      { bvfLen   :: Natural    -- concrete n
      , bvfElTy  :: Term       -- A
      , bvfDflt  :: Term       -- the "default" arg used in atWithDefault
      , bvfBody  :: Term       -- the inner gen lambda's body, with rec
                               -- still bound — to be lowered
      }
  | StreamCorec
      { scElTy   :: Term       -- A (or a pair of element types)
      , scBody   :: Term       -- the MkStream's index function body
      , scIsPair :: Bool       -- mutual streams via PairType
      }
  | Unmatched String           -- diagnostic for L-5

classifyFix :: Term -> FixShape
classifyFix t = ...
  -- Match (App (App (Constant "Prelude.fix") tyArg) bodyArg)
  -- Strip the outer \rec lambda from bodyArg.
  -- Branch on the type-argument head:
  --   Vec n A   + body = gen n A (\i -> ...)        -> BoundedVecFold
  --   Stream A  + body = MkStream A (\i -> ...)     -> StreamCorec
  --   PairType (Stream _) (Stream _) + appropriate  -> StreamCorec scIsPair=True
  --   otherwise                                     -> Unmatched
```

### Lowering: `lowerFix :: FixShape -> Term`

For `BoundedVecFold`: emit a SAWCore term that calls a new
support-library def `genFix` (declared in
`SAWCorePrimitives.lean`, see below) with the body's `e`
transformed to take a `Nat → α` lookup function instead of the
recursive `Vec n α`. The transformation rewrites every
`atWithDefault n α d rec j` to `lookup j` and is otherwise the
identity on the body.

For `StreamCorec`: emit a SAWCore term calling
`mkStreamFix` with the index function similarly rewritten —
`Stream#rec _ _ (\s -> s j) rec` becomes `lookup j`.

`Unmatched` falls through to the existing L-5 reject with a
diagnostic from `Monad.hs`'s `RejectedPrimitive` constructor —
same emission path as today.

### Wiring

`Term.hs:translateIdentToIdent` at the `Prelude.fix` site (currently
the L-5 reject) calls `classifyFix` on the parent application
node, dispatches via `lowerFix` for matched shapes, and falls
through for unmatched. Because `classifyFix` needs to see the
arguments of `fix`, this requires hoisting the dispatch up one
level — to the `App (App fix tyArg) bodyArg` constructor in the
emit pass — so the existing identitarian dispatch can't handle it
in isolation. A small refactor of the apply-dispatch site.

## Lean support library additions

In `lean/CryptolToLean/SAWCorePrimitives.lean`, the actual landed
definitions (Phase 5 commits c1002541d / 8bcf137c4):

```lean
/-- Stream-corec fix: produces a `Stream α` whose index function
recursively references earlier elements. Builds the prefix
[v 0, v 1, …, v (i)] structurally on Nat via `mkStreamFixPrefix`,
then reads index i. Productivity assumed (Cryptol frontend). -/
def mkStreamFixPrefix (α : Type) (d : α)
    (body : (Nat → α) → Nat → α) : Nat → List α
  | 0     => []
  | k + 1 =>
      let prev := mkStreamFixPrefix α d body k
      prev ++ [body (fun j => prev.getD j d) k]

def mkStreamFixIdx (α : Type) (d : α)
    (body : (Nat → α) → Nat → α) (i : Nat) : α :=
  (mkStreamFixPrefix α d body (i + 1)).getD i d

def mkStreamFix (α : Type) (d : α)
    (body : (Nat → α) → Nat → α) : Stream α :=
  Stream.MkStream (mkStreamFixIdx α d body)
```

`mkStreamFixPair` (Slice A.5) follows the same pattern with
mutual prefixes — see SAWCorePrimitives.lean:266-394.

`genFix` for the bounded-Vec-fold case is scaffolded similarly
but the recognizer match in FixShapes.hs is currently dormant
(see §"Phase 5d" in `2026-05-02_revised-plan.md`).

The earlier-drafted sketch in this doc used a `where`-clause
non-structurally-decreasing recursion (`mkStreamFixLookup` calling
itself at `n + 1`); the implementation switched to a List-prefix
+ `getD` form which IS structurally recursive on Nat. Same
semantics; only the latter elaborates. The structural-recursion
content
is what matters.)

`SpecialTreatment.hs` gets corresponding entries that route the
*translator-emitted* `genFix`/`mkStreamFix` references to these
defs. `Prelude.fix` itself stays in the reject list — the
translator never emits a bare reference; only `genFix`/`mkStreamFix`
calls.

## Test plan

### Smoketests (translator-internal)

- `classifyFix` recognizer pin: synthetic terms for each of
  {bounded-vec-fold, stream-corec, mutual-stream-pair, bv-gated,
  num-dispatch, garbage} pinned to expected `FixShape`. Pinned by
  test path `smoketest/SmokeTest.hs`.
- `lowerFix` round-trip: hand-construct a known fix term, lower
  it, pretty-print the result, compare against a `.lean.good`
  reference. Asserts the lowering is shape-stable.

### Integration tests (`otherTests/saw-core-lean/`)

- `test_recursion_popcount.{saw,log.good,lean.good}` — popcount
  on [32]; emit elaborates under `lake env lean`. Pinned `.lean.good`
  exhibits the lowered form (no `fix`, no `genFix.fix_unfold`,
  just a `genFix n α d f`-shaped call).
- `test_recursion_stream_fibs.{saw,log.good,lean.good}` — streamFibs
  emits successfully; `lake env lean` elaborates the result.

### End-to-end semantic verification (`otherTests/saw-core-lean/proofs/`)

Strongest pin per Link 3:

- `proofs/E6_popcount/` (CLOSED): popcount spec-vs-impl equivalence
  discharge. The `BoundedVecFold` lowering preserves popcount
  semantics — if it didn't, this proof would fail. Companion driver:
  `drivers/cryptol_module_popcount/`.
- `proofs/recursion_stream_corec/` (CLOSED): single-stream
  `mkStreamFix` discharge against `RecOnes.cry`'s `allTrue` stream
  (i=0 and i=1 values). Catches lookup-substitution drops, recursor
  case-order swaps, and `mkStreamFixPrefix` ordering bugs.
- `proofs/stream_fibs_corec/` (CLOSED 2026-05-07, audit H-2): mutual
  stream `mkStreamFixPair` discharge against `StreamFibs.cry`'s
  `streamFibs` (indices 0, 1, 2). Index 1 fires the cross-stream
  lookup; index 2 fires the β-side recursive `lkα + lkβ` step
  through `bvAdd`.

### Negative pins (rejection still fires for shapes 3+4)

- `saw-boundary/sha512_fix_rejection/` (CLOSED): the SHA-related
  test continues to be caught by `polymorphismResidual`.
- `saw-boundary/fix_rejection/` and `saw-boundary/fix_unfold_rejection/`
  (CLOSED): non-matched `fix` / `fix_unfold` shapes refuse cleanly.
- Bitvector-gated partial recursion (factorial-style) is *not* a
  separate driver today; the broader `fix_rejection` covers it via
  the same diagnostic path.

## What stays rejected

Bitvector-gated partial recursion (factorial), polymorphic
`Num#rec1`-dispatched recursion (SHA-512), and any other fix shape
unmatched by `classifyFix`. These continue through L-5 with
diagnostics that explain the obstruction in user-actionable terms.

Same coverage gap as Rocq, which rejects all fix outright. The
Phase 5 design doesn't widen this gap — it only adds shapes 1+2 on
top.

## Hand-rewriting Prelude fix-users (parallel sub-task)

Independent of the shape-recognizer work: SAWCore Prelude defs that
internally use `fix` (e.g., `streamScanl`) won't be reached by the
recognizer because they're closed-over inside Prelude defs that
`scNormalize` doesn't fully unfold. Following Rocq's pattern, hand-
write Lean equivalents in `SAWCorePreludeExtra.lean` using
structural Lean recursion, with `SpecialTreatment` routing.

Audit step: enumerate Prelude.sawcore fix-users
(`grep -n "Prelude.fix" Prelude.sawcore`); cross-reference Rocq's
`SAWCorePreludeExtra.v` for parity.

This is mechanical mirror work — no novel design required. ~1-2
days. Can run in parallel with the shape-recognizer
implementation.

## Implementation phasing

Three independent slices, each pin-then-implement:

1. **Slice A: StreamCorec** *(2-3 days)* — simpler than
   BoundedVecFold (no `gen` rewriting needed). Land first to
   validate the recognizer-and-lower architecture on the easier
   case.
2. **Slice B: BoundedVecFold** *(3-5 days)* — popcount-shape, more
   intricate body rewriting.
3. **Slice C: Prelude fix-users hand-rewrite** *(1-2 days)* —
   parallelizable with A or B.

Total: ~1.5 weeks, plus residual-trust doc update (~1 day).

Each slice closes the lockdown loop:

- detector + lowering implementation
- smoketest pinning the recognizer
- integration test pinning the translator output
- end-to-end proof pinning the semantic faithfulness
- residual-trust doc updated to cite the shape and the test

Phase 5 is **complete** when:

- Slices A, B, C land.
- `doc/2026-05-XX_residual-trust.md` documents the Cryptol
  productivity trust assumption (Link 1) and the
  `scNormalizeForLean` preservation claim (Link 2).
- The phase plan (`2026-05-02_post-audit-plan.md`) has §"Phase 5"
  marked complete with citations to the slice tests.

## Open questions to resolve during implementation

1. **`Vec` opacity vs the `genFix` definition.** L-4 sealed `Vec`'s
   constructors against user pattern-matching. `genFix` needs
   `Vector.nil`/`snoc` (or equivalent) inside the support library —
   are those reachable from inside `CryptolToLean.SAWCorePrimitives`
   without violating L-4's user-facing seal? If not, `genFix` may
   need to live in a privileged sub-namespace or use a different
   constructor approach.

2. **PairType handling for mutual streams.** The streamFibs shape
   uses `PairType (Stream A) (Stream A)`. The lowering produces a
   `Prod (Stream A) (Stream A)` in Lean — does this round-trip
   through `SpecialTreatment`'s `PairType` handling cleanly?
   Probably yes (PairType already maps to a Lean `inductive`), but
   verify during Slice A.

3. **Diagnostic phrasing for unmatched shapes.** The current
   `RejectedPrimitive` diagnostic for `fix` is generic. The
   bv-gated case (shape 3) deserves a specific message: "the
   recursion's decreasing argument is a bitvector subtraction
   which can wrap; consider providing an explicit Nat bound". The
   Num#rec1 case is already covered by `polymorphismResidual`.

These are all implementation-time questions; they don't change the
soundness argument or the strategic shape of the design.
