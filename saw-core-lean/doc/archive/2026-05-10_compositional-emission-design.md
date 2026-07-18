# Compositional emission: design note for the Lean backend

*2026-05-10. Companion to `2026-05-02_recursion-design.md` and the
archived `2026-04-22_universe-*.md` series. Triggered by the
ChaCha20 `core` override-driven obligation hanging
`scNormalizeForLean`.*

## Context

The current Lean backend runs `scNormalizeForLean` between
`propToTerm` and `Lean.translateGoalAsDeclImports` (Exporter.hs:1408
in `writeLeanProp`; analogous in `writeLeanTerm`). This pass:

1. Constant-folds Nat/Int/Bool literals (`scLiteralFold`).
2. Iteratively `scNormalize`s, unfolding every `Constant nm` not in
   an opaque set.
3. Iterates to a fixed point, capped at 100 iterations.

The pass exists to do two jobs:

- **J1 — unfold Cryptol/SAWCore-prelude defs** so the translator
  doesn't hit unmapped names like `Cryptol.seq` / `ecReverse` /
  `finNumRec`.
- **J2 — specialize away sort-k≥1 universe binders.** Lean 4 is
  non-cumulative (kernel design, see
  `archive/2026-04-22_universe-external-research.md` finding #1).
  The current `translateSort` collapses every `sort k` to `Type`
  (Term.hs:165–167). The `polymorphismResidual` gate refuses any
  term whose type still binds a `sort k ≥ 1` after specialization.
  Normalization is what makes the gate's "after specialization"
  precondition hold: symbolic execution typically passes concrete
  types in, and `scNormalize` reduces the polymorphic prelude
  callees to monomorphic shape.

`scNormalizeForLean` hangs on the ChaCha20 `core` obligation with
the 8 qround overrides because of J1, not J2: the 320 nested
`Cryptol.update` references wrapping `Cryptol.qround` references
unfold into a giant term, then re-walk over and over. The user
defs (`qround`, `cdround`, `core`, `blocked`, `iterate`) are all
sort-0 throughout — no universe issue. We just don't want them
unfolded.

## How Rocq avoids this

`writeRocqProp` (Exporter.hs:517) is:

```haskell
writeRocqProp name notations skips path t = do
  sc <- getSharedContext
  tm <- io (propToTerm sc t)
  writeRocqTerm name notations skips path tm
```

No normalize step. `writeRocqTerm` directly translates and writes.
The Rocq side then has separate emitters that materialize every
referenced Constant:

- `writeRocqSAWCorePrelude` — full SAWCore prelude as Rocq
- `writeRocqCryptolPrimitivesForSAWCore` — Cryptol primitives as Rocq
- `writeRocqCryptolModule` — any user Cryptol module as Rocq

A goal can reference *any* Constant; the user emits the
corresponding modules once and proofs link them. Rocq's
cumulativity (`Prop ≤ Type 0 ≤ Type 1 ≤ …`) makes universe levels
elaborate automatically at each call site, so J2 isn't a problem.

## Why we can't just copy Rocq

J2 is the obstacle. Three concrete things would surface:

1. **Each emitted prelude def** has occurrences of `sort k ≥ 1` in
   its type (e.g. SAWCore `Eq : (t : sort 1) → t → t → Prop`).
   `translateSort` currently collapses to `Type` — so `Eq` would
   emit as `def Eq (t : Type) (x y : t) : Prop := …`, which is
   monomorphic and breaks for `Eq (sort 0) Bool True`.
2. **Each call site** references a Constant whose universe levels
   must be supplied explicitly. Lean's universe inference fails
   often enough (see `archive/2026-04-22_universe-internal-investigation.md`
   on `eq_cong`, `coerce__def`, etc. — ~100 elaboration errors in
   the first attempt) that we'd need `mathport`-style explicit
   `@Foo.{u₀, u₁, …}` at every reference.
3. **`polymorphismResidual`** rejects the un-specialized goal type
   because Cryptol-prelude defs' types have surviving `sort 1`
   binders. We'd need to lift the gate from "reject if sort-k≥1
   binder survives" to "reject only if sort-k≥1 binder survives
   AND no auto-emitted def with that universe shape is in scope."

The first two are the "P4/P6 universe work" parked in
`archive/2026-04-22_universe-internal-investigation.md`. The fix
is per-binder fresh universe variables in `translateSort` +
`mathport`-style explicit level emission at call sites. Per the
investigation's confidence note: "**High**: Option D1 (per-binder
fresh) handles all three groups [of universe errors]." Effort
estimate then: 1–2 days plus regression coverage.

## The proposed architecture

A layered pipeline that mirrors Rocq's but accounts for Lean's
universe rigidity. From bottom to top:

```
┌─────────────────────────────────────────────────────────┐
│ Layer 6:  User goal emissions                           │  offline_lean
│           (small, all references go down)               │
├─────────────────────────────────────────────────────────┤
│ Layer 5:  User Cryptol modules (auto-emitted)           │  write_lean_cryptol_module
│           (chacha20.cry → ChaCha20.lean)                │
├─────────────────────────────────────────────────────────┤
│ Layer 4:  Bridge lemmas (hand-written PROOFS)           │  hand-written .lean
│           (parametric bridges, cryptolIterate_succ,     │
│            foldr_and_gen_eq_true_of_all, etc.)          │
├─────────────────────────────────────────────────────────┤
│ Layer 3:  Hand-tuned overrides via SpecialTreatment     │  hand-written .lean
│           (BitVec mapping, ite-permutation, error       │  + SpecialTreatment
│            two-tier, cryptolIterate structural recursion)│
├─────────────────────────────────────────────────────────┤
│ Layer 2:  Cryptol primitives (auto-emitted)             │  write_lean_cryptol_primitives
│           (ecReverse, finNumRec, seq, etc.)             │
├─────────────────────────────────────────────────────────┤
│ Layer 1:  SAWCore prelude (auto-emitted)                │  write_lean_saw_core_prelude
│           (Eq, coerce, addNat, fix, etc.)               │
└─────────────────────────────────────────────────────────┘
```

Each layer's emission becomes its own Lean file, imported by the
layer above. A user's discharge workflow becomes:

```saw
write_lean_saw_core_prelude          "SAWCorePreludeAuto.lean"  [] [];
write_lean_cryptol_primitives        "CryptolPrimitives.lean"   [] [];
write_lean_cryptol_module "X.cry"    "X.lean"                   [] [];
prove_print (offline_lean "goal")    {{ ... goal ... }};
```

The goal file imports SAWCorePreludeAuto, CryptolPrimitives, and X
(plus the hand-written layers), and references are resolved
through that chain.

## What stays hand-written, what becomes auto

### Stays hand-written (Layer 3 + 4)

Five categories where auto-emission is either unsound, less
ergonomic, or unsupported:

1. **BitVec mapping.** Lean's native `BitVec w` is faster and more
   ergonomic than the auto-emitted `Vec w Bool`. We map `bvAdd`,
   `bvXor`, etc. via SpecialTreatment to `BitVec`-level operators.
   The hand-tuned mapping uses `vecToBitVec` / `bitVecToVec`
   coercions to bridge.

2. **Bool eliminator case-swap.** SAWCore's `Bool` data declares
   `True; False;` in that order, so `Bool#rec` takes
   `(motive, trueCase, falseCase, scrutinee)`. Lean's auto-derived
   `Bool.rec` is the opposite (False first). The hand-written
   `iteDep` / `ite` in `SAWCorePreludeExtra.lean` corrects the
   permutation. Auto-emission would silently swap branches — L-16
   was exactly this bug.

3. **`error` as explicit partiality.** SAWCore's
   `error : (α : sort 1) → String → α` admits `α = Prop`, enabling
   the L-17 Check class. The live backend does not transcribe that
   primitive as an axiom. Value-position errors route through
   `Except`; raw/proof/type-position errors become explicit proof
   obligations or refusals.

4. **Corecursion/fix contracts.** SAWCore's `Prelude.fix` is opaque to
   Lean's structural recursion checker. The live backend therefore uses
   generic proof-carrying fixed-point obligations rather than
   shape-specific structural helper definitions. Recurrence/productivity
   reasoning belongs in Lean-checked proof libraries.

5. **Bridge lemmas.** `saw_self_ref_comp_iterate`,
   `foldl_eq_natRec_atWithDefault`, `foldr_and_gen_eq_true_of_all`,
   the `cryptolIterate_succ` / `_zero` family, etc. These are
   PROOFS over the layered defs — they have no SAW analog. Pure
   hand-written.

### Becomes auto (Layers 1, 2, 5)

**Layer 1 — SAWCore prelude.** Roughly 200 defs (Nat, Int, Bool,
Vec, Stream, Either, PairType, Eq, coerce, finNumRec, etc.).
Each gets auto-emitted as a Lean def. Currently most go through
SpecialTreatment in `SAWCoreLean/SpecialTreatment.hs` (256
entries) — auto-emission would replace most of these with direct
emit + the hand-tuned Layer 3 overlay for the items above.

**Layer 2 — Cryptol primitives.** The Cryptol-specific wrappers
(`ecReverse`, `seq`, the Cryptol numeric/comparison classes, etc.).
Currently we don't emit these; `scNormalizeForLean` unfolds them
into Layer 1 shapes. Auto-emission lets them stay as references
and unfold lazily during discharge.

**Layer 5 — User Cryptol modules.** Already works via
`writeLeanCryptolModule`. No change needed.

### What scNormalizeForLean becomes

After the port, `scNormalizeForLean`'s J1 role is obsolete (every
prelude reference resolves through the auto-emitted layers). J2
also becomes obsolete (Layer 1/2 emissions are universe-polymorphic
at the def level, so references at concrete types elaborate by
Lean's normal universe inference).

We keep it as an **opt-in** proof-script primitive
(`normalize_for_lean_then : [String] -> ProofScript ()` or via the
existing `goal_normalize`), for goals that genuinely benefit from
pre-normalization — e.g. very long Cryptol identity chains that
would otherwise force the user to unfold a dozen layers in the
proof. Default off.

## The universe work that gates this

Per `archive/2026-04-22_universe-internal-investigation.md`, the
required changes to `translateSort` and the support library:

1. **Per-binder fresh universe variable.** Replace the current
   "collapse to Type" with: at each `sort k` occurrence in a
   binder position, allocate a fresh `u_n` variable. The
   def's universe-variable list grows accordingly. Value-position
   `Sort k` nodes emit concrete `Type k` (caller determines
   context).

2. **Explicit `.{u₀, u₁, …}` at call sites.** Each `Constant nm`
   reference in the emitted Lean uses `@nm.{u₀, u₁, …}` with the
   levels determined by SAW's `scTypeOf` at the call site. This
   sidesteps Lean's universe-inference failures (mathport pattern).

3. **Universe-polymorphic hand-written library.** The current
   `SAWCorePreludeExtra.lean` is mostly monomorphic; the items
   that take `Sort` arguments (`iteDep`, `ite`) become
   `@[reducible] noncomputable def iteDep.{u} (p : Bool → Sort u)`
   etc. Already done for `iteDep`/`ite`. Need to audit the rest.

4. **`polymorphismResidual` becomes a translator-emission gate**
   rather than a goal-emission gate. A goal whose type has a
   surviving `sort k ≥ 1` binder is fine if the auto-emitted
   layers provide an appropriately universe-polymorphic def for
   the offending reference. The gate's diagnostic stays — it's
   still useful for parse_core users — but the trigger moves.

## Soundness considerations

Every existing soundness property must transfer faithfully:

| Lockdown # | Property | Survival path |
|---|---|---|
| L-1 | sort-k≥1 binders rejected | Becomes "rejected unless an auto-emitted def covers it"; gate location moves |
| L-2 | unsafeAssert axiom shape | Layer 1 emits `unsafeAssert` directly as Lean axiom; hand-tuned at Layer 3 to match SAW's shape |
| L-3 | recursor opacity auto-derived | Layer 1 emission must respect; auto-emit recursors as axioms when their SAW type has the bad shape |
| L-4 | Vec ctor/rec not reachable | Layer 3 mapping (BitVec) replaces the auto-emit; auto-emit produces refs that Layer 3 overrides |
| L-5 | `fix` rejected at SAW boundary | Stays — SAW Prelude `fix` is in SpecialTreatment as a `reject` |
| L-6 | normalize 100-iter cap | scNormalizeForLean still has it for the opt-in path; doesn't fire on default |
| L-7 | iteDep/ite case-permutation | Layer 3 hand-tuned; auto-emit produces the SAWCore version, Layer 3 overrides |
| L-8 | coerce axiom shape | Same as L-2 |
| L-9 | @-prefix on ctor/rec heads | Becomes routine emission detail |
| L-10 | translateSort universe-collapse | Replaced by per-binder fresh; new pinned contract |
| L-11 | escapeIdent identifier safety | Unchanged |
| L-12 | writeLeanCryptolModule passes through every soundness gate | Auto-emit pipeline must honor all gates |
| L-13 | every boundary regression-tested | Need new tests for the auto-emit pipeline |
| L-14 | missing SpecialTreatment auto-detected | Becomes less load-bearing as SpecialTreatment shrinks |
| L-15 | soundness audit runs in CI | Unchanged; runs over new architecture |
| L-16 | Bool#rec emission swap | Layer 3 covers; auto-emit produces the SAWCore version intact |
| L-17 | error two-tier | Layer 3 covers; auto-emit produces `error_unrestricted`, hand-tuned `error` overrides |

Property-based fuzzing (the existing hostile-prover audit) re-runs
over the new architecture as a regression. Likely needs to expand
to cover the auto-emission pipeline's specific failure modes.

## Risks

1. **Universe inference brittleness.** Even with explicit levels,
   Lean's universe unification has known limits (Lean issue #2297
   per `archive/2026-04-22_universe-external-research.md` §5).
   Fallback: `PULift` to bridge unsolvable gaps. Test coverage
   must include universe-polymorphic call shapes that previously
   only the WIP machinery handled.

2. **Auto-emit blow-up.** A naive auto-emit of the SAWCore prelude
   produces ~200 defs in one Lean file. Reasonable in size, but
   we may need to split by module for compile time. Tractable; the
   Rocq emission already does this.

3. **Library file regeneration vs. hand-written split.** The
   current `SAWCorePrelude_proofs.lean` mixes def-equivalents with
   proofs. We need to separate: defs auto-emitted go to
   `SAWCorePreludeAuto.lean`; proofs over them stay in
   `SAWCorePrelude_proofs.lean`. Compile order: Auto first,
   proofs after.

4. **Discharge ergonomics.** Without `scNormalizeForLean` inlining
   everything, user proofs need explicit `unfold cryptolIterate`
   / `unfold core` / etc. The existing `unfold ...` tactic and our
   bridge lemmas cover this, but proof length may grow. Mitigation:
   for high-traffic items, Layer 3 SpecialTreatment maps directly
   to nicer Lean forms (e.g. BitVec).

5. **Compile-time cost.** Importing the auto-emitted prelude adds
   compile-time overhead to every user discharge. Acceptable for
   correctness; we measure and optimize if it becomes painful.

6. **Soundness regression risk during the port.** A 1-2 week
   architectural shift touching the prelude emission has a real
   chance of breaking subtle soundness contracts. Mitigation:
   land it gated, run the full fuzz/property-based suite, keep
   the old code path as a comparison mode for the first month.

## Staged plan

**Stage A — immediate (1 day): unblock ChaCha20 `core`.**
Make `offline_lean_skip`'s name resolution work. Once a user can
mark `chacha20.qround` opaque, `scNormalizeForLean` no longer
explodes on the override-driven obligation. The ChaCha20 demo
lands as a regression test that pins the compositional path.
No architecture change.

**Stage B — investigation (3 days): catalog the prelude.**
Run `dump_lean_residual_primitives` over every existing demo's
emission. Catalog: which prelude constants does each demo actually
reference? Which are unfolded by `scNormalizeForLean` vs which
are already mapped? Identify the minimum prelude surface
auto-emission needs to cover for the existing test suite to pass
under the new architecture.

**Stage C — universe work (3 days): finish P4.**
Per-binder fresh universe variables in `translateSort`; explicit
level emission at call sites; audit `SAWCorePreludeExtra.lean`
for universe polymorphism gaps. Validate on the existing
~100-error WIP probe set (parked, but reproducible). Land as
its own commit; no architecture change yet, just sound universe
handling.

**Stage D — auto-emit Layer 1 (1 week): SAWCore prelude.**
Implement `writeLeanSAWCorePrelude` mirroring `writeRocqSAWCorePrelude`.
Walks the SAWCore prelude module, translates each def, emits to
a Lean file. Must honor every soundness gate
(`polymorphismResidual`, recursor opacity, etc.). Test: the
auto-emitted file elaborates standalone in Lean.

**Stage E — auto-emit Layer 2 (3 days): Cryptol primitives.**
`writeLeanCryptolPrimitivesForSAWCore` mirroring the Rocq pair.
Depends on Stage D. Test: existing Cryptol-module demos elaborate
against the auto-emitted Layer 2 + their own auto-emitted module.

**Stage F — make `scNormalizeForLean` opt-in (1 day).**
Remove the call from `writeLeanProp` and `writeLeanTerm`. Add a
proof-script tactic `normalize_for_lean [skips]` for the opt-in
case. Update existing tests where they relied on inlining — most
should keep working because the prelude is now in scope via the
auto-emitted layers.

**Stage G — shrink `SpecialTreatment` (3 days).**
Audit `SAWCoreLean/SpecialTreatment.hs`. Items that the
auto-emitted Layer 1 covers can be deleted. Items in Layer 3
(BitVec, ite-permutation, error two-tier, corecursion) stay.
Target: shrink from 256 entries to ~50.

**Stage H — regression + docs (1 week).**
Property-based fuzzing over the new pipeline. Update doc/
to reflect the new architecture. Catalog new residual-trust
items if any. Run the existing regression suite end-to-end.

Total estimate: 3–4 weeks of focused work, gated as discrete
commits with regression coverage at each stage. The ChaCha20
demo lands at Stage A; the architectural payoff (scalability
to SHA, AES, full streams) lands at Stage F+.

## Decision points before starting

1. **Do we adopt this plan as the path of record?** If yes, Stage
   A starts immediately; Stage B catalogs scope.
2. **Should Stage C (P4 universe) be a precondition or pursued in
   parallel?** P4 is gated on the catalog from Stage B telling us
   which universe shapes are actually needed.
3. **What's the success bar?** Minimum: ChaCha20 core lands
   end-to-end via Lean (Stage A). Stretch: all existing demos
   pass under the new architecture (Stages A–H complete). The
   Stage A success is independent of the rest.
4. **How do we test the new architecture without breaking
   existing demos?** Stage F (making `scNormalizeForLean` opt-in)
   is the risky one. Keep the old `offline_lean` path with the
   normalize step as a fallback during transition; gate the
   shrunk SpecialTreatment behind a flag until everything passes.

## What this doc isn't

- Not a defense of the current architecture. The hang on ChaCha20
  `core` is a real bug; the current architecture has known
  scaling limits.
- Not a critique of saw-core-lean's history. The
  `scNormalizeForLean`-then-translate pipeline made sense as the
  shortest path to get a working Lean backend with sound universe
  handling. The investigation that produced this note builds on
  that foundation.
- Not the only viable design. An alternative is to keep
  `scNormalizeForLean` and fix only the user-def-unfolding cost
  (e.g., a term-size cap, lazy unfolding). That's lower-risk
  short-term but doesn't address the underlying scalability gap.
