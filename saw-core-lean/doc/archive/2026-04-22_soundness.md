# Soundness discipline for saw-core-lean

*Draft — 2026-04-22.*

> **Reading order note (2026-05-01).** This doc was written under
> the original architecture in which the SAWCore Prelude was
> translated as a universe-polymorphic Lean library. That
> architecture was abandoned in the 2026-04-23 specialization
> pivot (see `2026-04-23_specialization-approach.md`). What
> survived from this doc, what changed, and what to read instead:
>
> - **Survived** verbatim: the absolute rule (§"Absolute rule"),
>   the four legitimate-vs-broken pattern taxonomy, and the audit
>   process at the end. These are architecture-independent.
> - **Changed**: the "current status" section's claim that ~100
>   Prelude elaboration errors are tolerated as loud-failure
>   signals. Under specialization the Prelude is no longer
>   translated; those errors are gone because the file isn't
>   emitted. The replacement loud-failure surface is documented
>   in `2026-04-24_soundness-boundaries.md`.
> - **Stale approximations** in §"Known approximations":
>   - `bitvector n → BitVec n` is wrong about current behaviour;
>     we now use `bitvector n := Vec n Bool` (faithful but loses
>     `BitVec` ergonomics — see Arc 3 in
>     `2026-05-01_status-and-next-steps.md`).
>   - `seq (TCNum n) a → Vec n a` is no longer the issue it was
>     under the old architecture; specialization unfolds `seq`
>     before the translator sees it.
>   - The `Inhabited` class discussion is dead code — the
>     auto-injection was removed in Stage 4 (`27f9136ff`).
> - **Replaced** by `2026-04-24_soundness-boundaries.md` for
>   user-facing soundness rules, and the two
>   `2026-04-24_audit-*.md` docs for full mechanism.
>
> Keep this file as historical record of the pre-pivot soundness
> contract and the audit discipline that carried over.

## Absolute rule

**The translator must never emit Lean output that silently elaborates
when the SAWCore source couldn't actually be faithfully translated.**
When translation can't be carried through, the tool fails — loudly,
with a pointer to the specific def or primitive that's the problem.
The cost of a loud failure is "user knows what to fix." The cost of
silent acceptance is "user proves a Cryptol property in Lean that
doesn't actually hold, or holds under the wrong semantics."

This document catalogs the soundness-relevant decisions made in the
translator and the support library, calls out every deliberate
approximation, and lists what the tool does when translation can't
cross the SAWCore/Lean semantic boundary.

## Three legitimate patterns and one broken one

### Legitimate: precise mapping

The Lean side offers a primitive with identical semantics. Map it via
`mapsToCore` / `mapsTo` and you're done. Currently in the table:

| SAWCore | Lean | Notes |
|---|---|---|
| `Prelude.Bool` | `Bool` | Both 2-element. |
| `Prelude.Nat` | `Nat` | Both arbitrary-precision. |
| `Prelude.Integer` | `Int` | Both arbitrary-precision signed. |
| `Prelude.String` | `String` | UTF-8 on both sides. |
| `Prelude.True`/`False` | `true`/`false` | Bool literals. |
| `Prelude.UnitType`/`Unit` | `Unit`/`Unit.unit` | Unit types. |
| `Prelude.Bit` | `CryptolToLean.SAWCoreScaffolding.Bit` | handwritten `abbrev Bit := Bool`. |

### Legitimate: handwritten realization via `DefReplace` or paired
`DefSkip` + support-lib

Some SAWCore primitives don't map to Lean core cleanly but have a
hand-crafted Lean equivalent in `CryptolToLean/`. Here `skip` is
safe **because the handwritten support library provides the name at
the same Lean-qualified path** the use sites reach. This is exactly
the pattern the Rocq side uses for its Scaffolding support.

Rule: **never add a `skip` entry unless the Lean name the use sites
will reference actually resolves in the support library.**

### Legitimate: explicit failure

When the SAWCore def uses constructs Lean can't represent — or when
a semantic gap means translation would produce wrong output —
the translator throws a `TranslationError`. Currently:

- `NotSupported t` — e.g. recursion via `Prelude.fix`
- `UnderAppliedMacro _ _` — a `UseMacro` table entry with
  insufficient arity
- `LocalVarOutOfBounds`, `BadTerm` — malformed SAWCore input

When Lean can't elaborate what the translator emitted (e.g., the
`sort 1` / `Prop` impedance around the `Eq` family in
`Prelude.sawcore`), the `lake build` / `lake env lean` step fails.
That failure **is the loud-failure signal**. Do not silence it.

### Broken: `skip` without a handwritten realization

Adding a `skip` entry for a def with nontrivial Lean use sites, when
no handwritten realization exists, silently creates a dangling
reference. Lean's elaborator then:

- emits an `Unknown identifier` error (best case — user sees it), or
- infers a placeholder metavariable (worse — the surrounding type
  checks under a meaningless unification), or
- a later user adds a hand-written `def X := sorry` to make `lake`
  happy, making the whole chain unsound without the translator
  author ever knowing.

**Never do this.** A prior revision of this branch added skip entries
for `eq_cong`/`sym`/`trans`/`coerce__def`/etc. to silence the ~100
Lean elaboration errors from auto-translating the proof-heavy core of
`Prelude.sawcore`. That was reverted on review: a translator that
emits 100 loud Lean errors is correct behavior; a translator that
silences them by removing source is not.

## Known approximations (catalog)

Each of these deserves scrutiny and a plan.

### `Prelude.Eq` → Lean core `Eq`

SAWCore: `Eq : (t : sort 1) -> t -> t -> sort 0`.
Lean: `Eq : {α : Sort u} -> α -> α -> Prop`.

The types line up for the *value* of `Eq`. The recursor does not:
SAWCore's `Eq__rec` takes a motive `(y : t) -> Eq t x y -> sort 1`,
Lean's takes a motive `{motive : (b : α) -> a = b -> Sort u}` (any
universe). This means some SAWCore Prelude defs that pass a motive
at `sort 1` won't elaborate against Lean's `Eq.rec` at `Prop`. The
current plan: **let them fail.** Real Cryptol specs don't exercise
these defs, but if a user's property uses them, they'll get a
legitimate elaboration error.

### `Prelude.bitvector n` → `BitVec n`

SAWCore defines `bitvector n := Vec n Bool`. A packed 8-bit value
(`BitVec 8`) and an 8-element `Vec` of `Bool` are semantically
distinct — indexing, equality, and bitwise operations don't commute
between them. The scaffolding currently maps `bitvector n :=
BitVec n`.

**Soundness implication:** anything in the generated prelude that
treats `bitvector n` as a `Vec` of `Bool` (structural eliminators,
`at`, `append`, etc.) will either:
- fail to typecheck (good — loud failure), or
- typecheck only because of a surface-level compatibility in the
  translated term, producing wrong results at runtime (bad).

The honest alternative is `abbrev bitvector (n : Nat) : Type := Vec n
Bool` in the scaffolding, at the cost of giving up Lean's native
`BitVec` ergonomics. The current mapping is an optimistic
approximation that needs audit once real Cryptol bitvector programs
are translated and exercised.

### `Cryptol.seq (TCNum n) a` → `Vec n a`

Cryptol's `seq : Num -> sort 0 -> sort 0` takes a `Num` (which has
two constructors, `TCNum` and `TCInf`). Our scaffolding `Vec` takes
a plain `Nat`. The translator's Cryptol→Lean mapping of `seq` doesn't
strip the `TCNum`, so the Lean elaborator sees `Vec (TCNum n) a`
where `TCNum n : Num`, not `Nat`. This **will fail to elaborate** —
loud failure, correct.

To fix properly, `Vec` in the scaffolding should take `Num` and
internally project to `Nat` (or the `seq` mapping should inject a
projection). Either approach is a real design decision; the current
state fails loudly while we decide.

### `Inhabited` — class instead of data

Lean core's `Inhabited` is `Type -> Prop`. SAWCore's `isort` can be
at any sort level. The scaffolding defines its own universe-
polymorphic `class Inhabited.{u} (α : Sort u) : Type u`, with a
bridge instance from `_root_.Inhabited`. This is *not* the Lean
Prelude's `Inhabited` — they're separate classes, and a user who
imports mathlib will find two competing `Inhabited`s.

Soundness is preserved (the bridge instance means any Lean-
inhabited type satisfies our class), but users should be aware of
the duplication. Plan: consider using a unification-friendlier name
(`SAWInhabited`) to reduce confusion.

## Audit process

When adding a new SpecialTreatment entry:

1. State the SAWCore type. State the Lean type.
2. Are they semantically equivalent under all universe/sort
   combinations that appear in SAWCore sources? If not, document the
   failure mode in this file.
3. Is the entry `skip`? If yes, verify the Lean name resolves in the
   handwritten support library, *and* add the handwritten def in
   the same commit.
4. Is the entry `UseMacro`? Verify the macro produces terms that are
   well-formed and well-typed under *every* input arity the macro
   promises to handle.

When Lean's elaborator rejects generator output:

1. Is the error a semantic mismatch (e.g. universe impedance)?
   Document here. Do not silence by skipping — the error is correct.
2. Is the error a mechanical translator bug (wrong parenthesization,
   missing `@`, etc.)? Fix the translator.
3. Is the error a support-lib gap (Lean expects a name the support
   lib doesn't provide)? Add the def to the handwritten support lib;
   don't route around it via `skip`.

## Current status

The Phase 2C commits land the translator's faithful-by-default
behavior. The generated `SAWCorePrelude.lean` has ~100 Lean
elaboration errors concentrated in the proof-heavy core; none of
them is silenced. Real Cryptol programs translated via
`write_lean_term` / `offline_lean` don't touch those defs and should
elaborate cleanly against the parts of the prelude that do.
