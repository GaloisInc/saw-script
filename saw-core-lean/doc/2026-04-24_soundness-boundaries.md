# Soundness boundaries — user-facing summary

*Status as of `77f66e9c2` (Stage 4.2). Distilled from the two
companion audits in this directory:*

- *`2026-04-24_audit-primitives-fidelity.md` — handwritten Lean
  declarations vs SAWCore primitives*
- *`2026-04-24_audit-nat-mapping.md` — SAW-Nat-to-Lean-Nat mapping*

The audits go deeper into mechanism. This doc is the actionable
summary: what guarantee the Lean output gives, what users (both
Lean-side and SAW-side) must avoid, and what failure modes look
like.

## What the translator guarantees

For any SAWCore term that

1. is **monomorphic at sort 0** after normalization (Cryptol's
   `{a}`-polymorphism over types is fine; explicit
   `(t : sort k)` for `k ≥ 1` is not), AND
2. does not retain a residual `Nat#rec` / `Pos#rec` reference
   after `scNormalize` to a fixed point,

the emitted Lean code is convertible-equivalent to the SAWCore
input. "Convertible-equivalent" here means: the Lean elaborator's
definitional equality matches SAWCore's evaluation behaviour, modulo
the documented mappings (`Nat ≡ Lean.Nat`, `Integer ≡ Lean.Int`,
etc.).

Term shapes outside (1) or (2) are **refused at translation time**
with a specific diagnostic:

- `polymorphismResidual` for shape (1) — see
  `Exporter.hs` and `test_lean_soundness_polymorphic`.
- `UnsoundRecursor` for shape (2) — see `Term.hs` Recursor case
  and `test_lean_soundness_natrec`.

Refusal is loud (non-zero exit, descriptive message). The
translator never silently emits a term that would mistranslate.

## What Lean-side users must NOT do

The handwritten support library `CryptolToLean.SAWCorePrimitives`
exposes axioms and inductives that the translator emits references
to. Those declarations have the right *types* for everything the
translator emits, but their universe-polymorphism is sometimes
wider than SAW's. **Reading the docstrings is part of using the
library safely.** Specifically:

### Don't apply `error` outside the translator's emission

`error.{u} : (α : Sort (u+1)) → String → α` admits `Type`,
`Type 1`, `Type 2`, … but **excludes `Prop`** by construction.
This is the entire reason for the `(u+1)` rather than `u`: a
Lean-side user instantiating `error False ""` would extract a
proof of `False` from nothing, and SAW's `isort 1` source forbids
this.

The translator never emits `error` at `Prop` (Cryptol's value-
level types are all `Type`-sized). If you find yourself wanting
to use `error` in your own Lean proofs, **don't** — write a
specific axiom for what you mean instead.

### Don't apply `unsafeAssert` to fabricate equalities

`unsafeAssert.{u} : (α : Sort u) → (x y : α) → @Eq α x y` is the
SAWCore `unsafeAssert` axiom verbatim. Inside SAWCore it's used
as part of the `coerce`-via-equality dance for Cryptol size
arithmetic, where the translator can audit each call site. Lean-
side, it's a load-bearing axiom you must not extend casually.

If a translated term references `unsafeAssert`, the SAWCore proof
obligation is that the equated terms are convertible at SAWCore's
evaluator. The translator currently emits `unsafeAssert` only for
the size-coercion case in Cryptol's `Num.rec`-driven width
arithmetic; the equality there is between
`subNat n 0` and `n`, which is true at Lean's `Nat.sub` too.

### Don't reach inside the translator's `Vec` abstraction

`CryptolToLean.SAWCoreVectors.Vec n α := Vector α n` is a
`Lean.Vector`-aliased type. Lean exposes `Vector.mk` /
`Vector.rec` / etc.; SAWCore exposes only its `at` / `gen` /
`atWithDefault` interface. The translator uses only the SAWCore-
visible operations, but the Lean alias permits poking inside.

Doing so doesn't break translation soundness, but it leaves
a Cryptol-semantics gap: a Lean proof that depends on
`Vector`-internal structure won't have a SAWCore counterpart.

## What the translator's mappings imply

Three structural mappings are non-trivial. Users should know about
them before working with translated output.

### SAWCore `Nat` ≡ Lean `Nat`

SAWCore's `Nat` is `Zero | NatPos Pos` (binary-positive, similar
to Coq's stdlib). Lean's `Nat` is `zero | succ` (unary). Same
abstract values; different representations.

The translator collapses SAW Nat literals (`NatPos (Bit0 (Bit0
One))`) to Lean Nat literals (`4`) at translation time, and maps
`addNat`/`subNat` to `Nat.add`/`Nat.sub` (saturating subtraction
in both, by direct equivalence).

What this means for soundness:

- Concrete SAW Nat values match Lean Nat values exactly.
- A surviving `Nat#rec` would mean SAW's `Zero / NatPos`
  case-split applied through Lean's `zero / succ` recursor —
  silent miscompilation. The `UnsoundRecursor` guard in
  `Term.hs` refuses this.
- The opaque list `leanOpaqueBuiltins` (in
  `SAWCentral.Prover.Exporter`) names every SAWCore Prelude def
  whose body uses `Nat#rec`/`Pos#rec`; normalization is told to
  leave them alone so the recursor doesn't surface. **This list
  must stay aligned with the Prelude**: when adding new SAWCore
  primitives or unfolding new defs, walk their bodies and extend
  the list. (See `2026-04-24_audit-nat-mapping.md` §5.2 for the
  current list.)

### SAWCore `Integer` ≡ Lean `Int`

Direct alias. `intAdd`/`intSub`/`intMul`/`intDiv`/`intMod`/
`intNeg`/`intEq`/`intLe` are declared as opaque axioms — Lean
sees the same operation names but doesn't reduce them. This is
intentional: SAW's `intDiv`/`intMod` semantics on negative
numbers and zero divisors are spelled out in
`Prelude.sawcore`; Lean's native `Int.div`/`Int.mod` may
disagree on edge cases. Treating them as axioms means the user
gets predictable shape but the reduction behaviour is left to
SAW. (This is one of the larger items in Arc 3 of the
2026-05-01 status doc.)

### SAWCore `Bit` ≡ Lean `Bool`

Two-element type, same constructors. SAW's source declares them
as `True, False` (in that order); Lean's are `false, true` (in
that order). This **does** matter for case elimination order:
`SAWCorePreludeExtra.iteDep` is the case-permuted wrapper that
keeps SAW's True-first ordering visible at use sites. The `rfl`
proofs in that file pin down that the wrapping is correct.

## Failure modes catalogue

What you'll see when something goes wrong:

| Symptom                                            | Where          | What it means                                         |
|----------------------------------------------------|----------------|-------------------------------------------------------|
| `polymorphismResidual` exit                        | saw-time       | Term has a `(t : sort k ≥ 1)` binder. Refused (D3).  |
| `UnsoundRecursor` exit                             | saw-time       | A `Nat#rec`/`Pos#rec` survived normalization.        |
| `scNormalizeForLean exceeded 100 iterations`        | saw-time       | A constant unfolds in a non-terminating cycle. Bug. |
| `UnderAppliedMacro`                                 | saw-time       | A `replace`/`UseMacro` entry got fewer args than declared. SpecialTreatment table mismatch. |
| `Unknown identifier CryptolToLean.SAWCorePrelude.foo` | Lean-time | `foo` survived as a SAWCore reference but no SpecialTreatment entry maps it. Add one to `SpecialTreatment.hs`. |
| `unknown identifier 'Bool.true'`                    | Lean-time      | Lean's `Bool` constructors are `Bool.false`/`Bool.true` — match the SpecialTreatment mapping. |
| `error: dependsOnNoncomputable`                     | Lean-time      | A user `def` references our axioms but isn't marked `noncomputable`. Add the marker. |

The first four are **correct refusals** by the translator. The last
three are **integration errors** in the translator/support library
that we've fixed previous instances of and should fix new ones.

## The bottom line

If your saw script translates without saw-time error and the
emitted `.lean` files elaborate without errors at `lake env lean`,
the output is a faithful Lean rendering of the SAWCore semantics.
If either step errors, that's the safety net firing — the
translator is not silently producing wrong output.

The translator's compromises are scoped: it makes specific
non-trivial structural mappings (Nat, Bit, Vec, Integer) and
documents them. Users who don't reach inside those mappings get
soundness for free.
