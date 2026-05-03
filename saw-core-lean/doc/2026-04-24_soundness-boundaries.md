# Soundness boundaries — user-facing summary

*Status as of Phase 1a soundness lockdown (2026-05-02). Distilled
from the audits in this directory and the lockdown catalog in
`2026-05-02_post-audit-plan.md`:*

- *`2026-04-24_audit-primitives-fidelity.md` — handwritten Lean
  declarations vs SAWCore primitives*
- *`2026-04-24_audit-nat-mapping.md` — SAW-Nat-to-Lean-Nat mapping*
- *`audit/2026-05-02_soundness-and-rocq-parity.md` — full
  re-audit under the lockdown bar*

The audits go deeper into mechanism. This doc is the actionable
summary: what guarantee the Lean output gives, what users (both
Lean-side and SAW-side) must avoid, and what failure modes look
like. **Every claim below cites the regression test that pins it**
— if the test went away, the claim is no longer trustworthy.

## What the translator guarantees

For any SAWCore term that

1. is **monomorphic at sort 0** after normalization (Cryptol's
   `{a}`-polymorphism over types is fine; explicit
   `(t : sort k)` for `k ≥ 1` anywhere in the type is not), AND
2. does not retain a residual recursor reference over an unsound
   datatype after `scNormalize` to a fixed point, AND
3. does not reach `Prelude.fix` or `Prelude.fix_unfold` after
   specialization,

the emitted Lean code is convertible-equivalent to the SAWCore
input. "Convertible-equivalent" here means: the Lean elaborator's
definitional equality matches SAWCore's evaluation behaviour, modulo
the documented mappings (`Nat ≡ Lean.Nat`, `Integer ≡ Lean.Int`,
etc.).

Term shapes outside (1), (2), or (3) are **refused at translation
time** with a specific diagnostic. Refusal is loud (non-zero exit,
descriptive message). The translator never silently emits a term
that would mistranslate.

| Refusal               | Test path                                                           | Lockdown item |
|-----------------------|---------------------------------------------------------------------|---------------|
| `polymorphismResidual` outer | `intTests/test_lean_soundness_polymorphic/`                  | L-1           |
| `polymorphismResidual` nested | `intTests/test_lean_soundness_polymorphic_nested/`          | L-1           |
| `UnsoundRecursor` (Nat/Pos)  | `intTests/test_lean_soundness_natrec/`                       | original      |
| `UnsoundRecursor` auto-derive (Z/AccessibleNat/AccessiblePos) | `saw-core-lean-smoketest:discoverNatRecReachers` | L-3 |
| `RejectedPrimitive` (`fix`)  | `intTests/test_lean_soundness_fix_rejection/`                | L-5           |
| `scNormalize` cap fired      | `saw-core-lean-smoketest:scNormalize cap fails loud`         | L-6           |

The polymorphism gate now runs across every entry-point: not just
`writeLeanTerm` and `writeLeanProp`, but also the Cryptol-module
walk in `writeLeanCryptolModule` (L-12).

## What Lean-side users must NOT do

The handwritten support library `CryptolToLean.SAWCorePrimitives`
exposes axioms and inductives that the translator emits references
to. Each axiom's universe shape now matches SAW's primitive
exactly (post-lockdown); the docstrings explain why each shape is
load-bearing.

### Don't apply `error` outside the translator's emission

`error.{u} : (α : Sort (u+1)) → String → α` admits `Type`,
`Type 1`, `Type 2`, … but **excludes `Prop`** by construction.
A Lean-side user instantiating `error False ""` would extract a
proof of `False` from nothing.

Pinned by `intTests/test_lean_soundness_error_prop/` — `attack.lean`
(`error False ""` must fail elaboration) and `non_prop.lean`
(translator-emitted shapes must succeed).

### Don't apply `unsafeAssert` to fabricate equalities

`unsafeAssert : (α : Type) → (x y : α) → @Eq α x y` matches SAW's
`(a : sort 1)` exactly, no universe polymorphism (L-2 tightening).
Inside SAWCore it's used as part of the `coerce`-via-equality
dance for Cryptol size arithmetic; Lean-side, it's a load-bearing
axiom you must not extend casually.

The `α = Prop` attack vector (deriving `Eq Prop True False` and
transporting `True.intro` to `False`) is admitted under both SAW's
shape and ours — this is a SAW-inherent residual trust, not a
Lean-side widening. SAW Prelude itself uses
`unsafeAssert (sort 0) a b` inside `unsafeCoerce`
(`Prelude.sawcore:292`).

Pinned by `intTests/test_lean_soundness_unsafe_assert_prop/` —
`attack.lean` (uses at `Type 1` must fail; the Prop attack is
documented as faithful-but-trusted) and `non_prop.lean`
(translator-emitted Num/Bool/Vec uses must succeed).

### Don't apply `coerce` outside its sort 0 universe

`coerce : (α β : Type) → @Eq Type α β → α → β` matches SAW's
`(a b : sort 0)` exactly. Pinned by
`intTests/test_lean_soundness_coerce_shape/` — `attack.lean`
(uses at `Type 1` must fail) and `positive.lean` (translator-
emitted Num/Vec uses must succeed). L-8 lockdown.

### Don't reach inside the translator's `Vec` abstraction

`CryptolToLean.SAWCoreVectors.Vec n α := Vector α n` is a
`Lean.Vector` alias. SAW's `Vec n α` and Lean's `Vector α n` are
mathematically isomorphic — both are length-`n` tuples of `α`
— so pattern-matching a `Vec` value via `Vector.mk` doesn't break
soundness. But it isn't part of the translator-supported surface
and has no compatibility guarantee across future arcs.

L-4 lockdown analysis (in
`saw-core-lean/lean/CryptolToLean/SAWCoreVectors.lean`'s file
header) explains why this is documented residual trust rather
than a feasibly-killable gap. The translator never emits
`Vector.mk` / `Vector.rec`; all translator-emitted `Vec` operations
go through the `gen`/`atWithDefault`/`bvAdd`/etc. axioms in
`SAWCorePrimitives.lean`.

## What the translator's mappings imply

Three structural mappings are non-trivial. Users should know about
them before working with translated output.

### SAWCore `Nat` ≡ Lean `Nat`

SAWCore's `Nat` is `Zero | NatPos Pos` (binary-positive). Lean's
`Nat` is `zero | succ` (unary). Same abstract values; different
representations.

The translator collapses SAW Nat literals (`NatPos (Bit0 (Bit0
One))`) to Lean Nat literals (`4`) at translation time, and maps
`addNat`/`subNat` to `Nat.add`/`Nat.sub` (saturating subtraction
in both, by direct equivalence).

What this means for soundness:

- Concrete SAW Nat values match Lean Nat values exactly.
- A surviving `Nat#rec` would mean SAW's `Zero / NatPos`
  case-split applied through Lean's `zero / succ` recursor —
  silent miscompilation. The `UnsoundRecursor` guard in
  `Term.hs` refuses this. Pinned by
  `intTests/test_lean_soundness_natrec/`.
- `discoverNatRecReachers` (in `SAWCentral.Prover.Exporter`) walks
  every Prelude def at translator startup and marks any def whose
  body directly contains a recursor over `Nat`, `Pos`, `Z`,
  `AccessibleNat`, or `AccessiblePos` as opaque under
  normalization. This is auto-derived (no hand-maintained safety
  list), pinned by the L-3 smoketest. The textual
  `leanOpaqueBuiltins` list (also in `Exporter.hs`) is
  convenience-only post-L-3 — it keeps adjacent defs opaque for
  surface cleanliness, but soundness no longer depends on it.

### SAWCore `Integer` ≡ Lean `Int`

Direct alias. `intAdd`/`intSub`/`intMul`/`intDiv`/`intMod`/
`intNeg`/`intEq`/`intLe` are declared as opaque axioms — Lean
sees the same operation names but doesn't reduce them. This is
intentional: SAW's `intDiv`/`intMod` semantics on negative
numbers and zero divisors are spelled out in
`Prelude.sawcore`; Lean's native `Int.div`/`Int.mod` may
disagree on edge cases. Treating them as axioms means the user
gets predictable shape but the reduction behaviour is left to
SAW.

### SAWCore `Bit` ≡ Lean `Bool`

Two-element type, same constructors. SAW's source declares them
as `True, False` (in that order); Lean's are `false, true` (in
that order). This **does** matter for case elimination order:
`SAWCorePreludeExtra.iteDep` is the case-permuted wrapper that
keeps SAW's True-first ordering visible at use sites. The `rfl`
proofs in `SAWCorePreludeExtra.lean` pin the wrapper's correctness
at lake-build time; the L-7 smoketest
(`SAW ite/iteDep argument order preserved`) pins the translator's
emission order at cabal-test time, catching upstream regressions
that would feed wrong-ordered args into a still-correct wrapper.

### `translateSort` collapses every non-Prop sort to `Type`

`translateSort` (`Term.hs:148`) is the single point of trust in
universe handling: SAW `propSort` → Lean `Prop`; every other SAW
sort → Lean `Type`. Combined with L-1's polymorphism gate (which
rejects sort `k > 0` binders anywhere in the type tree), the
maximal universe a translator-emitted term can produce is `Type`.

Pinned by the L-10 smoketests
(`translateSort: SAW sort 0 collapses to Lean Type` and
`SAW Prop stays as Lean Prop`).

### Constructor / recursor heads emit `@`-prefixed

SAWCore applies all constructor and recursor parameters
(including datatype parameters) explicitly. Lean's
auto-generated `<DT>.ctor` / `<DT>.rec` take them as implicits.
The translator emits a leading `@` (`Lean.ExplVar`) so SAWCore's
positional argument list lines up with Lean's — failing to do
this would silently mis-apply args at every constructor or
recursor use site.

Pinned at the smoketest level for constructors
(`applied constructor emits @-prefix at use site`); the recursor
side is pinned indirectly by every `.lean.good` integration-test
file containing `@<DT>.rec`. L-9 lockdown.

### `escapeIdent` reserves the `Op_` namespace

SAW identifiers go through `escapeIdent`. After L-11:

- Names with non-`[A-Za-z0-9_']` characters are Z-encoded with the
  `Op_` prefix.
- Names that match Lean reserved words (curated list:
  `match`, `do`, `for`, `where`, `instance`, `Type`, `Prop`, ...)
  are also Z-encoded — without this, `def match := ...` would fail
  Lean parsing.
- Names beginning with `Op_` are re-escaped — the escape namespace
  is disjoint from the passthrough namespace, so a SAW name
  `Op_match` and the Z-encoded form of `match` can't collide.

Pinned by smoketests
(`escapeIdent: ordinary alphanumeric names pass through`,
`special chars trigger Z-encoding`, `Lean reserved words get
escaped`, `distinct inputs produce distinct outputs`). L-11
lockdown.

## Failure modes catalogue

What you'll see when something goes wrong:

| Symptom                                            | Where          | What it means                                         |
|----------------------------------------------------|----------------|-------------------------------------------------------|
| `polymorphismResidual` exit                        | saw-time       | Term has a `(t : sort k ≥ 1)` binder anywhere in the type tree. L-1: gate checks the full term tree, not just the outer pi-spine. |
| `UnsoundRecursor` exit                             | saw-time       | A `Nat#rec` / `Pos#rec` / `Z#rec` / `AccessibleNat#rec` / `AccessiblePos#rec` survived normalization. |
| `RejectedPrimitive` exit                           | saw-time       | A SAW primitive the translator deliberately refuses (currently `fix` and `fix_unfold`). |
| `scNormalizeForLean exceeded 100 iterations`        | saw-time       | A constant unfolds in a non-terminating cycle. Bug. |
| `UnderAppliedMacro`                                 | saw-time       | A `replace`/`UseMacro` entry got fewer args than declared. SpecialTreatment table mismatch. |
| `Unknown identifier CryptolToLean.SAWCorePrelude.foo` | Lean-time | `foo` survived as a SAWCore reference but no SpecialTreatment entry maps it. (Future Phase 1a item L-14: detect at translator init instead of at Lean elaboration.) |
| `unknown identifier 'Bool.true'`                    | Lean-time      | Lean's `Bool` constructors are `Bool.false`/`Bool.true` — match the SpecialTreatment mapping. |
| `error: dependsOnNoncomputable`                     | Lean-time      | A user `def` references our axioms but isn't marked `noncomputable`. Add the marker. |

The first five are **correct refusals** by the translator. The
last three are **integration errors** in the translator/support
library that we've fixed previous instances of.

## Residual trust assumptions

Not every soundness boundary is feasibly-killable inside Lean's
type system. The following are documented residual trust:

1. **`unsafeAssert` at `α = Prop`** — admitted by both SAW's
   primitive and our faithful Lean transposition. The SAW Prelude
   itself uses this in `unsafeCoerce`. Tightening the Lean side
   would diverge from SAW's semantics.
2. **`Vec n α := Vector α n` exposes Lean's `Vector.mk`/`Vector.rec`** —
   the alias is a faithful representation; pattern-matching
   doesn't introduce divergence (analyzed in L-4 above). Sealing
   would not actually hide `Vector` from users (it lives in stdlib).
3. **The opaque axiom set in `CryptolToLean.SAWCorePrimitives`** —
   `bvAdd`, `bvAnd`, etc. are uninterpreted. We trust SAW's
   semantics for them; Lean has no way to reduce them, so
   `decide`/`native_decide` cannot fire on translated goals.
   This is an ergonomic trade-off, not a soundness claim — the
   axioms have the right types and unsoundness would require
   declaring an axiom *with the wrong type*, which we don't.

A future arc swapping bv operations for native `Lean.BitVec`
bindings (with proven-coherence theorems) would close item 3 for
bitvector terms specifically. See
`doc/2026-05-01_bitvec-binding-decision.md` for the deferral.

## The bottom line

If your saw script translates without saw-time error and the
emitted `.lean` files elaborate without errors at `lake env lean`,
the output is a faithful Lean rendering of the SAWCore semantics.
If either step errors, that's the safety net firing — the
translator is not silently producing wrong output.

The translator's compromises are scoped: it makes specific
non-trivial structural mappings (Nat, Bit, Vec, Integer) and
documents them. Every mapping has a regression test that would
fail loudly if the mapping drifted. Users who don't reach inside
the documented residual trust list above get soundness for free.
