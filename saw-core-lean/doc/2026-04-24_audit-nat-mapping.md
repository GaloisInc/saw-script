# Audit: SAW-Nat to Lean-Nat mapping

*2026-04-24*

Scope: the chain `SAWCore Nat/Pos --> scNormalizeForLean --> SpecialTreatment --> Lean Nat`.
Audit goal: identify inputs under which the current translation diverges
from SAW semantics or fails to elaborate.

Verdict up front: **the mapping is sound on a narrow concrete slice and
unsound (or non-elaborating) on a broad symbolic slice.** The gap is
not shielded by `leanOpaqueBuiltins`; it is shielded only by the fact
that recent demos (e.g. `rev.cry`) never instantiate the unsound
surface. `polymorphismResidual` does not catch any of it.

## 1. Mapping table

All SAW names below live in `Prelude`. "Holds iff" conditions are
*necessary* — if any is violated at translation time the emitted Lean
either mis-denotes or fails to elaborate.

| SAW | Lean target | Semantic claim | Holds iff |
|---|---|---|---|
| `Nat` (inductive) | `_root_.Nat` | Both denote the mathematical N. | Always at the *type* level (both are N). But SAW inhabitants have shape `Zero \| NatPos Pos`, Lean's have shape `zero \| succ Nat`. Terms that destructure via `Nat#rec` or `Pos#rec` do **not** match — see §2. |
| `Zero` | `(0 : Nat)` | `Zero` denotes `0`. | Always. Constructor with no args. |
| `NatPos` | `id` | `NatPos p = p` at the level of Lean `Nat` values, because we conflate `Pos` and `Nat`. | Holds iff `p` already denotes a non-zero Lean `Nat`, which is true precisely when `p` was produced by the `One`/`Bit0`/`Bit1` chain that we also remap to Lean `Nat`. |
| `One` | `(1 : Nat)` | 1 = 1. | Always. |
| `Bit0 n` | `bit0_macro n = 2 * n` | `Bit0 n` denotes `2*n`. | Always at the value level. **Ignores** that SAW's `Pos#rec` has case order `One, Bit0, Bit1` with a motive `Pos -> Sort`, while no Lean recursor exists on `Nat` with that shape. |
| `Bit1 n` | `bit1_macro n = 2*n + 1` | `Bit1 n` denotes `2*n+1`. | Same caveat as `Bit0`. |
| `Succ` | `Nat.succ` (def-opaque) | `Succ n = n + 1`. | Holds. `Succ` is in `leanOpaqueBuiltins`, so its SAW body (`NatPos (Nat#rec ... posInc n)`) never surfaces; the translator emits a call that Lean resolves to `Nat.succ`. Equivalence with SAW's body is provable but not checked. |
| `addNat` | `Nat.add` (reducible wrapper) | Both commutative monoid add on N. | Holds (opaque in `leanOpaqueBuiltins`, Lean realisation is `Nat.add`). |
| `subNat` | `Nat.sub` | Truncated subtraction, saturates at 0. | Holds. SAW `subNat x y = ZtoNat (subNZ x y)` where `ZtoNat ZNeg _ = Zero`, matching Lean's `Nat.sub`. |
| `mulNat`, `divModNat`, `equalNat`, `ltNat`, `minNat`, `maxNat` | *none* — kept opaque | — | **Unsound-on-use.** These are in `leanOpaqueBuiltins` so `scNormalize` leaves them as references, but `SpecialTreatment` has no `mapsTo` entry. A surviving `mulNat x y` emits `CryptolToLean.SAWCorePrelude.mulNat`, which **is not defined** on the Lean side. Elaboration fails loudly — unsound-by-omission, fails-closed. |
| `Pos` (inductive) | — (no mapping) | — | If a `Pos` type annotation ever reaches the translator, we emit `CryptolToLean.SAWCorePrelude.Pos`, which does not exist. Fails-closed (elaboration error), but an uninformative one. |
| `Pos#rec`, `Nat#rec` | `@Pos.rec`, `@Nat.rec` (via `Recursor` branch in `Term.hs`) | — | **Unsound on survival.** See §2. |
| `Nat__rec` | (not mapped, not opaque) | — | Unfolds during normalization into `AccessibleNat#rec1` over `AccessibleNat_all n`. If `n` is symbolic, a residual `AccessibleNat#rec1` or `Nat#rec` surfaces at a type whose Lean counterpart does not exist. See §3. |
| `leNat`, `expNat`, `widthNat`, `doubleNat`, `divNat`, `modNat`, `pred`, `natCase`, `if0Nat` | (not mapped, not opaque) | — | Unfold to bodies containing raw `Nat#rec` / `Pos#rec`. On symbolic args, residues survive. See §3. |
| `BitM`, `posSub`, `dblZ`, `dblZinc`, `dblZdec`, `posEq`, `posLe`, `posLt`, `posExp`, `Pos_cases`, `Nat_cases`, `Nat_cases2`, `Z`, `ZZero`, `ZPos`, `ZNeg`, `AccessibleNat*`, `AccessiblePos*` | (not mapped, not opaque) | — | Same as above — unfolding exposes raw SAW recursors over `Pos` / `Nat` / `Z` / `AccessiblePos`, none of which have Lean-side realisations. |

## 2. `Nat#rec` / `Pos#rec` soundness

### The translator's current emission

`Term.hs` (lines 559-571) translates a `Recursor d` node as `@d.rec`.
For SAW's `Nat` the target ident is `Nat`, so the head becomes
`@Nat.rec`. The surrounding `App` node passes all arguments
positionally in SAW order:

```
Nat#rec  motive  branch_Zero  branch_NatPos  n
```

Lean's auto-generated eliminator for the native `Nat` is

```lean
Nat.rec : {motive : Nat → Sort u_1} → motive Nat.zero
        → ((n : Nat) → motive n → motive (n.succ))
        → (t : Nat) → motive t
```

Case order matches by accident (`Zero` ↔ `zero`), but the second
branches are completely incompatible:

- SAW wants `(p : Pos) → motive (NatPos p)` — unary in `Pos`, no IH.
- Lean supplies `(k : Nat) → motive k → motive (Nat.succ k)` — binary
  in `(Nat, motive k)`, with IH.

So a surviving `Nat#rec` emits a Lean term Lean will try to type-check
with an incompatible branch signature. This is an elaboration error
at the Lean level (fails-closed). It would not be a silent
mis-denotation unless the motive is the constant family
`(_ : Nat) → A` for some `A : Type 0` that happens to make both
branch shapes unify — see §2.1.

### 2.1 Silent-divergence construction (motive-is-constant case)

Consider SAW input:

```
(n : Nat) → Nat#rec (λ(_:Nat) → Bool) True (λ(_:Pos) → False) n
```

- Surviving after `scNormalize`: `n` is a bound variable, never a
  constructor, so `asRecursorApp` never finds a redex. The whole term
  stays.
- Emitted Lean: `@Nat.rec (λ_ => Bool) true (λ_ => false) n`.
- Lean elaboration: `@Nat.rec` expects the second branch at type
  `(k : Nat) → (λ_ => Bool) k → (λ_ => Bool) k.succ`, i.e.
  `Nat → Bool → Bool`. SAW's supplies `Pos → Bool`, i.e.
  `Nat → Bool` (since `Pos ↦ Nat`). Under-applied: **Lean reports a
  type error**.

So in the constant-motive case Lean catches the mismatch at
elaboration time. Fails-closed, not silent.

### 2.2 Silent-divergence construction (motive ignores the IH)

Replace the SAW branch with `λ(p : Pos) → f p` for some `f : Nat → A`:

```
Nat#rec (λ_:Nat → A) z (λp:Pos → f p) n
```

- Emitted Lean: `@Nat.rec (λ_ => A) z (λp => f p) n`.
- Lean's branch expects `(k : Nat) → A → A`. User supplied `λp => f p`
  of type `Nat → A`. Again under-applied: elaboration fails.

This would become **silent** only if we had a wrapper converting the
SAW branch `(Pos → A)` into a Lean branch `(Nat → A → A)` by dropping
the IH and applying `f` to the outer `Nat`. In that hypothetical
wrapper the two semantics differ: SAW reduces
`Nat#rec _ z f (NatPos p) = f p`, while a wrapper for `Nat.rec` would
reduce to `f (Nat.succ k)` where `k` is the predecessor. The inputs
are related by `NatPos p = p + 1` at the value level **if** `p` on the
Pos side is remapped to the Lean `Nat` value `p`, which is exactly
what we do. So the two reductions would in fact agree — but only
because of the specific `NatPos ↦ id` and `Bit0/Bit1/One ↦ Lean Nat`
conflation. **This is the one coincidence that the current mapping
relies on, and it only holds at the value level.** Anything typed —
including `Eq Nat x y` reasoning that computes via the reduction rule
— breaks.

### 2.3 Does any user term reach this?

A plain Cryptol program does not write `Nat#rec` directly. But
`cryptol-saw-core`'s `Cryptol.sawcore` uses `Nat__rec` at
`ecSDiv`/`ecSMod`/line 2043 and uses `natCase`, `if0Nat`,
`Nat_cases`, `Nat_cases2` in many places. Each of those:

- is **not** in `leanOpaqueBuiltins`
- is **not** in `SpecialTreatment`
- unfolds during `scNormalize` into a body containing raw `Nat#rec`
  or `Pos#rec` over a symbolic Nat argument.

So any user function that invokes Cryptol `(/)`, `(%)`, `(^^)`, signed
division, or uses enumeration/comprehension at an argument where the
type index `n` does not reduce to a concrete literal, risks a
surviving recursor. Cryptol's `reverse`/`[0..<n]` at fixed `n`
survives via `gen (addNat 1 (subNat n 0)) _ _`; `addNat` and `subNat`
are opaque and concrete, so no `Nat#rec` surfaces. **This is why
`rev.cry` happens to work.**

## 3. Failure modes catalogue

Ordered from most-likely to least-likely for user Cryptol input.

### 3.1 (high) Cryptol `(/)`, `(%)`, `(^^)` lowering

`ecDiv`/`ecMod`/`ecExp` in `Cryptol.sawcore` route through
`divNat`/`modNat`/`expNat`, which are *not* opaque and whose bodies
use `Nat#rec` over a Pos. On symbolic inputs, normalization exposes a
`Nat#rec`. Emitted `@Nat.rec` with SAW-order args will fail Lean
elaboration. `divModNat` is opaque, but `divNat x y = (divModNat x
y).0` (so it's a projection — opaque chain holds) — however `expNat`
and `widthNat` are *not* opaque. A user term with `x ^^ y` where `y`
is a symbolic `Nat` will blow this.

### 3.2 (high) Symbolic-length enumeration

`[0..<n]` with `n` a polymorphic binder (`{n} (fin n) =>`) lowers to
`ecFromTo`/`ecFromToLessThan`, whose bodies use `finNumRec` /
`Num#rec1`. `Num` is a Cryptol-prelude inductive; its recursor reduces
when the argument is a `TCNum _` or `TCInf` constructor. If the
enumeration bound enters as `TCNum n` with `n` a bound SAW `Nat`, the
`Num#rec1` reduces, leaving `gen (subNat bound first) a (...)`.
`subNat` is opaque, so the `gen`'s length stays as `subNat bound
first` — **this elaborates**, and `subNat` maps to Lean `Nat.sub`, so
it's semantically correct. **No failure here.**

But the moment the user writes a function that *matches on* the
length or computes a downstream Nat via a non-opaque def (e.g.
`width n`, `lg2 n` without going through `ecWidth` to a concrete Num),
the chain breaks.

### 3.3 (high) `ecSDiv`/`ecSMod` signed vector div/mod

These call `Nat__rec` directly in their bodies (Cryptol.sawcore lines
1309, 1318). `Nat__rec` is not opaque; its body normalizes to
`AccessibleNat#rec1 ... (AccessibleNat_all n)` — `AccessibleNat_all`
is itself defined via `Nat#rec` (line 1346). On a symbolic `n`, the
outer `AccessibleNat#rec1` won't reduce (no ctor at arg position).
Translator emits `@AccessibleNat.rec` referring to a Lean type that
does not exist. **Loud elaboration failure.**

### 3.4 (high) Cryptol comprehensions where a `natCase`/`if0Nat`
shape survives. These appear at lines 134, 158, 369, 385, 1438, 1528,
1556, 1990 of `Cryptol.sawcore`. Each is a thin wrapper over
`Nat_cases`/`Nat__rec` which, on a symbolic Nat, exposes a raw
`Nat#rec`. Emitted `@Nat.rec` → branch-arity mismatch in Lean.

### 3.5 (medium) User writes `(fin n) => [n]a -> ...` and then
internally projects a `length` or uses ``n` for a symbolic length,
possibly routed through `ecNumber` / `PLiteral`. `PLiteralSeqBool`
applies `bvNat` after a `Num#rec1`. `bvNat` is primitive on the Lean
side (eventually — currently not), so a literal like `1 : [8]` goes
fine. Symbolic: routed through `natToBv` variants that ultimately
take an `Nat` argument that `gen`/`bvNat` consume without inspection.
**Probably fine** for most current demos.

### 3.6 (medium) Any property that uses Cryptol's `number` type class
in a nontrivial way. Lowers through `PLiteral : Nat -> a`. Most
literals concretize. Symbolic uses depend on case 3.2.

### 3.7 (low) User writes a SAWScript that includes a Cryptol term
whose type has `Pos` appearing as a bound variable. This is not
expressible in Cryptol surface syntax, so requires a hand-written
`.sawcore`. Probably not a user-facing hazard.

### 3.8 (low) `polymorphismResidual` does not help here. It only
rejects binders at `sort k` with `k ≥ 1`. A surviving `Nat#rec` is a
term-level construct; its *type* may be `sort 0 → sort 0 → ...` which
passes the residual check cleanly.

## 4. What about the "coincidence" that `NatPos = id` *could*
accidentally work?

Value-level-only. If the emitted `@Nat.rec` ever type-checked (which
it won't — branch shape mismatch), then for a concrete `NatPos p`
argument both sides compute to the same Lean Nat since `NatPos` and
`Bit0/Bit1/One` are all flattened to Lean `Nat`. But since elaboration
fails first, we never observe this. The "coincidence" is not
load-bearing — it just happens to be true and irrelevant.

## 5. Recommendations

In priority order.

### 5.1 (MUST) Loud-fail on surviving `Nat#rec` / `Pos#rec`

In `Term.hs`, change the `Recursor crec` branch: if
`recursorDataType crec` is SAW Prelude `Nat` or `Pos` (or `Z`,
`AccessibleNat`, `AccessiblePos`), emit a `TranslationError` with a
clear message ("this term uses `Nat#rec` over a symbolic Nat after
normalization; the Lean backend currently requires all Nat
eliminations to reduce to a constructor — refactor or add a
handwritten wrapper"). Do not attempt to emit `@Nat.rec`.

Rationale: the current code path silently produces Lean that fails to
elaborate. The user gets a Lean-elaborator error pointing at a `.lean`
file they don't control. Far better to fail at the Haskell-side with
a SAW-level message.

### 5.2 (MUST) Extend `leanOpaqueBuiltins` to cover the rest of the
Nat-via-`Nat#rec` surface

Add at least:

```
leNat, expNat, widthNat, doubleNat, divNat, modNat,
pred, natCase, if0Nat, eqNat, Nat_cases, Nat_cases2,
Nat__rec, Pos_cases,
BitM, posSub, posEq, posLe, posLt, posExp, posDivMod,
dblZ, dblZinc, dblZdec, ZtoNat (already), subNZ (already),
AccessibleNat_all, AccessiblePos_all,
AccessibleNat_NatPos, AccessiblePos_Bit0, AccessiblePos_Bit1
```

For each, either

- add a matching `mapsTo` realisation in `SAWCorePrimitives.lean`
  (preferred for `leNat`, `expNat`, `widthNat`, `divNat`, `modNat`,
  `pred`, `if0Nat`, `natCase`, `Nat_cases`, `Nat__rec`), or
- add a `mapsTo` to a stub that is itself `axiom`ized (acceptable for
  the `Z`/`AccessibleNat`/`AccessiblePos` scaffolding, which users
  should never hit at value level).

This removes the entire class of failure 3.1, 3.3, 3.4.

### 5.3 (SHOULD) Declare SAW `Pos` on the Lean side and map it

Either:
(a) `inductive Pos : Type where | One | Bit0 : Pos → Pos | Bit1 : Pos → Pos`
with a handwritten `Pos.rec` (which Lean auto-generates correctly),
plus a `posToNat : Pos → Nat` conversion, and map `NatPos ↦ posToNat`.
This is the Rocq approach (`Pos.to_nat`).

or

(b) Keep the current `Pos ↦ Nat` conflation, add `abbrev Pos := Nat`
on the Lean side, and provide a handwritten `Pos_rec` with
`One ↦ 1`, `Bit0 ↦ 2*n`, `Bit1 ↦ 2*n+1` case semantics. This is
*not* Lean's auto-generated recursor; it must be handwritten to match
SAW's reduction rules. Soundness would rest on the provable
equivalence between the binary-positive `Pos` and the Lean-Nat
representation with `1 ≤ x` invariant.

(a) is safer. (b) keeps the literal-collapse macro nice, but puts a
bespoke `Pos_rec` into the soundness TCB.

### 5.4 (SHOULD) Write `Nat__rec` as a handwritten def

`SAWCorePrimitives.Nat_dunder_rec : (p : Nat → Type) → p 0 →
((n : Nat) → p n → p (n+1)) → (n : Nat) → p n := @Nat.rec`. This is
*exactly* Lean's `Nat.rec` shape. Map SAW `Nat__rec` to it via
`mapsTo`. This covers the case where Cryptol reduces to `Nat__rec`
(ecSDiv, ecSMod, line 2043, and everything going through
AccessibleNat). The SAW-side definition uses the
`AccessibleNat`-wrapped recursor, but its externally-visible behavior
is `Nat__rec p z s Zero = z; Nat__rec p z s (Succ n) = s n (Nat__rec
p z s n)`. Handwritten `Nat_dunder_rec = @Nat.rec` satisfies both
equations. Add to `leanOpaqueBuiltins`.

### 5.5 (SHOULD) Document the soundness boundary in
`CryptolToLean/SAWCorePrimitives.lean`

At the top of the file, spell out: "This backend maps SAW `Nat` to
Lean `Nat` with `Pos` / binary-positive constructors flattened to
numeric values. This is sound for value-level arithmetic and for any
`Nat#rec`-free SAW term. User input that, after specialization,
exposes a `Nat#rec` or `Pos#rec` on a symbolic argument is
**rejected** (see §5.1). Callers should prefer `Nat__rec` (handled
specially) for induction over naturals."

### 5.6 (NICE) Regression test the failure mode

A smoketest: construct a SAWCore term `λ (n : Nat) → Nat#rec (λ_ →
Bool) True (λ_:Pos → False) n`, run `writeLeanTerm` on it, assert
that translation fails with the §5.1 error — not with a Lean
elaboration error.

## 6. What stays sound under the current code as of `c1f319ea5`

- Concrete literals: `1`, `42`, `0xff`. All normalize away.
- Fixed-width bitvectors at concrete width. `bvNat` on `(w, k)` with
  `w, k` literal.
- `rev.cry`'s `implRev` / `specRev` at concrete `[4][8]`. `gen`,
  `addNat 1 (subNat n 0)` with `n = 4` reduces.
- Anything built out of `addNat` / `subNat` / `Succ` / `Zero` /
  constructors on concrete values.

## 7. What is unsound-on-use TODAY

- Any Cryptol `x / y`, `x % y`, `x ^^ y` on non-literal `Nat`s.
- Any Cryptol polymorphic `{n} (fin n) =>` function whose body runs
  through `ecSDiv`/`ecSMod`/`widthNat` at the type level with a
  symbolic `n`.
- Any SAWScript input that directly writes `Nat__rec`, `natCase`, or
  `if0Nat`.
- Any property that quantifies over a Cryptol `Integer` and converts
  through `intToNat` then eliminates via `Nat__rec`.

"Unsound-on-use" here means: the translator emits Lean that does not
elaborate, which is fails-closed but opaque-to-the-user. It does not
currently mean "the translator emits Lean that elaborates with the
wrong meaning" — I could not construct such a silent-wrong-meaning
input against the current code, because the branch-shape mismatch in
`@Nat.rec` blocks Lean elaboration. A future change that introduced
a `Nat_rec` wrapper with a coerced branch shape would create a silent
mis-denotation channel; §5.3(b) is where to be careful.

## 8. Absolute-soundness-rule compliance

The soundness discipline doc (2026-04-22_soundness.md §"Legitimate:
explicit failure") says the translator must fail loudly when it
cannot cross the SAW/Lean boundary. Today's code mostly fails
loudly, but through a Lean-side elaboration error rather than a
SAWCoreLean-side `TranslationError`. §5.1 closes that gap. §5.2
shrinks the surface so normal Cryptol programs stop hitting the gap
at all.

Nothing in this audit found a SAWCore input that the current
translator accepts and emits silently-wrong Lean output for. The
risk is elevated by the sheer number of non-opaque defs whose bodies
use `Nat#rec` — a single future SpecialTreatment addition that
mapped `Nat#rec` to a wrapper without re-proving equivalence would
shift the mode from fails-closed to silent-wrong. Treat any such PR
with the same care as a change to a proof kernel.
