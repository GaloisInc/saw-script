# Output readability review

*2026-05-09. Companion to `2026-05-09_release-case-study.md`.
Reviews the actual `.lean` files the backend emits today and lists
concrete improvements, organized by whether they conflict with the
§2.4 obvious-correctness principle in
`2026-05-05_long-term-plan.md`.*

## What "readable" means here

Two audiences:

1. **The user discharging the `theorem goal_holds := by sorry`.**
   They open the emitted file, `cases`/`unfold`/`bv_decide` their
   way to a closed proof. Readability is functional: can they
   identify the LHS/RHS, apply the right cookbook pattern, write
   tactics that target the right subterm?
2. **An auditor / new contributor reading the translator's
   output.** They want to confirm "yes, this Cryptol thing
   maps to that Lean thing." Readability is comparative: do
   homologous Cryptol and Lean structures sit at homologous
   visual positions?

Both audiences are currently underserved.

## The state of play, by example

Reading the `out/` files in `examples/saw-lean/` against the
matching `.cry` source:

### Trivial cases are fine

`idBool` (one-line Cryptol identity at `Bit`) emits as:

```lean
noncomputable def idBool (b : Bool) : Bool :=
  b
```

That's optimal. `Simple.addOne x = bvAdd 8 x (bvNat 8 1)` and
the surrounding `Simple` module are similarly clean while they
stay monomorphic-bv-arithmetic.

### Polymorphism over `Num` is brutal

`Rev.specRev` (one-line in Cryptol — `specRev xs = reverse xs`)
emits as a 16-line definition whose body is dominated by:

```lean
@Num.rec (fun (n' : Num) => (a' : Type) -> @Num.rec
  (fun (num : Num) => Type)
  (fun (n'' : Nat) => CryptolToLean.SAWCoreVectors.Vec n'' a')
  (Stream a') n' -> @Num.rec (fun (num : Num) => Type)
  (fun (n'' : Nat) => CryptolToLean.SAWCoreVectors.Vec n'' a')
  (Stream a') n')
```

That's the SAWCore `(n : Num) → Vec/Stream a` motive, repeated in
type and value position. It's faithful — `Num.rec` dispatches
between the bounded (`Vec n a`) and infinite (`Stream a`) cases —
but it shows up four times in `specRev` alone, and >20 times in
`implRev`.

### Class dictionaries are the worst pain point

`Rev.implRev`, `Rev.roundtrip`, anything that hits Cryptol's
`PCmp`/`PEq`/`PIntegral`/`PArith`/`PLogic` surfaces a
`RecordType "integralRing" (RecordType "ringZero" ix (RecordType
"add" (ix -> ix -> ix) (RecordType "sub" …)))` chain. Each chain
is ~10 nested `RecordType` constructors; each *use* needs a
matching `RecordType.rec` peeler chain to extract a single
projection. `roundtrip` (Cryptol: one `==` between two streams)
emits ~100 lines for what should be one line.

This is the *same* unmapped-class-dictionary issue called out in
the README and in `2026-05-09_release-case-study.md` §
"Capability surface." It's primarily a capability gap, but the
secondary cost is that even modules that don't trip the unmapped
identifier get visually drowned out.

### Cryptol `coerce` ceremony

Every Cryptol type-arithmetic identity (`n - 0 = n`, `n + 0 =
n`, etc.) emits as:

```lean
coerce (Vec 4 (Vec 8 Bool)) (Vec 4 (Vec 8 Bool))
  (@Eq.rec Num (Num.TCNum 4) (fun (y' : Num) (eq' : @Eq Num
    (Num.TCNum (subNat 4 0)) y') => @Eq Type (Vec 4 (Vec 8 Bool))
    (@Num.rec (fun (num : Num) => Type)
      (fun (n : Nat) => Vec n (Vec 8 Bool))
      (Stream (Vec 8 Bool)) y'))
    (@Eq.refl Type (Vec 4 (Vec 8 Bool)))
    (Num.TCNum 4)
    (unsafeAssert Num (Num.TCNum 4) (Num.TCNum 4)))
  (... actual value ...)
```

Semantically: `(... actual value ...)`. That whole `Eq.rec`/
`unsafeAssert` ceremony is "Cryptol's type checker says these
two `Num`s are equal; pretend they are." It clutters every
non-trivial polymorphic emission and there's no visual signal
distinguishing the meat from the ceremony.

### `error_unrestricted "at: index out of bounds"` everywhere

Every `atWithDefault N α dflt v i` in emitted code has
`error_unrestricted α "at: index out of bounds"` as its `dflt`.
Faithful to SAW (well-typed Cryptol guarantees `i < N`, but the
SAWCore primitive requires *some* default), but it appears
inline at every indexing site, often nested 4–6 deep.

### Variable name churn

Nested binders with the same source name produce `n'`, `n''`,
`n'''`, `n''''` chains by `nextVariant` (`Term.hs:170`). A user
reading `revInvolutive` sees `i`, `i'`, `i''`, `i'''`, `i''''`
in adjacent positions and has no way to tell which `i'''` is
the "outer comprehension index" vs the "inner reverse-table
index."

## Categorizing fixes against §2.4

The plan's obvious-correctness principle (§2.4 of
`2026-05-05_long-term-plan.md`) constrains what's acceptable: any
translator-side rewrite that recognizes a *shape* is presumptively
rejected; equivalences belong in the Lean library, applied at
proof time. That eliminates the most aggressive readability
fixes — but a lot of cosmetic improvement is fully compatible.

### Tier 1 — pure cosmetics, §2.4-safe, half-day each

These are import-scope / printer / preamble changes. None of
them changes the term structure that `.lean.good` files pin.
(They will churn the `.good` fixtures one-time, but there's no
soundness surface.)

| Fix | Mechanism | Cost saving |
|---|---|---|
| Add `open CryptolToLean.SAWCoreVectors` to the preamble | one-line change in `Lean.hs::preamble` (or extend `implicitlyOpenedModules` in `SpecialTreatment.hs`) | ~30 chars per `Vec` occurrence; many hundreds per module file |
| Add `open CryptolToLean.SAWCorePreludeExtra` to the preamble | same | ~35 chars per `ite`/`iteDep` occurrence |
| Source-provenance comments on top-level `def`s | `translateDefDoc` emits `-- <Cryptol source path:line> <ident>` ahead of each `def` | one comment per def; pure metadata |
| Tighten `fillSep` layout in `Pretty.hs::App` case | the printer currently wraps mid-application at arbitrary spots; switching to `nest 2 (group (fillSep ...))` per-application restores hangs without the previous compounding (Pretty.hs:163-171 explains why the previous form was rejected — the fix is to `nest` only at the App's root, not at every nested App, which avoids the compounding the comment warns against) | continuation lines align with arg list, scanning improves |
| Better fresh-name policy for shadowed binders | replace `nextVariant` (`x` → `x'` → `x''`) with positional suffixes (`x_1`, `x_2`) or scope-depth suffixes; `i'''''` becomes `i_4` | reading nested comprehensions becomes possible |

### Tier 2 — Lean-library cosmetics, §2.4-safe by construction

These are *additive* in the support library. They don't change
emission; they make emission read better at proof time. All
kernel-checked.

- **Notation for `bv*` ops.** Add `notation:65 x " +ᵇ " y => bvAdd _ x y`
  (and similar for `-`, `*`, `<`, `≤`, `≪`, `≫`, `^`, `&`, `|`)
  in `CryptolToLean.SAWCoreBitvectors`. Goals print with
  infix operators where they currently print with `bvAdd 8 x y`.
- **`@[simp] coerce_unsafeAssert_id`.** State and prove
  `∀ α (h : @Eq Type α α) x, coerce α α h x = x` (or the more
  specific `Num.TCNum`-shape lemma if needed for elaboration
  hygiene). User proofs add `simp [coerce_unsafeAssert_id]` and
  the type-coercion ceremony collapses.
- **`@[simp] atWithDefault_lt`.** A simp-lemma that reduces
  `atWithDefault N α dflt v i` when `i < N` is provable from the
  surrounding context, hiding the `error_unrestricted` argument
  from the goal printer. Where `i < N` is *not* derivable
  context-locally, the user's tactic needs to know about it
  anyway — exposing the `error_unrestricted` is at least
  honest signal.
- **`@[reducible] iteDep` / `@[reducible] ite` already are.**
  Confirm via `lean_hover_info` that goal printing benefits;
  if the printer still shows `CryptolToLean.SAWCorePreludeExtra.ite`,
  add a `@[pp_using_anonymous_constructor]`-style hint or define
  `notation` for it.

### Tier 3 — translator changes, need §2.4 review

These hit the translator and affect `.good` fixtures. Each needs
explicit justification before landing.

- **Class-dictionary `SpecialTreatment` mapping.** Map
  `Cryptol.PEqVec` / `PEqInteger` / `PCmpVec` etc. to Lean-side
  `def`s that take an `Inhabited`/`DecidableEq` constraint or
  return a fixed implementation, instead of unfolding to bare
  `RecordType` chains. The mapping is a name-rewrite
  (SpecialTreatment is exactly the §2.4-allowed mechanism for
  this — it's the dispatch table, not a shape-pattern), but
  there's a non-trivial design question about which Lean
  surface to target (Lean classes? bare `def`s? a record?).
  *This is also the capability gap from the case-study note —
  doing it once kills two birds.*
- **Optional: hoist repeated type subterms as `abbrev`s.**
  Currently `translateTermLet` excludes types from sharing
  (Term.hs:911) because Lean's elaborator doesn't always unfold
  let-bound types in motive checks. `abbrev` is `@[reducible]`
  by default and *does* unfold during elaboration. So a
  variant of `translateTermLet` that hoists shared-type
  subterms to `abbrev`-style auxiliary decls (rather than
  inline `let`s) sidesteps the motive-check issue while still
  compressing the visual mass of repeated `Num.rec` motives.
  Audit P-1 carefully: `shouldMemoizeTerm` controls when
  sharing fires; the `abbrev` variant must use the same gate
  so it doesn't introduce shared names where none existed.
- **Suppression of trivial coerce/unsafeAssert chains:
  REJECTED.** This is shape-pattern matching that asserts a
  semantic equivalence ("this is identity"). Per §2.4 it
  belongs in the Lean library as a `@[simp]` lemma (Tier 2),
  not in the translator. Listed here only to record the
  decision.

## Recommended landing order

1. **Tier 1 in one sitting.** Half-day; updates a lot of
   `.good` fixtures but the diff is mechanical (regex). Visible
   improvement out of proportion to cost.
2. **Tier 2 incrementally** as case studies surface specific
   pain points. The case-study note's headline (ChaCha20)
   would benefit immediately from bv-op notation and the
   coerce-id simp lemma.
3. **Tier 3 deferred** until the case-study note's §4.1 work
   is in flight — class-dictionary mapping in particular has
   significant overlap with that work and shouldn't be
   double-implemented.

## What this doesn't address

- **`Num.rec` motive bloat for polymorphic-over-size Cryptol.**
  Even with all Tier 1+2 fixes, `(n : Num) → Vec n a` defs will
  still print their motive at every use. The cleaner long-term
  fix is on the SAWCore side (a typed-Num primitive that doesn't
  surface `Num.rec` after specialization), not the Lean side.
  Out of scope here.
- **Polymorphic recursors in general.** `@Either.rec`,
  `@Stream.rec`, `@RecordType.rec` all emit faithful but verbose
  args. No fix beyond the structural ones above.
- **Source variable names.** SAWCore loses Cryptol's
  user-supplied identifiers during normalization; the translator
  has no way to recover `xs`/`ys`/`acc` when the SAWCore term
  presents them as De Bruijn or freshly-minted `e_1`/`e_2`. A
  sourcemap-style annotation (Cryptol parser → SAWCore-Term
  metadata → translator) would fix it, but that's deep upstream
  work.
