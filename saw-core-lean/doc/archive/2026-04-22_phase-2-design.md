# Phase 2 Design: preludes + Cryptol modules

*Draft — 2026-04-22*

## 1. Goal

Close the gap from the current Phase-1 state (translator emits a correct
SAWCore-shaped Lean AST, but most referenced primitives dangle) to a
state where:

- `saw-lean-example/out/implRev.lean` elaborates cleanly under
  `lake build` — every identifier resolves and Lean accepts the
  definition as well-typed.
- `saw-lean-example/demo.saw`'s three Rocq-analog commands all have
  Lean-side equivalents:
  - `write_lean_sawcore_prelude`
  - `write_lean_cryptol_primitives_for_sawcore`
  - `write_lean_cryptol_module`
- The two preludes are regenerated once via the new commands, checked
  into `saw-core-lean/lean/CryptolToLean/`, and become stable build
  inputs the way Rocq's `rocq/generated/CryptolToRocq/*.v` are.

The prelude-generator commands themselves stay out of any hot path —
they're regenerated on the (infrequent) occasions that `Prelude.sawcore`
or `Cryptol.sawcore` change. The generator machinery still has to exist
for those regenerations and for `write_lean_cryptol_module`, which walks
a user-supplied Cryptol module through the same SAWCore-module-walker.

Explicit non-goals for Phase 2:

- Proof-script reuse / actual discharge of `by sorry` stubs. Still Phase 3+.
- Rewriting recursive SAWCore terms (`Prelude.fix`) as
  `def … termination_by`. Still deferred; the translator rejects those
  as in Rocq.
- Any mathlib-flavored support content. Phase 2 stays std-only, same
  decision as Phase 1.
- Generator-side pretty-printing improvements (paren nesting, line
  wrapping). The audit pass (running concurrently with this doc's
  writing) may surface issues worth fixing; if so, they belong to
  whatever sub-task they land in, not to Phase 2 directly.

## 2. What Phase 1 already gave us

- `SAWCoreLean.SpecialTreatment` with the `Def*/Use*` machinery and
  `findSpecialTreatment`. The table is thin; most entries land as
  part of Phase 2.
- `SAWCoreLean.Term` with full `Term → Language.Lean.AST` coverage
  for `Sort`/`Pi`/`Lambda`/`App`/`Variable`/`Constant`, special-
  treatment dispatch, and recursive body emission via
  `topLevelDeclarations`.
- `SAWCoreLean.Lean.translateTermAsDeclImports` and
  `translateGoalAsDeclImports` — the two single-term entry points
  `write_lean_term` and `offline_lean` sit behind.
- Lake project `saw-core-lean/lean/` with three handwritten stubs
  (`SAWCoreScaffolding.lean`, `SAWCoreVectors.lean`,
  `SAWCoreBitvectors.lean`) each ~15 lines.

## 3. The three new commands (shapes)

Mirror `saw-central/src/SAWCentral/Prover/Exporter.hs` 1:1 on the Rocq
analog, differing only in names, imports, and the lack of Rocq-specific
knobs (`vectorModule`, `monadicTranslation`, `postPreamble`).

### 3.1 `write_lean_sawcore_prelude`

```haskell
writeLeanSAWCorePrelude :: FilePath -> [(Text, Text)] -> [Text] -> IO ()
```

Loads `preludeModule` into a fresh `SharedContext`, translates the
whole thing via `Lean.translateSAWModule`, writes the result. Generator
only — not on the regular emission path.

### 3.2 `write_lean_cryptol_primitives_for_sawcore`

```haskell
writeLeanCryptolPrimitivesForSAWCore :: FilePath -> [(Text, Text)] -> [Text] -> IO ()
```

Same shape, but loads both the SAWCore and Cryptol preludes and
translates the Cryptol prelude. Generator only.

### 3.3 `write_lean_cryptol_module`

```haskell
writeLeanCryptolModule :: FilePath -> FilePath -> [(Text, Text)] -> [Text] -> TopLevel ()
```

Translates a user's `.cry` file via `Lean.translateCryptolModule`.
This is the one end users invoke repeatedly.

### 3.4 Interpreter wiring

`do_write_lean_sawcore_prelude`, `do_write_lean_cryptol_primitives_for_sawcore`,
`do_write_lean_cryptol_module` alongside `do_write_lean_term`, with
`prim` entries at the same docstring granularity as the Rocq analogs.

## 4. `SAWCoreLean.SAWModule` (the core new module)

The Rocq analog is 208 lines. Lean version will be similar; the work is
mechanical but has a few decision points.

### 4.1 Public entry: `translateDecl`

Walks one `ModuleDecl`:

- `TypeDecl (DataType { … })` → `translateDataType` → `Lean.InductiveDecl`
- `DefDecl (Def { … })` → `translateDef` → `Lean.Definition` / `Lean.Axiom`
- `InjectCodeDecl "Lean" txt` → `Lean.Snippet txt`
- `InjectCodeDecl "Rocq" _` / other → empty doc (ignored on the Lean
  side; Rocq analog ignores non-"Rocq" entries the same way)

### 4.2 `translateDataType`

Mirrors Rocq's `translateDataType` but produces `Lean.InductiveDecl`.
Two Lean-specific things to handle up front:

- **Constructor names qualify.** Lean constructors live inside the
  inductive's namespace automatically (`Foo.bar`); the `Ctor.ctorName`
  in SAWCore may come pre-qualified. The Rocq code strips the leading
  `ModuleName.TypeName.` prefix; we strip the same way and let Lean's
  namespacing do the rest.
- **`where` form, not `:=` form.** The AST already uses `InductiveDecl`
  whose pretty printer emits the `inductive … where | …` shape.
  `dropPi` stays identical (strip the inductive's parameters from each
  constructor's type).

### 4.3 `translateDef`

Largely a direct port. Three cases from `DefQualifier`:

- `NoQualifier` with `Just body` → `Lean.Definition`
- `AxiomQualifier` / `PrimQualifier` → `Lean.Axiom`

Special-treatment routing is already in `SpecialTreatment.hs`:

- `DefPreserve` → emit with unchanged short name.
- `DefRename targetName` → emit with the renamed name.
- `DefReplace str` → emit as `Lean.Snippet str` (the raw Lean text).
- `DefSkip` → emit a `Lean.Comment "Foo was skipped"` marker (same as
  Rocq).

### 4.4 The monad wiring

Rocq uses a second monad layer (`ModuleTranslationMonad`) that carries
`(Maybe ModuleName, ModuleMap)` as its reader environment and lifts
into `TermTranslationMonad` at each call. Exact same shape works here;
just rename `Rocq → Lean`. `liftTermTranslationMonad` builds a
`runTermTranslationMonad` invocation with the module context.

**Caveat:** our Phase-1 `runTermTranslationMonad` dropped `modname`
from its signature (design doc §3.1 called it out as unneeded for
single-term emission). Phase 2 adds it back — needed for
`translateIdentWithArgs`'s current-module awareness, if we port Rocq's
`identToRocq` logic that doesn't qualify references to the current
module. Low priority. Start by qualifying everything (current Phase-1
behavior) and revisit only if the output becomes awkward.

## 5. `SAWCoreLean.CryptolModule`

The Rocq analog is 63 lines. It walks a `CryptolModule`'s term map,
translates each `(Name, Term, Type)` triple into a `Lean.Definition`
via the existing `TermTranslation` plumbing, and accumulates them as
`topLevelDeclarations`. Already lines up with the Phase-1 state-
carrying refactor — this is mostly plumbing.

Wrapping the output in a Lean `namespace` named after the `.cry`
module file is a small surface difference: Rocq uses `Section`, we
already renamed `Decl.Section → Namespace` back in Phase 0. So
`Rocq.Section nm decls` becomes `Lean.Namespace nm decls` and the
pretty printer emits `namespace nm ... end nm`. This aligns naturally
with the §3 choice of one-namespace-per-file from the Phase-1 design.

## 6. Support-lib expansion (`lean/CryptolToLean/*.lean`)

Phase 1 landed three stub files totaling ~50 lines. Phase 2 grows
these, but not as much as the Rocq side — Lean's `BitVec`/`Vector`/
`Nat` cover a lot that Rocq has to build by hand.

### 6.1 Rocq reference sizes

| File | Rocq LOC | Lean equivalent | Est. LOC |
|---|---|---|---|
| `SAWCoreScaffolding.v` | 538 | `SAWCoreScaffolding.lean` | ~150 |
| `SAWCoreVectorsAsRocqVectors.v` | 525 | `SAWCoreVectors.lean` | ~100 |
| `SAWCoreVectorsAsRocqLists.v` | 88 | (drop — design §5.2) | 0 |
| `RocqVectorsExtra.v` | 29 | folded into `SAWCoreVectors.lean` | (above) |
| `SAWCoreBitvectors.v` | 810 | `SAWCoreBitvectors.lean` | ~100 |
| `SAWCoreBitvectorsZifyU64.v` | 377 | (drop — native `BitVec`) | 0 |
| `SAWCorePrelude_proofs.v` | 171 | (drop — proofs not in Phase 2 scope) | 0 |
| `SAWCorePreludeExtra.v` | 86 | `SAWCorePreludeExtra.lean` | ~80 |
| `CryptolPrimitivesForSAWCoreExtra.v` | 89 | `CryptolPrimitivesForSAWCoreExtra.lean` | ~80 |
| `Everything.v` | 15 | covered by the root `CryptolToLean.lean` | 0 |
| **Total** | **2728** | | **~510** |

That's a ~5× shrink. Most of the Rocq bulk is bitvector machinery that
Lean's native `BitVec` library subsumes.

### 6.2 What the prelude generators need the support lib to provide

Concrete primitives the current `implRev.lean` references that need
homes:

- `Num`, `TCNum`, `TCInf` (the `Fin n | Inf` Cryptol kind) — goes in
  `CryptolPrimitivesForSAWCoreExtra.lean`, or is emitted by the
  generator from `Cryptol.sawcore`.
- `tcSub`, `seq_cong1`, `seqMap`, `ecAt`, `ecMinus`, `ecNumber`,
  `ecFromToLessThan`, `ecEq` — from `Cryptol.sawcore`, emitted by the
  generator.
- `coerce`, `unsafeAssert`, `EqTrue` — from `Prelude.sawcore`, emitted
  by the generator. The `unsafeAssert` axiom needs a hand-written
  realization (SpecialTreatment `DefReplace` or a target in
  `SAWCorePreludeExtra.lean`).
- `PEqSeq`, `PEqSeqBool`, `PIntegralInteger`, `PRingInteger`,
  `PLiteralInteger` — Cryptol's type-class-dictionary machinery, from
  `Cryptol.sawcore`.

## 7. Rough spots anticipated

### 7.1 Lean's inductive positivity / well-foundedness

SAWCore has few recursive data types in `Prelude.sawcore` — mostly
`List`, `Vec`, `Nat`, `Stream`. Lean 4 accepts all of these as
`inductive` / `coinductive`. The Cryptol prelude is flatter (mostly
`Def`s). No expected blockers.

### 7.2 Recursion in `Prelude.sawcore`

`Prelude.sawcore` has recursive definitions (`foldr`, `Nat__rec`,
auto-generated eliminators). Options per def:

1. Translator emits `def` + `termination_by` clause — requires new
   translator support (Phase 4).
2. `DefReplace` with handwritten Lean in `SAWCorePreludeExtra.lean`.
3. `DefSkip` and require the caller to bring their own.

Baseline: option 2 for the handful of recursive primitives. Catalogue
them when porting, and prefer replacement over deeper translator work
until Phase 4.

### 7.3 Universe polymorphism

Lean 4 universe variables are written as `def foo.{u} : Type u := …`.
Our Phase-0 AST doesn't carry explicit universe variables — `Sort`
has just `Prop | Type`. If the generated preludes exercise serious
universe polymorphism (`foldr : (a : sort 0) (b : sort 0) → …` is
mostly at a fixed universe), we may need to extend the AST. **Action:**
try generating without universe support first; add it when something
concretely fails to elaborate.

### 7.4 Eliminator/recursor naming

SAWCore auto-generates `<TypeName>__rec` eliminators. Lean
auto-generates `<TypeName>.rec`. SpecialTreatment maps
`Prelude.List__rec → List.rec` (etc.) so use sites resolve.

### 7.5 `Prelude.fix`

Stays rejected, same as Rocq. Revisit in Phase 4 with `termination_by`.

### 7.6 Cryptol numeric-type-class dictionaries

`PIntegralInteger`, `PRingInteger`, `PLiteralInteger` and friends are
large objects in `Cryptol.sawcore` — whole records of per-type class
methods. These *should* translate straightforwardly (they're ordinary
data), but the output will be verbose. Not a correctness concern.

### 7.7 `Int` in `ecAt` / range constructors

Phase 1 maps `Prelude.Integer → Int` (Lean core). The generated prelude
will exercise this for real. `Int` is Lean's signed arbitrary-precision
integer, which is a reasonable target for Cryptol's `Integer`. The
audit pass will say if this is right or if we want something else.
Result affects one SpecialTreatment entry.

## 8. Phased sub-plan for Phase 2

Each sub-step is a PR-sized unit.

**2A — SAWModule walker (≈2 days).** Port `SAWCoreRocq.SAWModule`. Add
`Lean.translateSAWModule` to `SAWCoreLean.Lean`. Add `modname` back
to `runTermTranslationMonad`. No interpreter wiring yet; just the
module-level infrastructure compiling.

**2B — prelude generators (≈½ day).** Wire
`writeLeanSAWCorePrelude` and `writeLeanCryptolPrimitivesForSAWCore`
in `saw-central`'s `Exporter.hs`, plus interpreter `prim` entries.
Run them once; look at the raw output; note what breaks.

**2C — generated-prelude commitment (≈1 day).** Check in
`lean/CryptolToLean/SAWCorePrelude.lean` and
`CryptolPrimitivesForSAWCore.lean` (the machine output). `lake build`
the whole support library; iterate on SpecialTreatment table entries
and hand-written `*Extra.lean` content until it compiles. This is
where we'll find out which Rocq-style `DefReplace` realizations we
need.

**2D — `write_lean_cryptol_module` (≈½ day).** Port
`SAWCoreRocq.CryptolModule`. Add `writeLeanCryptolModule` in
`Exporter.hs`, plus `prim` entry. Rerun the `saw-lean-example/demo.saw`
three-line demo and verify `out/Rev.lean` + `out/implRev.lean`
both `lake build` under the support lib.

**2E — polish / Phase-2 wrap-up.** Handle whatever the audit surfaces
that's in scope. Update `demo.saw` and its README to describe the
full working flow. Close Phase 2.

Rough total: ~1 week of focused work (vs. design doc's 2-week
estimate; the Phase-1 work compressed the unknowns).

## 9. Open questions to decide

1. **Hand-written realizations of which primitives.** Need a catalog.
   Candidates already visible: `unsafeAssert` (axiom with no Lean
   equivalent), `coerce` (can use Lean's `Eq.mp`), `error` (Lean has
   `panic!`). Decide per-primitive in 2C as we meet them.

2. **Should generated preludes live under `lean/CryptolToLean/` in
   git, or under `lean/CryptolToLean/generated/`?** Rocq uses
   `rocq/generated/CryptolToRocq/` sibling to `handwritten/`. Mild
   preference for the nested `generated/` convention — makes it obvious
   what not to hand-edit. Downside: means the preamble imports change.

3. **Skip list conventions.** `constantSkips` is a list of short names.
   Rocq's practice is to skip a handful of Cryptol primitives that
   collide with Rocq keywords. Our list of Lean keyword collisions
   will be different (e.g. `at` is reserved in Rocq but not Lean;
   `end` might be a problem for us). Inventory when we see failures.

4. **Universe polymorphism in the AST.** As §7.3 — wait for concrete
   failures. Not worth extending the AST speculatively.

5. **Cryptol module output namespace.** A user's `Foo.cry` translates
   to what? Proposals:
   - `CryptolToLean.Foo.*` — nested under the support lib, matches
     Phase-1 namespace convention.
   - `UserCryptol.Foo.*` — separate top-level namespace for user code.
   - Just `Foo.*` — flat, no wrapper.

   Leaning toward **`CryptolToLean.Foo.*`** for symmetry with the
   `SAWCorePrelude` / `CryptolPrimitivesForSAWCore` siblings. Users
   who don't like it can `open CryptolToLean.Foo` or alias.

## 10. Success criteria for closing Phase 2

- `saw demo.saw` in `saw-lean-example/` produces four files (idBool,
  implRev, invol_prove0, eq_spec_prove0) plus a fifth (`Rev.lean`),
  analogous to the Rocq example's five outputs.
- `cd saw-core-lean/lean && lake build` succeeds with the generated
  `SAWCorePrelude.lean` and `CryptolPrimitivesForSAWCore.lean`
  committed.
- `out/idBool.lean`, `out/implRev.lean`, `out/Rev.lean` each elaborate
  cleanly under `lake env lean`.
- `out/invol_prove0.lean` and `out/eq_spec_prove0.lean` each elaborate
  with exactly one warning — the expected `sorry`.
- Generated content is regeneratable via the two new `write_lean_*`
  commands without manual editing.

If that holds, Phase 3 (`offline_lean` polish, test-suite port,
manual documentation) and Phase 4 (recursion, perf, proof automation)
are the remaining roadmap items.

## 11. What's deliberately *not* in this doc

- Detailed API for each of the ~50 primitives we expect to hand-write
  or rename. That belongs in the commit messages as each lands — the
  design-doc abstraction is "run the generator, fix what breaks,
  commit."
- A per-file line-by-line plan for the support lib. Write the files as
  the generator output tells us what shape they need.
- An audit response. The audit currently running will produce a
  separate set of findings; each gets triaged into either a Phase-1
  followup or a 2A–2E sub-step, not folded into this doc.
