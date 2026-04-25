# Stage 3: translator sketch for specialization

*Draft — 2026-04-23*

Follows Stage 2's validation that hand-specialized `implRev4`
elaborates in Lean. This document describes the translator changes
needed to emit that output automatically.

## 0. The core insight

The existing translator already handles every SAWCore construct
that appears in a normalized term: `Sort`, `Pi`, `Lambda`, `App`,
`Variable`, `Constant` (for axioms/primitives), `Recursor`, and
`FTermF`'s usual constructors. All we need is **one preprocessing
step**: run `scNormalize` on each top-level term before translating.

The Phase-1 "recursively translate bodies" machinery in
`translateConstant` can then go away, because after normalization
there are no `NoQualifier` defs left to translate bodies for —
they've all been unfolded.

## 1. Two architectural decisions up front

### Decision 1: Where does normalization happen?

**Option X: Upfront, in `writeLeanTerm` / `writeLeanCryptolModule`.**
The translator sees already-normalized terms. Entry-point code:

```haskell
writeLeanTerm name _notations skips path t = do
  sc <- getSharedContext
  mm <- io $ scGetModuleMap sc
  tp <- io $ scTypeOf sc t
  let unfold = shouldUnfoldName skips mm
  t'  <- io $ scNormalize sc unfold t
  tp' <- io $ scNormalize sc unfold tp
  case Lean.translateTermAsDeclImports config mm name t' tp' of
    …
```

**Option Y: Per-constant, inside `translateConstant`.** Only
normalize when about to recurse into a body.

**Choose X.** Simpler. Normalization is a closed operation; doing
it once at the boundary is cleaner than weaving it through the
walker. Also: `scNormalize` internally memoises on term indices, so
normalizing the top-level term normalizes all its subterms by
structural descent — we get the full normalization with one call.

### Decision 2: How are SAWCore primitives declared in the output?

After normalization, every surviving `Constant` reference is one of:
- An axiom (`AxiomQualifier` or `PrimQualifier` def, no body)
- An inductive data constructor (e.g. `Num.TCNum`, `Either.Left`)
- An inductive type name (e.g. `Num`, `Either`, `Nat`)
- An auto-generated recursor (e.g. `Num#rec1`, `Either#rec`)

**Option A: Inline in each translated file.** Every `writeLeanTerm`
output starts with a block of axioms/inductives for everything its
term transitively references.

**Option B: Handwritten `CryptolToLean.SAWCorePrimitives` support
module.** Declares all SAWCore primitives as axioms/inductives
once. Translated output just imports it and references.

**Choose B.** Clean output, matches the existing scaffolding
pattern (`SAWCoreScaffolding`, `SAWCorePreludeExtra`). The
handwritten primitive declarations are small and stable —
enumerated from the SAWCore Prelude's `primitive` / `axiom`
directives and its inductive `data` declarations.

Sketch of `CryptolToLean.SAWCorePrimitives`:

```lean
namespace CryptolToLean.SAWCorePrimitives

-- Inductives from Prelude.sawcore
inductive Either.{u, v} (α : Sort u) (β : Sort v) : Sort (max 1 (max u v)) where
  | Left  : α → Either α β
  | Right : β → Either α β

inductive Num : Type where
  | TCNum : Nat → Num
  | TCInf : Num

-- axioms / primitives
axiom Stream : Type → Type
axiom Integer : Type
axiom subNat : Nat → Nat → Nat
axiom addNat : Nat → Nat → Nat
axiom coerce : (α β : Type) → @Eq Type α β → α → β
axiom unsafeAssert.{u} : (α : Sort u) → (x y : α) → @Eq α x y
axiom error : (α : Type) → String → α
axiom gen : (n : Nat) → (α : Type) → (Nat → α) → Vec n α
axiom atWithDefault : (n : Nat) → (α : Type) → α → Vec n α → Nat → α
-- …etc

end CryptolToLean.SAWCorePrimitives
```

Universe-polymorphic where the SAWCore signature demands it (e.g.
`unsafeAssert : (a : sort 1) -> ...`), but these are the /only/
places we need polymorphism — the user-program's translated output
no longer has any.

## 2. Translator changes

### 2a. `SAWCoreLean.Lean.translateTermAsDeclImports` adds normalization

```haskell
translateTermAsDeclImports ::
  TranslationConfiguration -> ModuleMap -> Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann)
translateTermAsDeclImports configuration mm name t tp = do
  -- Normalize here, lifting IO to a pure Either via an unsafe escape
  -- — actually can't do this inside the Either monad, so normalization
  -- belongs at the writeLean* entry-point level (Option X above).
  ...
```

Actually, `scNormalize` is in IO. So normalization lives in the
`writeLeanTerm` / `writeLeanCryptolModule` entry points in
`saw-central/Exporter.hs`, not in the pure translator. That's
fine — the translator stays pure; the entry points preprocess.

### 2b. `SAWCentral.Prover.Exporter.writeLeanTerm` normalizes before translation

```haskell
writeLeanTerm name notations skips path t = do
  let configuration = leanTranslationConfiguration notations skips
  sc <- getSharedContext
  mm <- io $ scGetModuleMap sc

  -- Compute the unfold predicate: unfold everything except axioms,
  -- primitives, data constructors, recursors, and whatever the user
  -- asked to keep opaque via `skips`.
  skipIdxs <- mconcat <$> mapM (resolveName sc) skips
  let unfold nm = shouldUnfold mm skipIdxs nm

  t'  <- io $ scNormalize sc unfold t
  tp  <- io $ scTypeOf sc t'
  case Lean.translateTermAsDeclImports configuration mm
       (Lean.Ident (Text.unpack name)) t' tp of
    Left err -> …
    Right doc -> …
```

`shouldUnfold mm skipIdxs nm` is True iff:
- `nm` is not in `skipIdxs` (user's opaque list)
- `nm` is a `NoQualifier` def in `mm` (i.e., has a body)

It's False for: axioms, primitives, constructors, recursors, and
anything the user listed as opaque.

The "primitives whose SAWCore source says `primitive` but whose
Haskell implementation is a real reduction rule" list from
`normalize_term_opaque` (see `Builtins.hs:796-805`) — we probably
don't need that extra set for the Cryptol translation use case,
but worth revisiting if we see unexpected non-termination.

### 2c. `SAWCoreLean.Term.translateConstant` simplifies dramatically

Currently `translateConstant` does:
1. Dispatch via SpecialTreatment
2. For `ImportedName` (no treatment), translate the constant's body
   recursively and add a peer `def` to `topLevelDeclarations`.

After specialization, step 2 is **dead code** — every constant
reference is either in the treatment table or it's a
primitive/axiom/constructor/recursor that normalization left alone.
Axioms and inductives resolve via the `CryptolToLean.SAWCorePrimitives`
import.

New shape:

```haskell
translateConstant :: TermTranslationMonad m => Name -> m Lean.Term
translateConstant nm
  | ModuleIdentifier ident <- nameInfo nm =
      translateIdentWithArgs ident []
  | otherwise = do
      -- ImportedName with no SpecialTreatment: this should be rare
      -- after normalization — either the user's Cryptol file defines
      -- an axiom or we've hit a bug. Emit as qualified reference.
      let nm_str = Text.unpack (toShortName (nameInfo nm))
      pure (Lean.Var (escapeIdent (Lean.Ident nm_str)))
```

No more `topLevelDeclarations` pushes for body translations. The
state field can stay (still used for the letify-shared-subterms
pass, see §2d) but the "translate body" path goes away.

### 2d. Shared-subterm let-lifting still matters

SAWCore's shared representation means `normalize_term` output uses
let-bindings aggressively (observed in Stage 1:
`let x\`1 = Vec 8 Bool; x\`2 = Either Nat Nat; …`). The current
translator has a `translateTermLet` / shared-subterms pass that
lifts these into Lean `let`-bindings. Keep that mechanism.

### 2e. Universe handling simplifies back to concrete `Type`

With specialization, every `sort 0` in a user program's translated
output is at a concrete `Type 0` context. The P4 v2
universe-polymorphism machinery (SortVar, SortMax1Var, universe
lists on Decl) can stay in the AST as infrastructure but is rarely
exercised.

For the one case in the Stage 2 probe where universe polymorphism
*did* matter (`Num_rec1.{u}` in the coerce-proof), it's because
the `SAWCorePrimitives` file declares the recursor alias as
universe-polymorphic. The translator emits a plain `Num_rec1 (motive
:= fun _ => Type) …` and Lean infers `.{0}`. Fine.

`translateSort` goes back to:

```haskell
translateSort :: TermTranslationMonad m => Sort -> m Lean.Sort
translateSort s
  | s == propSort = pure Lean.Prop
  | otherwise     = pure Lean.Type
```

The same collapse as pre-P4. Approach-C's per-binder-fresh
universe allocation is no longer needed because we never emit a
polymorphic def in user output.

**Exception**: if the user hands a genuinely polymorphic Cryptol
term to `writeLeanTerm` (e.g. a `forall n, a. ...`-typed term),
the normalized output still has free type vars. We detect this and
either (a) fall back to the polymorphic path (preserving the P4 v2
machinery on the WIP branch) or (b) refuse with a clear error.
Ship (b) for simplicity; add (a) only if real users hit the need.

## 3. Output file shape

After specialization, a typical `writeLeanTerm` output looks like:

```lean
-- Auto-generated by saw-core-lean (specialization mode)
import CryptolToLean

noncomputable def implRev4 : Vec 4 (Vec 8 Bool) → Vec 4 (Vec 8 Bool) :=
  fun (xs : Vec 4 (Vec 8 Bool)) =>
    let x1 := CryptolToLean.SAWCoreVectors.Vec 8 Bool;
    let x2 := CryptolToLean.SAWCorePrimitives.Either Nat Nat;
    let x3 := CryptolToLean.SAWCorePrimitives.Num.TCNum 4;
    let x4 := CryptolToLean.SAWCorePrimitives.subNat 4 0;
    …
    (CryptolToLean.SAWCorePrimitives.coerce x8 x6 …)
    …
```

- One import line (`CryptolToLean`) bringing in scaffolding + primitives.
- One `def` per user-visible Cryptol/SAWCore name in the input.
- No auxiliary peer defs for Prelude constants — they live in
  `CryptolToLean.SAWCorePrimitives`.

Result: typical output shrinks from 50-100+ lines (current,
auto-translated Prelude inlined) to 20-40 lines (just the user's
logic).

## 4. Caching / memoisation

Since the normalized term is shared (SAWCore's hash-consing), the
translator should translate each distinct subterm once and bind it
to a `let`. The current `translateTermLet` pass does exactly this.
Keep.

No new caching needed for specialization: `scNormalize` itself
memoises, and the translator's letify pass handles the rest.

## 5. What changes for `offline_lean`

`offline_lean` emits a `def goal : Prop := …` followed by a
`theorem goal_holds := by sorry`. Under specialization:

- The goal term is SAWCore-normalized before translation.
- The emitted goal is self-contained (only references primitives in
  `CryptolToLean.SAWCorePrimitives`).
- The theorem stub is unchanged.

No structural changes; `writeLeanProp` follows the same pattern as
`writeLeanTerm` (normalize first, then translate).

## 6. What changes for `write_lean_cryptol_module`

A Cryptol module declares multiple named terms. Each gets a
normalized `writeLeanTerm`-style translation. The whole module
wraps in a `namespace Foo … end Foo` block as before. No structural
changes.

Subtle interaction: if two defs in the module reference a shared
Prelude constant, that constant still lives in
`CryptolToLean.SAWCorePrimitives`, so there's no duplication across
defs. Good.

## 7. Remove `write_lean_sawcore_prelude` and
`write_lean_cryptol_primitives_for_sawcore`

Before specialization, these commands translated the whole SAWCore
Prelude / Cryptol prelude as universe-polymorphic Lean libraries —
the idea being that user programs would import the resulting
`SAWCorePrelude.lean` and instantiate at use sites.

Under the specialization architecture, that design is dead. User
programs get self-contained output that imports a small
handwritten `CryptolToLean.SAWCorePrimitives` support module;
there's no role for an auto-translated prelude file.

**Remove both commands.** Reasons:

- No user-facing saw script references them except the debugging
  `gen-preludes.saw` I wrote.
- The output they produce does not elaborate in Lean and we've
  shown we can't make it elaborate without the universe
  machinery we're moving away from. Keeping them around pointing
  at known-broken output is a misleading artifact.
- They're surface area — docstrings, interpreter wiring,
  cabal-dep wiring, test-skip behaviour — for code that's not on
  any real user path.
- If we later want "dump the SAWCore prelude as Lean" as a
  debugging tool, we can add it back with a design matching the
  new architecture (likely emitting the primitives enumeration
  that goes into `SAWCorePrimitives.lean`).

The `SAWCoreLean.SAWModule` walker stays — it's still used by
`write_lean_cryptol_module` to walk the user's translated Cryptol
module. But `translateSAWModule` (the entry that wraps a whole
SAWCore `Module`) gets dropped.

Delete list:

- `SAWCentral.Prover.Exporter.writeLeanSAWCorePrelude`
- `SAWCentral.Prover.Exporter.writeLeanCryptolPrimitivesForSAWCore`
- `SAWScript.Interpreter.do_write_lean_sawcore_prelude`
- `SAWScript.Interpreter.do_write_lean_cryptol_primitives_for_sawcore`
- Their `prim` entries
- `SAWCoreLean.Lean.translateSAWModule` (entry point for the prelude walker)
- `saw-lean-example/gen-preludes.saw`

## 8. Support-lib file changes

### New: `CryptolToLean/SAWCorePrimitives.lean`

Handwritten enumeration of all SAWCore primitives used by typical
Cryptol output. ~60-100 lines. Derived from `Prelude.sawcore`'s
`primitive`/`axiom` declarations + visible data/inductive
declarations.

For Stage 4, I'd seed this from the Stage 2 probe
(`.tmp/stage2/ImplRev4.lean` lines 28-88) as a starting point, then
extend it as other demo programs surface additional primitives.

### Unchanged: `SAWCoreScaffolding`, `SAWCoreVectors`,
`SAWCoreBitvectors`, `SAWCorePreludeExtra`

These still serve their pre-specialization purposes. `Vec` binds
to std Vector; `bitvector` to `Vec n Bool`; `Inhabited`
universe-polymorphic class; `iteDep`/`ite` wrappers. All of these
are still used when `SpecialTreatment` entries map SAWCore names
to scaffolding primitives.

### Unchanged: `CryptolToLean.lean` root module

Re-exports scaffolding + `SAWCorePrimitives`. Adds the new import
line.

### Demoted: `SAWCorePrelude.lean` (auto-generated)

Kept as reference output but not imported from translated user
programs.

## 9. SpecialTreatment table simplifications

Under specialization, many `SpecialTreatment` entries become
redundant — the `normalize_term` pass unfolds them anyway. But
keeping them is fine:

- `mapsToCore "Bool"` etc. still trigger for constructor references
  (`Prelude.True` → `true`). Correct.
- `mapsToCoreExpl "Eq"` still needed — `Eq` is an inductive,
  survives normalization, and needs the Lean-core mapping.
- `mapsTo sawScaffoldingModule "Vec"` — same.
- `iteDep` family — handwritten in SAWCorePreludeExtra; `mapsTo`
  routes references there.
- `skip` entries for primitives whose target is in
  `SAWCorePrimitives.lean` — new entries needed for each primitive
  we enumerate.

Estimate: 10-20 new `mapsTo sawCorePrimitivesModule "foo"` entries
in the SpecialTreatment table. Mechanical.

## 10. What can go wrong

### 10a. Normalization loops

SAWCore's `scNormalize` has a fixpoint loop in `App`/`Constant`
reduction. If a Prelude def is recursive (via `Prelude.fix`), it
loops. BUT: `scNormalize`'s predicate-based unfolding gives us a
knob — we simply don't unfold `Prelude.fix` or any def that uses
it. The existing translator already rejects `Prelude.fix`-using
defs; propagate that to the unfold predicate.

Verify: Stage 4 probe should run on several Cryptol examples and
confirm none of them normalize into a loop.

### 10b. Size explosion

Stage 1 showed `implRev4` normalizes to ~35 lines. For a real SHA
verification, could it be much bigger?

Mitigation #1: SAWCore's shared terms mean repeated subterms share
structure. The emitted Lean `let` bindings preserve sharing, so a
subterm appearing 20 times in the surface form emits once.

Mitigation #2: If output size is still a concern, `normalize_term_opaque`
(with a user-chosen opaque list) lets us keep certain defs opaque.
The translator gets the opaque list via the user's `[String]`
argument to `writeLeanTerm`. Then those opaque constants stay as
references, and the translator emits them as... something — this is
where it gets complex, because we'd need a polymorphic peer def for
opaque defs. Defer for now; re-address if real users hit size
issues.

### 10c. `Eq#rec1` on non-trivial motives

The Stage 2 probe showed `Num_rec1 {motive := fun _ => Type} …` —
Lean inferred the universe. What about motives that construct
types with `sort k` for `k > 0` concretely? I haven't probed;
worth a test.

### 10d. Translator state field `_topLevelDeclarations`

Currently holds auxiliary defs from the pre-specialization
body-translation path. Under specialization it's empty. Either
remove the field or keep for future per-module features (like if
`writeLeanCryptolModule` needs to emit helper defs). Leaning keep,
harmlessly empty.

### 10e. P4 v2 universe machinery

AST fields (`universe lists`, `SortVar`, `SortMax1Var`,
`SortMax1Vars`) stay in the AST. They're used by
`write_lean_sawcore_prelude` (which we demote but keep emitting).
For `writeLeanTerm` in specialization mode, we emit empty universe
lists and `TypeLvl 0` sorts; the machinery is dormant.

## 11. Backport from `saw-core-lean-p6-wip`?

No. The WIP branch's universe-polymorphism attempts can stay
parked. If/when we need genuinely polymorphic user terms, we'll
unstash it.

## 12. Implementation steps for Stage 4

1. **Remove `write_lean_sawcore_prelude` and
   `write_lean_cryptol_primitives_for_sawcore`** per §7. This
   subtracts surface area up front so we're not dragging the
   polymorphic-library design alongside specialization.
2. **Create `CryptolToLean/SAWCorePrimitives.lean`** with
   ~20 axioms + ~5 inductives covering the `implRev4` use case.
   (Extend in later passes as other demos surface needs.)
3. **Add `scNormalize` preprocessing** to `writeLeanTerm`,
   `writeLeanProp`, `writeLeanCryptolModule` in
   `saw-central/Exporter.hs`. Detect residual free type variables
   after normalization and refuse with a clear error (D3).
4. **Revert `translateSort` to pre-P4 concrete behavior**
   (collapse non-`propSort` to `Lean.Type`). Since the prelude
   walker is gone, the P4 v2 universe-polymorphism machinery
   (SortVar, SortMax1Vars, universe lists on Decl) becomes
   dormant — we can remove those AST extensions in a follow-up
   cleanup, but keep them for the first pass to minimise churn.
5. **Simplify `translateConstant`** — remove body-translation path
   for `ImportedName`; all constants become references via the
   `SpecialTreatment` table or are axioms/inductives/recursors
   resolved via `SAWCorePrimitives`.
6. **Add `mapsTo sawCorePrimitivesModule`** entries for each
   primitive enumerated in step 2.
7. **Regenerate `saw-lean-example/demo.saw`**. Verify all four
   outputs (idBool, implRev, Rev, invol_prove0, eq_spec_prove0)
   elaborate under `lake env lean`.
8. **Update docs**: soundness doc to add "specialization" as the
   primary strategy; existing P4/P6 docs stay as history.

Order: step 1 removes surface area. Steps 2-3 produce raw
output. Steps 4-5 clean up. Step 6 makes output compile. Steps
7-8 validate and document.

## 13. Effort estimate

- **Stage 4 implementation: 1 day** for the translator changes +
  SAWCorePrimitives enumeration. Most of the work is in step 1
  (writing the primitives file) and step 5 (new SpecialTreatment
  entries).
- **Validation: 2-4 hours** running demos and verifying Lean
  elaboration.
- **Doc updates: 1 hour.**

Total: about a working day. De-risked by Stage 2's probe.

## 14. Summary

Specialization via `scNormalize` at the entry point + a handwritten
`SAWCorePrimitives.lean` support file gives us:
- Self-contained Lean output per user program
- No universe polymorphism at the user level
- No Prop/Type cumulativity concerns
- ~1 day of focused implementation work

The P4 v2 universe machinery and the P6 investigation work weren't
wasted — they're preserved as alternatives for the polymorphic-user
case (if we ever need it). The main branch cleanly reverts to
concrete-type emission with added normalization.

Decisions locked in after user review:

- **D1 ✓**: Normalize upfront in the `writeLean*` entry points;
  handwritten `CryptolToLean.SAWCorePrimitives.lean` declares all
  SAWCore primitives the translator emits references to.
- **D2 ✓**: Remove `write_lean_sawcore_prelude` and
  `write_lean_cryptol_primitives_for_sawcore`. They're dead weight
  under the specialization architecture; can be added back later
  with a new design if a real use case appears.
- **D3 ✓**: If a user's term retains free type variables after
  normalization, refuse with a clear `TranslationError`. A
  polymorphic-emission fallback lands only if real users need it.

Ready to implement.
