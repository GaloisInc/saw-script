# Target architecture for saw-core-lean (post-rearchitecting)

*2026-05-11. Successor to `2026-05-10_compositional-emission-design.md`.
Goes deeper on the **concrete shape** of the target system. Does
not propose a timeline — that's a separate agent's deliverable.*

## Definitive purpose

saw-core-lean exists to mirror the Rocq backend's user-visible feature
surface in Lean, with Lean's kernel as the checker. Proof-obligation
discharge is the primary verification workflow, but Cryptol-to-Lean
module translation remains in scope because it mirrors
`write_rocq_cryptol_module`. The design point is still the Rocq backend:
short emit functions (propToTerm -> translate -> write),
separately-emitted prelude / Cryptol-primitives / user-module files that
goal emissions link against, no normalization pass between SAW and the
translator.

This document specifies, for each of seven concerns, exactly what the
target architecture looks like.

---

## 1. Public SAWScript API surface

The Lean primitives mirror Rocq's `write_rocq_*` and `offline_rocq`
suite one-for-one. `offline_lean_skip` is removed; its existence was
a workaround for `scNormalizeForLean` hangs and goes away when
normalization goes away.

### 1.1 `offline_lean : String -> ProofScript ()`

Emits the current proof goal to a single Lean file. Path-relative
naming, like `offline_rocq`. Behaviour:

- runs `propToTerm` on the goal,
- abstracts any free SAWCore `Variable` nodes into outer Pi binders
  (Crucible-driven goals carry symbolic-input variables),
- calls `translateGoalAsDeclImports`,
- writes `<path>` with:
  - the preamble (imports + opens, see §5),
  - a `def <name> : Prop := …` for the goal,
  - a `theorem <name>_holds : <name> := by sorry` discharge stub.

What it lets the user do: drop a `prove_print (offline_lean
"goal.lean") {{ … }}` into any SAW driver, then open `goal.lean` in
Lean and discharge by hand.

### 1.2 `write_lean_term : String -> [(String, String)] -> [String] -> String -> Term -> TopLevel ()`

Direct term-to-Lean emission. Arguments: name, notation rewrites,
skip list, output path, term. Behaviour: like `offline_lean` minus
the goal/sorry stub — emits one `def` directly. Mirrors
`write_rocq_term`.

Use case: SAW-side term construction (`parse_core`, `term_apply`)
that needs Lean elaboration without a proof goal context. Skips
list is the only path for users to mark constants opaque under the
new architecture (and is rarely needed, because the auto-emitted
prelude resolves what `scNormalizeForLean` used to unfold).

### 1.3 `write_lean_saw_core_prelude : String -> [(String, String)] -> [String] -> TopLevel ()`

**New.** Mirror of `write_rocq_sawcore_prelude`. Walks the SAWCore
`Prelude` module and emits each non-rejected def as a Lean
declaration. Arguments: output path, notation renamings, skip list.

Output is a self-contained Lean file `SAWCorePreludeAuto.lean` (or
whatever the user names it) consisting of:
- the standard preamble (imports + opens),
- a `namespace SAWCorePrelude` block,
- one Lean `def` / `axiom` / `inductive` per non-skipped SAW prelude
  declaration,
- `end SAWCorePrelude`.

What it lets the user do: regenerate the auto-emitted prelude as a
build artifact. In the common case the user never calls it
directly — the file is checked in at `lean/CryptolToLean/Auto/
SAWCorePrelude.lean` and refreshed whenever SAWCore's prelude
changes. The primitive exists so the artifact can be regenerated
deterministically.

### 1.4 `write_lean_cryptol_primitives : String -> [(String, String)] -> [String] -> TopLevel ()`

**New.** Mirror of `write_rocq_cryptol_primitives_for_sawcore`.
Walks the Cryptol primitives module (`CryptolPrimitivesForSAWCore`)
and emits each non-rejected def as a Lean declaration. Same shape
as §1.3. Wraps output in `namespace CryptolPrimitives`.

### 1.5 `write_lean_cryptol_module : String -> String -> [(String, String)] -> [String] -> TopLevel ()`

Existing primitive. Stays. Translates a user `.cry` file to a Lean
namespace block. The internal normalize callback gets simplified to
`pure` (identity) — see §3 — but the API doesn't change.

### 1.6 What disappears

- `offline_lean_skip`: removed. Its sole purpose was managing
  `scNormalizeForLean`'s opaque set; with normalization gone, skips
  go through `write_lean_term`'s normal skips argument when needed.

### 1.7 What stays implicit but accessible

A debug helper (`dump_lean_residual_primitives`) for cataloguing
which prelude constants a goal references. Useful for triaging when
a goal references a constant neither the auto-emit nor
SpecialTreatment handles. Already exists; no change.

---

## 2. New emitters

### 2.1 `writeLeanSAWCorePrelude` (in `SAWCentral.Prover.Exporter`)

```haskell
writeLeanSAWCorePrelude ::
  FilePath ->            -- ^ output path
  [(Text, Text)] ->      -- ^ notation renamings
  [Text] ->              -- ^ ident skip list
  IO ()
writeLeanSAWCorePrelude outputFile notations skips = do
  sc  <- mkSharedContext
  ()  <- scLoadPreludeModule sc
  mm  <- scGetModuleMap sc
  m   <- scFindModule sc nameOfSAWCorePrelude
  let configuration = leanTranslationConfiguration notations skips
  m'  <- Lean.translateSAWModule sc configuration mm m
  let doc = vcat [ Lean.preamble False configuration, m' ]
  case outputFile of
    ""  -> print doc
    "-" -> print doc
    _   -> writeLeanFile outputFile (show doc)
```

Verbatim shape of `writeRocqSAWCorePrelude` modulo the `Lean.*`
module-translation entry point. The new piece is
`Lean.translateSAWModule`, which mirrors `Rocq.translateSAWModule`:

```haskell
-- in SAWCoreLean.Lean
translateSAWModule ::
  SharedContext -> TranslationConfiguration -> ModuleMap -> Module ->
  IO (Doc ann)
translateSAWModule sc cfg mm m = do
  decls <- mapM (SAWModule.translateDecl sc cfg (Just (moduleName m)) mm)
                (moduleDecls m)
  let nm = pretty (Text.intercalate "." (moduleNamePieces (moduleName m)))
  pure $ vsep $
    [ "namespace" <+> nm
    , ""
    ] ++ decls ++
    [ "end" <+> nm
    , ""
    ]
```

… and a new `SAWCoreLean.SAWModule.translateDecl` that mirrors the
Rocq counterpart but produces Lean `Decl`s.

#### How emission handles universes

Lean's non-cumulativity is the hard constraint (`archive/
2026-04-22_universe-internal-investigation.md`). The auto-emit
respects it via three rules:

1. **Per-binder fresh universe variables.** `translateSort`
   allocates a fresh `u_n` for each `sort k` occurrence in a binder
   position. The emitted `def` gathers these into its
   `.{u₀ u₁ …}` declaration. This is the `D1` option from the
   universe investigation — confidence: high.

2. **Explicit `.{…}` at call sites.** Each `Constant nm` reference
   in the emitted Lean uses `@nm.{u₀, …}` with levels determined by
   `scTypeOf` at the call site. This is the mathport pattern; it
   sidesteps Lean's universe-inference failures.

3. **PULift fallback.** Where universe unification still fails (Lean
   issue #2297-class), we emit a `PULift` (or `ULift`/`PLift`)
   bridge — produces a small overhead, eliminates the failure mode.

`polymorphismResidual` becomes a translator-internal gate (§7) that
fires only when neither auto-emit nor SpecialTreatment provides a
universe-polymorphic def for an offending reference.

#### File naming convention

By convention:

- `SAWCorePreludeAuto.lean` for the §1.3 emitter output.
- `CryptolPrimitivesAuto.lean` for the §1.4 emitter.
- The user picks the goal filename via `offline_lean`'s argument.

Both auto files live under `lean/CryptolToLean/Auto/` in the
checked-in tree:

```
lean/CryptolToLean/Auto/SAWCorePrelude.lean
lean/CryptolToLean/Auto/CryptolPrimitives.lean
```

They're regenerated as a build step (deterministic from SAW HEAD)
and verified by CI to match the committed copy.

#### What's imported

`SAWCorePreludeAuto.lean` opens with:

```lean
import CryptolToLean.SAWCorePrimitives
import CryptolToLean.SAWCorePreludeExtra
```

`CryptolPrimitivesAuto.lean` adds:

```lean
import CryptolToLean.Auto.SAWCorePrelude
```

Compile order is bottom-up: hand-written primitives →
auto-emitted prelude → auto-emitted Cryptol primitives →
hand-written proofs library → user goal file.

### 2.2 `SAWCoreLean.SAWModule` (new internal module)

Mirrors `SAWCoreRocq.SAWModule`. Public surface:

```haskell
module SAWCoreLean.SAWModule (translateDecl) where

translateDecl ::
  SharedContext ->
  TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  ModuleDecl ->
  IO (Doc ann)
```

Internally:
- `translateDataType` → Lean `inductive` block
- `translateDef` → Lean `def` / `axiom` based on `DefQualifier`
- SpecialTreatment entries with `DefSkip` produce a comment;
  `DefReplace` produces a verbatim snippet;
  `DefPreserve` / `DefRename` produce a Lean decl by translating
  the SAW def's type and body via existing `translateTerm`.

#### Axiom vs. def

The Rocq emitter maps `AxiomQualifier` and `PrimQualifier` to Rocq
`Axiom`. The Lean emitter does the same: `axiom <name> : <type>`.
This includes `error`, `coerce`, `unsafeAssert`, `fix`, etc. — but
SpecialTreatment (Layer 3) intercepts each before the axiom emission
fires, redirecting to the hand-tuned soundness-preserving overlay
(see §4 and §7 for L-2, L-3, L-5, L-8, L-17).

---

## 3. Changes to `translateGoalAsDeclImports` / `writeLeanProp`

### 3.1 `writeLeanProp` becomes minimal

The new shape:

```haskell
writeLeanProp ::
  Text -> [(Text, Text)] -> [Text] -> FilePath -> Prop ->
  TopLevel ()
writeLeanProp name notations skips path t = do
  let configuration = leanTranslationConfiguration notations skips
  sc <- getSharedContext
  mm <- io $ scGetModuleMap sc
  tmRaw <- io (propToTerm sc t)
  tm <- io $ do
          let frees = SC.getAllVars tmRaw
          if null frees
            then pure tmRaw
            else SC.scPiList sc frees tmRaw
  tp <- io $ scTypeOf sc tm
  case Lean.translateGoalAsDeclImports configuration mm
         (Lean.Ident (Text.unpack name)) tm tp of
    Left err -> do
      err' <- liftIO $ Lean.ppTranslationError sc err
      throwTopLevel $ "Error translating: " ++ Text.unpack err'
    Right doc -> io $ case path of
      ""  -> print doc
      "-" -> print doc
      _   -> writeLeanFile path (show doc)
```

What changed vs. the current code:
- **No `scNormalizeForLean`.** The goal goes to the translator
  un-normalized.
- **No `polymorphismResidual` gate at the SAW boundary.** The gate
  moves into the translator (§7).
- Free-variable abstraction (`scPiList`) stays — Crucible goals carry
  symbolic inputs.

`writeLeanTerm` mirrors this shape (drop normalize + boundary gate).

### 3.2 `translateGoalAsDeclImports` unchanged in shape

The function still produces `def` + `theorem … _holds := by sorry`.
Its inputs change: it accepts `Term`s that may reference Cryptol /
SAWCore prelude `Constant`s without unfolding.

### 3.3 What `translateTerm` accepts now

`translateTerm` (the recursive walk in `Term.hs`) needs to handle
`Constant n` references that point at SAWCore prelude defs whose
bodies were previously unfolded by `scNormalizeForLean`. Two cases:

1. **`Constant n` with `ModuleIdentifier ident` info.** Already
   handled: route to `translateIdentWithArgs ident []`. With the
   auto-emitted prelude in scope, the emitted Lean reference
   (`SAWCorePrelude.foo` or — if Layer 3 maps it — the hand-tuned
   target) resolves through Lean's normal name resolution.

2. **`Constant n` with `ImportedName` info (Cryptol-defined).**
   Already handled: emit the bare short name with `escapeIdent`.
   Resolves through the auto-emitted Cryptol module or the user's
   hand-written one (depending on what the user emitted).

### 3.4 `translateConstant` / `translateIdentWithArgs` deltas

Concrete edits in `SAWCoreLean.Term`:

- **`translateIdentWithArgs i args`:** when the ident has no
  SpecialTreatment entry (`atUseSite = UsePreserve` is the default
  catch-all for SAW prelude defs that the auto-emit covers), emit a
  qualified reference to the auto-emitted prelude. The qualifier is
  determined by the ident's `identModule`:
  - `SAWCorePrelude.foo` if the ident is in the SAWCore prelude
    module,
  - `CryptolPrimitives.foo` if in the Cryptol primitives module,
  - `<user-module>.foo` for user Cryptol module defs.

- **`translateConstant`:** for the `ImportedName` branch (Cryptol
  names that have no `ModuleIdentifier`), emit the bare short name
  in whatever namespace the caller's preamble has open. Already
  works this way; no change.

- **L-14 gate becomes resolution-aware.** The "missing
  SpecialTreatment" detector fires only when the ident has neither
  a SpecialTreatment entry **nor** appears in the active
  auto-emitted module set. The auto-emitted set is computed once
  by walking the SAWCore prelude + Cryptol primitives module maps.

### 3.5 Cryptol module translation

`SAWCoreLean.CryptolModule.translateCryptolModule` keeps its
signature but its `normalize` callback is no longer needed —
remove it from the signature, callers pass `pure` (or we eliminate
the arg entirely). The internal loop becomes verbatim Rocq-shaped:
walk `moduleDecls`, translate each, emit a `namespace` block.

---

## 4. What stays in SpecialTreatment

The current `SAWCoreLean/SpecialTreatment.hs` has ~250 entries. The
new architecture targets ~40 entries across the following categories.
Counts are approximate.

### 4.1 Native-type bindings (~12 entries)

Hand-tuned mappings to Lean's standard library where the auto-emit
would produce a less-ergonomic structural copy.

- `Bool`, `Nat`, `Integer`, `String`, `True`, `False`, `Eq`, `Refl`
  → Lean's `Bool` / `Nat` / `Int` / `String` / `Eq` / `Eq.refl`
- `Vec` → Lean `Vector` (or our `Vec`, depending on Phase 9
  resolution)
- `bitvector` and the BitVec operator family (`bvAdd`, `bvXor`,
  `bvMul`, `bvShl`, `bvLshr`, `bvAshr`, `bvNot`, `bvAnd`, `bvOr`,
  `bvSub`, `bvUlt`, `bvSlt`, `bvUle`, `bvSle`, `bvEq`, `bvNat`,
  `bvToNat`, `bvAt`, `bvUExt`, `bvSExt`, `bvConcat`, `bvTake`,
  `bvDrop`, `bvUDiv`, `bvURem`, `bvSDiv`, `bvSRem`) — Phase 9
  bindings to Lean's native `BitVec`.

### 4.2 Soundness-critical overrides (~10 entries)

The L-* lockdowns demand that these *not* go through auto-emit. Each
has a hand-tuned target that closes a specific Check class.

- `iteDep`, `iteDep_True`, `iteDep_False`, `ite` → hand-written
  versions in `SAWCorePreludeExtra` (L-16; Bool#rec case
  permutation).
- `error`, `error_unrestricted` → two-tier (L-17; the
  `Inhabited`-constrained `error` vs. the unrestricted axiom).
- `coerce` → axiom matching SAW's exact shape (L-8).
- `unsafeAssert` → axiom matching SAW's exact shape (L-2).
- `Prelude.fix` → `UseReject` with the L-5 rejection rationale.
  Even though the translator intercepts `fix` for recognized
  recursion shapes (StreamCorec, BoundedVecFold, etc.), the
  *fallback* must reject — and SpecialTreatment is the place where
  the reject is catalogued and tested.
- A handful of recursor axiomatizations whose SAW shape is unsound
  if defined (L-3 auto-derives some; a small set stays
  hand-curated).

### 4.3 Corecursion lowerings (~5 entries)

The Phase 5 / 5b recognition shapes route through `classifyFix` in
`SAWCoreLean.Term`, so they don't have direct SpecialTreatment
entries by name. But the support library — `mkStreamFix`,
`mkStreamFixPair`, `streamScanl`, `cryptolIterate` — appears in
SpecialTreatment as `mapsTo` entries pointing into
`SAWCorePreludeExtra`. About 5 entries:

- `streamScanl` → `SAWCorePreludeExtra.streamScanl`
- `cryptolIterate` (synthetic — produced by `lowerPolyStreamIterate`)
- `mkStreamFix`, `mkStreamFixPair` (synthetic — produced by
  `lowerStreamCorec`, `lowerPairStreamCorec`)
- `MkStream`, `streamGet` if their auto-emit form is suboptimal.

### 4.4 Datatype shape adapters (~8 entries)

Where SAW's constructor / recursor shape differs from what Lean's
auto-derived versions provide. Mostly the `Pair` / `Either` / `Num`
family.

- `Num`, `TCNum`, `TCInf` → primitives `Num` (Cryptol Nat-or-Inf)
- `UnitType`, `Unit` → `UnitType`
- `PairType`, `PairValue`, `Pair_fst`, `Pair_snd`, `PairType1`,
  `PairValue1` (the SAW-level pair-of-pairs)
- `Either`, `Left`, `Right`, `Stream`

These could in principle migrate to auto-emit, but two
considerations keep them hand-tuned:
- they appear in `SAWCorePrimitives.lean` (load-bearing for
  BitVec / pair structural lemmas);
- the constructor `@`-explicit-arg pattern (L-9) is easier to keep
  pinned with named SpecialTreatment entries than as a translator-
  internal flag.

### 4.5 Cryptol class dictionaries (~5 entries, target)

The Cryptol class dictionaries (`PRing`, `PEq`, `PCmp`, `PLogic`,
`PIntegral`) currently appear in SpecialTreatment as map-to entries.
Open task #167 (CG-2) covers proper handling; for now we keep
hand-tuned entries until that task lands.

### 4.6 Total count

Rough breakdown:
- 12 native-type bindings
- 10 soundness overrides
- 5 corecursion lowerings
- 8 datatype adapters
- 5 class dictionaries
- ≈ 40 entries.

The current ~250 shrinks by 5x once the auto-emit absorbs the
load-bearing prelude bulk. The remaining ~210 entries get deleted
along with the dead code in `Term.hs` that handled their bespoke
emission.

---

## 5. Lake project structure

### 5.1 Target file layout

```
lean/
├── lakefile.toml
├── lean-toolchain
├── CryptolToLean.lean                ─ root (hand-written, stays)
└── CryptolToLean/
    ├── SAWCoreScaffolding.lean       ─ hand-written, stays
    ├── SAWCoreVectors.lean           ─ hand-written, stays
    ├── SAWCoreBitvectors.lean        ─ hand-written, stays
    ├── SAWCorePrimitives.lean        ─ hand-written, stays
    ├── SAWCorePreludeExtra.lean      ─ hand-written, stays
    ├── SAWCoreBitvectors_proofs.lean ─ hand-written, stays
    ├── SAWCorePrelude_proofs.lean    ─ hand-written, stays
    ├── Tactics.lean                  ─ hand-written, stays
    └── Auto/
        ├── SAWCorePrelude.lean       ─ AUTO-GENERATED (new)
        └── CryptolPrimitives.lean    ─ AUTO-GENERATED (new)
```

### 5.2 Compile order

Bottom-up dependency chain:

1. `SAWCoreScaffolding.lean` (base axioms / aliases)
2. `SAWCoreVectors.lean` (Vec / Vector definitions)
3. `SAWCoreBitvectors.lean` (BitVec operator names)
4. `SAWCorePrimitives.lean` (Pair, Either, Stream, Num, Unit)
5. `SAWCorePreludeExtra.lean` (iteDep, ite, error two-tier,
   mkStreamFix*, streamScanl, cryptolIterate)
6. `Auto/SAWCorePrelude.lean` (auto-emitted prelude defs)
7. `Auto/CryptolPrimitives.lean` (auto-emitted Cryptol primitives)
8. `SAWCoreBitvectors_proofs.lean` (bridge lemmas over BitVec)
9. `SAWCorePrelude_proofs.lean` (bridge lemmas over prelude)
10. `Tactics.lean` (proof-script helpers)
11. `CryptolToLean.lean` (re-export root)

Then user emissions:

```
<project>/SAWGeneratedPrelude.lean  -- optional regen artifact
<project>/SAWGeneratedCryptol.lean  -- optional regen artifact
<project>/MyModule.lean             -- write_lean_cryptol_module output
<project>/GoalFoo.lean              -- offline_lean output
<project>/MyProofs.lean             -- hand-written discharge
```

### 5.3 What CryptolToLean.lean re-exports

```lean
/- Root module: re-exports the hand-written support library and the
   auto-emitted layers. User goal files import this single module. -/

import CryptolToLean.SAWCoreScaffolding
import CryptolToLean.SAWCoreVectors
import CryptolToLean.SAWCoreBitvectors
import CryptolToLean.SAWCorePrimitives
import CryptolToLean.SAWCorePreludeExtra
import CryptolToLean.Auto.SAWCorePrelude
import CryptolToLean.Auto.CryptolPrimitives
import CryptolToLean.SAWCoreBitvectors_proofs
import CryptolToLean.SAWCorePrelude_proofs
import CryptolToLean.Tactics
```

A user's goal file imports just `CryptolToLean` and one or more user
Cryptol-module outputs.

### 5.4 Auto-regeneration discipline

The auto-emitted files are **checked in** to the repo. CI runs
`saw -B regenerate_auto.saw` and `diff -u` against the committed
copies; any drift fails CI loudly. This:

- avoids forcing every user to have a SAW build to compile the
  library,
- makes auto-emit changes visible at code review,
- lets the test suite cite specific line numbers in stable files.

The `regenerate_auto.saw` driver invokes
`write_lean_saw_core_prelude` and `write_lean_cryptol_primitives`.

---

## 6. End-to-end discharge flow

Worked example: the user verifies the ChaCha20 `core` function in
LLVM with eight `qround` overrides, then discharges in Lean.

### 6.1 SAW driver (chacha20_core.saw)

```saw
import "chacha20.cry";

let qround = llvm_extract m "qround";
let core   = llvm_extract m "chacha_core";

q1 <- llvm_verify m "qround" [] false qround_spec abc;
…
q8 <- llvm_verify m "qround" [] false qround_spec abc;

prove_print
  (do {
     simplify (cryptol_ss ());
     offline_lean "ChaCha20Core.lean";
   })
  (llvm_verify m "chacha_core" [q1,q2,…,q8] false core_spec
                (do { simplify (cryptol_ss ()); offline_lean "..."; }));
```

### 6.2 What each step produces

1. The user's repo already has `Auto/SAWCorePrelude.lean` and
   `Auto/CryptolPrimitives.lean` checked in (regenerated by CI).
2. `llvm_verify` produces obligations after the `qround` overrides
   are applied. Each obligation references `chacha20.qround`,
   `chacha20.cdround`, `chacha20.core`, Cryptol-prelude `seq` /
   `ecAt` / `ecPlus`, and SAWCore-prelude `coerce` / `ite` / etc.
3. The compositional override structure means `qround` calls in the
   `core` obligation **stay as references** to `chacha20.qround`
   — they don't unfold (this is the override-driven structure
   step 1 of task #179 validated).
4. `offline_lean "ChaCha20Core.lean"` emits a single Lean file.

### 6.3 The emitted file

```lean
/- Mandatory imports from saw-core-lean -/
import CryptolToLean
import ChaCha20         -- user's write_lean_cryptol_module output

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

/- Code generated by saw-core-lean -/

def ChaCha20Core_goal : Prop :=
  ∀ (block : BitVec 512) (key : BitVec 256) (nonce : BitVec 96)
    (ctr : BitVec 32),
    ChaCha20.core block key nonce ctr =
    ChaCha20.cdround_compose key nonce ctr block

theorem ChaCha20Core_goal_holds : ChaCha20Core_goal := by
  sorry
```

### 6.4 The user's discharge file

```lean
import «ChaCha20Core»

theorem ChaCha20Core_goal_discharge : ChaCha20Core_goal := by
  intro block key nonce ctr
  unfold ChaCha20.core ChaCha20.cdround_compose
  simp [ChaCha20.qround_def, ChaCha20.cdround_def]
  -- … goal reduces to a pure structural equality over the qround
  -- composition. Use the bridge lemmas:
  rw [foldl_eq_natRec_atWithDefault]
  rfl
```

The discharge file does **not** import `ChaCha20Core` to overwrite
the goal stub — it states the same proposition and proves it. SAW
treats the proof-script side as the user's responsibility; the
`sorry` in `ChaCha20Core.lean` is a scaffold the user replaces in
place.

### 6.5 What each architectural piece contributed

- `Auto/SAWCorePrelude.lean` provides the un-mapped SAWCore prelude
  defs (e.g. `seq` is a `Vec` indexing operator now mapped to
  whatever the auto-emit produced; user proofs unfold with
  `unfold SAWCorePrelude.seq`).
- `Auto/CryptolPrimitives.lean` provides `ecAt`, `ecPlus`, `eq` etc.
- `ChaCha20.lean` (from `write_lean_cryptol_module`) provides the
  user functions `qround`, `cdround`, `core` as Lean defs.
- `SAWCorePreludeExtra.lean` provides `cryptolIterate` (needed
  because `core` uses a Cryptol comprehension that lowers to the
  `cryptolIterate` shape).
- `SAWCorePrelude_proofs.lean` provides
  `foldl_eq_natRec_atWithDefault` and friends for the discharge.
- `SAWCoreBitvectors_proofs.lean` provides BitVec-shape lemmas
  (`bvAdd_comm`, etc.).
- The translator core in `Term.hs` produced the goal Prop without
  inlining anything.

This is the validation that the architecture delivers: a goal
referencing 320 nested `qround` invocations (from §3.1 of the
2026-05-10 design) emits in O(1) translator time, against a fixed
library that handles every name resolution.

---

## 7. Soundness preservation table

Every soundness property pinned by an L-* lockdown carries over.
Where it lives under the new architecture:

| L-# | Property | Survival path under new architecture |
|---|---|---|
| L-1 | Reject sort k≥1 binders that the auto-emit can't cover | Moves from `polymorphismResidual` at the SAW boundary into the translator: rejects only when the binder's universe shape is not covered by an auto-emitted polymorphic def (or a SpecialTreatment override). Diagnostic stays. |
| L-2 | `unsafeAssert` axiom shape matches SAW exactly | Stays in SpecialTreatment (§4.2). Hand-tuned `axiom unsafeAssert : …` in `SAWCorePreludeExtra` matches the SAW shape; auto-emit can't produce because SAW marks it `PrimQualifier`. |
| L-3 | Auto-derive opacity for unsound recursor types | The translator's recursor-emission path checks the recursor's SAW type before emitting; unsound shapes (e.g. `Bool#rec` for `Sort k`) become axioms in the auto-emitted prelude. Same logic, runs at auto-emit time. Tested by re-running the L-3 audit over the auto-emitted file. |
| L-4 | Vec ctor and rec not reachable | Auto-emit produces `Vec` as a SAW-level inductive but SpecialTreatment (§4.1) overrides it with `Vector` (or our `Vec`). The SAW-level ctor / rec never appears at use sites. |
| L-5 | `fix` rejected at SAW boundary | `Prelude.fix` → `UseReject` in SpecialTreatment (§4.2). The auto-emit doesn't override this — the SpecialTreatment treatment fires *before* `translateDef` runs, producing a comment in the auto-emitted file ("Prelude.fix was skipped") and rejecting at every use site that doesn't match a `classifyFix` recognizer. |
| L-6 | `scNormalize` 100-iter cap fails loud | Becomes vacuous in the default path (no `scNormalizeForLean` call). The cap stays in the codebase for any future opt-in `goal_normalize` primitive — but it's no longer in `writeLeanProp`. The test remains as a regression guard against accidentally reintroducing a normalize step without the cap. |
| L-7 | `iteDep` / `ite` case-permutation pinned at Haskell side | Stays in SpecialTreatment (§4.2) with `mapsTo` to `SAWCorePreludeExtra`. The hand-tuned Lean defs carry the case swap; auto-emit doesn't touch these. |
| L-8 | `coerce` axiom shape | Same shape as L-2. SpecialTreatment override; hand-tuned axiom in `SAWCorePreludeExtra`. |
| L-9 | `@`-prefix on constructor/recursor heads | Becomes a translator-internal emission rule (already is): `isCtor` check in `originalDispatch`. Re-tested over auto-emitted ctors. |
| L-10 | `translateSort` universe-collapse contract pinned | **Replaced** by the per-binder fresh-universe rule from §2.1. The contract changes from "collapse to Type" to "fresh universe variable per binder occurrence, explicit `.{…}` at call sites." New regression test pins the new behaviour. |
| L-11 | `escapeIdent` identifier safety | Unchanged. Routine emission detail. |
| L-12 | `write_lean_cryptol_module` passes every gate | Auto-emit pipeline must respect every gate. Implementation: each of `writeLeanSAWCorePrelude` and `writeLeanCryptolPrimitives` runs `polymorphismResidual` on each emitted def's type before emission (with the §7-L-1 caveat that the check is resolution-aware). L-12 test extends to cover the new emitters. |
| L-13 | Every boundary in the 2026-04-24 doc has a regression test | The doc gets updated to reflect the new architecture; each boundary's regression test re-runs over the new pipeline. New boundaries (auto-emit per-module, auto-regenerate vs. checked-in diff) get their own tests. |
| L-14 | Auto-detect missing SpecialTreatment entries at startup | **Reshaped.** Becomes "reject only if neither the auto-emit nor SpecialTreatment provides a resolution." Implementation: the startup audit computes the set of names covered by auto-emit (union of SAWCore prelude + Cryptol primitives module decl names) and the set covered by SpecialTreatment; warns/fails only when both are empty for a referenced name. |
| L-15 | Soundness audit runs in CI | Unchanged. Runs over the new architecture as a regression. |
| L-16 | `Bool#rec` emission swap | Stays in SpecialTreatment (§4.2). Auto-emit would re-introduce the swap because the SAWCore `Bool` ctor order is `True; False;`. The SpecialTreatment override redirects every reference to `SAWCorePreludeExtra.iteDep` / `ite`, which carry the manual swap. |
| L-17 | `error` two-tier | Stays in SpecialTreatment (§4.2). Auto-emit produces `error_unrestricted` as the axiom (matching SAW's `error : (α : sort 1) → String → α`). The Inhabited-constrained `error` lives in `SAWCorePreludeExtra` and SpecialTreatment redirects user references to it. The auto-emitted `error_unrestricted` is reachable only via `parse_core` insertion. |

### 7.1 New residual-trust items

The new architecture introduces two new trust boundaries:

1. **Auto-regeneration is deterministic and CI-checked.** A user
   compiles against the committed `Auto/*.lean`; CI verifies
   `saw regenerate_auto.saw && diff` against the committed copy.
   Trust failure: a non-conforming / buggy patch to the auto-emitter
   could ship a different committed file. Mitigation: CI diff;
   reviewer attention on `Auto/*.lean` changes; per-file
   regeneration test in the soundness CI job.

2. **Universe-explicit emission is correct.** The new
   `translateSort` (per-binder fresh) plus call-site `.{…}`
   discipline must produce universe-correct Lean — anything else
   either fails Lean elaboration loudly (safe) or silently picks
   the wrong instance (unsafe). The unsafe failure mode is
   theoretical: Lean's universe checker is decidable, so a
   wrong-universe instance would manifest as an elaboration error
   on first use. The auto-emitted prelude file compiling standalone
   is the primary signal.

Both go in the `2026-05-02_residual-trust.md` catalog.

---

## Summary

The target architecture is the Rocq design template applied to Lean,
with three concessions for Lean's universe non-cumulativity:

1. Per-binder fresh universe variables in `translateSort`,
2. Explicit `.{…}` at every call site,
3. PULift fallback for unification gaps.

The Haskell side shrinks dramatically (`scNormalizeForLean` moves
to an opt-in primitive, SpecialTreatment drops from ~250 to ~40
entries, dead emission code goes). The Lean side gains two
auto-emitted layers under `lean/CryptolToLean/Auto/`, checked in
and CI-verified. The discharge flow is: emit goal file →
`import CryptolToLean` → discharge with tactics over the same
bridge-lemma library we already have.

Every L-* lockdown carries over, with L-1, L-10, L-14 reshaped to
fit the auto-emit pipeline; L-6 becomes a guard on a path that
default-off; L-3 moves to auto-emit time. The architecture meets the
definitive purpose: SAW proof obligations discharged in Lean's
kernel, scaling to obligations that the current normalize-then-
translate path can't fit through.
