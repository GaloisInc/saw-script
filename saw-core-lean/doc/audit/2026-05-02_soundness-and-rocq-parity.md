# Soundness + Rocq Parity Audit
*2026-05-02*

Scope: `saw-core-lean/` translator + `lean/CryptolToLean/` support
library; `saw-central/src/SAWCentral/Prover/Exporter.hs` integration;
comparison with `saw-core-rocq/`. Read-only audit. Citations are
`file:line` relative to the saw-script repo.

## Summary

- The four declared soundness gates are real and enforced
  (`UnsoundRecursor` for Nat/Pos, `polymorphismResidual`,
  `scNormalizeForLean` 100-iter cap, `error.{u} : Sort (u+1)`),
  but **`polymorphismResidual` only inspects the outer pi-spine** of
  the term's type, missing nested `sort k≥1` binders (S-1).
- `unsafeAssert` is faithful at every translator-emitted use, but the
  Lean axiom is universe-polymorphic where SAW's is `sort 1`-only.
  Hand-written-Lean attack surface, not translator-emitted (S-2).
- `discoverNatRecReachers` covers `Nat#rec`/`Pos#rec` directly but
  **does not auto-derive opacity for `Z#rec`, `AccessibleNat#rec`,
  `AccessiblePos#rec`** — only the textual `leanOpaqueBuiltins` list
  covers these. A SAWCore Prelude addition introducing a new def with
  one of those recursors would not be picked up automatically (S-3).
- Rocq parity gaps that matter: **no `translateSAWModule` on the Lean
  side** (so no `write_lean_sawcore_prelude`,
  `write_lean_cryptol_primitives_for_sawcore` prims), no `Fix` /
  recursive-def support, no `IntMod`/`Rational`/`IsLeNat`/`Maybe`/
  `List`/`Void` SpecialTreatment entries, plus a long tail of
  un-mapped Nat/Pos/Z arithmetic the nat-mapping audit already lists.
- The `error.{u}` Prop hole flagged in the 2026-04-24 audit is closed
  (current code is `Sort (u+1)`). ✓

## Soundness findings

### What's solid

- `UnsoundRecursor` guard for SAW Nat/Pos at
  `saw-core-lean/src/SAWCoreLean/Term.hs:580-597`. Throws before
  emitting `@Nat.rec`/`@Pos.rec` whose branch shapes diverge from
  Lean's auto-generated recursors. Pinned by
  `intTests/test_lean_soundness_natrec/`.
- `polymorphismResidual` D3 check at
  `saw-central/src/SAWCentral/Prover/Exporter.hs:788-802`, called from
  `writeLeanTerm:817` and `writeLeanProp:843`. Pinned by
  `intTests/test_lean_soundness_polymorphic/`.
- `scNormalizeForLean` (`Exporter.hs:546-569`): iterates
  `scNormalize` to a fixed point with a 100-iteration `fail`-loud
  cap. Termination check uses `termIndex` equality.
- `error.{u} : (α : Sort (u+1)) → String → α` at
  `lean/CryptolToLean/SAWCorePrimitives.lean:270`: excludes `Prop` by
  construction. Pinned by `intTests/test_lean_soundness_error_prop/`.
- `iteDep` / `ite` realisations at
  `lean/CryptolToLean/SAWCorePreludeExtra.lean:40-58`: the case-order
  permutation is correct (SAW: True-first; Lean's `Bool.rec`:
  False-first), and the `rfl`-proven reduction lemmas pin both sides.
- `discoverNatRecReachers` (`Exporter.hs:653-700`) walks all module
  defs, marks the body opaque if its *direct* subterms contain
  `Nat#rec`/`Pos#rec`. Comment explains why the walk should NOT
  recurse through `Constant` references — adjacent opacity prevents
  inner recursors from surfacing during normalization.
- `leanOpaqueBuiltins` (`Exporter.hs:721-776`) extends the auto-derive
  with `subNZ`, `ZtoNat`, the Bool-Vec bitvector defs, and the
  `Pair_fst`/`Pair_snd` projection wrappers.
- `coerce` is faithful: `(α β : Type) → @Eq Type α β → α → β`
  (`SAWCorePrimitives.lean:250`) matches SAW's `(a b : sort 0)`
  exactly, not universe-polymorphic.
- The auto-`@`-prefix on constructor uses (`Term.hs:315-318`) and
  recursor heads (`Term.hs:602-603`) forces SAW's
  positional-explicit argument list through Lean's auto-implicits,
  preventing silent mis-application.

### Gaps / risks

#### S-1. `polymorphismResidual` only checks outer pi-spine

`Exporter.hs:790`: `let (params, _body) = asPiList tp`. `asPiList`
(`saw-core/src/SAWCore/Recognizer.hs:380`) walks only the outer
pi-spine. A type like `(f : (α : sort 1) -> β) -> γ` has its
`sort 1` binder nested inside an argument type and so escapes.
`translateSort` (`Term.hs:148-151`) collapses every non-`Prop` sort
to `Lean.Type` — silently weakening the universe. Reachable from a
higher-order term taking a polymorphic-function argument; rare in
Cryptol practice but possible. Severity: medium. No test exercises
it.

#### S-2. `unsafeAssert` axiom is broader than SAW's

`SAWCorePrimitives.lean:255`:
`axiom unsafeAssert.{u} : (α : Sort u) → (x y : α) → @Eq α x y`.
SAW: `(a : sort 1) -> (x y : a) -> Eq a x y`. The Lean form admits
`α : Prop` (vacuous, since `Eq` on Prop follows from proof
irrelevance — no inconsistency) and `α : Type k>0` (no
translator-emitted use can reach it because `translateSort`
collapses all sorts to `Type 0`). Translator-reachable use is sound.
Hand-written-Lean attack surface: a downstream user can assert
function extensionality etc. without SAW vouching for it. The
2026-04-24 audit Caveat 1 considered the broader shape acceptable
because `unsafeAssert` is globally available to translated theorems
anyway; worth confirming this is the right call. A
parallel-with-`error` tightening to `Sort (u+1)` is conservative.
Severity: low; documented and bounded.

#### S-3. Auto-derived opacity misses `Z#rec`, `AccessibleNat#rec`, `AccessiblePos#rec`

`discoverNatRecReachers` (`Exporter.hs:653-700`) only matches
`Nat#rec`/`Pos#rec`. The textual list compensates for the known
surface (`subNZ`, `ZtoNat`, `AccessibleNat_all` per
`Exporter.hs:737-762`), but a future Prelude addition introducing a
new `Z#rec`-using or `Accessible*#rec`-using def would not be
auto-detected. Result per nat-mapping audit §3.3: loud Lean-time
elaboration failure (no Lean target for those types). Fail-closed,
but not at the SAW level the `UnsoundRecursor` discipline asks for.
Severity: low.

#### S-4. `Vec n α := Vector α n` exposes Lean's `Vector.mk`

Documented in `2026-04-24_audit-primitives-fidelity.md` Caveat 3.
`SAWCoreVectors.lean:14`. Hand-written Lean proofs can pattern-match
via `Vector.mk` / `Vector.rec`, reaching beyond SAW's abstraction.
Translator never emits these constructors, so translated-output
soundness is unaffected. Same shape as Rocq's `Vector` binding;
documented and accepted.

#### S-5. `Prelude.fix` rejection is not at the SAW translator boundary

The status doc and the soundness boundaries doc claim "`Prelude.fix`
is rejected by the translator". There is **no explicit refusal** in
`saw-core-lean/src/`: SAW's `fix` is `primitive`, `scNormalize` does
not unfold it, the translator hits a `Constant` reference with no
matching `SpecialTreatment`, and emits
`CryptolToLean.SAWCorePrelude.fix` — a non-existent name. Failure
surfaces at `lake env lean` time, not at `writeLeanTerm`. Rocq's
`("fix", skip)` (`saw-core-rocq/.../SpecialTreatment.hs:245`) has
the same downstream effect, but Rocq's `Term.hs:653` *also* explicitly
matches `"Prelude.fix"` and throws `badTerm`. Severity: low.

#### S-6. `unsafeAssertBVULt`, `unsafeAssertBVULe` not mapped

SAW Prelude axiomatises both at `Prelude.sawcore:2391-2393`. Rocq
routes them through `solveUnsafeAssertBVULt` /
`solveUnsafeAssertBVULe` tactics
(`saw-core-rocq/.../SpecialTreatment.hs:248-249`). Lean has no
entries; reachable terms fail at Lean elaboration. No soundness
violation; surface gap.

## Rocq parity findings

### Reached parity

- Top-level entries `translateTermAsDeclImports`,
  `translateCryptolModule` present in both with matching signatures
  (Lean threads a `normalize :: Term -> IO Term` callback for
  specialization).
- `preamble`, `escapeIdent`, `moduleDeclName`,
  `translateModuleName` all shaped equivalently
  (`Lean.hs:54-69` ↔ `Rocq.hs:51-67`).
- `TranslationError` constructors mirror Rocq one-to-one
  (`Monad.hs:42-60`); Lean adds `UnderAppliedMacro` and
  `UnsoundRecursor`.
- Special-treatment combinators `mapsTo`, `mapsToCore` (Lean only),
  `realize`, `rename`, `replace`, `replaceDropArgs`, `skip` mirror
  Rocq's.
- `Either`, `PairType`, `RecordType`, `EmptyType`, `UnitType`,
  `Stream`, `Eq`/`Refl`, `Bool`, `Nat`/`Zero`/`Succ` (with
  literal-collapse macros for `Bit0`/`Bit1`/`NatPos`/`One`),
  `Integer`+ops, `bitvector`+ops (Lean's surface broader than
  Rocq's: `bvugt`/`bvuge`/`bvPopcount`/`bvCountLeadingZeros`/
  `bvCountTrailingZeros` are mapped where Rocq skips them),
  `Vec`, `gen`, `atWithDefault`, `foldr`/`foldl`, `coerce`,
  `unsafeAssert`, `error`, `iteDep`/`ite` family — all present with
  semantically-matching realisations.
- Per-translator entry points `writeLean*` mirror `writeRocq*`
  shapes in `Exporter.hs`; SAWScript prims `write_lean_term`,
  `offline_lean`, `write_lean_cryptol_module` mirror `write_rocq_*`/
  `offline_rocq` (`Interpreter.hs:5249-5290`).
- `intTests/test_lean_*` covers all but ~2 of Rocq's
  `otherTests/saw-core-rocq/` test fixtures after the
  `otherTests/saw-core-lean/` build-out — the 2026-05-01 status
  doc's "9 unmirrored" is now stale; only `test_cryptol_module_sha512`
  and a pinned-`test_offline_*` pair remain genuinely missing.

### Gaps

#### P-1. No `translateSAWModule` / `SAWModule.hs` on the Lean side

Rocq has `saw-core-rocq/src/SAWCoreRocq/SAWModule.hs` (208 LoC) and
exposes `translateSAWModule` from `Rocq.hs:82-90`. Called by
`writeRocqSAWCorePrelude` and
`writeRocqCryptolPrimitivesForSAWCore` (`Exporter.hs:951-990`):
walks SAW `moduleDecls`, emits `Module ... End` with each
`TypeDecl` → Rocq `Inductive`, `DefDecl` → `Definition`/`Axiom`,
`InjectCodeDecl` → inline snippet. Wired as
`write_rocq_sawcore_prelude` and
`write_rocq_cryptol_primitives_for_sawcore` (`Interpreter.hs:5183-5230`).

Lean has no analog. `Language.Lean.AST` supports `InductiveDecl`
shapes (`AST.hs:171-179`) but no construction site exists in
`Term.hs`/`CryptolModule.hs` — only `Lean.Definition` is emitted.
Consequences: no `write_lean_sawcore_prelude` /
`write_lean_cryptol_primitives_for_sawcore` prims; no Lean
realisation for SAWCore `inject "Lean"` snippets if a user adds them;
no "compile a `.sawcore` module to Lean" workflow. Severity: medium.
Specialization design intentionally sidesteps full module emission,
but the capability gap is real.

#### P-2. Rocq SpecialTreatment entries with no Lean equivalent

Comparing
`saw-core-rocq/src/SAWCoreRocq/SpecialTreatment.hs:235-558` against
`saw-core-lean/src/SAWCoreLean/SpecialTreatment.hs:287-458`:

- **Logic**: `Void`, `and`/`or`/`xor`/`not`/`boolEq` (and `_eq`
  lemmas), `Pair__rec`, `fst`/`snd`, `Eq__rec`.
- **SAW unsafe corners**: `sawLet`, `unsafeCoerce`,
  `unsafeCoerce_same`, `unsafeAssertBVULt`/`Le`, `coerce__def`,
  `coerce__eq`, `uip`.
- **Strings**: `equalString`, `appendString`.
- **Nat/Pos/Z arithmetic** (per the nat-mapping audit's
  enumeration): `divModNat`, `mulNat`, `expNat`, `widthNat`,
  `minNat`, `maxNat`, `Nat__rec`, `if0Nat`, `Pos_cases`, `BitM`,
  `posInc`/`Add`/`Mul`/`Exp`, `eqPos`, `Z`, `ZZero`, `ZPos`,
  `ZNeg`, `subNZ`, the `Pos` inductive itself.
- **Cryptol numeric types**: `IntMod` + ops, `Rational` + ops.
- **Int**: `intMin`, `intMax`, `intAbs` (Lean has `intLt`).
- **Containers**: `Maybe`, `List`/`Cons`/`Nil`/`List__rec`.
- **Vectors**: `EmptyVec`, `at`, `atWithProof`, `coerceVec`,
  `head`, `tail`, `genWithProof`, `scanl`, `take0`, `drop0`, `zip`,
  `head_gen`, `tail_gen`, `streamScanl`.
- **Lemma names**: `eqNatPrec`, `eqNatAdd0`, `eqNatAddS`,
  `eqNatAddComm`, `addNat_assoc`, `IsLtNat_Zero_absurd`,
  `IsLeNat_SuccSucc`, etc.
- **Nat predicates**: `IsLeNat`, `IsLeNat_*`, `IsLtNat`.

A user term that, after specialization, references one of these
will fail at Lean elaboration with "unknown identifier". Per the
nat-mapping audit this is fail-closed but opaque-to-the-user; a
SAW-level diagnostic would be more helpful. Severity: medium —
this is the "fill-as-needed" surface the design accepted, but
cost-per-demo grows with Cryptol-prelude breadth.

#### P-3. No `Fix` AST node, no recursive-def support

`Language.Rocq.AST.Term` has `Fix Ident [Binder] Term Term`;
`Language.Lean.AST.Term` deliberately omits it
(`AST.hs:74-76`). Rocq throws `badTerm` on `Prelude.fix`
(`saw-core-rocq/.../Term.hs:653`); Lean fails with an unmapped
reference (S-5 above). Either way recursive defs don't translate.
Cryptol idioms beyond `rev.cry` (streams via `fix`,
Merkle-Damgard, `iterate`) are blocked. Tracked as Arc 4.4.

#### P-4. No SAW Prelude / CryptolPrimitives prim emission flow

Direct consequence of P-1. `write_rocq_sawcore_prelude` /
`write_rocq_cryptol_primitives_for_sawcore` write the full
SAWCore Prelude / Cryptol-stdlib as Rocq files; no Lean analog.
Specialization architecture sidesteps this for users, but blocks
auditing-the-Prelude-as-Lean and any future `.sawcore`-as-Lean flow.

#### P-5. Configuration knobs

`Lean.TranslationConfiguration` (`Monad.hs:90-98`) has only
`constantRenaming`, `constantSkips`. Rocq adds `monadicTranslation`
(free-monad encoding for Heapster), `postPreamble` (caller-supplied
imports), `vectorModule` (List vs Vector retarget). Lean's preamble
is hard-coded at `import CryptolToLean` plus
`open implicitlyOpenedModules`. Mild ergonomic gap on
`postPreamble`; the others are out-of-scope by design.

#### P-6. Output-shape differences

- Rocq emits `Section ... End` for Cryptol modules
  (`Rocq.hs:103`); Lean emits `namespace ... end` (`Lean.hs:122`).
  Both are right for their target.
- Rocq emits `Module ... End` for SAW modules; Lean has no
  equivalent (P-1).
- Rocq's `Fixpoint` keyword is reachable through `Fix`; Lean's
  `def` cannot represent recursion (P-3).
- Rocq exercises inductive-decl emission for the Prelude path; Lean
  has the AST and pretty-printer plumbing but no construction site
  in `Term.hs`/`CryptolModule.hs`.
- `Lean.preamble` auto-opens `CryptolToLean.SAWCorePrimitives`
  (`SpecialTreatment.hs:255`) so emitted output uses bare
  short names where possible; Rocq does not auto-`Import`/`Export`.
  Lean's ergonomic win.

#### P-7. `dump_lean_residual_primitives`

Lean has it (`Exporter.hs:604-633`, `Interpreter.hs:5292-5305`);
Rocq doesn't. Asymmetry, not a parity gap — Rocq doesn't use
specialization-as-fixed-point so doesn't need it.

## Recommendations

In rough priority order. None propose implementations.

1. **Close S-1**: replace the outer-pi-spine
   `polymorphismResidual` walk with a full term-tree traversal
   catching `TypeSort k>0` at any binder position. Add a smoketest.
2. **Close S-3**: extend `discoverNatRecReachers` to scan for `Z`,
   `AccessibleNat`, `AccessiblePos` recursors as well as Nat/Pos.
3. **Close S-5/P-3 surface**: add explicit `SpecialTreatment`
   entries for `fix` and `fix_unfold` that throw a
   `TranslationError`. Mirrors Rocq's `Term.hs:653` `badTerm` —
   loud at SAW time rather than Lean time.
4. **S-2 decision**: tighten `unsafeAssert` to `Sort (u+1)` (parallel
   with `error`), or document explicitly in
   `2026-04-24_soundness-boundaries.md` why we accept the
   broader-than-SAW shape. Pick one.
5. **P-2 triage**: each missing Rocq SpecialTreatment a future
   demo surfaces will need a Lean realisation in
   `SAWCorePrimitives.lean` plus a `mapsTo`. Use
   `dump_lean_residual_primitives` as the discovery tool.
6. **P-1 strategic decision**: do we want
   `translateSAWModule` for Lean? Specialization design says no for
   end users, but it would unblock auditing the SAW Prelude as
   Lean and close prim-surface symmetry. Defer until a concrete
   user materialises.
7. **Minor**: remove or document the dead `bitvector`
   SpecialTreatment entry at `SpecialTreatment.hs:347` (per
   `2026-04-24_audit-primitives-fidelity.md` Unchecked corner 1).
