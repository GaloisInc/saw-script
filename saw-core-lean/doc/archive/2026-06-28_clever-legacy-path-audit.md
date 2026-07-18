# Clever / Legacy Path Audit

Date: 2026-06-28

Scope: current worktree under `saw-core-lean`, with the code treated as
untrusted. The project rule applied here is strict: Haskell should be
obviously correct and near-syntactic. Haskell-side equivalence recognizers,
semantic rewrites, backup paths, and legacy lowering paths should be removed
unless they only emit literal Lean obligations plus optional Lean-side checked
helper lemmas.

Note: this audit observes the current disk state. In this worktree,
`src/SAWCoreLean/FixShapes.hs` is deleted according to Git status, but many
comments, tests, and Lean helpers still refer to the older fix-shape recognizer
architecture.

## Findings

### 1. Def-site replacement can inject handwritten semantics

References:

* `src/SAWCoreLean/SpecialTreatment.hs:87` defines `DefReplace` as verbatim
  Lean source for a SAW definition.
* `src/SAWCoreLean/SpecialTreatment.hs:374` exposes `replaceDef`.
* `src/SAWCoreLean/SpecialTreatment.hs:466` replaces `sawLet`.
* `src/SAWCoreLean/SpecialTreatment.hs:494` replaces `xor`.
* `src/SAWCoreLean/SpecialTreatment.hs:499` replaces `boolEq`.
* `src/SAWCoreLean/SAWModule.hs:90` dispatches `DefReplace`.

Why this violates or might violate the rule:

`DefReplace` skips translation of the SAW body and emits a handwritten Lean
definition from a Haskell table. Lean checks that the handwritten term has its
declared Lean type, but it does not check equivalence to the skipped SAW body.
This is a semantic transposition path in Haskell, not literal obligation
emission.

Suggested replacement:

Remove generic `DefReplace` as a backend feature. For each needed prelude
replacement, place the Lean implementation in the support library and require a
Lean theorem that states the correspondence to the literal emitted SAW shape, or
emit the literal SAW body plus a local obligation/theorem stub for any desired
rewrite. Haskell should only select a named helper with an explicit checked
contract, not inject unproved replacement source.

### 2. Axiom/primitive auto-emission is a latent trust backdoor

References:

* `src/SAWCoreLean/SAWModule.hs:120` sends `AxiomQualifier` and `PrimQualifier`
  through `emitAxiom`.
* `src/SAWCoreLean/SAWModule.hs:123` emits a Lean `axiom`.

Why this violates or might violate the rule:

Most primitive use-sites are guarded by `SpecialTreatment`, but the module
walker still has a generic path that turns SAW axioms/primitives into Lean
axioms whenever a def-site treatment preserves them. In untrusted code, this is
too broad: a table mistake can silently expand Lean's trusted base.

Suggested replacement:

Make the generic `AxiomQualifier` / `PrimQualifier` path reject by default.
Allow only narrowly named Lean support-library declarations with checked
contracts, or emit local proof obligations. If true Lean axioms remain, they
should be manifest support-library trust assumptions, not reachable through
ordinary Haskell preservation machinery.

### 3. Use-site macro machinery performs Haskell-side semantic rewriting

References:

* `src/SAWCoreLean/SpecialTreatment.hs:134` defines `UseMacro`.
* `src/SAWCoreLean/SpecialTreatment.hs:142` defines `UseMacroOrVar` with
  fallback behavior.
* `src/SAWCoreLean/SpecialTreatment.hs:331` defines `replaceDropArgs`.
* `src/SAWCoreLean/SpecialTreatment.hs:656` maps `Zero`, `One`, `Succ`,
  `Bit0`, `Bit1`, and `NatPos`.
* `src/SAWCoreLean/SpecialTreatment.hs:1117` implements `collapseOrApply`.
* `src/SAWCoreLean/Term.hs:2024` applies `UseMacro`.
* `src/SAWCoreLean/Term.hs:2036` applies `UseMacroOrVar`.

Why this violates or might violate the rule:

The Nat/Pos path collapses SAW's binary-positive constructors into Lean
`NatLit`s in Haskell, and falls back to helper calls such as `bit0_macro`,
`bit1_macro`, or `id` for non-literal cases. This is not just syntax emission:
it computes and selects an equivalent representation. The fallback branch is
also a backup path by design.

Suggested replacement:

Emit literal Lean constructors or named Lean functions corresponding one-to-one
with the SAW constructors, then prove simplification lemmas in Lean that turn
closed constructor chains into numerals. If readability requires numeral output,
make it a Lean-side pretty/proof step or require a checked theorem for the
collapse.

### 4. Phase-beta raw/wrapped classification is a broad Haskell semantic model

References:

* `src/SAWCoreLean/Term.hs:521` defines `shouldWrapBinder`.
* `src/SAWCoreLean/Term.hs:572` defines dependency-based
  `typeArgPositions`.
* `src/SAWCoreLean/Term.hs:619` defines `typeArgPositionsBinders`.
* `src/SAWCoreLean/Term.hs:642` defines heuristic `isTypeProducing`.
* `src/SAWCoreLean/Term.hs:1047` defines `argumentBindPlan`.
* `src/SAWCoreLean/Term.hs:1092` defines `natValueResult`.
* `src/SAWCoreLean/Term.hs:1106` defines `phaseBetaResultShape`.
* `src/SAWCoreLean/Term.hs:1814` builds lifted applications and eta-expands
  partial applications based on these classifiers.

Why this violates or might violate the rule:

These functions classify SAW terms as value-domain, type/index-domain,
proof-domain, function-shaped, or wrapped by inspecting syntax, free variables,
module-map return types, and translated Lean shapes. The result controls whether
the emitted Lean term inserts `Except String`, `Bind.bind`, `Pure.pure`, eta
expansion, or raw application. This is a large semantic adapter in Haskell. Some
of it may be necessary for the current `Except` translation, but it is not
"near-syntactic" in the audit sense.

Suggested replacement:

Move the raw/wrapped convention into an explicit typed translation relation or
schema that Lean checks. Haskell should emit the source-shaped term and the
declared expected convention, while Lean helper lemmas prove the bridge between
raw and wrapped forms. If Haskell must keep a convention pass temporarily,
reduce it to table-driven syntactic emission with no fallback inference from
free-variable dependency or result-shape heuristics.

### 5. `liftRawValue` is a syntactic raw-value recognizer used in many rewrites

References:

* `src/SAWCoreLean/SpecialTreatment.hs:293` defines `liftRawValue`.
* `src/SAWCoreLean/SpecialTreatment.hs:301` recognizes `NatLit`, `IntLit`,
  `StringLit`, selected constructor names, and empty lists.
* `src/SAWCoreLean/SpecialTreatment.hs:633` uses it for `ite`.
* `src/SAWCoreLean/SpecialTreatment.hs:816` uses it for `error`.
* `src/SAWCoreLean/Term.hs:968` uses it in lifted application emission.
* `src/SAWCoreLean/Term.hs:2838` uses it for array literal sequencing.
* `src/SAWCoreLean/Term.hs:3367` uses it for top-level closed-value fixups.

Why this violates or might violate the rule:

The function is explicitly a recognizer for Lean AST fragments that are assumed
to be raw values. It changes the emitted term by inserting `Pure.pure`. This may
be type-directed plumbing rather than a mathematical equivalence, but it is
still a Haskell-side shape recognizer whose correctness is non-local: adding a
constructor name or missing one changes semantics/error propagation.

Suggested replacement:

Make raw-value lifting part of each literal/constructor emission rule itself, or
emit a Lean-side adapter whose type forces the required lift. Avoid a global
post-hoc recognizer over arbitrary Lean AST. For branch helpers such as `iteM`,
prefer Lean overloads or checked helper lemmas that accept the literal source
shape directly.

### 6. `rawifyExceptToRaw` is a dead or legacy semantic rewrite engine

References:

* `src/SAWCoreLean/Term.hs:1192` documents `rawifyExceptToRaw`.
* `src/SAWCoreLean/Term.hs:1204` implements the rawifier.
* `src/SAWCoreLean/Term.hs:1226` reassociates nested `Bind.bind`.
* `src/SAWCoreLean/Term.hs:1240` hoists or inlines effects based on blocked
  names.
* `src/SAWCoreLean/Term.hs:1276` rewrites `let` shadows.
* `src/SAWCoreLean/Term.hs:1301` rewrites `atWithDefaultM`; `:1303` proves
  in-bounds by Haskell literal comparison through `atIndexDefinitelyInBounds`.
* `src/SAWCoreLean/Term.hs:1320` rewrites `mkStreamM`.
* `src/SAWCoreLean/Term.hs:1328` and `:1342` rawify recursor calls.
* `src/SAWCoreLean/Term.hs:1411` through `:1489` recognize pure eta shadows
  and effect syntax.

Why this violates or might violate the rule:

This is exactly the class of Haskell-side clever equivalence engine the rule is
trying to remove. It proves purity, hoistability, in-bounds indexing, monadic
rawification, and recursor equivalences by pattern matching on generated Lean
AST. Current `rg` results show no call sites in `src/`, which makes it dead or
legacy surface. If reconnected, it would be a high-risk semantic rewrite.

Suggested replacement:

Delete it if it is dead. If any lowering still needs the behavior, emit the
literal monadic term plus Lean propositions such as totality, purity,
productivity, and in-bounds obligations. Put the hoisting/rawification lemmas in
Lean, where failed equivalences become failed proofs instead of mistranslation.

### 7. Direct `MkStream` lowering is mostly proof-carrying but still shape-driven

References:

* `src/SAWCoreLean/Term.hs:1168` defines `lowerMkStreamSound`.
* `src/SAWCoreLean/Term.hs:1171` accepts only a unary Lean lambda shape.
* `src/SAWCoreLean/Term.hs:1180` emits `saw_mkStream_total_exists`.
* `src/SAWCoreLean/Term.hs:1186` emits `saw_mkStream_choose`.
* `src/SAWCoreLean/Term.hs:1685` intercepts `Prelude.MkStream`.
* `src/SAWCoreLean/Term.hs:1690` has the `deferMkStreamLowering` switch.
* `lean/CryptolToLean/SAWCorePrimitives.lean:755` defines the corresponding
  proof-carrying totality contract.

Why this violates or might violate the rule:

Unlike the rawifier, this path does emit a Lean-side totality obligation. That
is aligned with the rule. The remaining concern is that Haskell still recognizes
and lowers a specific function shape, with a dormant `deferMkStreamLowering`
legacy switch. The accepted shape is small, but it is still a special lowering
path rather than literal emission.

Suggested replacement:

Keep only the proof-carrying contract. Prefer emitting the literal `mkStreamM`
shape and a local theorem obligation that states it is total, then use a Lean
helper to convert after the proof. Remove the dormant deferral flag if no longer
needed, so there is one visible path.

### 8. Generic `Prelude.fix` now emits obligations, but hidden `sorry` is still a
check-stage hazard

References:

* `src/SAWCoreLean/Term.hs:1677` intercepts `Prelude.fix`.
* `src/SAWCoreLean/Term.hs:2141` lowers to a unique-fixed-point obligation.
* `src/SAWCoreLean/Term.hs:2187` emits `saw_fix_unique_exists`.
* `src/SAWCoreLean/Term.hs:2194` emits `saw_fix_choose`.
* `src/SAWCoreLean/Term.hs:1593` defines `proofObligationPlaceholder` as
  `Lean.Tactic "sorry"`.
* `src/SAWCoreLean/Term.hs:1602` through `:1626` insert local proof
  obligations using that placeholder.
* `lean/CryptolToLean/SAWCorePrimitives.lean:712` defines the Lean-side
  generic fix contract.

Why this violates or might violate the rule:

The current generic fix path is directionally right: it emits a Lean obligation
instead of choosing a value by a Haskell recognizer. The problem is that the
obligation is inserted as a local `let` proof initialized by `by sorry`. Unless
the downstream check-stage reliably rejects all `sorry`, the emitted artifact
can typecheck without a proof. That would turn an explicit obligation into an
unchecked assumption.

Suggested replacement:

Emit obligations as named theorem declarations or as holes that cannot be
accepted in completed artifacts. At minimum, make the no-`sorry` check a hard
part of the Lean backend contract and document the exact command that enforces
it. Prefer a structure where the main definition depends on explicitly named
proof parameters, and a separate checked discharge file supplies them.

### 9. Shape-specific fix helpers and stale recognizer tests remain as legacy
surface

References:

* `lean/CryptolToLean/SAWCorePrimitives.lean:648` introduces recursion
  lowering helpers for shapes recognized by `SAWCoreLean.FixShapes`.
* `lean/CryptolToLean/SAWCorePrimitives.lean:682` describes
  `mkStreamFix` as a recognizer target.
* `lean/CryptolToLean/SAWCorePrimitives.lean:797` introduces `genFix`.
* `lean/CryptolToLean/SAWCorePrimitives.lean:819` describes `genFix` as a
  recognizer target.
* `lean/CryptolToLean/SAWCorePrimitives.lean:893` introduces mutual stream
  fix helpers.
* `lean/CryptolToLean/SAWCorePrimitives.lean:1078` describes
  `saw_unreachable_default` as a fix-shape lowering default.
* `smoketest/SmokeTest.hs:804`, `:911`, and `:940` still assert direct
  lowering to `mkStreamFix`, `genFixVecChecked`, and `mkStreamFixPair`.

Why this violates or might violate the rule:

The Haskell recognizer file appears deleted in this worktree, but the support
library and tests still encode the old target architecture. The raw helpers use
default-backed prefix construction, and the comments still justify them through
Cryptol productivity and recognizer extraction. Even if currently unreachable,
this is a legacy path waiting to be reconnected.

Suggested replacement:

Retire direct shape-specific Haskell lowering tests and comments. Keep only
checked Lean helpers that require explicit productivity/body-soundness proofs,
or keep the helpers internal to proof scripts over literal emitted terms. Tests
should assert that unrecognized `fix` emits generic unique-fix obligations and
that no direct `mkStreamFix`/`genFix` lowering is produced unless the generated
term also contains the required Lean-side proof obligations.

### 10. Imported-name fallback and renaming are unproved realization paths

References:

* `src/SAWCoreLean/Monad.hs:251` defines `constantRenaming`.
* `src/SAWCoreLean/Monad.hs:256` defines `constantSkips`.
* `src/SAWCoreLean/Term.hs:2207` documents imported constants as externally
  supplied realizations.
* `src/SAWCoreLean/Term.hs:2214` emits imported constants as escaped or renamed
  Lean variables.

Why this violates or might violate the rule:

For `ImportedName`s, the backend can emit a bare or renamed Lean reference and
trust the caller to supply a realization. That is a backup path outside the
literal SAW-to-Lean obligation discipline. It may be useful for user constants,
but in an untrusted audit it is a semantic hole unless the realization is tied
to a checked contract.

Suggested replacement:

Require imported-name realizations to be explicit parameters or imports with
declared Lean theorem obligations connecting them to the source term. If
renaming remains, produce an audit-visible declaration that records the mapping
and the proof obligation expected for it.

## Summary

The highest-risk current Haskell-side code is not the deleted `FixShapes.hs`;
it is the remaining general machinery that recognizes shapes and changes
semantics: `DefReplace`, `UseMacroOrVar` numeric collapse/fallbacks,
raw/wrapped inference, global raw-value lifting, and the dead `rawifyExceptToRaw`
engine. The generic `fix` and `MkStream` paths are closer to the desired
proof-carrying architecture, but they should emit obligations in a form that
cannot be accepted with hidden `sorry`, and stale shape-specific helpers/tests
should be retired or made explicitly proof-carrying.
