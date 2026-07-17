# Proof-Primitive Obligation Plan

**Date**: 2026-07-01

## Execution Goal

Implement proof-carrying emission for SAWCore proof primitives, proof axioms,
and lemma axioms in the SAW-Lean backend.

At the end of this phase, every in-scope fully applied proof surface must do
one of the following:

1. emit a visible Lean proof obligation for the exact proposition required by
   the source term and consume checked evidence for that proposition;
2. call a Lean support-library theorem or checked helper whose definition/proof
   is kernel checked and whose type exactly realizes the SAWCore primitive; or
3. reject at SAW translation time with a pinned final-boundary diagnostic, but
   only when we have explicitly decided that the source surface is outside the
   Lean backend's intended feature set.

The target is sound emission, not proof automation. Generated artifacts may
contain open proof stubs. The backend succeeds in this phase when the emitted
Lean states the right proposition, threads the right evidence, and refuses to
trust unverified SAW proof terms or Lean axioms.

End-user contract: once this phase and the broader backend parity work are
complete, a user may have to prove the emitted Lean goals, but they must not
have to change Haskell emission or Lean generation to make an in-scope SAWCore
term representable. If a new user example requires a backend code change rather
than merely a proof, proof-library lemma, or documented final-boundary
decision, that is a backend coverage bug.

Strict phase boundary: do not build Lean automation while executing this plan.
Do not add convenience tactics, tactic macros, generated proof-search scripts,
large simp bundles, arithmetic search, BV decision procedures, or proof-library
lemmas whose purpose is to make current proof obligations discharge
automatically. That is a later proof-ergonomics phase. The only Lean code in
scope here is checked realization infrastructure: small definitions or
theorems whose statements are directly tied to SAWCore primitive semantics.

## Why This Is Next

Partial operations and bounds/index operations now follow the desired
proof-carrying style for fully applied emissions: Haskell emits a visible
contract and Lean checks the evidence. The next known-gap family with the same
soundness profile is SAWCore's proof surface:

- equality and coercion proof axioms such as `uip` and `coerce__eq`;
- proof-producing primitives such as `equalNatToEqNat`, `proveLeNat`,
  `bvEqToEq`, `bvEqToEqNat`, and `bvultToIsLtNat`;
- bitvector proof lemmas such as `bvAddZeroL` and related arithmetic/order
  lemmas;
- vector/list proof lemmas such as `head_gen` and `foldr_nil`;
- assertion-style proof axioms such as `unsafeAssertBVULt` and
  `unsafeAssertBVULe`.

These are currently pinned as known gaps in the obligation corpus. Leaving them
as broad rejection entries blocks Rocq-parity proof-discharge workflows. Mapping
them naively as Lean `axiom`s would be unsound because it would expand the
trusted base beyond Lean's kernel and the checked support library.

This phase converts that surface into the same design already used elsewhere:
Haskell constructs syntax and explicit contracts; Lean checks mathematical
evidence.

## Relationship To Auto-Emitted Prelude Translation

This plan does not replace the Lean Prelude translation story. It depends on
it.

The current backend already has a universe-aware `write_lean_sawcore_prelude`
path:

- the Prelude walker translates SAWCore Prelude declarations directly through
  the module translator, not through user-term normalization;
- proof/type infrastructure can auto-emit in `RawValueMode` over fresh
  `Sort u` binders;
- value-domain facades either use the wrapped `Except String` convention or
  map to checked support-library declarations whose carrier binders live in
  `Type u`;
- `translateSort` allocates fresh universe variables for binder-position
  `sort k >= 1`, and call sites can supply explicit universe levels to
  universe-polymorphic constants.

That machinery solves the Lean expressibility problem: SAWCore definitions with
higher-sort binders can be represented in Lean without collapsing universes or
asking Lean's inference to guess the wrong level.

It does not by itself solve the proof-primitive soundness problem. SAWCore
`axiom` declarations and proof-producing primitives are not safe merely because
the auto-emitter can print their types. A naive translation of:

```lean
axiom uip : ...
axiom coerce__eq : ...
```

would make those statements trusted Lean assumptions. That is exactly what this
backend must not do. The proof-primitive phase is therefore the layer above
auto-emission:

- auto-emitted raw Prelude definitions remain the baseline for ordinary
  definitional content;
- proof axioms and proof-producing primitives need checked theorem
  realizations or emitted local obligations;
- skipped proof-equation conveniences remain skipped until we decide whether
  they are raw checked theorems, wrapped checked theorems, or proof-library
  lemmas.

This distinction is what makes the task finite. We are not inventing a custom
translation for the whole Prelude. We are surveying the finite residue left
after universe-aware Prelude emission: declarations whose source status is
`axiom`, whose result is proof/evidence, or whose current `SpecialTreatment`
entry rejects because a checked realization has not been supplied.

## Why Lean Needs More Than The Rocq Path

Rocq parity is a feature target, not a mandate to copy Rocq's trusted base.

The Rocq backend avoids much of this explicit obligation machinery because its
translation pipeline and support library make different trust choices:

- `SAWCoreRocq.SAWModule` maps `AxiomQualifier` and `PrimQualifier` directly to
  Rocq `Axiom`;
- Rocq `SpecialTreatment` maps some proof primitives to existing Rocq proof
  constants or tactics, for example `uip` to `UIP`, `coerce__eq` to `eq_refl`,
  and `unsafeAssert*` to Ltac proof search;
- the handwritten Rocq support library contains additional assumptions and
  proof tactics for bitvector and assertion surfaces;
- Rocq's universe/cumulativity behavior lets many Prelude references elaborate
  without the explicit universe-level machinery Lean needs.

That is a workable Rocq backend design, but it means part of the Rocq story is
"the generated development imports a support theory with these assumptions and
tactics." The Lean backend's hard requirement is stronger: a completed Lean
artifact should be accepted because Lean checked the exact emitted proposition,
not because the emitter introduced a fresh trusted axiom or silently trusted a
SAW proof object.

So the Lean analogue is deliberately stricter:

- where Rocq can import or generate an axiom, Lean must either prove the
  corresponding theorem in the support library or emit it as a local proof
  obligation;
- where Rocq runs a tactic during translation, Lean emission should expose the
  proposition and leave discharge to a later checked proof phase;
- where Rocq's support theory assumes a bitvector/vector lemma, Lean must have
  an axiom-clean theorem realization before the row counts as complete;
- where Rocq's universe system infers the right instantiation, Lean uses the
  explicit universe-aware Prelude machinery already implemented.

This is why the proof-primitive task is not whack-a-mole. The finite work item
is the residue between "Rocq can name or assume this proof surface" and "Lean
has an axiom-clean checked realization or explicit obligation for this proof
surface." The source of truth is finite: `Prelude.sawcore`,
`Cryptol.sawcore`, the Rocq special-treatment/support-library surface, and the
Lean rejection table.

After that residue is inventoried and classified, new user programs should not
create new emission-design categories. They may expose an unimplemented row,
hard proof obligation, missing proof-library theorem, performance issue, or
upstream SAWCore addition. They should not require users to modify the emitter.

## Non-Negotiable Rules

- Haskell must not prove propositions, normalize proof goals, run arithmetic or
  bitvector reasoning, inspect generated Lean syntax to decide a proof, or use
  source proof terms as evidence for a different proposition.
- Haskell must not translate SAW proof axioms into Lean `axiom`s, `opaque`
  unchecked constants, `unsafe` declarations, native-evaluation assumptions, or
  imports that widen the trusted base.
- Haskell must not preserve old fallback behavior for proof primitives. A
  fallback that emits a raw primitive name, an unchecked helper, or a trusted
  proof term is a bug, not compatibility code.
- Haskell may translate ordinary arguments, construct the exact Lean
  proposition for an obligation, bind a local proof placeholder, and pass that
  evidence to a checked consumer.
- Haskell may call a named Lean theorem/helper only when that declaration is
  kernel checked and its type is the contract being claimed. The helper's name
  is not trusted; its type and axiom report are the authority.
- A translated SAW proof argument may be passed only at its exact translated
  type. Any conversion from one proof proposition to another must happen via a
  checked Lean theorem/helper or an emitted local obligation.
- Do not choose between a theorem realization and a local obligation based on
  whether the current example would then pass. Choose based on whether the
  support-library theorem is already checked and audits cleanly.
- Do not hide failures. If the emitted proposition is correct but the proof is
  not automated, the case is an obligation or proof-ergonomics known gap, not a
  reason to weaken the proposition.
- Under-applied proof primitives remain final-boundary rejections until a
  proof-carrying higher-order wrapper is designed.

## Soundness Surface

SAWCore proof primitives are especially sensitive because their results can be
used to transport values across equalities. A bad translation can make an
unrelated proposition available to Lean and then use it to coerce a value, prove
a false branch condition, or erase a failed bound.

The core soundness rule is:

> The emitted Lean term may use only evidence that Lean can check at the exact
> proposition required by the emitted consumer.

This rules out several tempting shortcuts:

- treating a SAW `Eq` proof as a Lean equality proof at a different type;
- assuming `bvEq n x y = True` implies `x = y` in Haskell;
- replacing `unsafeAssertBVULt n x y` with a proof of `True`;
- mapping `uip`, `coerce__eq`, or BV lemmas to Lean axioms because they are
  expected to be true;
- using a source proof term for `IsLeNat`/`IsLtNat` directly as Lean evidence
  for `<=`/`<` without a checked realization theorem;
- emitting convenience rewrites that depend on the current examples rather than
  on a general checked contract.

It is acceptable for Haskell to emit a proposition that a human or later proof
library must prove. It is not acceptable for Haskell to silently decide that the
proposition has been proved.

## In-Scope Surfaces

The first implementation target is the existing proof-primitive obligation
corpus:

- `obligations/proof_uip`
- `obligations/proof_coerce_eq`
- `obligations/proof_equal_nat_to_eq_nat`
- `obligations/proof_prove_le_nat`
- `obligations/proof_bv_forall`
- `obligations/proof_bv_add_zero_l`
- `obligations/proof_bv_eq_to_eq`
- `obligations/proof_foldr_nil`
- `obligations/proof_head_gen`
- `obligations/proof_unsafe_assert_bvult`
- `obligations/proof_unsafe_assert_bvule`

The first checkpoint must also audit the broader `SpecialTreatment` rejection
surface and classify every proof-like Prelude entry as one of:

- already covered by this plan's representative corpus;
- needing a new focused obligation fixture;
- covered by a separate phase, such as recursors, datatype/list encodings, or
  imported declaration realization;
- a true final boundary with written rationale.

Known proof-like entries in `Prelude.sawcore` include, but are not limited to:

- equality/coercion: `uip`, `coerce__eq`, `unsafeAssert`,
  `equalNatToEqNat`, `bvEqToEq`, `bvEqToEqNat`;
- Nat/order proofs: `natCompareLe`, `proveLeNat`, `eqNatPrec`,
  `eqNatAdd0`, `eqNatAddS`, `eqNatAddComm`, `addNat_assoc`,
  `IsLtNat_Zero_absurd`, `IsLeNat_SuccSucc`;
- vector/list lemmas: `head_gen`, `tail_gen`, `at_single`,
  `foldr_nil`, `foldr_cons`, `foldl_nil`, `foldl_cons`, `vecEq_refl`,
  `take0`, `drop0`, `map_map`;
- bitvector proof/lemma families: `bvForall`, `bvNat_bvToNat`,
  `bvAddZeroL`, `bvAddZeroR`, `bvShiftL_bvShl`, `bvShiftR_bvShr`,
  `bvEq_refl`, `equalNat_bv`, `bveq_sameL`, `bveq_sameR`,
  `bveq_same2`, `not_bvult_zero`, `trans_bvult_bvule`,
  `bvult_sub_add_bvult`, `bvult_sum_bvult_sub`,
  `IsLtNat_to_bvult`, `bvult_to_IsLtNat`;
- assertion-style BV bounds: `unsafeAssertBVULt`, `unsafeAssertBVULe`.

This list is a survey starting point, not permission to ignore a proof-like
entry that appears elsewhere in the Prelude or Cryptol wrapper surface.

## Out Of Scope For This Phase

The following work is related but separate:

- proving broad automation tactics for the emitted obligations;
- making all existing executable differential rows pass automatically;
- designing a proof-carrying higher-order representation for under-applied
  proof primitives;
- implementing datatype/list encodings, direct recursors, arrays, floats, or
  loaded custom primitive/axiom declarations;
- replacing all SAWCore proof lemmas with an optimized Lean proof library;
- final SAW-side proof replay, import isolation, or user-facing proof
  ergonomics.

If any of these are needed to complete a proof-primitive row, stop and record a
known gap rather than expanding this phase.

## Correct Contract Shapes

There are two allowed positive shapes.

### Local obligation shape

Use this when the backend can state the exact required proposition but the
checked support-library proof is not yet available:

```lean
let h_proof_obligation_ : Prop := <exact proposition required here>
let h_proof_ : h_proof_obligation_ := by
  sorry
<body that consumes h_proof_>
```

The proposition must be the actual translated result type or consumer
precondition. It must mention the translated arguments used by the result. It
must not be `True`, a disconnected theorem, or a weaker approximation.

### Checked realization shape

Use this when the support library has a kernel-checked realization:

```lean
<checked_theorem_or_helper> <translated arguments> <translated premises>
```

The declaration must be a Lean `def`/`theorem`/`lemma` whose proof checks under
the pinned toolchain. It must not be a Lean `axiom` added for this backend. The
test must be able to audit the generated artifact for the checked declaration
name and for absence of forbidden circumvents.

Candidate contract families:

| Source surface | Required contract family |
| --- | --- |
| `uip t x y pf1 pf2` | equality of the translated proof terms at the translated equality type, realized by a checked Lean proof-irrelevance/UIP theorem or emitted exactly as an obligation |
| `coerce__eq` | equality between the translated `coerce` implementation and `coerce__def`, proved in Lean or emitted as that exact obligation |
| `equalNatToEqNat m n pf` | from the translated proof of `equalNat m n = True` to the translated `eqNat m n` proposition, via a checked theorem or target obligation |
| `proveLeNat x y` | a checked Maybe-valued realization whose `Just` branch carries Lean evidence of the translated `IsLeNat x y`; otherwise keep as known gap |
| `bvEqToEq n x y pf` | from translated `bvEq n x y = True` evidence to translated vector equality, via a checked theorem or target equality obligation |
| `bvEqToEqNat n x y pf` | from translated vector equality to translated Nat equality of `bvToNat` results |
| `bvultToIsLtNat n x y pf` | from translated unsigned-less-than Boolean evidence to translated Nat less-than evidence |
| `bvAddZeroL n x` / `bvAddZeroR n x` | equality between the translated BV addition expression and `x`, realized by checked BV lemmas |
| `head_gen n a f` | equality between translated `head (gen ...)` and translated `f 0`, realized by a checked vector theorem or emitted as exact equality obligation |
| `foldr_nil a b f x v` | equality between translated `foldr ... 0 ... v` and `x`, realized by a checked vector/fold theorem or emitted as exact equality obligation |
| `unsafeAssertBVULt n x y` | local obligation or checked theorem requiring translated `bvult n x y = True` |
| `unsafeAssertBVULe n x y` | local obligation or checked theorem requiring translated `bvule n x y = True` |

For assertion-style primitives, unconditional theorem realization is usually
wrong: `unsafeAssertBVULt` and `unsafeAssertBVULe` are only sound when the
corresponding comparison fact is proved. If the source surface reaches the
backend, emit that comparison as an obligation rather than claiming it is
always true.

## Haskell Architecture

Add a declarative proof-primitive contract path rather than bespoke lowering
branches for each fixture.

The contract table should specify:

- source module and source identifier;
- exact arity required for the lowering;
- argument modes:
  - ordinary translated value/type/index argument;
  - translated premise proof that may be passed only at its exact type;
  - source proof argument that is ignored and replaced by a Lean obligation;
  - result proposition to be emitted as an obligation;
- whether the positive path is a local obligation or checked realization;
- checked Lean theorem/helper name, when one exists;
- forbidden circumvent names for tests.

Acceptable Haskell responsibilities:

- translate arguments according to declared modes;
- construct the exact target proposition from already translated terms;
- emit a local proof binding with a stable name;
- call a checked theorem/helper with explicitly translated premises;
- reject non-exact-arity forms with a clear diagnostic.

Forbidden Haskell responsibilities:

- deciding that a proof proposition is true;
- reducing Nat or BV expressions to make a proof easier;
- inspecting Lean syntax to detect `Refl`, zero, equality, or bounds;
- trusting a SAW proof term as evidence for a proposition other than its exact
  translated type;
- emitting Lean axioms for SAW axioms;
- falling through to old raw primitive mappings or skipped declarations;
- adding shape-specific code whose only purpose is to make one litmus pass.

If the existing checked-application contract machinery can express these
surfaces cleanly, reuse it. If not, introduce a sibling abstraction such as
`ProofPrimitiveContract`. The name is not important; the important property is
that proof primitives are data-driven contracts, not scattered semantic
rewrites.

## Lean Support Library Policy

Lean support declarations added in this phase must be checked realizations, not
automation.

Allowed:

- small theorems that exactly state a SAWCore proof primitive's semantics;
- thin helpers that consume explicit proof evidence in their type;
- realization theorems tying existing support-library definitions to the
  SAWCore statement;
- local proof obligations left open in emitted artifacts.

Forbidden:

- Lean `axiom`s for SAW proof primitives;
- `unsafe`, native-evaluation, or proof-local native axioms;
- broad tactics or generated tactic scripts intended to discharge the current
  corpus automatically;
- new helper definitions that duplicate SAW semantics without a realization
  theorem;
- proof search hidden behind helper names.

Every new theorem/helper must have an axiom audit before it is treated as a
completed realization. If the proof requires substantial library work, keep the
backend row as a local obligation or known gap and record the proof-library
work separately.

## Testing Plan

All tests must live under `make test-saw-core-lean-conformance`.

### Promote existing known-gap fixtures

Promote each existing `obligations/proof_*` fixture only after the emitted
artifact has one of the allowed positive shapes.

Each positive `expected.txt` must require:

- the local proof obligation name and proposition, or the checked realization
  theorem/helper name;
- evidence consumption by the emitted term;
- the actual translated arguments appearing in the proposition or theorem
  application;
- absence of forbidden circumvents such as raw proof primitive names, Lean
  `axiom`, `unsafe`, `admit`, obsolete rejection fallthrough, or unrelated
  totalizing helpers.

### Preserve and refine known gaps

If a proof primitive still rejects, keep a `.known-gap` fixture that pins the
current failure stage and diagnostic. If the rejection disappears but the
emitted artifact lacks the required contract, the test must fail until it is
promoted or reclassified with a new pinned failure.

Do not reclassify a source proof surface as a final boundary merely because it
is hard to realize. A final boundary requires an explicit design decision that
the backend will not support that source surface.

### Add missing representative fixtures

The first checkpoint must compare the rejection table against the conformance
matrix. Add minimal fixtures for any proof-like family that is currently only
mentioned in comments or TODO prose. The corpus should cover families, not every
redundant lemma, but a family is not covered unless a representative fixture
exercises the distinct contract shape.

Examples of likely missing representative rows:

- `bvEqToEqNat`;
- `bvultToIsLtNat`;
- `natCompareLe`;
- `bvAddZeroR` if it does not share the exact emitted realization path with
  `bvAddZeroL`;
- at least one conditional/congruence lemma if its proof shape differs from
  equality conversion and BV arithmetic lemmas.

### Audit generated artifacts

For positive rows, the harness should inspect the backend-emitted artifact
itself. Do not build a hand-written equivalent observer and call that
conformance. The obligation-shape harness may normalize whitespace for stable
matching, but it must not reconstruct the proposition.

## Acceptance Criteria

This phase is complete only when all of the following are true:

1. Every existing `obligations/proof_*` known-gap fixture is either promoted to
   a positive obligation/realization test or remains a pinned known gap with a
   precise reason.
2. The `SpecialTreatment` proof-like rejection surface has been surveyed and
   represented in the conformance matrix by positive rows, known gaps, separate
   phase references, or explicit final-boundary rationale.
3. No SAW proof primitive or axiom is translated to a Lean axiom or unchecked
   helper.
4. Fully applied in-scope proof primitives use a shared declarative contract
   path rather than scattered Haskell semantic branches.
5. The emitted proposition for each local obligation is exact: it mentions the
   translated arguments and is the proposition required by the consumer.
6. Checked realization helpers/theorems have Lean axiom audits recorded before
   the corresponding row is treated as complete.
7. Under-applied proof primitives reject with pinned diagnostics unless a
   separate proof-carrying higher-order wrapper plan exists.
8. `otherTests/saw-core-lean/CONFORMANCE.md` records each target row as
   `obligation`, `known gap`, or `boundary` and links any residual work to
   `TODO.md`.
9. No new Lean automation was added to make the rows pass.

## Stop Conditions

Stop and reassess rather than patching forward if any of these occur:

- a proof primitive's intended Lean proposition is unclear after reading
  `Prelude.sawcore`;
- the only available positive implementation would require a Lean axiom;
- an implementation needs Haskell to inspect or prove semantic facts;
- a helper duplicates nontrivial SAW semantics without a checked realization
  theorem;
- a fixture can only pass by weakening the obligation or hiding the proof
  dependency;
- completing a row requires broad proof automation rather than emission
  correctness.

In those cases, keep or add a focused known-gap fixture and record the precise
design question in `TODO.md`.

## Expected Work Order

1. Survey `Prelude.sawcore` proof-like primitives/axioms and the
   `SpecialTreatment` rejection table; update the conformance matrix with any
   missing representative proof families.
2. Design the declarative proof-primitive contract table and identify which
   initial rows should use local obligations versus existing checked support
   theorems.
3. Promote the safest equality/Nat rows first, such as `equalNatToEqNat` and
   proof obligations for assertion-style primitives, because their contract
   shapes are easiest to audit.
4. Promote checked theorem rows only when the Lean support theorem is already
   proven and axiom-clean.
5. Leave BV-heavy and vector/fold lemma rows as obligations or known gaps until
   the Lean proof library can realize them without backend automation.
6. Run the focused conformance target and keep known gaps visible; do not
   convert proof-ergonomics failures into backend shortcuts.
