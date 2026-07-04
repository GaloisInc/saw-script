# Raw/Wrapped Recursor and Dictionary Convention Plan

**Date**: 2026-07-02

## Just Woke Up: Start Here

**Status update, 2026-07-02**: this plan reached a useful checkpoint, but it is
no longer the active top-level goal. The recursor convention remains valid local
architecture; however, full conformance exposed raw logical proof-transport
failures that require the broader position/callee convention described in
`doc/2026-07-02_position-callee-conventions-design.md`. Continue with
`doc/2026-07-02_position-callee-conventions-goal.md` before adding more
wrapping patches.

This is the next backend-completion task after the 2026-07-02 example refresh.
It exists because ordinary Cryptol module examples still fail when wrapped
value computations, especially dictionaries, flow into raw Lean recursors.

Do not start by changing code. First read:

1. this document;
2. `doc/2026-06-26_phase-beta-expected-shape.md`;
3. `doc/2026-07-01_complete-wrapping-migration-goal.md`;
4. the P0 rows in `TODO.md`;
5. the recursor rows in `otherTests/saw-core-lean/CONFORMANCE.md`;
6. `src/SAWCoreLean/Term.hs`, especially `translateRecursorAppWithShape`,
   `translateRecursorMotive`, and `translateCaseHandler`.

The task is not "make examples pass". The task is:

> Define and implement one explicit recursor calling convention that handles
> wrapped value scrutinees, raw Lean recursors, and dictionary projection
> without semantic Haskell rewrites.

If a target example needs a different semantic feature, preserve the failure
and classify it. Do not broaden this task to proof automation, stream
productivity, direct-recursion parity, or whole-module golden churn.

## Execution Goal

At the end of this phase, every in-scope supported recursor application must
fall into one of these outcomes:

1. emit a raw Lean recursor call with a raw scrutinee;
2. sequence a wrapped scrutinee with `Bind.bind`, run the raw Lean recursor in
   the continuation, and return a wrapped value result;
3. reject at SAW translation time with a principled diagnostic because the
   source term would require extracting a raw value, type, proof, proposition,
   or function from a wrapped computation.

The goal is a small, auditable convention. Haskell may decide positions and
shapes. Haskell must not prove that a wrapped computation is successful, erase
an `Except.error`, inspect generated Lean syntax to infer safety, or special
case one dictionary/record fixture.

## Central Invariant

Keep this invariant in front of every code change:

> A raw Lean recursor only ever receives a raw scrutinee. If the source
> scrutinee is wrapped, the only allowed way to get that raw scrutinee is inside
> the success continuation of `Bind.bind`, and only when the recursor result is
> itself a value computation.

This is the phase's design center. If a proposed patch cannot be explained as
preserving this invariant, stop and redesign. Do not make progress by
recognizing a specific dictionary, record projection, stream helper, fixture
name, or generated Lean syntax shape.

## Why This Is P0

The example refresh identified this as the highest-impact target-example gap.
It blocks ordinary whole-module Cryptol paths, not just proof ergonomics:

| Witness | Current failure shape |
| --- | --- |
| `drivers/cryptol_module_simple` | wrapped equality dictionary is projected with raw `RecordType.rec` |
| `drivers/cryptol_polymorphic_class_dict` | same wrapped dictionary/raw record-rec convention |
| `differential/cryptol_vector_eq_dictionary` | minimal true-differential PEqSeq dictionary reproduction |
| `differential/unit_recursor_raw_scrutinee` | value-producing `UnitType.rec` receives an `Except String UnitType` scrutinee |
| `differential/stream_helpers` | wrapped stream construction/helper result flows into raw `Stream.rec`; only the generic recursor convention is in scope |
| `drivers/sequences` | likely contains this gap plus separate sequence/proof issues |

Passing record examples such as `differential/record_projection_binder`,
`drivers/cryptol_module_record_update`, `drivers/cryptol_module_point`, and
`proofs/point_shift_property` show that the existing architecture is close.
They must remain regressions for this work.

## Non-Negotiable Rules

- Haskell stays dumb. It translates source syntax, carries explicit shape
  metadata, builds declared Lean applications, and rejects unsupported
  conventions.
- Do not rawify an arbitrary `Except String a` into `a`.
- Do not convert a wrapped dictionary, wrapped stream, or wrapped value into a
  raw value by default.
- Do not inspect emitted Lean ASTs to decide that a term is "really pure",
  "already a recursor", "obviously a dictionary", or "safe to unwrap".
- Do not special-case `PEqSeq`, `RecordType.rec`, `Stream.rec`,
  `UnitType.rec`, or any current fixture name as the implementation strategy.
- Do not add Lean automation, generated proof scripts, tactics, simp bundles,
  or proof-library work in this phase.
- Do not refresh goldens to hide the current failure. Promote known gaps only
  after reviewing the emitted artifact against this convention.
- Do not preserve fallback, backup, or legacy behavior that bypasses the
  explicit convention.
- Do not edit this goal document during execution to make the goal easier or
  broader. If reality differs from the plan, stop and report the decision point;
  update follow-up notes only after the design choice is made.

## In Scope

This phase covers recursor applications already accepted by the backend's
recursor path when their only blocker is raw/wrapped value sequencing.

In-scope surfaces:

- a value-domain scrutinee whose translated term has `BindingWrapped`;
- Lean recursor heads reached through `CompiledRecursor` when the failure is
  only the generic raw-scrutinee/value-result convention. This may include a
  `Stream.rec` occurrence, but not stream productivity, `MkStream` totality,
  `Prelude.fix`, or stream-specific semantic rewriting;
- recursor motives whose final result is a runtime value;
- case-handler binder conventions already handled by
  `translateCaseHandler`, including raw constructor fields and body-entry
  value shadows;
- dictionaries represented as ordinary record values, as long as the solution
  follows the same recursor convention used for non-dictionary values.

## Out Of Scope

The following must remain known gaps or boundary rows unless a later plan
explicitly includes them:

- adding support for unsupported direct recursors such as direct `Bool#rec`,
  `Nat#rec`, `Z#rec`, `Accessible`, or user datatypes;
- `ListSort`, `FunsTo`, algebraic enum encodings, loaded primitive/axiom
  declarations, and raw Lean injection policy;
- proof primitives and proof-valued obligation automation;
- stream totality/productivity proofs, `Prelude.fix`, or semantic rewrites for
  stream recursion;
- direct vector fallback/defaulting cleanup;
- higher-order proof-carrying wrappers;
- whole-module proof ergonomics, large crypto, SHA512, and final SAW-side
  replay UX.

## Core Convention

Lean's recursor receives a raw inductive scrutinee. Phase beta says ordinary
value computations may be wrapped in `Except String`. Therefore the recursor
emitter needs a first-class convention for the scrutinee/result boundary.

For a fully supplied supported recursor:

1. translate the scrutinee in its natural source shape;
2. translate recursor parameters, motive, indices, and case handlers according
   to recursor positions, not according to generated Lean syntax;
3. build a raw recursor call only with a raw scrutinee;
4. if the recursor result is value-domain, translate the motive so its body
   returns `Except String T`, independent of whether the scrutinee is raw or
   wrapped. Case bodies then produce wrapped results under the same motive;
5. if the translated scrutinee is wrapped and the recursor result is a
   value-domain result, emit:

   ```lean
   Bind.bind scrutinee (fun rawScrutinee =>
     <raw recursor call using rawScrutinee>)
   ```

6. if the translated scrutinee is raw and the recursor result is value-domain,
   emit the raw recursor call directly. Because the motive already returns
   `Except String T`, the recursor call's natural shape is already wrapped;
   do not add another `Pure.pure`;
7. if the recursor result is a type, proposition, proof, function-shaped result,
   or other raw-only position, require a convention that does not extract from
   `Except`. If no such convention is explicitly designed, a wrapped scrutinee
   in that situation must be rejected or left as a pinned known gap.

This is not a dictionary-specific rule. A dictionary is just a value. If a
dictionary-producing computation is wrapped, a raw dictionary projection may
occur only inside a `Bind.bind` continuation that receives the raw dictionary.

## Result-Shape Matrix

The implementation should make this matrix explicit. The exact Haskell data
type names may vary, but this decision table must be present in the code rather
than scattered among local booleans.

| Scrutinee shape | Motive/result kind | Emission |
| --- | --- | --- |
| raw | value result | raw recursor call with a motive returning `Except String T`; final shape is wrapped |
| wrapped | value result | `Bind.bind scrutinee (fun rawScrutinee => raw recursor call)` where the raw recursor call already returns `Except String T`; final shape is wrapped |
| raw | type/proof/raw result | raw recursor call; final shape is raw |
| wrapped | type/proof/raw result | reject with a clear diagnostic; no raw extraction from `Except` |
| raw | function-shaped result | raw recursor call; final shape is `BindingFunction` if the returned function convention is known |
| wrapped | function-shaped result | reject unless a separate eta-expanded function convention is explicitly designed; no raw extraction from `Except` |

The wrapped-scrutinee rows for raw and function-shaped results are the crucial
soundness boundary. An expression of type `Except String a` cannot supply an
`a` to a raw type/proof/function computation without assuming success. Haskell
must not make that assumption.

The recursor translator computes the recursor expression's natural shape. It
does not know the surrounding expected shape at this boundary. Later use sites
may adapt a `TranslatedTerm` according to their own expected convention, but the
recursor emitter itself must not add `Pure.pure` based on a guessed surrounding
context.

## Required Abstraction

Introduce or refactor toward a single recursor-convention decision. It can be
small and local, but it should have named concepts instead of independent
booleans that can drift.

One acceptable shape is:

```haskell
data RecursorResultMode
  = RecursorReturnsWrappedValue
  | RecursorReturnsRawTypeOrProof
  | RecursorReturnsFunction

data RecursorScrutineeMode
  = ScrutineeAlreadyRaw
  | ScrutineeWrappedValue

data RecursorConvention = RecursorConvention
  { recScrutineeMode :: RecursorScrutineeMode
  , recResultMode    :: RecursorResultMode
  , recFinalShape    :: BindingShape
  }
```

The names are not binding. The required property is that one function computes
the convention from:

- the translated scrutinee shape;
- the motive body classification;
- the existing Phase-beta value/type/proof position rules.

That function should be the only place that answers:

- should the motive body be wrapped with `Except`? For value results, the
  answer is yes independent of scrutinee shape;
- should case-handler bodies produce wrapped results?
- may the scrutinee be sequenced with `Bind.bind`?
- what `BindingShape` does the whole recursor expression provide?

Helper emission can then be simple:

- `emitRawRecursorCall rawScrutinee` builds `recHead preArgs rawScrutinee postArgs`;
- `emitValueRecursorResult` calls the raw recursor directly for a raw scrutinee
  and binds only the scrutinee for a wrapped scrutinee;
- `emitRawRecursorResult` requires a raw scrutinee and otherwise rejects.

This should simplify the current `motiveReturnsRaw`,
`motiveReturnsWrappedValue`, and `recursorReturnsValue` logic instead of adding
more parallel flags.

## Motive and Case Handler Rules

Motive translation remains position-sensitive:

- motive binders are raw because Lean recursors apply motives to raw inductive
  values;
- a value-producing motive in the Phase-beta path always returns
  `Except String T`, independent of scrutinee shape;
- type-producing, proposition-producing, proof-producing, and opaque
  type-family motives stay raw;
- function-shaped motive results are not type/proof results. They must be
  classified as function-shaped and either emitted with a known function
  convention or rejected. Do not misclassify them as raw type/proof results or
  wrap them as ordinary values;
- variable-headed type families must not be mistaken for value results.

Case handler translation must continue to respect constructor-field roles:

- structural constructor fields are raw recursor inputs;
- fields typed by datatype parameters use the actual translated parameter type;
- for value-producing recursor results, raw value fields may be shadowed at
  body entry with `Pure.pure` so the Phase-beta body sees wrapped values;
- for raw type/proof motives, fields stay raw and no value shadows are added.

Do not solve dictionary projection by changing all record case fields to raw or
all fields to wrapped. The field convention is already positional and should
remain so.

## Soundness Argument

The convention is sound because it uses only Lean-checked operations with their
ordinary meanings:

- `Pure.pure` embeds a raw value as a successful value computation;
- `Bind.bind` sequences a wrapped computation and exposes the raw value only in
  the success continuation;
- Lean's raw recursor sees only a raw scrutinee;
- type, proof, proposition, and function-shaped positions never consume an
  `Except` by assumption;
- dictionaries are not trusted specially. They are projected only after the
  computation that produced them has succeeded.

The Haskell side does not prove equivalence or totality. If a required raw value
is available only under `Except`, Haskell either sequences it in a value
computation or rejects. If a required raw type, proof, proposition, or function
would require extracting from `Except`, Haskell rejects. That is exactly the
Phase-beta semantic model.

## Main Risks

This task is small in code size but deep in semantics. The main risks are:

- result-classification mistakes: a recursor result misclassified as value,
  raw type/proof, or function-shaped can produce ill-typed Lean or hide an
  `Except` boundary;
- motive-shape churn: making value-producing motives always return
  `Except String T` is the principled rule, but it may perturb existing passing
  recursor output;
- error-erasure cheats: successful examples alone do not prove that
  `Except.error` propagates;
- stream scope creep: `Stream.rec` can pull in stream productivity,
  `MkStream`, or `Prelude.fix` semantics, which are out of scope here;
- function-valued recursor results: a sound eta-expanded convention may exist,
  but it is a separate design unless this phase explicitly adds it.

Derisk by making ambiguity reject. If classification is not obviously a
value-result, raw type/proof/raw-result, or known function result, emit a clear
SAW translation rejection and pin the row. Do not guess.

## Execution Order

Follow this order. Do not skip ahead to whole-module examples.

1. Commit the planning checkpoint before backend edits, so implementation can
   be reviewed against a stable goal.
2. Add focused tests before changing recursor behavior:
   - a wrapped-scrutinee/value-result row that should eventually conform;
   - a wrapped-scrutinee/raw-result row that must reject at SAW translation with
     a named diagnostic;
   - an `Except.error "sentinel"` observer for an emitted wrapped-scrutinee
     recursor function, proving the error is propagated rather than erased;
   - a raw-scrutinee/value-result row whose branch body is already effectful or
     error-producing, proving the motive result is already `Except String T`
     and is not double-wrapped.
3. Extract the explicit `RecursorConvention` decision. The first backend patch
   should be mostly structural: one convention decision, one emission switch,
   fewer scattered booleans.
4. Implement only the matrix rows covered by the convention. Reject unsupported
   raw/function cases instead of preserving old behavior.
5. Review the first emitted Lean artifacts manually. For each promoted row,
   check that:
   - a value-producing motive returns `Except String T`;
   - a raw-scrutinee recursor is not additionally wrapped with `Pure.pure`;
   - a wrapped scrutinee is sequenced with `Bind.bind`;
   - dictionary projection occurs only inside the bind continuation;
   - `Except.error` is not defaulted or erased;
   - there is no fixture-name, recursor-name, or generated-syntax special path.
6. Promote focused rows only after artifact review. Then try the target
   examples: `cryptol_module_simple`, `cryptol_polymorphic_class_dict`, and
   finally `sequences` sub-failure classification.

If any step demands a broader design, stop and report the decision point. Do
not silently expand the phase.

## Implementation Steps

1. Add the explicit recursor-convention decision near
   `translateRecursorAppWithShape`.
2. Replace the local result booleans with the convention object while keeping
   the existing motive/body classification logic as input.
3. Route motive translation and case-handler translation from the convention,
   not from independently recomputed predicates.
4. Ensure the raw recursor call builder always receives a raw scrutinee.
5. Emit the wrapped-scrutinee/value-result case with `Bind.bind`.
6. Emit the raw-scrutinee/value-result case as the raw recursor call whose
   motive already returns `Except String T`. Do not double-wrap it with
   `Pure.pure`.
7. Reject wrapped-scrutinee/raw-result cases with a diagnostic that names the
   recursor and says the backend cannot extract a raw result from an
   `Except`-wrapped scrutinee.
8. Reject wrapped-scrutinee/function-result cases unless this phase explicitly
   adds a checked eta-expanded function convention. Do not fabricate a raw
   function by closing over an unwrapped scrutinee.
9. Delete any legacy/fallback path made unreachable by the convention.

Keep each step small. If the implementation starts recognizing specific Lean
names or generated syntax, stop and redesign.

## Regression and Promotion Plan

Start with focused witnesses. Do not begin by refreshing whole-module goldens.

Required focused rows:

- keep `differential/record_projection_binder` passing;
- keep `drivers/cryptol_module_record_update` passing;
- keep `drivers/cryptol_module_point` passing;
- keep `proofs/point_shift_property` passing;
- add or update at least one boundary row for a raw type/proof/raw-result
  recursor with a wrapped value scrutinee. It must expect SAW translation
  rejection with the new diagnostic, not a Lean elaboration failure;
- add or update at least one observer that applies an emitted wrapped-scrutinee
  recursor function to `Except.error "sentinel"` and checks that the same error
  propagates. This prevents a fake rawification/defaulting implementation from
  passing only successful inputs;
- add or update at least one raw-scrutinee value-result recursor whose branch
  body is already effectful or error-producing, to pin that the motive result is
  `Except String T` and is not double-wrapped with `Pure.pure`;
- promote `differential/unit_recursor_raw_scrutinee` only if the emitted
  observer imports the backend artifact and differentially compares the result;
- promote `differential/cryptol_vector_eq_dictionary` only after the emitted
  artifact shows the dictionary projection occurs inside the general recursor
  convention, not through a dictionary special case.

Then re-run target examples:

- `drivers/cryptol_module_simple`;
- `drivers/cryptol_polymorphic_class_dict`;
- `drivers/sequences`, with sub-failures classified before any golden refresh.

Treat `differential/stream_helpers` carefully. Promote it only if the generic
recursor convention is sufficient and the emitted observer has no unresolved
`MkStream`, `fix`, productivity, rawifying-function, or stream-specific semantic
obligation. If any of those appear, keep it pinned and move that work to a
separate stream plan.

Final validation for the phase:

- `make -C otherTests/saw-core-lean conformance`;
- focused driver/proof rows listed above;
- `make -C otherTests/saw-core-lean test` to measure remaining classified
  failures, not to force a green full suite.

## Stop Conditions

Stop and ask for design review if any of these occurs:

- a desired emission requires a raw value, type, proof, or proposition from a
  wrapped scrutinee outside a value-result `Bind.bind` continuation;
- a desired emission requires a raw function from a wrapped scrutinee without a
  separately designed checked function convention;
- the fix appears to require proving stream productivity or fixed-point
  equivalence;
- the implementation wants to classify `RecordType.rec`, `PEqSeq`, or
  `Stream.rec` by name;
- an existing passing record/proof example would need a fixture-specific
  exception to remain green;
- the only way to make a row pass is to weaken a known gap, observer, or golden.

The AI may declare this goal done, rather than continue, if further progress
would require violating these rules or choosing among incompatible designs that
need user input.

## Done Criteria

This phase is complete when:

- the recursor convention is represented explicitly in the translator;
- wrapped-scrutinee/value-result recursors are sequenced through `Bind.bind`;
- raw, type, proof, proposition, and function-shaped recursors never silently
  consume wrapped scrutinees;
- dictionary recursor failures are fixed, rejected, or reclassified by the same
  convention used for non-dictionary values;
- focused conformance rows protect both the fixed gap and the passing record
  regressions;
- remaining target-example failures are classified as non-P0 work.

The backend need not automatically prove user obligations at the end of this
phase. The only requirement is sound, clear, auditable emission.
