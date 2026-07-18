# Position and Callee Conventions for Sound Phase-Beta Emission

**Date**: 2026-07-02

## Status

Design investigation note. Do not treat this as an implementation goal until it
has been reviewed and either accepted or split into a concrete execution plan.

This note responds to the proof-transport regression exposed during the
raw/wrapped recursor and dictionary work. The important conclusion is:

> A callee convention is necessary, but it is not enough by itself. The clean
> design is a position-indexed representation discipline, with callee
> conventions deriving expected positions for applications.

The shorter semantic contract for this design is
`doc/2026-07-02_position-callee-calculus.md`. Read that note first when the
question is "what are we claiming?", and read this note when the question is
"why did the current code lead us here?".

## Why This Note Exists

The raw/wrapped recursor task introduced a principled local abstraction:
`RecursorConvention`. That abstraction fixed real dictionary/record recursor
gaps without special-casing `PEqSeq`, `RecordType.rec`, or fixture names.

The full conformance run then exposed failures in proof rows such as
`obligations/proof_add_nat_assoc`:

```lean
Type mismatch
  ... pure zero_macro
has type
  Except String Nat
but is expected to have type
  Nat
```

That is not a dictionary or recursor-scrutinee problem. The local proof
primitive obligation is present. The failure is that a raw logical equality
eliminator was translated through the ordinary Phase-beta application path, so
its motive/branch was treated as a runtime value computation.

Fixing that by adding special cases for `Eq__rec`, `Nat`, or the proof rows
would be the wrong direction. The failure is evidence that the backend needs a
more explicit account of positions and callee conventions.

## Inputs Reviewed

- `saw-core-lean/doc/2026-06-26_phase-beta-expected-shape.md`
- `saw-core-lean/doc/2026-07-01_complete-wrapping-migration-goal.md`
- `saw-core-lean/doc/2026-07-02_raw-wrapped-recursor-dictionary-plan.md`
- `saw-core-lean/src/SAWCoreLean/Term.hs`
- `saw-core-lean/src/SAWCoreLean/SpecialTreatment.hs`
- `saw-core-rocq/src/SAWCoreRocq/Term.hs`
- `saw-core-rocq/src/SAWCoreRocq/SpecialTreatment.hs`
- `saw-core-rocq/rocq/handwritten/CryptolToRocq/SAWCoreScaffolding.v`

Two read-only audit agents were also used:

- Rocq backend review: Rocq is mostly table-driven at use sites. It does not
  have a raw/wrapped value-computation convention, but it does distinguish
  proof/type infrastructure through explicit mappings and handwritten shims.
- Lean backend review: the Lean backend has real pieces of the right design,
  but `BindingShape`, `shouldWrapBinder`, `natValueResult`, `UseMapsToWrapped`,
  proof contracts, and recursor conventions are not yet one position calculus.

A third theory pass reached the same central conclusion: the intended semantic
split is position-based, not name-based.

## Rocq Lessons

Rocq does not solve the Lean problem directly.

The Rocq backend has no active `Except String` Phase-beta convention. SAW
values, proofs, and types all translate into one Rocq term language. `error` is
realized in the support library as an axiom-like inhabitant, not as an explicit
effect.

What Rocq does teach is structural:

- use-site behavior is table-driven by `SpecialTreatment`;
- proof/type infrastructure is not translated by the same accidental path as
  ordinary computation;
- `Eq__rec` is mapped to a handwritten shim because SAW equality elimination is
  not simply arbitrary generated syntax;
- recursors either map to raw target recursors or to explicit support shims.

The Lean backend should keep the table-driven lesson, but enrich the table with
the semantic axis Rocq lacks: runtime computation versus logical/type/proof
position.

## Semantic Model

There are two related but distinct translations.

### Raw Type Translation

`T(τ)` is the Lean type corresponding to the SAWCore type expression `τ`.

Examples:

- `T(Bool) = Bool`
- `T(Nat) = Nat`
- `T(Vec n Bool) = Vec n Bool`
- `T(Eq α x y) = Prop`-level equality/proposition structure
- `T(sort k)` is a Lean universe/sort

This translation is used for type expressions, indices, propositions, proofs,
motives, and raw Lean support-library formals.

### Runtime Value Representation

`V(τ)` is the Lean representation of a SAW term when it is a runtime value
computation.

For ordinary value types:

```text
V(τ) = Except String (T(τ))
```

For function-shaped values, `V` is structural: the function's binder and result
positions each have their own expected representation. For a value-level
function from `α` to `β`, the Phase-beta shape is morally:

```lean
V(α) -> V(β)
```

This is why there is no sound general adapter:

```lean
(A -> Except String B) -> (A -> B)
```

Such an adapter would have to erase errors.

For type, proof, proposition, motive, and index positions, the expected
representation is raw. They do not acquire `Except`.

### Nat Is Not Special

The current implementation treats `Nat` specially because it is both a value
type and an index type. In the clean model, `Nat` is not an exception. Its
representation is determined by position:

- width/index `Nat`: raw `Nat`;
- proof/logical `Nat`: raw `Nat`;
- runtime computed `Nat`, such as `bvToNat x`: `Except String Nat`;
- raw support primitive formal expecting a `Nat`: raw, with a wrapped actual
  opened only in a continuation that preserves errors.

This removes the need for broad syntactic rules like "Nat is always raw" plus
repair predicates like `natValueResult`. The implementation may still migrate
incrementally, but the theory should not present Nat as a semantic special
case.

## Expected Shapes

The central abstraction should be an expected shape, not a question like
"should this syntax wrap?"

Illustrative shape:

```haskell
data ExpectedShape
  = ExpectRuntimeValue RawType
  | ExpectRaw RawReason RawType
  | ExpectFunction FunctionConvention

data RawReason
  = TypePosition
  | IndexPosition
  | ProofPosition
  | PropositionPosition
  | MotivePosition
  | RawLeanFormal
  | RawLogicalEliminator
  | StructuralRecursorField
```

The exact Haskell names do not matter. The required property is that every
translation site can explain why a term is expected raw, wrapped, or
function-shaped.

`BindingShape` should eventually carry enough information to avoid collapsing
all raw terms together. Today `BindingRaw` means "not currently an outer
`Except`"; it does not say whether the term is a raw value, index, proof, type,
or logical eliminator result. That overloading is a source of design pressure.

## Central Operations

The clean design has two central operations:

```haskell
translateNatural :: Term -> m TranslatedTerm
adaptTo          :: ExpectedShape -> TranslatedTerm -> m Lean.Term
```

or equivalently:

```haskell
translateAt :: ExpectedShape -> Term -> m TranslatedTerm
```

Allowed adaptations:

- raw value to runtime value: `Pure.pure`;
- runtime value to raw value only inside `Bind.bind`, with a continuation whose
  result keeps the error observable or whose precondition is Lean-checked;
- runtime value to runtime value: identity;
- raw type/index/proof/proposition/motive to raw: identity;
- raw function to wrapped-function formal by eta-expanding and adapting each
  argument/result slot according to an explicit function convention;
- proof-carrying helper invocation only after emitting/consuming the declared
  Lean proposition.

Forbidden adaptations:

- wrapped value to raw value by defaulting;
- wrapped proof/type/proposition/motive;
- arbitrary wrapped function to raw function;
- emitted-Lean AST inspection to decide a term is "really pure";
- weakening or hiding a proof obligation to make a row pass.

## Callee Conventions

A callee convention is how an application derives expected shapes for its
arguments and result. It should live in or beside `SpecialTreatment`, not be
inferred from generated Lean syntax or fixture names.

Illustrative shape:

```haskell
data CalleeConvention
  = CalleePhaseBetaDefinition FunctionConvention
  | CalleeRawLeanTarget RawCalleeConvention
  | CalleeRawLogical LogicalCalleeConvention
  | CalleeWrappedHelper WrappedHelperConvention
  | CalleeProofObligation ProofContract
  | CalleeMacro MacroConvention
  | CalleeReject Text
```

### Phase-Beta Definition

A definition emitted by this backend in Phase-beta form already expects
Phase-beta arguments and returns Phase-beta results. It should not be called by
binding all arguments down to raw values.

### Raw Lean Target

A raw Lean target, such as many support primitives, expects raw Lean formals.
For value formals, a wrapped actual may be opened with `Bind.bind` if the whole
application result remains a runtime value. The raw result may be lifted with
`Pure.pure`.

This is the principled version of the current `argumentBindPlan` /
`buildLifted` path.

### Raw Logical Callee

Raw logical callees include equality eliminators and proof/type infrastructure:
`Eq__rec`, `sym`, `trans`, `eq_cong`, `coerce__def`, proof lemmas, and similar
SAW Prelude logic.

This convention is not the same as "all arguments raw". A proposition about a
runtime value may mention the runtime representation of that value. For
example, equality over a value-domain type may compare `Except String T` terms.

The key difference is that the callee's result and motive structure live in the
logical/type layer unless a separately declared value boundary says otherwise.
The application path must not decide to wrap a raw logical eliminator merely
because the syntactic result type is `Nat` or variable-headed.

The `proof_add_nat_assoc` failure is precisely this violation:

- `Eq__rec` is a raw logical eliminator;
- the motive result is a raw logical `Nat` used by proof transport;
- generic Phase-beta application classified the branch as
  `Except String Nat`;
- Lean correctly rejected the mismatch.

### Wrapped Helper

Wrapped helpers are support-library functions whose signatures already speak
the runtime representation, such as checked vector helpers and monadic folds.
They must declare each formal's convention explicitly.

The current `UseMapsToWrapped` is a good seed, but it is not complete because
the result shape is implicit and function arguments do not yet carry full
argument/result metadata.

### Proof Obligation Emitter

Some source operations cannot be faithfully emitted by computation alone. The
backend may emit a Lean proposition and a local proof placeholder, or call a
checked helper that consumes such evidence.

This is the right pattern for:

- partial division/modulus;
- vector bounds;
- `fix`;
- raw `error`;
- `unsafeAssert`;
- SAW proof primitives and lemma axioms.

The Haskell side may construct the proposition. It must not prove or weaken it.

### Macro

Macros are not exempt. A macro must declare:

- how many source arguments it consumes;
- the expected shapes of those arguments;
- the shape of the produced term;
- the convention for any remaining arguments.

## Equality and Proof Transport

Equality is the most important stress test for the design.

SAW `Eq α x y` lives in `Prop`, so the proposition itself is raw. But the type
being compared may be a runtime representation:

- equality over raw type/index/proof data compares raw terms;
- equality over runtime values compares their runtime representations;
- equality proofs themselves are raw Lean proofs.

`Eq__rec` is a raw logical eliminator. Its motive is a type/proposition family,
not a runtime computation just because the motive body syntactically names a
value type. If the backend wants an equality transport that produces a runtime
value, that must be represented as an explicit value boundary:

- either the motive result is explicitly the runtime representation;
- or the raw transported value is lifted into runtime form at the boundary;
- or the operation rejects until such a convention is designed.

This is a design point, not a fixture patch.

## Recursors in This Model

The current `RecursorConvention` is mostly consistent with this model. It is a
specialized callee/position convention for raw Lean recursors:

- raw Lean recursors consume raw scrutinees;
- wrapped scrutinees can be opened only inside `Bind.bind`;
- opening is allowed only when the final recursor result preserves errors;
- raw/type/proof/proposition recursor results never extract from `Except`;
- dictionaries are just values and receive no special trust.

The design issue is not the recursor convention itself. The issue is that
recursor result classification still relies on local predicates rather than the
same expected-shape machinery that applications and proof transport should use.

## Current Rough Edges

1. `BindingShape` is too coarse.
   It tracks raw/wrapped/function, but not why a raw term is raw.

2. `shouldWrapBinder` is doing position work by inspecting syntax.
   It excludes `Nat`, `Eq`, `Pi`, and `Sort`, while `natValueResult` later
   repairs some result positions. This is a symptom of the missing
   expected-shape abstraction.

3. `DefPreserveRaw` is def-site only.
   A raw-emitted proof/type definition can still be used through the generic
   Phase-beta application path. The semantics needs a use-site logical
   convention, not an accidental inference from def-site treatment.

4. Proof contracts and reject entries depend on dispatch ordering.
   Fully applied proof primitives are intercepted before the reject table, but
   residual uses reject. This can be sound, but it should be made explicit as a
   convention rather than an audit surprise.

5. The expected-shape TODO currently claims callee convention migration is
   complete. The proof-transport failure shows it is not complete in the
   stronger semantic sense required here.

6. Documentation around `error_unrestricted` is stale in some places. The live
   design is value `error` as `saw_throw_error` and raw `error` as a visible
   `False` obligation.

## Soundness Argument

The proposed design is sound by construction if every emitted term is produced
under an expected shape and every adaptation is one of the allowed adaptations.

Induction principle:

1. Type, index, proposition, proof, and motive positions translate to raw Lean
   terms checked by the Lean kernel.
2. Runtime value positions translate to `Except String T`.
3. Raw-to-runtime value adaptation is `Pure.pure`, preserving successful value
   semantics.
4. Runtime-to-raw adaptation occurs only in a continuation that receives the
   raw value from `Bind.bind`, so errors are propagated rather than erased.
5. Proof-carrying operations expose their preconditions as Lean propositions;
   unresolved placeholders cannot be accepted by the final checker.
6. Unsupported or ambiguous positions reject, which is sound because no Lean
   proof is produced.

No Haskell-side semantic equivalence is trusted. Haskell only chooses a
declared convention, constructs syntax, emits obligations, and rejects when no
convention applies.

## Impact on the Current Raw/Wrapped Recursor Goal

The current recursor work should not be thrown away. It is a valid local
instance of the larger position/callee design.

But the current goal should not be declared complete until we decide how to
handle the raw logical callee boundary. Otherwise the full conformance suite
will continue to expose failures that look like wrapping regressions but are
really missing expected-shape information.

Recommended shift:

1. Keep the explicit `RecursorConvention`.
2. Stop expanding the recursor goal to patch proof rows locally.
3. Add a new accepted design section or follow-up goal for position/callee
   conventions.
4. Treat `proof_add_nat_assoc` and adjacent rows as the load-bearing examples
   for raw logical callees.

## Implementation Direction

This should be a deliberate refactor, not a quick patch.

1. Introduce small explicit data types for expected shapes and callee
   conventions. Initially they can wrap existing behavior rather than change
   every site.
2. Extend `UseSiteTreatment` or a sibling table with a use-site convention
   axis. Do not infer use-site logical behavior from `DefPreserveRaw`.
3. Migrate `originalDispatchWithShape` to dispatch through callee convention:
   raw Lean target, Phase-beta definition, raw logical callee, wrapped helper,
   proof obligation, macro, reject.
4. Make `Eq`, `Refl`, `Eq__rec`, and the raw Prelude proof combinators the
   first raw-logical examples. Add focused tests before broad migration.
5. Re-express `RecursorConvention` as the recursor instance of this model, or
   at least make its result classification call the shared expected-shape
   predicates.
6. Gradually demote `shouldWrapBinder`, `natValueResult`, `skipBinderWrap`, and
   `inRecursorCaseBinder` from semantic authorities to compatibility plumbing.
7. Keep ambiguity loud. If the convention cannot say whether a term is runtime
   or logical, reject and add a fixture.

## Regression Targets

Focused rows that should guide the design:

- `obligations/proof_add_nat_assoc`
- `obligations/proof_eq_nat_add_0`
- `obligations/proof_eq_nat_add_s`
- `obligations/proof_eq_nat_add_comm`
- `obligations/proof_equal_nat_to_eq_nat`
- smoke test: `Eq.rec proof supplied to coerce stays raw`
- existing `Eq` over wrapped values tests, to ensure raw logical convention
  does not incorrectly rawify propositions about runtime values
- recursor rows promoted by the raw/wrapped recursor task:
  `recursor_wrapped_scrutinee_error_propagates`,
  `recursor_wrapped_scrutinee_function_result_error_propagates`,
  `unit_recursor_raw_scrutinee`,
  `cryptol_vector_eq_dictionary`

## Stop Conditions

Stop and redesign if an implementation wants to:

- classify by fixture name or generated Lean syntax;
- use `DefPreserveRaw` as a hidden proxy for use-site semantics without an
  explicit convention;
- add a raw logical convention that simply translates all arguments raw and
  breaks equality over runtime values;
- keep wrapping proof/type/motive terms because it makes a value example pass;
- convert wrapped functions to raw functions without a proof-carrying contract;
- accept unresolved `sorry` obligations as completed backend evidence.

## Open Questions

1. How much type information should `BindingShape` carry immediately?
   Full `ExpectedShape` payloads are cleaner, but a staged migration may be
   safer.

2. Should raw logical callees be represented as explicit argument-mode tables,
   or can some be derived from their SAWCore types plus a logical-result mode?
   `Eq__rec` suggests at least motives need explicit handling.

3. Should `translateDefDoc` translate the body against the declared top-level
   type as an expected shape, instead of translating body and type separately
   and applying only a closed-value fixup?

4. Are there legitimate runtime uses of raw `Eq__rec` that produce value
   computations? If yes, they need an explicit value-boundary convention rather
   than the current generic Phase-beta guess.

5. Which stale soundness docs should be updated once this design is accepted,
   especially around `error_unrestricted`?
