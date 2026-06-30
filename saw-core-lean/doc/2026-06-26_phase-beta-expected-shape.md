# Phase beta expected-shape architecture

**Date**: 2026-06-26
**Status**: proposed design record for the next stabilization work.
**Scope**: the Phase beta `Except String` wrapping discipline in
`SAWCoreLean.Term`, its interaction with Lean signatures, and the
abstraction that should replace local wrap special cases.

## Decision

Keep the Phase beta semantic model: SAW value computations translate to
Lean computations in `Except String`, while type, index, motive, and
proof positions stay raw.

Change the implementation model. The translator should stop asking
"does this syntax need wrapping?" at individual call sites. It should
ask one central question:

> What Lean shape is expected at this position?

Every binder, argument, result, recursor case field, constructor field,
and let-bound variable should be translated or adapted according to that
expected shape. The abstraction is a position/calling-convention
abstraction, not a growing list of pattern exceptions.

## Why the current code is close but not stable

The current implementation has the right semantic ingredients:

- `shouldWrapBinder` separates value-like types from sorts, propositions,
  `Nat`, `Eq`, and Pi types.
- `skipBinderWrap` keeps type/index/motive binders raw.
- `inRecursorCaseBinder` keeps case-handler binders compatible with
  Lean-generated recursor signatures.
- `wrappedVars` records some variables whose Lean type is
  `Except String _`.
- `argumentBindPlan` decides where an application needs `Bind.bind`.
- `isLikelyWrappedTerm` recognizes some wrapped results syntactically.

Those pieces are useful, but they are not one abstraction. They encode
position information through booleans, whitelists, and local syntactic
checks. That is why each new hard case looks like another patch:

- `Nat` is raw as an index but wrapped as the result of value
  computations such as `bvToNat`.
- Proof recursors and type-producing recursors must stay raw even when
  their scrutinee is a value.
- `Stream.rec` case fields are structural raw constructor fields, but
  `RecordType.rec` fields whose type is a datatype parameter should use
  the translated actual parameter type.
- A variable-headed type can be a value-domain formal in one position
  and a motive/type-family result in another.
- A raw Lean primitive, a Lean constructor, a Lean recursor, and a
  Phase-beta-emitted SAW definition do not all expect the same argument
  convention.

The most recent failing shape, `RecordType.rec`, exposes the missing
abstraction clearly. The case handler currently knows only "the first N
binders are constructor fields". That is insufficient. It must know
which constructor fields are structural raw fields and which are fields
whose Lean type is the actual datatype parameter supplied to the
recursor.

## Core invariant

There are two layers:

1. **Raw type translation**: `T(tau)` is the Lean type corresponding to
   a SAW type expression `tau`.
2. **Expression translation at a position**: a SAW term `e : tau`
   translates either as a raw Lean expression of type `T(tau)` or as a
   wrapped Lean expression of type `Except String (T(tau))`, depending
   on the position.

Default Phase beta expression shape:

| SAW position | Expected Lean shape |
|---|---|
| Runtime value computation | `Except String (T(tau))` |
| Type expression / sort expression | raw |
| Dependent index argument | raw |
| Proposition / proof term | raw |
| Motive binder / type-family binder | raw |
| Lean recursor structural field | raw, then adapted for the case body if needed |
| Datatype-parameter field | the already translated actual datatype parameter type |

This is a position rule. It is not a syntactic type-name rule.

`Nat` is the main example. A `Nat` used as `Vec n alpha`'s index is raw.
A `Nat` returned by a value computation is `Except String Nat`. A raw
`Nat` formal binds a wrapped actual only when the actual is known to be
wrapped.

## Proposed abstraction

The implementation should introduce explicit expected shapes and
binding shapes. The exact Haskell names can vary, but the concepts
should be present.

```haskell
data ExpectedShape
  = ExpectRaw RawReason Lean.Type
  | ExpectWrapped Lean.Type
  | ExpectTypeLike Lean.Type
  | ExpectFunction [ExpectedBinder] ExpectedShape

data RawReason
  = TypePosition
  | IndexPosition
  | ProofPosition
  | MotivePosition
  | RawLeanFormal
  | StructuralRecursorField

data BindingShape
  = BoundRaw Lean.Type
  | BoundWrapped Lean.Type
  | BoundFunction FunctionShape
  | BoundTypeLike Lean.Type

data CalleeConvention
  = CalleeRawLean
  | CalleePhaseBeta
  | CalleeWrappedHelper
  | CalleeMacro MacroConvention
```

`ExpectedShape` says what a use site expects. `BindingShape` records
what a variable provides after it has been introduced. `CalleeConvention`
says what a named Lean target expects at its formals and returns.

The current `wrappedVars :: Set Lean.Ident` should become, or be
wrapped by, a map from Lean identifiers to `BindingShape`. A set can
only answer "is this variable an outer `Except`?". It cannot represent
function-shaped values such as:

```lean
Except String A -> Except String A -> Except String Bool
```

That function shape is exactly what the `RecordType.rec` failure needs
to preserve.

## Central operation

The translator needs one central operation:

```haskell
translateAt :: ExpectedShape -> Term -> m (Lean.Term, BindingShape)
```

or an equivalent pair of operations:

```haskell
translateNatural :: Term -> m (Lean.Term, BindingShape)
adaptTo        :: ExpectedShape -> (Lean.Term, BindingShape) -> m Lean.Term
```

The important rule is that adaptation is centralized.

Allowed adaptations:

- raw value to wrapped value: `Pure.pure raw`
- wrapped value to raw value: `Bind.bind wrapped (\x => ...)`, in an
  application/recursor context where the continuation uses `x`
- wrapped value to wrapped value: identity
- raw type/index/proof to raw type/index/proof: identity
- proof/type to wrapped: forbidden
- wrapped proof/type: forbidden by construction
- wrapped function to raw function: forbidden unless a named adapter has
  enforced or proved preconditions

The last item is the key guardrail. There is no general, sound function:

```lean
(A -> Except String B) -> (A -> B)
```

because it would have to erase errors. Any place that appears to need
that conversion must either:

- use a target whose formal accepts the wrapped function,
- use a support-library adapter whose preconditions are enforced by the
  translator or proved in Lean, or
- reject translation.

This rule prevents "just shadow it with a lambda" from becoming an
unsound universal escape hatch.

## Soundness surface

The backend has one hard requirement: emitted Lean must never prove a
SAW obligation that is false in SAW's semantics. There are no acceptable
"mostly sound" cases.

That requirement divides the implementation surface into four classes.

### Kernel-checked surface

This is the preferred surface. The translator emits Lean definitions and
the Lean kernel checks them against their stated types. Ordinary
Phase-beta lifting belongs here:

- `Pure.pure` injects raw values into `Except`.
- `Bind.bind` sequences wrapped computations and propagates errors.
- raw type/index/proof positions do not mention `Except`.
- equality goals remain `Prop`, possibly over wrapped values.

If the emitted term elaborates, Lean has checked that the raw/wrapped
types line up. Elaboration alone does not prove semantic faithfulness,
but it prevents many classes of accidental unsound coercion.

### Translator rejection surface

When the backend cannot emit a faithful Lean term, it must reject at
translation time. Rejection is sound: SAW receives no Lean proof.

This is the correct response for:

- a recursor whose case order or motive convention cannot be mapped
  faithfully;
- a wrapped-function-to-raw-function demand with no enforced adapter;
- a primitive whose Lean target would require an unproved semantic
  equation;
- any future position that does not fit the expected-shape calculus.

Rejecting more programs is acceptable. Emitting a plausible but
semantically different Lean term is not.

### Axiomatic surface

Some Lean support-library declarations are axioms or opaque primitives.
Those are part of the trusted base, not exceptions. They are acceptable
only when their statement is a faithful transposition of the SAW
primitive's intended meaning, and they must be audited as such.

The expected-shape design should not add new axioms. If it seems to need
one, that is a design review point, not an implementation detail.

### Adapter surface

Adapters are the dangerous surface. A rawifying adapter from a wrapped
function to a raw function can hide errors:

```lean
(A -> Except String B) -> (A -> B)
```

There is no total, sound implementation of this type for arbitrary
inputs. Any adapter with this character is forbidden unless its
precondition is enforced, proved, or encoded in the type.

Acceptable adapter patterns:

- **Type-preserving adapters**: the adapter keeps errors observable in
  the result type, e.g. it returns `Except String ...`.
- **Proved-unreachable adapters**: the translator emits the adapter only
  after checking a syntactic condition that implies the error branch is
  unreachable, and that implication is backed by a Lean theorem or a
  separately audited SAW/translator invariant.
- **Total raw adapters**: the adapter never consumes an `Except` value,
  so it cannot erase an error.

Unacceptable adapter patterns:

- replacing `Except.error` with `default`;
- catching an error and manufacturing a raw value;
- relying on "this should not happen in generated Cryptol" without an
  enforced syntactic gate or proof;
- adding a helper because it makes Lean elaborate while changing the
  meaning of SAW errors.

Under this requirement, existing or proposed helpers such as `mkStreamM`
must be reviewed carefully. If they convert per-index
`Except String alpha` into a raw `Stream alpha` by defaulting on errors,
they are not sound as general adapters. They are acceptable only if the
backend enforces a narrow input class where errors cannot occur and that
fact is justified by a checked theorem or a documented, test-pinned
translator invariant. Otherwise the backend must reject that shape or
choose a representation that keeps the error observable, such as
`Except String (Stream alpha)` with no per-index error erasure, or
`Stream (Except String alpha)` if downstream recursor design can support
it faithfully.

## Callee conventions

Application translation must be driven by the Lean target's calling
convention.

### Raw Lean targets

Raw Lean targets include most handwritten primitives, constructors, and
Lean-generated recursors. Their value formals are raw Lean values.

For a raw target:

1. Translate each actual in its natural Phase beta shape.
2. For each raw value formal, bind a wrapped actual with `Bind.bind`.
3. Pass type, index, and proof arguments raw.
4. Apply the raw target to raw values.
5. If the target result is a value result, wrap the raw result with
   `Pure.pure`.

This is the principled version of the current `argumentBindPlan` and
`buildLifted`.

### Phase-beta emitted SAW definitions

A definition emitted by this backend has Phase-beta formals and result.
For example, a value function over bitvectors should have a Lean type
like:

```lean
Except String (Vec 8 Bool) -> Except String (Vec 8 Bool)
```

A call to such a definition should pass wrapped value arguments directly
and receive a wrapped result directly. It should not bind the argument
down to raw and call the definition at raw types.

This is a distinct convention from raw primitives. If the backend moves
toward more compositional emission, this distinction becomes
load-bearing.

### Wrapped helpers

Some support-library helpers intentionally have wrapped signatures:
`genM`, `foldrM`, `iteM`, `mkStreamM`, `atWithDefaultM`, and similar
Phase-beta helpers. These should be declared as wrapped helpers in the
callee-convention table, not rediscovered by string matching in
`isLikelyWrappedTerm`.

The current `UseMapsToWrapped` is a useful seed, but the convention
should be more explicit: formals and result shapes should be part of
the use-site treatment.

### Macros

Macros are not exempt from shape discipline. A macro should declare the
shape of the term it returns and the expected shape of any remaining
arguments. If a macro expands to a raw Lean primitive, it uses the raw
callee convention. If it expands to a wrapped helper, it uses the
wrapped-helper convention.

## Binder conventions

### Value lambda and Pi binders

Value-level SAW binders normally introduce wrapped bindings:

```lean
fun (x : Except String (T tau)) => ...
```

A binder stays raw when the position is known to be type/index/proof
like, for example a numeric width parameter used in later binder types
or the return type.

The current `typeArgPositions` idea is the right seed, but the result
should be an expected-shape decision for the binder, not a transient
boolean flag.

### Quantifiers

SAW verification conditions quantify over raw program inputs, not over
`Except.error` values. A quantifier over value-domain inputs should
therefore introduce raw Lean variables and shadow them inside the body
with `Pure.pure` when the body is a Phase-beta computation.

This is not an exception to Phase beta. It is a different binder
position: a logical quantifier position, not a runtime computation
lambda.

### Motives and type families

Motive binders are raw. A recursor supplies a raw scrutinee to the
motive. A motive that produces a type or proof stays raw. A motive that
produces a value-domain result returns a wrapped value type in its body.

This distinction must remain explicit because binding a proof-producing
recursor through `Except` is both ill-typed and unsound.

## Recursor case handlers

Recursor case handlers need a per-binder plan, not just an arity.

The plan is derived from:

- the `CompiledRecursor`,
- the constructor order,
- each constructor's `CtorArgStruct`,
- the translated actual datatype parameters supplied to the recursor,
- the motive result shape.

Conceptually:

```haskell
data CaseBinderRole
  = StructuralField RawType
  | ParameterField Int Lean.Type
  | RecursiveField RawType
  | MotiveResultBinder ExpectedShape
```

Rules:

- A structural constructor field is bound at the raw constructor-field
  type required by Lean's recursor. If the case body uses it as a
  Phase-beta value, introduce a body-entry adapter such as
  `let x := Pure.pure x`.
- A field whose constructor type is exactly a datatype parameter is
  bound at the translated actual parameter type. Do not reclassify it
  from the constructor's source syntax.
- If the actual parameter type is a wrapped function shape, record the
  binding as a `BoundFunction` with wrapped argument/result convention.
  Do not eta-expand it as if it were a raw function.
- Binders that come from a function-valued motive result are ordinary
  value binders for that returned function. They are not constructor
  fields and should use normal Phase-beta binder rules.

This explains the difference between the current hard cases:

- `Stream.MkStream : (Nat -> alpha) -> Stream alpha` has a structural
  function field. Lean's recursor supplies `s : Nat -> alpha` raw.
  The case body may need an adapter to use `s i` as a wrapped value.
- `RecordType.RecordValue : alpha -> beta -> RecordType s alpha beta`
  has fields whose types are datatype parameters. If the recursor is
  instantiated with
  `alpha = Except String A -> Except String A -> Except String Bool`,
  the case binder for that field already has the wrapped-function type.
  It must not be rebound as raw `A -> A -> Bool`.

The current arity-only split is a useful interim repair, but it is not
the final abstraction.

## Constructor applications

Constructors are raw Lean targets unless explicitly mapped to a wrapped
helper. That means a constructor application follows the raw-callee
rule: bind wrapped field actuals to raw values, call the constructor,
and wrap the constructed result if the expression is a runtime value.

Higher-order constructor fields require special care. If a constructor
expects a raw function field such as:

```lean
Nat -> alpha
```

and the natural Phase-beta translation of the actual function is:

```lean
Nat -> Except String alpha
```

there is no general sound adaptation to the raw function type. The
translator must use a declared helper whose preconditions are enforced
or proved, or reject.

This keeps support helpers principled. `mkStreamM` is not a pattern
patch for `Stream`; it is a declared adapter for one rawifying boundary
that must satisfy the adapter rules in "Soundness surface". If it
defaults on `Except.error` for inputs the translator can emit, it is not
sound and must be replaced or made unreachable by construction.

For ordinary first-order constructors, no helper is needed:

```lean
Bind.bind x (fun xRaw =>
  Bind.bind y (fun yRaw =>
    Pure.pure (Ctor xRaw yRaw)))
```

## Let bindings and sharing

Let-bound shared subterms should record their `BindingShape` in the
environment. The current `isLikelyWrappedTerm` whitelist is a
transitional approximation.

The robust rule is:

1. Translate the RHS and obtain its shape.
2. Bind the Lean name to that shape in the environment while
   translating the body.
3. At a later use site, adapt based on the recorded shape.

This removes the need to recognize wrappedness from Lean syntax such as
`Bind.bind`, `Pure.pure`, helper names, or `.rec` heads.

## Variable-headed types

Variable-headed types are not a special case. They are the reason the
expected-shape abstraction is necessary.

A type variable can appear:

- as a type-level argument, where it is raw;
- as the type of a runtime value, where values of that type are wrapped;
- as a datatype parameter that already contains a Phase-beta function
  shape;
- as a motive result, where it may be type-like or proof-like.

The translator should not decide based on "the head is a variable".
It should decide based on the expected position and the binding shape
known for that variable.

This resolves the pressure around `Eq`, `Eq.rec`, `coerce`, and record
fields without creating a blanket "wrap all variable heads" rule.

## Proofs and propositions

Proofs and propositions stay raw.

This is not optional. Translating a proposition to
`Except String Prop` would allow an error value to inhabit a proof
obligation. That would make the backend unsound.

For equality over values, the equality's carrier may itself be a
wrapped value type:

```lean
Eq (Except String (Vec 8 Bool)) lhs rhs
```

The proposition `Eq ...` remains raw `Prop`; only the values being
compared live in `Except`.

Recursors whose motives produce types or proofs also stay raw. The
scrutinee is only unwrapped through `Bind.bind` when the recursor result
is a value computation.

## Soundness argument

The design supports the intended faithfulness statement:

> If SAW evaluates a value expression `e : tau` to a value `v`, the Lean
> translation at wrapped value position evaluates to `Except.ok T(v)`.
> If SAW evaluates `e` to an error, the Lean translation evaluates to an
> `Except.error` carrying that error. Type, index, and proof positions
> translate raw and cannot be inhabited by `Except.error`.

The proof is by structural induction over translation positions:

- Value literals and raw constructor results enter the computation with
  `Pure.pure`.
- Value applications sequence wrapped arguments with `Bind.bind`, so an
  error in any argument propagates to the whole computation.
- Raw type/index/proof positions never introduce `Except`, so they
  cannot use an error as a type, index, or proof.
- Recursor scrutinees are unwrapped only for value-producing recursors;
  type- and proof-producing recursors are applied raw.
- Case-handler structural fields are raw because Lean's recursor
  supplies raw constructor data; any use of them in value computations
  goes through explicit raw-to-wrapped adaptation.
- Datatype-parameter fields use the translated actual parameter type,
  preserving higher-order Phase-beta structure through records and
  polymorphic datatypes.
- Let bindings preserve the shape of their RHS in the environment.

The only operations not justified by this induction are rawifying
adapters from wrapped functions to raw functions. Those must satisfy the
adapter-surface rules above, or translation must reject. This is the
boundary that keeps the design from silently erasing errors.

## Robustness checklist

The expected-shape design handles the known hard cases as follows:

| Case | Expected-shape answer |
|---|---|
| `Nat` width/index | raw `IndexPosition` |
| `Nat` result of `bvToNat`/`intToNat` | wrapped value result |
| Raw primitive over values | bind wrapped actuals, call raw primitive, wrap result |
| Phase-beta emitted function | pass wrapped actuals directly |
| `Eq` over values | raw `Prop` comparing wrapped values |
| `Eq` over types/proofs | raw throughout |
| `coerce` value argument | adapt the coerced value; keep equality proof raw |
| Type-producing recursor | raw scrutinee and raw result |
| Proof-producing recursor | raw scrutinee and raw proof result |
| Value-producing recursor | bind wrapped scrutinee, apply raw recursor, wrapped result |
| `Stream.rec` structural field | raw field with body-entry adapter |
| `RecordType.rec` parameter field | actual parameter type, no raw eta shadow |
| Shared let-bound wrapped term | environment records `BoundWrapped` |
| Shared let-bound raw term | environment records `BoundRaw` |
| Higher-order raw constructor field | declared adapter or reject |

This checklist should become regression coverage as the implementation
is refactored.

## Implementation direction

The next implementation should be deliberately small but should move
toward this abstraction.

1. Add an internal expected-shape/binding-shape data type near the
   existing Phase beta helpers, or in a small `SAWCoreLean.PhaseBeta`
   module if that keeps `Term.hs` readable.
2. Replace `wrappedVars :: Set Lean.Ident` with a shape environment, or
   add a shape environment beside it and migrate uses incrementally.
3. Extend `SpecialTreatment` use-site entries with callee conventions
   for raw Lean targets, wrapped helpers, and macros.
4. Replace the recursor case-handler arity split with a per-binder plan
   derived from `CtorArgStruct` and translated actual datatype
   parameters.
5. Make constructor application use the same callee-convention/adaptation
   path as ordinary raw targets.
6. Retire `isLikelyWrappedTerm` once let bindings and helper calls carry
   explicit result shapes.
7. Keep `skipBinderWrap` and `inRecursorCaseBinder` only as temporary
   compatibility plumbing while call sites migrate; they should not be
   the long-term public representation of positions.

Do not refresh golden files until generated Lean elaborates under this
discipline. Golden diffs before this point would lock in transitional
syntax rather than the architecture.

## Acceptance criteria

The design should be considered implemented when:

- generated driver Lean elaborates without relying on stale `.good`
  files;
- the focused `cryptol_module_simple` record/recursor case elaborates
  without raw eta-shadowing a datatype-parameter function field;
- stream constructor and stream recursor cases elaborate through declared
  adapters or explicit rejection, not through accidental rawification;
- `Eq.rec` and `coerce` keep proofs raw while adapting only value terms;
- no support-library helper silently erases `Except.error` for any input
  the translator can emit;
- the full `saw-core-lean-smoketest` and `cabal build exe:saw` pass;
- a direct Lean sweep over generated driver `.lean` files passes before
  `.lean.good` regeneration.

## Relationship to earlier docs

This note refines `2026-05-11_beta_replan.md` and
`2026-05-14_wrap-invariant-audit.md`.

It agrees with the earlier semantic decision: value computations use
`Except String`; propositions, types, motives, and indices do not.

It changes the implementation recommendation from "patch the remaining
wrap gaps" to "represent expected shape explicitly". The goal is to make
future hard cases classify into a small set of position/callee
conventions. If a new case does not fit those conventions, the correct
backend behavior is to reject or extend the design with a checked
adapter/precondition, not to add another local syntactic exception.
