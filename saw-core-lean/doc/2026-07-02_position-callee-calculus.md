# Position/Callee Calculus

**Date**: 2026-07-02

## Purpose

This note gives the small semantic model behind the SAWCore-to-Lean backend's
raw/wrapped convention. It is intentionally shorter and more abstract than an
implementation plan. Its job is to make the design reviewable:

> For every source term, the emitted Lean shape is determined by the source
> term, the expected position, and the callee convention. Haskell does not
> prove semantic equivalences; it only follows this representation discipline,
> emits checked obligations, or rejects.

This is not a full formalization of SAWCore. It is the contract the Haskell
emitter must satisfy so that later Lean-side proof work has a sound target.

## Implementation Status (2026-07-11)

The calculus is now the implementation, not an approximation of it
(position-directed translation plan, Slices 0–7 complete):

- Positions are `ExpectedPosition`/`RawReason` values; callee
  conventions are `ArgMode`/`ResultMode` contract tables plus the
  declared `FunctionConvention`, `MotiveConvention`, `EqRecConvention`,
  and `RecursorConvention` records; production records
  (`TranslatedTermAt`) are the single source of truth for what a
  translation produced.
- Adaptation happens only at the `adaptTo` chokepoint; the forbidden
  adaptations below are unrepresentable (`ForbiddenAdaptation`), never
  defaulted.
- Equality subjects classify by the operand-domain rule
  (`standaloneEqualitySubjectRep`); no surround declares a subject
  representation.
- The value-domain result rule has a single authority
  (`phaseBetaResultIsValue`); the value-domain predicates
  (`shouldWrapBinder`, `isVariableHead`, `natValueResult`) are
  documented convention-internal helpers, not position authorities.
- Every directly-emitted `@Foo.rec` carries a Lean-checked
  constructor-order assertion (`saw_ctor_order`).
- A source lint in the smoketest keeps the deleted heuristic families
  deleted (emitted-term shape inspection, transitional callee escape
  hatches, mode-guards) and caps the two documented emitted-TYPE
  self-mirrors at their current consumer counts.

Remaining rough edges, all documented and loud:

- Two emitted-TYPE self-mirrors survive with lint ceilings:
  `bindingShapeOfType` (binder-site classification of types the caller
  itself just emitted) and the `peelLeanPiTypes`/`isExceptStringType`
  result peel in `applyKnownFunctionWithShape` (the function-value
  family's result shape). Demoting the latter needs its own
  inert-oracle step; do not add consumers.
- `skipBinderWrap` and `inRecursorCaseBinder` survive as documented
  convention-scoped context flags.
- The gap/rejection families listed at the end of this note remain
  rejection boundaries (direct recursors for the six gated families,
  user datatypes, floats, etc.).

## Two Translations

The design separates raw type translation from runtime value representation.

`T(tau)` is the Lean type corresponding to the SAWCore type expression `tau`.
It is used for types, indices, propositions, proofs, motives, and raw Lean
support-library formals.

Examples:

```text
T(Bool)        = Bool
T(Nat)         = Nat
T(Vec n Bool)  = Vec n Bool
T(sort k)      = a Lean universe/sort
```

Equality propositions are not context-free under `T`. Their Lean carrier
depends on the declared equality subject representation; see "Raw Logical
Callees" below. This is deliberate. The same source type family `Eq a x y`
may express equality over raw values in proof/index positions or equality over
runtime computations in value-level propositions.

For a non-function value type, `V(tau)` is the Lean representation of a
SAWCore term when that term is a runtime value computation:

```text
V(tau) = Except String (T(tau))
```

Function representation is structural, not `Except String (T(a -> b))`.
A value-level function is not made raw by stripping `Except`; its argument and
result slots each have their own expected positions. A function convention
defines the representation:

```text
F((x : a)@rho_arg -> rho_result) =
  (x : R(rho_arg, a)) -> R(rho_result, b[x])
```

For a simple value-level function, this is morally:

```text
F((x : a)@RuntimeValue -> RuntimeValue) =
  V(a) -> V(b)
```

Dependent occurrences are only well formed when later types/motives can refer
to the representation actually bound in Lean. If a later raw type, index, or
motive needs the successful value inside `Except`, the backend must use an
explicit sequencing convention in a runtime result position or reject.

This is the central reason there is no general sound adapter:

```text
(A -> Except String B) -> (A -> B)
```

Such an adapter would have to erase errors.

## Positions

The representation of a term is determined by its expected position, not only
by its SAWCore type.

Use this small set of positions as the conceptual model:

```text
rho ::=
  RuntimeValue
  RawValue(raw reason)
  RawType
  RawIndex
  RawProposition(prop convention)
  RawProof
  RawMotive
  RawLeanFormal(raw reason)
  RawLogical
  FunctionConvention(...)
```

The representation function `R(rho, tau)` is:

```text
R(RuntimeValue, tau) = Except String (T(tau))

R(RawValue r, tau)   = T(tau)
R(RawType, tau)        = T(tau)
R(RawIndex, tau)       = T(tau)
R(RawProposition p, tau) = P(p, tau)
R(RawProof, tau)       = T(tau)
R(RawMotive, tau)      = T(tau)
R(RawLeanFormal r, tau)= T(tau)
R(RawLogical, tau)     = T(tau)
R(FunctionConvention c, Pi x:a. b) = F(c)
```

`P(p, tau)` is proposition translation under a proposition convention. For
non-equality propositions this is usually the raw proposition produced from
`T`. For equality propositions, `p` must include the explicit equality subject
representation; `Eq[rho_eq]` below is the only equality proposition
translation rule.

`FunctionConvention` recursively assigns positions to the function's binders
and result.

The translation judgment is only valid for well-formed position/type pairs:

```text
WFPos(rho, tau)
```

The important well-formedness rules are:

- proof, proposition, type, motive, and index terms may only appear in raw
  positions;
- `RuntimeValue` is for non-function value computations;
- raw successful values use `RawValue`; raw values are distinct from raw
  proofs, raw propositions, raw indices, and raw motives even though all have
  Lean representation `T(tau)`;
- function-typed terms use an explicit `FunctionConvention`;
- `RawLeanFormal` must state why the formal is raw: raw value, type, index,
  proposition, proof, motive, or structural field;
- dependent binder positions must be well scoped over the representation bound
  in Lean. If a later type/index/motive requires an `A`, a prior binder of type
  `Except String A` is not a valid dependency;
- if no rule establishes `WFPos(rho, tau)`, translation rejects.

`Nat` is therefore not special. It is raw in index/proof/logical positions and
wrapped in runtime-value positions. Any implementation rule that says "`Nat`
is always raw" or "`Nat` is always wrapped" is wrong.

### The domain map (canonical, 2026-07-17)

Every rule above that asks "is `tau` a value-domain type?" consults ONE
total classification, the domain map `D(tau)`, implemented as
`classifyDomain` (SAWCoreLean.Convention). No position rule may re-derive
the answer with its own head dispatch; a position rule may only PROJECT
`D(tau)` into its position vocabulary. (History: before 2026-07-17 the
implementation carried ~8 hand-copied cascades that disagreed on
variable-headed types — the Either@core/Stream@core over-rejections. The
coherence audit `2026-07-17_domain-map-coherence-audit.md` is the record.)

```text
D(sort k)            = RawTypeDomain
D(Num)               = RawTypeDomain    (recorded representation choice)
D(Nat)               = NatDomain        (position-projected: index vs
                                         computed value — see above)
D(Eq ...)            = RawPropDomain
D(Pi x:a. b)         = FunctionDomain
D(x args), x a variable:
    kind(x) = Pi ... -> sort k, k a Type sort  = ValueDomain
    kind(x) = Pi ... -> Prop                   = RawPropDomain
    kind(x) not sort-valued (term-level head)  = ValueDomain
    (bare x is the zero-argument case; bare-vs-applied is NOT a
     distinction the calculus recognizes)
D(anything else)     = ValueDomain
     (String, Integer, Rational, records/pairs, Stream, and every
      other constant-headed data type; isort/qsort FLAGS are
      advisory and strip to their TypeSort — no separate arm)
```

Only `Eq`-shaped propositions are domain-classified `RawPropDomain`. A
non-`Eq` constant-headed proposition falls to `ValueDomain` and rides
the Prop backstop below (loud at elaboration, never silent) — the WFPos
"propositions are raw" rule is enforced for them by Lean, not by `D`.

Three positional gates legitimately SHADOW the domain answer, and are
the only ones: (1) the dependency/index gate — a binder whose variable
feeds a later binder's type, a type, or an index position is raw
regardless of `D` (the WFPos dependency rule above: a later
`A`-dependency cannot be satisfied by an `Except String A` binder);
(2) the recursor elimination sort (below); (3) the quantifier-Pi
binder-discipline gate — a Pi whose BODY is a proposition (`Eq`-shaped
or `Prop`-sorted) binds its binders raw with value shadows, a
binder-discipline question `D` cannot express because the Pi itself is
`FunctionDomain` (2026-07-18 exception hunt, Finding 4). Everything
else may only project `D`.

One raw REASON is load-bearing: `adaptTo` admits `BindingFunction` at
`ExpectRaw RawMotivePosition` only (defensive; motives normally travel
at `ExpectFunctionPosition`). The `RawReason` label space is therefore
not fully inert — reasons must reflect logical roles (2026-07-18
exception hunt, Finding 5).

**Variable-headed types are KIND-DIRECTED.** The head variable's declared
kind is in Γ; its result sort decides the domain. No rule may classify a
variable-headed type by kind-blind syntactic head tests (the retired
`isVariableHead` recognizer); `isVariableHeadTypeFamily` survives only as
a kind-based sort-valued-head recognizer inside orthogonal
type-producing checks, never as a wrap authority.

**The Prop backstop (load-bearing).** SAWCore ADMITS `Prop <= sort 0`
cumulativity, so a Type-sort-kinded head CAN be instantiated at a
proposition. `ValueDomain` classification (wrapping as
`Except String (T(tau))`) remains sound because the emitted Lean is the
backstop: `Except String P` at `P : Prop` is ill-typed in Lean 4, so the
bad instantiation fails loudly at elaboration — never silently. Any
change to the wrapping carrier must re-establish a backstop with this
property, or `D` must grow an explicit exclusion.

Recursor motive results project `D` with one extra parameter, the
elimination sort: a `ValueDomain` or `NatDomain` motive body is a runtime
value only under non-`Prop` elimination (mirroring the Nat rule); `Prop`
elimination keeps the logical family raw.

## Translation Judgment

The core judgment is:

```text
Gamma |- e : tau ==>_rho L : R(rho, tau)
```

Read this as:

> Under binding environment `Gamma`, source term `e` of SAWCore type `tau`
> translates at expected position `rho` to Lean term `L` with representation
> `R(rho, tau)`.

`Gamma` records the representation of already translated variables. It must
record more than "is this variable wrapped?". For review purposes, each binding
should have:

```text
source type, Lean name, expected position, representation shape, exact Lean type
```

A raw proof variable, a raw index variable, and a raw value formal all have no
outer `Except`, but they are not interchangeable. Collapsing them into one
undifferentiated "raw" bucket is only safe as transitional plumbing, not as the
semantic model.

For binders:

```text
Gamma, x : (tau, rho, Lx : R(rho, tau))
```

Subsequent translated types, indices, and motives may refer to `Lx` only if
`Lx` has the raw representation they require. A runtime binder of type
`Except String A` is not available as an `A` in later raw positions. If a
dependent shape requires that successful value, the surrounding convention must
sequence the computation in a runtime result position or reject.

## Atomic Terms

The SAWCore term grammar has a small atomic surface in addition to application,
binders, and definitions. Each atomic form must still be translated at an
expected position.

- Variables are looked up in `Gamma`; the stored representation must match the
  requested position or adapt by the rules below.
- Constants are resolved through their def-site declaration and their use-site
  callee convention. A constant's raw definition status does not by itself
  authorize raw use.
- Sorts and sort flags live in raw type/universe positions. Sort flags are
  advisory metadata; the Lean backend may ignore a flag only when doing so does
  not change the Lean type/proposition being emitted.
- Recursor atoms are not ordinary functions. They use the recursor convention
  described below.
- String literals are ordinary values: raw in a declared raw-value position and
  lifted with `Pure.pure` in a runtime-value position.
- Array values are ordinary values only after an array realization policy
  exists. Until then, array literals and array primitives remain rejection or
  known-gap surfaces.

## Adaptation

Sometimes a natural translation has one representation and the surrounding
position expects another. The allowed adaptation relation is deliberately
small.

Allowed adaptations:

```text
raw value -> runtime value
  emit Pure.pure raw

runtime value -> runtime value
  identity

raw type/index/proof/proposition/motive -> same raw position
  identity

runtime value -> raw value for a raw result
  forbidden as a generic adaptation

raw function -> function convention
  eta-expand only when each argument/result slot is adapted by this same
  calculus

proof-carrying helper
  emit or consume the declared Lean proposition; the helper is trusted only if
  Lean checks the proposition path
```

Forbidden adaptations:

```text
runtime value -> raw value by defaulting
runtime function -> raw function
proof/type/proposition/motive -> Except
generated Lean AST inspection to decide that a wrapped term is "really pure"
Haskell-side semantic rewriting justified only by intuition
```

The important error-preservation rule is:

> Once a computation has type `Except String A`, Haskell may sequence it, pass
> its successful value to a continuation, and return a result that still
> exposes failure. Haskell may not silently choose an `A`.

The only generic runtime-to-raw sequencing rule is typed like this:

```text
e : Except String A
Gamma, x : A(raw value) |- k[x] : Except String B
--------------------------------------------------
Bind.bind e (fun x => k[x]) : Except String B
```

This rule is valid only when the final result position is `RuntimeValue` or a
function convention whose result remains runtime-valued. It is not valid in
raw type, proof, proposition, motive, or index positions.

Any apparent extraction rule with a raw final result must be a named checked
adapter, not a generic conversion. Such an adapter must expose a Lean-checked
fact tied to the exact computation, for example:

```text
e : Except String A
a : A
p : e = Except.ok a
```

or an equivalent theorem whose conclusion supplies the raw value. If no such
checked adapter exists, translation rejects.

## Callee Conventions

Application is where positions become concrete. A callee convention maps a
callee plus already known type information to argument positions and a result
position:

```text
ArgMode ::=
  TypeArg | IndexArg | RuntimeArg | RawValueArg | ProofArg
  | PropositionArg | MotiveArg | StructuralField
  | FunctionArg FunctionConvention

ResultMode ::=
  RuntimeResult | RawResult(raw reason) | FunctionResult FunctionConvention

ArityPolicy ::= Exact n | PartialAllowed residual convention | RejectPartial

CalleeConvention =
  { argument modes
  , result mode
  , allowed adaptations
  , strict sequencing order
  , arity policy
  , rejection cases
  }
```

The application rule is:

```text
Gamma |- f ==> callee convention K
K gives argument positions rho_i and result position rho_result
Gamma |- arg_i ==>_rho_i L_i
adapt each L_i only as K permits
emit declared Lean application
result has R(rho_result, result_type)
```

This is table-driven or data-driven. It is not inferred from the emitted Lean
syntax and it is not selected by fixture name.

Every use-site branch must have a convention. A generic fallback is allowed
only if it is itself a declared convention with explicit argument/result modes
and rejection cases. Def-site treatment such as "emit this declaration raw" is
not a use-site convention by itself.

For partial application, the convention must split into:

```text
supplied prefix modes
residual FunctionConvention
prefix adaptation policy
residual arity policy
```

Any `Bind.bind` introduced while adapting supplied prefix arguments must still
return a runtime-valued result whose error behavior remains observable. If a
wrapped prefix argument would have to be opened to build a raw residual
function, translation rejects unless a named checked adapter supplies the exact
residual function.

Sequencing order is part of the convention. When multiple runtime computations
are sequenced for one application, they must be bound in the source/application
order declared by the convention so first-error behavior is not changed
accidentally.

### Ordinary Phase-Beta Definitions

Definitions emitted by this backend in Phase-beta form use runtime-value
positions for ordinary value arguments and ordinary value results. They keep
errors explicit with `Except`.

They must not be called by first extracting all arguments to raw values.

### Raw Lean Targets

Some Lean support functions are raw Lean functions. Their formals use
`RawLeanFormal` positions.

If a raw formal expects a value and the actual is a runtime computation, the
application may be built under `Bind.bind` only when the whole surrounding
result remains error-preserving. The raw result may then be lifted with
`Pure.pure` if the outer expected position is `RuntimeValue`.

### Raw Logical Callees

Logical infrastructure lives in raw proof/type/proposition/motive positions.
This includes equality eliminators and proof combinators.

The convention is not "translate every argument raw". Equality may be about
runtime representations. The proposition is raw, but the terms being compared
are translated at an operand position supplied by the surrounding convention.
The source type alone does not decide this. For example, equality over a
runtime `Nat` computation compares the runtime representation, while equality
inside a raw Nat proof lemma compares raw Nat terms.

Every convention that emits or consumes an equality proposition must declare
the subject representation. This includes standalone proposition translation,
top-level obligation types, proof primitive contracts, `coerce`, `Refl`, and
`Eq.rec`. The translator must not infer the subject representation from type
names such as `Nat`.

Make the subject representation explicit:

```text
SubjectRep(a, rho_eq) = R(rho_eq, a)
```

For `rho_eq = RuntimeValue`, the Lean equality carrier is
`Except String (T(a))`. For raw positions, the carrier is `T(a)`. Equality over
runtime computations therefore intentionally compares the computations,
including their error behavior. If a proof should compare successful raw
values instead, its convention must use a raw subject and separately expose any
required no-error fact.

Minimum contracts:

```text
Eq[rho_eq] a x y
  a: raw type describing the compared SAWCore values
  x, y: SubjectRep(a, rho_eq)
  result: raw proposition Eq (SubjectRep(a, rho_eq)) x y

Refl[rho_eq] a x
  a: raw type describing the reflected SAWCore value
  x: SubjectRep(a, rho_eq)
  result: raw proof

Eq__rec / Eq.rec
  type, motive, equality proof, eliminator structure: raw logical
  equality operands: same operand-position convention as Eq
  branch and final result: position determined by the motive result
```

An `Eq.rec` convention must record at least:

```text
operand position rho_eq
carrier SubjectRep(a, rho_eq)
motive binder positions
motive result position
branch position
proof position
final result position
sort/universe class
```

These fields determine the Lean type of the equality proof, the motive, the
branch, and the result. `Gamma` must preserve that exact Lean proposition/proof
type for proof variables; "raw proof of source Eq" is not precise enough. If
the fields cannot be determined uniquely, the backend rejects instead of
guessing.

This explains the proof-transport failure class. If the motive result is a raw
proof-transported `Nat`, the branch `0` is raw `Nat`; wrapping it as
`Except String Nat` is a convention error. If a proposition compares runtime
computations, the compared terms may still be wrapped.

### Recursors

Recursors are another convention instance.

Raw target recursors consume raw structural scrutinees. If the source scrutinee
is a runtime computation and the recursor result is a runtime value, the
translator may bind the scrutinee and call the raw recursor in the continuation.

If the recursor result is raw proof/type/proposition/motive data, a wrapped
scrutinee cannot be extracted. The backend must reject or emit a checked
contract; it must not default the scrutinee.

### Records And Dictionaries

Records and dictionaries are ordinary values unless a convention says a
particular field is structural raw data.

The required rules are:

- constructor fields use the field positions declared by the datatype or
  helper convention;
- projections use the convention for the record representation they consume;
- dictionary records are not trusted proof evidence merely because they are
  dictionaries;
- record recursor motives and case-handler binders must distinguish structural
  raw fields from fields whose position comes from an actual datatype
  parameter;
- no record or dictionary value may be rawified by default to fit a Lean
  recursor or projection.

### Proof Obligations And Checked Helpers

Partial operations, proof primitives, `fix`, stream totality, bounds/index
facts, and similar surfaces follow the proof-carrying pattern:

1. emit the ordinary translated term or declared helper application;
2. expose the required Lean proposition as an obligation or checked helper
   precondition;
3. rely on Lean, not Haskell, to prove the proposition.

Haskell may recognize a source construct in order to emit the correct
contract. It may not treat the recognition as evidence that the contract is
true.

The broad pattern must be instantiated by a concrete contract schema:

- partial operation: consumed arguments, side-condition proposition, result
  position, zero/invalid-case behavior;
- checked application: helper name, raw/wrapped formal positions, checked
  precondition, result position;
- proof primitive: exact arity, source proof arguments, emitted proposition,
  rejection behavior for residual uses;
- raw `error`/`unsafeAssert`: stage, diagnostic or obligation, and result
  position;
- `fix`: emitted ordinary fix expression plus fixed-point existence/uniqueness
  contract;
- stream/productivity: emitted stream expression plus pointwise totality or
  productivity contract.

Under- or over-application is part of the schema. If the schema does not cover
the arity at hand, translation rejects.

`Prelude.error` follows the same representation discipline:

- runtime value result: emit an observable `Except.error`;
- raw type/index/proof/proposition/motive result: reject unless a named checked
  adapter exposes the required impossible/false precondition in Lean;
- function result: classify by the function convention, with errors remaining
  observable at the runtime-valued result slots.

## Definitions

Top-level declarations need a definition convention, not an after-the-fact
body repair.

```text
DefConvention ::=
  PhaseBetaDef FunctionConvention-or-position
  RawLogicalDef raw reason
  RawSupportDef declared Lean signature
  MacroDef declared expansion contract
  RejectDef diagnostic
```

The declaration type determines the expected position for the body together
with the def-site convention. The body is translated against that expected
position. A closed value may be lifted with `Pure.pure` only because the
definition convention says the definition denotes a runtime value computation.

Def-site treatment does not authorize use-site behavior. A declaration emitted
raw still needs an explicit callee convention when it is later applied.

Local shared `let`s use the same discipline. A let binding must choose an
expected position for its right-hand side, translate the right-hand side at
that position, and extend `Gamma` with the exact representation and Lean type
of the bound term before translating the body. A local let may not translate
the right-hand side in one shape and then repair the body with a later
raw/wrapped guess.

If one shared source right-hand side is demanded at multiple incompatible
positions, the backend may translate separate explicit bindings for those
positions or reject. It may share one Lean binding only when all uses agree on
the recorded representation and exact Lean type.

Use-site macros require their own callee convention:

```text
MacroConvention =
  { consumed arity
  , argument modes
  , result mode
  , residual policy
  , expansion contract
  , default-translation policy
  }
```

If a macro expands into a semantically different shape, that equivalence must
be checked in Lean or the macro must be rejected. Loaded primitives, loaded
axioms, and injected Lean code are not justified by this calculus merely
because they have Lean types. They require a declared support/realization
policy; until then they remain explicit known gaps or rejection boundaries.

## Gap And Rejection Families

This calculus should classify unsupported surfaces explicitly rather than
letting them fall through ordinary emission. Current families that may remain
known gaps or rejection boundaries include:

- unsupported direct recursors and user datatypes;
- list/function-sort encodings not yet represented in Lean;
- array literals, array primitives, floats, and other loaded primitive families
  without realization policy;
- loaded axioms and injected Lean code without provenance/realization policy;
- higher-order proof-carrying wrappers whose residual convention is not yet
  defined;
- stream-recursion/productivity and large crypto stress cases beyond the
  current proof-carrying contracts.

Each family can later move into the calculus by adding a concrete convention,
checked realization, or proof-obligation schema. Until then, rejection is the
sound behavior.

## What Soundness Means Here

This calculus does not prove that every Lean support definition matches
SAWCore semantics. That is a separate realization-theorem or conformance
surface.

It does protect the central backend invariant:

> Haskell emission never turns a failing runtime computation into a raw value,
> never turns proof/type/motive data into `Except`, and never relies on an
> unverified semantic equivalence to make a Lean term typecheck.

For a sound final backend, we still need:

- Lean support definitions whose semantics match SAWCore or have checked
  realization theorems;
- emitted obligations for partial/proof-carrying side conditions;
- a final replay path that requires Lean checking before SAW accepts a proof;
- conformance tests that compare SAW and Lean behavior for executable terms.

But these later surfaces should sit on top of this representation discipline,
not compensate for violations of it.

## Review Questions

When reviewing an implementation change, ask:

1. What expected position is this source subterm translated at?
2. Which callee convention selected that position?
3. If a representation changes, is the adapter one of the allowed adapters?
4. Can an `Except String A` become an `A` without an error-preserving bind or a
   checked precondition?
5. Are proofs, propositions, motives, types, or indices ever wrapped?
6. Is a semantic equivalence being proved by Haskell rather than emitted for
   Lean to check?
7. If the convention cannot classify the case, does the backend reject rather
   than guessing?
8. Does the use site have an explicit callee convention, or is it relying on a
   def-site raw/preserve flag?
9. For equality or proof transport, what is the explicit subject
   representation?
10. For a top-level declaration, what definition convention determined the
    body's expected position?

- For every type the rule classifies: which `Domain` does `D(tau)`
  assign, and does the rule PROJECT `classifyDomain` rather than
  re-derive the answer with its own head dispatch? If it shadows the
  domain answer, is it one of the two named positional gates?

If the answer to any of these questions is unclear, the implementation is not
yet reviewable enough for this semantic core.
