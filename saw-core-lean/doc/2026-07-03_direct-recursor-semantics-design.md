# Direct SAWCore Recursor Semantics Design

Date: 2026-07-03

This is a design note, not an execution goal. Its purpose is to settle the
semantic shape of direct SAWCore recursor support before implementation work
resumes.

## Problem

The Lean backend currently rejects several direct SAWCore recursors:

- `Bool#rec`
- `Nat#rec`
- `Pos#rec`
- `Z#rec`
- `AccessibleNat#rec`
- `AccessiblePos#rec`
- user-defined datatype recursors

The rejection is intentional. These recursors are not all Lean native recursors
with a different name. Some have different constructor order, different
constructor structure, or no current Lean representation at all. Emitting
`@D.rec` because the source contains `D#rec` is sound only when the target
datatype has the same constructors, the same constructor order, compatible
indices and parameters, and the same recursive-argument/IH convention.

The next fix must not be a local patch for one example. It needs to define the
general rule for when a SAWCore recursor can be emitted and what Lean-side
evidence justifies that emission.

## SAWCore Recursor Semantics

SAWCore recursors are represented by `CompiledRecursor` values. A compiled
recursor records:

- the datatype name,
- the elimination sort,
- the number of datatype parameters,
- the number of datatype indices,
- the constructor order from the SAWCore datatype declaration.

The SAWCore certified term machinery constructs the recursor type from the
datatype declaration. Its iota reduction is constructor-order driven:

```text
D#rec params motive case_1 ... case_k indices (Ctor_i params fields)
  --> case_i fields recursive_calls
```

Recursive calls are supplied only for constructor fields marked as recursive in
the datatype's `CtorArgStruct`. Non-recursive constructor fields receive no IH.
This matters for `Nat`: SAWCore's Prelude `Nat` is not Peano `Nat`.

```sawcore
data Nat : sort 0 where {
  Zero : Nat;
  NatPos : Pos -> Nat;
}
```

So source `Nat#rec` is a two-way split over `Zero` vs. `NatPos p`. Its
`NatPos` branch receives a positive-number payload and no recursive
hypothesis. It is not the same eliminator as Lean's Peano `Nat.rec`.

The Prelude separately defines `Nat__rec`, using `AccessibleNat`, to provide
Peano-style induction:

```sawcore
Nat__rec :
  (p : Nat -> sort 1) ->
  p Zero ->
  ((n : Nat) -> p n -> p (Succ n)) ->
  (n : Nat) -> p n
```

`Nat__rec` is morally Lean `Nat.rec` after the backend commits to representing
SAW `Nat` as Lean `Nat`. Raw `Nat#rec` is not.

## Rocq Backend Lesson

The Rocq backend has two relevant mechanisms.

First, generic datatype recursors are emitted by translating the datatype name
and appending Rocq's recursor suffix. For datatypes whose translated Rocq
inductive matches the SAWCore datatype, this is fine.

This generic path is not a sound precedent for the SAW Prelude datatypes whose
target representation differs. A leaked raw `Nat#rec` in Rocq would be routed
through `nat_rect`, but SAW's raw `Nat#rec` is not Peano induction. A leaked raw
`Pos#rec` is also not automatically safe, because Rocq's `positive_rect` has a
different constructor order than SAW's `Pos` declaration.

The useful Rocq lesson is the second mechanism: many Prelude surfaces are
routed through handwritten realizations in `SAWCoreScaffolding.v` rather than
trusted as raw recursor translations:

- `Bool`, `True`, and `False` map to Rocq `bool`, `true`, and `false`, but
  `iteDep` is implemented as a wrapper that preserves SAW's True-first
  argument order.
- `Nat` maps to Rocq `nat`, but `Nat__rec` maps to `nat_rect`.
- `if0Nat`, `Pos_cases`, `IsLeNat__rec`, and arithmetic operations map to
  named Rocq definitions with the intended source behavior.
- `Pos_cases` explicitly adapts Rocq's positive-recursion order to SAW's
  source order.
- `AccessibleNat`, `AccessiblePos`, and related proof witnesses are skipped
  or kept internal rather than exposed as arbitrary trusted translations.

The important lesson is not that Lean should copy every Rocq name. The lesson
is that public Prelude eliminators are realized by named target-side
definitions whose behavior is checked in the target proof assistant. Rocq is
also incomplete here as a model for raw Prelude recursors: its safety relies on
opacity, wrappers, and skipped internal surfaces. Lean needs an explicit
representation contract rather than a generic "append `.rec`" rule.

## Lean-Specific Constraints

Lean is not just a syntax target for Rocq's strategy.

1. **Constructor order can differ.**
   SAW `Bool` is declared `True; False`. Lean `Bool.rec` is False-first.
   Directly emitting `@Bool.rec` with SAW arguments silently swaps branches.

2. **Constructor structure can differ.**
   SAW `Nat` is `Zero | NatPos Pos`. Lean `Nat` is `zero | succ Nat`.
   Directly emitting `@Nat.rec` for raw `Nat#rec` is the wrong eliminator.

3. **Representation can be non-identical.**
   The current Lean backend maps SAW `Nat` to Lean `Nat` and maps the SAW
   constructors through helpers:

   - `Zero` -> `0`
   - `Succ` -> `Nat.succ`
   - `One` -> `1`
   - `Bit0 n` -> `2 * n`
   - `Bit1 n` -> `2 * n + 1`
   - `NatPos p` -> `p`

   This is fine for value-level arithmetic if the source `Pos` invariant is
   respected, but it is not by itself a proof that every source recursor maps
   to a native Lean recursor.

4. **Value-domain effects are explicit.**
   In Phase beta, value-domain SAWCore terms translate to
   `Except String alpha`. A recursor whose scrutinee or branches are
   value-domain computations must preserve error propagation. It cannot extract
   a raw scrutinee from `Except` unless the final target type also preserves the
   error.

5. **Universe levels are explicit.**
   Recursor wrappers must be universe-polymorphic over `Sort u`, not specialized
   to `Type`, unless the source recursor is genuinely restricted to value
   types. This is especially important for motives returning propositions or
   types.

## Design Rule

Every emitted SAWCore recursor must be justified by one of these cases.

### Case A: Structural Match

The target Lean inductive has the same semantic constructors as the source
datatype, in the same order, with compatible parameters, indices, recursive
arguments, and elimination universe.

Then the backend may emit the Lean auto-recursive eliminator, but only through
the existing position/callee convention:

- case-handler structural fields are raw,
- case-handler bodies use the ordinary expected-position rules,
- wrapped scrutinees are sequenced only when the result preserves errors,
- raw/type/proof results never extract from `Except`.

This is the right path for generated user datatypes only after the Lean backend
actually emits a matching Lean inductive for the source datatype. It is also
the current path for supported hand-modeled datatypes whose Lean definitions
match SAWCore closely enough, such as `UnitType`, `PairType`, `RecordType`,
`Either`, and current dictionary/record recursor rows.

### Case B: Source-Shaped Checked Realization

The target Lean carrier differs from the source datatype, but the support
library defines a source-shaped recursor whose type follows the SAWCore
recursor signature and whose body/proofs establish the source iota equations.

Then the backend may map the source recursor to that Lean definition. Haskell
does not inspect the motive, prove equations, permute branches ad hoc, or
recognize examples. It only selects the declared realization for the source
recursor name.

This is the right path for `Bool#rec`, raw `Nat#rec`, `Nat__rec`, `natCase`,
`if0Nat`, and `Pos_cases`.

### Case C: Proof-Carrying Obligation

If the backend cannot provide a checked realization, it may emit an explicit
Lean obligation that states the required recursor behavior or realization
contract. The emitted result may use a helper only if the helper consumes that
checked evidence.

This is appropriate when the representation is known but proving all equations
is deferred.

### Case D: Explicit Rejection

If neither a structural match, checked realization, nor proof-carrying
obligation is available, the backend must reject at SAW translation with a
specific diagnostic. Lean elaboration failure is not the desired interface.

## Proposed Lean Representation Strategy

### Bool

Keep SAW `Bool` represented by Lean `Bool`.

Add or expose a source-shaped direct recursor:

```lean
def sawBoolRec.{u}
    (motive : Bool -> Sort u)
    (trueCase : motive true)
    (falseCase : motive false)
    (b : Bool) : motive b :=
  Bool.rec falseCase trueCase b
```

Required equations:

```lean
sawBoolRec motive trueCase falseCase true  = trueCase
sawBoolRec motive trueCase falseCase false = falseCase
```

This is the direct-recursive analogue of the existing `iteDep` wrapper. It is
not automation; it is the source recursor with SAW constructor order.

### Nat Public Induction

Keep SAW `Nat` represented by Lean `Nat`.

`Nat__rec` is Peano induction, not raw binary-Nat elimination. It should map to
a support definition equivalent to Lean `Nat.rec`:

```lean
def sawNatInd.{u}
    (p : Nat -> Sort u)
    (z : p 0)
    (s : (n : Nat) -> p n -> p (n + 1))
    : (n : Nat) -> p n
```

This covers the user-facing `Nat__rec` surface and constants built from it,
including `natCase` where the motive is raw. Value-domain `natCase` still needs
the Phase beta error-propagation convention described below.

Required equations:

```lean
sawNatInd p z s 0       = z
sawNatInd p z s (n + 1) = s n (sawNatInd p z s n)
```

This is the Rocq `Nat__rec := nat_rect` idea translated to Lean, with explicit
universe handling.

### Raw Nat#rec

Raw `Nat#rec` is source binary-Nat case analysis:

```sawcore
Nat#rec motive zeroCase natPosCase n
```

It is faithful to map it to a Lean wrapper only if the wrapper follows the
source shape, not Lean Peano recursion:

```lean
def sawNatViewRec.{u}
    (motive : Nat -> Sort u)
    (zeroCase : motive 0)
    (natPosCase : (p : PosRep) -> motive (posToNat p))
    (n : Nat) : motive n
```

There are two possible `PosRep` choices:

1. **Preferred final design: define SAW `Pos` as a Lean inductive.**

   ```lean
   inductive PosRep : Type
     | One : PosRep
     | Bit0 : PosRep -> PosRep
     | Bit1 : PosRep -> PosRep
   ```

   Then define and prove:

   ```lean
   posToNat : PosRep -> Nat
   natSuccToPos : (n : Nat) -> PosRep
   posToNat (natSuccToPos n) = n + 1
   ```

   `sawNatViewRec` matches on Lean `n`. In the successor branch it calls
   `natPosCase (natSuccToPos k)` and transports across the checked theorem
   `posToNat (natSuccToPos k) = k + 1`.

   This is the cleanest soundness story: source `Pos` remains a real datatype,
   the impossible zero-positive case is unrepresentable, and raw `Pos#rec` can
   use the auto-generated Lean recursor because constructor order is under our
   control.

2. **Rejected transitional design: keep `Pos` as encoded `Nat`.**

   `PosRep = Nat`, `posToNat = id`, and `sawNatViewRec` calls the `NatPos`
   branch only with successor values.

   This is easier to retrofit but should not be used as a goal-doc plan. A Lean
   binder translated from source `Pos` would range over all `Nat`, including
   `0`. That can become unsound once `Pos` appears in negative positions,
   existentials, higher-order arguments, or user-visible propositions: Lean
   could produce or consume a `0 : Nat` witness for a source type whose values
   are strictly positive.

   This encoding is locally tolerable only in the current narrow constructor
   macro style, where free `Pos` values and raw `Pos#rec` remain rejected and
   the backend never exposes translated `Pos` binders as ordinary `Nat`
   binders. It is not a principled recursor support strategy.

Recommendation: do not implement raw `Nat#rec` until the `PosRep` decision is
made. If the project wants a final design rather than another migration later,
choose the inductive `PosRep` representation and adapt the constructor mappings
around it.

The required Lean-side facts for raw `Nat#rec` are stronger than merely proving
that every successor Nat has some positive representation. We need a
canonicality/inverse story sufficient to prove the source iota equation for the
actual `NatPos` payload:

```lean
posToNat (natSuccToPos n) = n + 1
natSuccToPos (posToNat p - 1) = p
-- or an equivalent canonicality/injectivity theorem

sawNatViewRec motive z c (posToNat p) = c p
```

Without the inverse/iota theorem, a Lean wrapper that pattern matches on native
`Nat` can reconstruct some positive representation for the successor branch,
but not necessarily the same payload the source `NatPos p` branch received.
That would not justify raw `Nat#rec`.

### Pos#rec and Pos_cases

With inductive `PosRep`, `Pos#rec` can be a structural match if the Lean
constructors are declared in SAW order:

```lean
inductive PosRep : Type
  | One
  | Bit0 : PosRep -> PosRep
  | Bit1 : PosRep -> PosRep
```

The generated `PosRep.rec` then has the source constructor order and supplies
recursive hypotheses for `Bit0` and `Bit1`, matching SAWCore's `RecursiveArg`
structure.

`Pos_cases` should remain a public support definition over this representation,
not a Haskell rewrite. Its equations should be checked in Lean.

### Z

There are two sane choices:

1. Represent source `Z` as its own Lean inductive:

   ```lean
   inductive ZRep : Type
     | ZZero
     | ZPos : PosRep -> ZRep
     | ZNeg : PosRep -> ZRep
   ```

   This gives direct `Z#rec` by structural match and makes the source
   constructor invariants explicit.

2. Represent public integer operations by Lean `Int`, while keeping source `Z`
   internal and rejected.

The first choice is better for complete SAWCore coverage. The second is a valid
near-term boundary if no current target examples need direct `Z` values. It
must remain an explicit known gap, not a Lean elaboration failure.

### AccessibleNat and AccessiblePos

`AccessibleNat` and `AccessiblePos` are internal proof/witness datatypes used
to implement induction in the SAW Prelude. They are not the right first public
surface.

For `Nat__rec`, prefer proving a Lean support definition with the Peano
equations rather than exposing `AccessibleNat` to Haskell emission. If direct
`Accessible*#rec` is later required for full SAWCore coverage, model the
families as Lean inductive families over the chosen `Nat`/`PosRep`
representation and prove the corresponding `Accessible*_all` constructors.

Until then, direct `Accessible*` recursors should stay pinned known gaps with
clear diagnostics.

### User Datatypes

For user-defined SAWCore datatypes, the final design should use Case A:
auto-emit a matching Lean inductive and use its Lean recursor only when the
constructor order, parameters, indices, and recursive fields are structurally
the same as SAWCore's `DataType`.

This should not be mixed with Prelude replacement work. Prelude datatypes such
as `Nat`, `Bool`, and `Z` are special because we intentionally map them to
Lean-native or support-library representations. User datatypes should be
literal unless and until a declared replacement is introduced.

## Haskell Emitter Shape

The Haskell side should grow a small declarative table for recursor
realizations. The table must classify the full source recursor shape, not just
the datatype name. A `CompiledRecursor` includes the datatype, elimination sort,
parameter count, index count, and constructor order; those are part of the
semantic contract. Different elimination sorts or indexed-family shapes are
not interchangeable.

```text
data RecursorRealization
  = StructuralLeanRecursor
  | SourceShapedSupportRecursor Lean.Ident
  | RecursorKnownGap Text
```

The table is not a proof engine. It only answers:

- which Lean callee realizes this source recursor,
- whether the existing recursor position convention may be used,
- whether unsupported shapes should reject.

The existing `RecursorConvention` and position/callee machinery remain the
right mechanism for raw vs. wrapped arguments and results. The new table should
replace hard-coded "these recursors are unsound" branches with positive,
documented realization choices where we have Lean support definitions.

The backend must not:

- map raw `Nat#rec` to Lean `Nat.rec`,
- map raw `Bool#rec` to Lean `Bool.rec`,
- infer safety from datatype name alone when the elimination sort, indices, or
  constructor order do not match the declared realization,
- inspect the motive to decide that a particular example is safe,
- synthesize branch permutations in Haskell,
- use source proof terms as trusted evidence,
- add Lean axioms for recursor equations that should be definitions or theorems.

The proof-carrying-obligation case must also be concrete: the emitted
obligation should state an exact realization theorem or exact iota equation for
the recursor surface being used. It must not be a vague "trust this recursor"
escape hatch.

## Soundness Argument

The soundness obligation for a source-shaped recursor realization is local and
auditable:

For every source constructor `Ctor_i`, the Lean support recursor must satisfy
the corresponding source iota equation under the chosen representation:

```text
realize(D#rec) motive cases (realize(Ctor_i fields))
  = realize(case_i fields recursive_calls)
```

For structural matches, this follows from Lean's generated recursor, provided
the Lean inductive is definitionally the same source datatype.

For source-shaped support recursors, this must be proved by Lean definitions or
Lean theorems. Haskell is trusted only to route `D#rec` to the named checked
realization, not to justify the equations.

For wrapped value-domain recursors, the additional soundness condition is error
preservation:

- if the scrutinee is `Except.error`, the emitted result must preserve that
  error whenever the result is value-domain;
- if the result is raw/type/proof, the backend must not extract a raw value from
  an effectful scrutinee;
- branch computations must remain in the translated result shape and must not
  be evaluated by Haskell.

This is exactly the "Haskell stays dumb" discipline: Haskell emits the source
recursor contract and Lean checks the representation equations.

## Testing Implications

The conformance suite should distinguish these surfaces.

1. Positive source-shaped realization tests:
   - `Bool#rec true/false` checks branch order.
   - `Nat__rec` checks Peano zero/succ equations.
   - raw `Nat#rec` checks `Zero` vs. `NatPos` behavior if and only if the
     `PosRep` representation is implemented.
   - `Pos#rec` checks `One`, `Bit0`, and `Bit1` equations once `PosRep` exists.

2. Boundary or known-gap tests:
   - `AccessibleNat#rec` and `AccessiblePos#rec` stay known gaps until their
     Lean inductive families exist.
   - `Z#rec` stays a known gap unless `ZRep` is introduced.
   - user datatype recursors stay known gaps until the backend emits matching
     Lean inductives.

3. Differential tests:
   - closed small terms should compare SAW evaluation with Lean evaluation;
   - proof-carrying or currently noncomputable cases may instead inspect the
     emitted obligation shape, but must remain visibly distinct from executable
     conformance.

4. Anti-regression checks:
   - emitted Lean for direct `Bool#rec` must not contain raw `@Bool.rec` with
     SAW argument order;
   - emitted Lean for raw `Nat#rec` must not contain raw `@Nat.rec`;
   - no direct recursor promotion may add `sorry`, `axiom`, or Haskell
     arithmetic/classifier logic.

5. Coverage for omitted hard cases:
   - indexed families such as `AccessibleNat : Nat -> sort 0` and
     `IsLeNat n : Nat -> Prop`;
   - recursive constructor arguments, including higher-order recursive
     arguments that require eta-expanded IHs;
   - elimination into `Prop`, `Type`, and higher `Sort u`;
   - value-domain recursors whose scrutinee or branches are
     `Except String`-wrapped;
   - user datatype auto-emission, which is not available merely because the
     generic recursor code exists.

## Recommended Path

The next design step is not to implement every recursor. It is to settle the
Nat/Pos representation decision, because that determines whether raw `Nat#rec`
can be implemented once or will require a second migration later.

Recommended final direction:

1. Start with the safe named-wrapper slice: `Bool#rec`, `Nat__rec`, raw
   `if0Nat`, and raw/type/proof `natCase`. These can be source-shaped support
   definitions over the current Lean `Bool`/`Nat` representation and do not
   require raw `Nat#rec`.
2. Introduce a Lean `PosRep` matching SAW `Pos`, with `posToNat`,
   `natSuccToPos`, inverse/canonicality facts, and checked constructor/iota
   equations.
3. Keep public SAW `Nat` represented by Lean `Nat`, but define source-shaped
   support recursors:
   - `sawNatInd` for `Nat__rec`;
   - `sawNatViewRec` for raw `Nat#rec`.
4. Add a declarative recursor-realization table in Haskell that routes only
   exact checked recursor shapes to those checked support recursors.
5. Add raw `Nat#rec` and `Pos#rec` only after the `PosRep` representation and
   iota proofs exist.
6. Keep `Z`, `AccessibleNat`, `AccessiblePos`, and user datatype recursors as
   known gaps until their representation story is equally explicit.

This converges toward complete Rocq parity without copying Rocq's accidental
fit to Coq/Rocq native datatypes. It also preserves the project rule that all
semantic reasoning lives in Lean: the Haskell backend chooses a declared
recursor realization, and Lean definitions/theorems justify that realization.
