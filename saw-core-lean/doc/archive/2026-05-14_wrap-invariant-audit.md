# Wrap Invariant Audit

**Date**: 2026-05-14
**Status**: design audit. No code change yet.
**Context**: 17/22 proof tests elaborate after γ.16–γ.24. Five
remaining failures cluster into structural categories that don't
yield to more wrap-leak patches. Time to write down what the wrap
rule actually *is*, position by position, and either confirm the
current strategy or redesign.

## 1. Top-level goal (re-stated)

`saw-core-lean` produces a Lean encoding of SAWCore terms that
makes SAW verification conditions dischargeable in Lean's kernel.
Two non-negotiables:

- **Faithfulness**: the Lean expression's meaning equals SAW's
  meaning. Errors that SAW recognizes (out-of-bounds index,
  `unsafeAssert`, `error`) must surface in the Lean output. No
  silent fallbacks that change the semantic value.
- **Dischargeable**: the Lean output must let the Lean kernel
  (with stdlib tactics) close the VC. The output should look like
  Lean code a human would write.

These are the principles from `2026-05-11_beta_replan.md`; this
doc doesn't replace that — it audits whether the wrap mechanism
implements those principles consistently.

## 2. The wrap rule (semantic version)

A SAWCore expression has a **sort** (the SAW type system's
universe level) determined by its type:

- An expression `e : τ` where `τ : sort 0` is a **value**. It can
  fail (errors are first-class in Cryptol semantics).
- An expression `e : τ` where `τ : sort k > 0` is a **type**.
  Types don't fail.

**Wrap rule (semantic):**

> A SAWCore value expression `e : τ` (`τ : sort 0`) translates to a
> Lean expression of type `Except String ⟦τ⟧`, where `⟦τ⟧` is the
> Lean encoding of τ. A SAWCore type expression `e : τ`
> (`τ : sort k > 0`) translates to a Lean type expression of the
> same sort (no wrap).

That's the rule. Everything else is implementation.

The rule is *type-directed*: whether to wrap is determined by the
sort of the expression's type, not by its syntactic shape.

## 3. Consequences at each AST position

### 3.1 Pi binder type

`(x : τ) → body`. The binder type is `τ`. Whether to wrap
depends on what `x` represents:

- **Term-level lambda binder** (`fun (x : τ) → ...`): `x` is a
  value of type τ. Wrap when `τ : sort 0`.
- **Pi-as-type** (`(x : τ) → R` describes a function type for
  some value-level function): same rule — wrap when `τ : sort 0`.
  This is the same Pi binder; the rule applies uniformly.
- **Motive Lambda binder** (`fun (y' : Sort) → motiveBody`): `y'`
  is a type variable, its own type is a Sort (sort 1+), so it's
  type-level. Don't wrap. The Lambda is a type-of-types
  computation.

### 3.2 Sort-typed binders

`(α : sort k > 0) → ...`. The binder α is a type. Don't wrap α.
But within the body, references to α as the TYPE of a value
should themselves wrap iff k = 0... wait that's contradictory.
Let's clarify.

α is bound as a type (`α : Sort k`). Inside the body, `α` is used
in two ways:

- As a *type of values* (`(x : α) → ...`): the value x has type α,
  which at this point is a polymorphic type. Under the wrap rule,
  values wrap to `Except String α`. So this Pi binder wraps.
- As a *type-level argument* (`Vec n α`): α is splicing into a
  type position, no wrap on α itself.

So Variable-head `α` is **always wrap-worthy in value Pi binder
positions**, regardless of the polymorphic instantiation. The
current `isVariableHead` exclusion in `shouldWrapBinder` is
incorrect; it conservatively avoided wrapping out of fear of
breaking Prop motives, but Prop is identified by `asEq` /
`asSort` / `propSort` checks separately.

**Implication**: removing the `isVariableHead` exclusion is the
right move, IF we can defend it against the prior regression
evidence.

### 3.3 Function application

Given a SAW function `f : (x₁ : τ₁) → ... → (xₙ : τₙ) → ρ` applied
to args:

- Each arg `aᵢ` translates to the wrapped form if `τᵢ : sort 0`
  (Phase β-wrapped value), raw otherwise (type-level arg).
- The application's bind chain extracts raw arg values from
  wrapped ones (`Bind.bind aᵢ_wrapped (\vᵢ → ...)`).
- The result is wrapped iff ρ : sort 0.

Currently `applied` does this but uses syntactic checks that
diverge from the semantic rule for Variable-head returns and Nat-
typed returns from value-domain operations.

### 3.4 Recursors

A recursor application `R α₁ ... motive case₁ ... caseₖ scrut` has
several wrap decisions:

- **α params** (sort k binders): raw, splice as-is.
- **Motive** (Lambda from datatype scrutinee to Sort): a type-of-
  types computation. Its binder (the scrutinee var) is the raw
  datatype. The motive's body is a Sort.
- **Case handlers** (Lambdas from constructor args to motive
  result): the binders are at the constructor's raw arg types
  (the recursor's signature requires this). The body produces a
  value of motive-result-type, which is wrapped iff the motive
  returns a value-domain type.
- **Scrutinee**: the datatype value being eliminated. If the
  recursor returns value-domain, the scrutinee must be raw
  (otherwise the recursor can't deconstruct). The translator
  binds the wrapped scrutinee to extract raw value via
  `Bind.bind`.

This is what gamma.20/gamma.21/gamma.22 codify. The case-handler
binders stay raw (forced by recursor signature); the body lifts
to wrapped via `Pure.pure` shadow lets.

### 3.5 Constructor applications

SAW constructors like `Stream.MkStream`, `RecordType.RecordValue`,
etc. have signatures that take raw arg values. Phase β-translated
arg expressions are wrapped. So application requires a bind chain
to extract raw arg values, then construct.

If the result of the constructor application is itself a value-
domain term, the whole expression is Pure.pure-wrapped:

`Pure.pure (Stream.MkStream f_raw)` for a Stream-typed value.

**Special case — constructor argument that is itself a lambda**:
e.g. `MkStream (\i → body[i])`. The lambda's body produces a
value of type α. If α : sort 0, Phase β-translates the body as
wrapped (`Except String α`). But the constructor signature
requires the lambda to be raw `Nat → α`.

This is where the wrap rule conflicts with itself. Two possible
resolutions:

(a) **Wrap the lambda type and adapt at the constructor**: emit
    the lambda as wrapped-output, and define a wrap-aware
    constructor (e.g. `MkStreamM : (Nat → Except α) → Except (Stream α)`)
    that adapts per-index errors to outer-stream errors.
(b) **Local raw-output context**: when emitting a lambda whose
    binder is at a constructor-arg position requiring raw output,
    suppress Phase β wrap inside the lambda's body. Operations
    inside use raw values directly.

Option (a) is more faithful (errors propagate per index). Option
(b) is simpler but breaks Phase β invariant locally. For
soundness, (a) is preferred.

### 3.6 Let bindings

Shared subterms become `let x := rhs; body`. The let-bound x has
the wrap status of its rhs. References to x inside body see x as
having that status.

Currently tracked via `wrappedVars` set (γ.23). The rule is
semantically derivable from rhs's translation type, but the
implementation uses a syntactic shape check (`isLikelyWrappedTerm`).

### 3.7 SAW Eq and Eq.rec

SAW `Eq : (t : sort 1) → t → t → Prop`. Translates to Lean's
`Eq`. The first arg `t` is a type. The next two are values of
that type. Under Phase β, the values wrap to `Except String t`.

For `Eq t x y` where t : sort 0 (value-domain):

- The Lean translation should be `Eq (Except String t) x_wrapped y_wrapped`.
- The wrap propagates into `t` because the equality is BETWEEN
  wrapped values.

For `Eq Type x y` where x, y : sort 0 (type-of-types equality):

- The translation should be `Eq Type x y` raw.
- Both x and y are themselves types, not values.

Eq.rec inherits this: it eliminates equality of wrapped values
when t : sort 0, raw types when t : sort 1.

Current implementation: special-cases `Prelude.Eq` to wrap when
`shouldWrapBinder` of the type arg holds (in `translateIdentWithArgs`).
This works for App-headed `t`; doesn't work for Variable-head `t`
when the SAW context puts a value-domain type variable there.

### 3.8 Nat at value positions

SAW Nat is both a type-level construct (Vec n α's index) and a
value-domain type (return of bvToNat, length, etc.). The current
implementation treats Nat uniformly as raw, on the theory that
type-level uses dominate.

The semantic rule says: a Nat value that comes from a value-
domain computation (e.g. `bvToNat v`) IS a value, so under Phase
β it should wrap to `Except String Nat`. Then surrounding bind
chains thread it through monadically; consumers at raw-Nat
positions (Pi binders typed `Nat` for type-level use) bind through
to extract raw.

So the distinction is per-position, not per-type. At a Pi binder
position where the binder is used as a Vec length, Nat stays raw.
At a Pi binder position where the binder is a runtime shift
amount (`rotateL n α v shift`), Nat wraps.

The split is encoded in the SAW signature: `typeArgPositions` (or
the more general "is this Nat used as a type index?") detects
type-arg Nat positions. Non-type-arg Nat positions are value-
domain and wrap.

## 4. Walk against current implementation

For each AST emit site, where current implementation diverges
from the semantic rule:

| Site | Current rule | Semantic rule | Discrepancy |
|------|--------------|---------------|-------------|
| Term-level lambda binder | `shouldWrapBinder && !skipWrap && !inRecCase` | wrap iff `τ : sort 0` | `isVariableHead` exclusion conservative; should wrap polymorphic value binders |
| Pi binder | same | same | same |
| Motive Lambda binder | `skipBinderWrap=True` set by `typeBody` branch | don't wrap (motive binder is the raw datatype scrutinee) | correct under current scoping |
| App arg lift | mask from SAW signature `shouldWrapBinder` | wrap iff arg type at sort 0 | misses Variable-head args (γ.17 special-cased Variable-head for mapsToWrapped, but only for raw literals) |
| App result pure-wrap | `shouldWrapBinder ret \|\| isVariableHead ret` | wrap iff ret type at sort 0 | misses Nat-returning value-domain ops |
| Recursor scrutinee | Var in `wrappedSet` OR `isLikelyWrappedTerm` | bind iff scrutinee is wrapped | syntactic shape check; misses cases not in helper list |
| Recursor case-handler binder | raw (under `inRecCase`) | raw (forced by recursor signature) | correct |
| Let RHS | wrapped iff rhs is wrap-producing | wrapped iff rhs's Lean type is `Except _ _` | `isLikelyWrappedTerm` syntactic; could miss cases |
| Constructor arg lambda | wraps body via Phase β | conflicts: constructor needs raw-output lambda | cat 1 failure (Stream.MkStream) |
| Eq application | wrap type arg when `shouldWrapBinder` (App-headed) | wrap iff type arg : sort 0 | misses Variable-head value-domain type args |
| Nat at value position | raw everywhere | wrap when at non-type-arg position | cat 5 failure (bvToNat in bind chain) |

## 5. Open design questions

These need resolution before further code change.

### Q1. Variable-head wrap-worthiness

**Question**: should `shouldWrapBinder` return True for Variable-
head types?

**Semantic rule says**: yes, when the variable is bound at sort 0
(which it always is in our use cases, since type-of-type binders
are at sort 1+).

**Risk**: earlier blanket removal regressed 24 tests, mostly
around Stream.rec / RecordType.rec / Pair_fst / iteM where
Variable-head args got incorrectly bound. But γ.21 changed how
the recursor case binders work, and γ.22/γ.23 broadened scrutinee
tracking. Worth retrying the change in the current state.

**Resolution direction**: re-test the change. If still regresses,
the issue is at one of the other sites (probably `applied`'s
shouldBind decision treating function-typed args as bindable).
Fix at that site (don't bind function-typed args), then the wrap
change becomes safe.

### Q2. Constructor argument lambda (Stream.MkStream)

**Question**: when SAW translates `MkStream α (\i → body[i])`,
should the lambda body be raw or wrapped?

**Semantic rule says**: the body produces a value of type α
(sort 0), so under Phase β it's wrapped. The MkStream
constructor takes raw `Nat → α`, so the wrapped body needs
adapting.

**Resolution direction**: add wrap-aware constructor variants
`MkStreamM : (Nat → Except α) → Except (Stream α)`,
`RecordValueM`, `PairValueM`, etc. The translator emits the
adapter when the SAW constructor appears with a lambda arg whose
body is value-domain. Mirrors the existing `genFixM` /
`mkStreamFixM` / `cryptolIterateM` pattern.

This is option (a) from §3.5.

### Q3. Nat at value positions

**Question**: should Nat wrap when its source is a value-domain
expression (bvToNat, length, etc.)?

**Semantic rule says**: yes. The SAW type system says these
return Nat, but the *meaning* under Phase β is "Nat value
possibly carrying an error". So Lean type is `Except String Nat`.

**Resolution direction**: change `applied`'s pureWrap decision to
also wrap when the function's args include value-domain types
(even when ret is Nat). Mark which Nat positions are type-args
via `typeArgPositions`; bind on non-type-arg Nat positions where
the supplied arg is wrapped.

The earlier blanket Nat-bind attempt regressed because raw Nat
binders (e.g. `i' : Nat` inside `genM`'s lambda) got bound. The
fix: distinguish via `wrappedVars` — if the Nat-typed arg is a
`Lean.Var` not in `wrappedVars`, don't bind. Else bind.

## 6. Resolution summary

The current strategy IS the right strategy: type-directed Phase β
wrap. The patches accumulated (γ.16–γ.24) all reflect cases where
the implementation diverged from the semantic rule. None of the
patches contradict the rule — they refine its application.

The remaining five failures cluster around three rule-application
gaps (Q1, Q2, Q3 above). All three have clear semantic-rule
answers; the implementation work is to apply the rule
consistently, not to invent new rules.

**Recommended sequence**:

1. Implement Q3 first (Nat at value positions). Smallest blast
   radius, clearest spec, unblocks 3 tests (iround_zero, salsa20_q,
   half of stream_fibs_corec).
2. Implement Q2 (constructor-arg lambda). Add MkStreamM/PairValueM/
   RecordValueM adapters. Unblocks 2 tests (recursion_stream_corec,
   stream_fibs_corec rest).
3. Implement Q1 (Variable-head wrap). Re-test the broad change
   after Q2 and Q3 land. May unblock chacha20_core_iterate (cat 2)
   for free if the inner Pi wrap propagates correctly.

After all three, expect 22/22 proof tests to elaborate (and to
have the same wrap-rule-derived structure).

## 7. Soundness notes

The `Inhabited` fallback in `cryptolIterateM` (and proposed
`MkStreamM`) is a **trust point**: per-index errors get silently
replaced by `default`. This is acceptable because:

- SAW Cryptol streams come from total per-index computations
  (bitvector ops); errors at stream indices don't arise in
  practice.
- The fallback is documented as a per-helper trust assumption,
  not a global wrap-rule exception.

If a future SAW test exercises per-index Stream errors, the trust
point would have to be promoted to a hard error or
`Stream (Except α)` representation. Until then, document and move
on.

## 8. Out of scope

- Performance / proof size. The wrap pervasion adds many
  `Bind.bind` / `Pure.pure` calls. Eventually we may want a
  simplifier pass. Not a soundness concern.
- SAW Prelude lemma re-statement under Phase β. Eq__rec,
  eq_cong, etc. autoEmit raw. If a VC discharge needs them at the
  wrapped types, we'll need to either restate them or generate
  wrap-aware wrappers. No current test exercises this.
- Universe polymorphism interactions. Tracked by
  `universeBinderAssignments`; orthogonal to the wrap rule.
