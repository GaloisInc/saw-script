# Phase β replan: type-directed SAW→Lean with `Except String`

**Date**: 2026-05-11 (rewrite after a session of false starts)
**Status of**: the saw-core-lean output layer that maps SAWcore terms
to Lean terms for VC discharge.

## What this is

saw-core-lean is the output layer of a SAW→Lean pipeline. SAWcore is
one IR; Lean is another. The job is to map SAWcore terms into Lean
terms whose Lean types make sense for SAW VC discharge in Lean's
kernel.

We don't care where the SAWcore term came from. Cryptol module,
SAWScript, hand-written via `parse_core`, auto-emitted SAW Prelude
entry — they're all SAWcore terms and translate the same way.

## Three guiding principles

1. **Soundness is absolute.** No Lean axioms beyond stdlib
   (`propext`, `Classical.choice`, `Quot.sound`). No `def`s whose
   meaning is stronger than what SAW asserts.
2. **Lean idiomatic.** Use Lean stdlib types and conventions. If
   Lean has something already (e.g. `Except`), use it directly — no
   vanity-named aliases. Output should look like Lean code a human
   would write.
3. **Designed for proofs.** A Lean VC has to be dischargeable using
   normal Lean proof tooling (`simp`, `omega`, `decide`, `rfl`,
   structural induction). The output must give the discharge a fair
   chance.

## The encoding decision for SAW's `error`

SAW's `error α msg : α` (and `unsafeAssert α x y : Eq α x y`) are
the only SAW primitives whose translation isn't structural. Phase α
already resolved `unsafeAssert` (tactic-discharged proof obligation,
mirrors Rocq). This plan resolves `error`.

The sound encoding is `Except String α` from Lean's stdlib. Cryptol
expressions that produce SAW value-typed results map to Lean
expressions of type `Except String α'` (where `α'` is the Lean
translation of the SAW value type). SAW's `error α msg` translates
to `Except.error msg : Except String α'`.

No new types in the hand library. `Except`, `Except.ok`,
`Except.error`, and the `Monad`/`Functor`/`Applicative` instances are
all stdlib. We use them as-is.

## The type-directed translation rule

A SAWcore term is translated based on its SAW type-of-type:

| SAW expression's type | Lean translation lives at |
|---|---|
| `sort u` (a type / type-of-types) | `Sort u` |
| `Prop` (a proposition / sort 0) | `Prop` |
| a *non-`Nat`* value type `α` (where `α : sort u`, `u ≥ 1`) | `Except String α'` |
| `Nat` (special — never wraps) | `Nat` |

Same rule applied to every SAWcore term, regardless of source. There
is no "Cryptol mode" flag.

### Why `Nat` is special

SAW's `Nat` plays a dual role: at *value position* (a regular Cryptol
value) and at *type-index position* (the size in `Vec n α`). Lean's
`Vec` (which is `Vector α n`) needs a plain `Nat` at the index. If
we wrap Nats, `Vec (Except String Nat) Bool` doesn't typecheck.

Pragmatic decision: Nat stays non-monadic. Operations on Nat
(`addNat`, `subNat`) stay non-monadic. Cryptol code that explicitly
errors at `Nat` type (rare) gets rejected at translation time. If
that turns out to limit useful coverage, Phase γ revisits.

### Why props don't wrap

A SAW proposition like `Eq α x y` translates to a Lean Prop:
`@Eq α' x y` (with `x`, `y` potentially Except-wrapped). The
proposition itself stays at `Prop`, not `Except String (Eq …)`.

Reason: `Cryptol (Eq …)` would mean "an Eq proof OR an error
message" — but errors are *values*, not propositions. A VC of type
`Except String (Eq …)` is trivially inhabitable by `Except.error msg`,
which doesn't discharge the VC's claim. Wrapping props is
soundness-broken.

Proofs themselves don't fail in SAW — `Eq.rec`, `sym`, `trans`, etc.
are structural eliminators, not partial. Stay non-monadic.

## Cascading: what changes in the translator output

A SAW expression `(x : α) → β` (where α is a non-Nat value type)
translates to `(x : Except String α') → β'` in Lean. So:

* Variable bindings in Cryptol-derived terms are at `Except String α`.
* Variable *references* in the body are at `Except String α` (no
  re-wrapping at use site — already wrapped from binding).
* Literal values at value position wrap in `Except.ok`.
* Function applications use applicative-style lifting:
  `f <type-params> <$> v_arg₁ <*> v_arg₂ <*> …`
  — where `<$>` and `<*>` are stdlib operators on `Except`.
* SAW's `error α msg` emits as `Except.error msg`.

### Example: `addOne x = x + 1`

SAWcore (after elaboration):
```
λ (x : Vec 8 Bool) → bvAdd 8 x (bvNat 8 1)
```

Lean translation:
```lean
fun (x : Except String (Vec 8 Bool)) =>
  bvAdd 8 <$> x <*> (bvNat 8 <$> Except.ok 1)
```

Type: `Except String (Vec 8 Bool) → Except String (Vec 8 Bool)`.

### Example: composition

SAWcore: `addOne (addOne y)`.

Lean: `addOne (addOne y)` — flat application, because `addOne y :
Except String (Vec 8 Bool)` which is exactly what `addOne` takes.

### Example: `error α msg`

SAWcore: `error (Vec 8 Bool) "boom"` (typed `Vec 8 Bool`).

Lean: `Except.error "boom" : Except String (Vec 8 Bool)`.

### Example: a SAW VC

SAWcore: `Eq (Vec 8 Bool) (addOne x) (bvAdd 8 x (bvNat 8 1))`.

Lean (a `Prop`):
```lean
@Eq (Except String (Vec 8 Bool))
    (addOne x)
    (bvAdd 8 <$> x <*> (bvNat 8 <$> Except.ok 1))
```

A discharge proves this Lean equality. Because the LHS and RHS are
the same applicative expression structurally, `rfl` (or
`simp [addOne]`) closes it for concrete cases.

## Hand library — what stays, what changes

**Stays** (no parallel monadic versions):

* All SAW Prelude polymorphic helpers — `Eq__rec`, `sym`, `trans`,
  `eq_cong`, `coerce__def`, etc. They're already polymorphic. Lean
  instantiates them at `Except String α` types as needed at the call
  site.
* Non-monadic value-domain ops — `bvAdd`, `bvNat`, `gen`,
  `atWithDefault`, `ite`, etc. The translator lifts them at call
  sites via `<$>`/`<*>`. No parallel monadic mirror.

**Changes**: nothing yet. The hand library doesn't need a redesign;
it needs the *translator* to start emitting type-directed wrapping.

## Translator — what changes

Per emission point in `SAWCoreLean.Term`:

* `translateBinder'` (and friends): if the binder's SAW type is a
  non-`Nat` value type (sort ≥ 1) AND the binder is not "rigid-used"
  (see below), bind at `Except String α'` instead of `α'`.
* `translateTerm` for `Variable nm`: emit `Var nm` unchanged — the
  binder already wraps.
* `translateTerm` for value literals at value position: emit
  `Except.ok lit`.
* `translateFTermF` for `App f args` where the result is value-typed:
  emit applicative-lifted form. Type-parameter args spliced in
  directly, value-arg args wrapped/lifted.
* `translateConstant` / SAW's `Prelude.error`: emit `Except.error msg`.
* Definition's return type: wrap in `Except String α'` if value-typed.

### Rigid-used detection

A binder is "rigid-used" if it appears in a position where Lean's
typechecker requires the unwrapped type (e.g. as the size index of
`Vec`, or the carrier of `Eq` at type-level use). Implementation:
walk subsequent binder types and the return type; if the binder
appears in a known rigid-index slot (`Vec _ _`, `Eq _ _ _` where the
binder is the first arg, etc.), don't wrap.

Minimum-viable rigid detection: hard-code the rigid slots for the
type constructors we care about (`Vec`, `Eq`, `Stream`). Extend as
needed.

## Phases

### β.1 — type-directed `translateBinder'`

For each SAW Pi/Lambda binder, decide whether to wrap based on its
SAW type and rigid-used analysis. Emit the wrapped or unwrapped
Lean binder.

Validation: hand-rolled SAW probe (`parse_core "\\(x : Vec 8 Bool) → x"`)
emits `(x : Except String (Vec 8 Bool)) → x`. Elaborates clean.

Estimated cost: ~2 days.

### β.2 — applicative lifting in `translateFTermF.App`

For `App f args` where the result is value-typed, emit the
applicative form. Each arg recursively translated; type-params
spliced; value-args lifted.

Validation: probe `parse_core "\\(x : Vec 8 Bool) → bvAdd 8 x x"`
emits `fun x => bvAdd 8 <$> x <*> x` and elaborates.

Estimated cost: ~2-3 days. Most of the work is plumbing — the rule
itself is small.

### β.3 — `Prelude.error` SpecialTreatment

Flip `error` from `reject` to a SpecialTreatment entry that emits
`Except.error msg`. With β.1 and β.2 in place, the surrounding
emission is monadically consistent.

Validation: probe with `parse_core "\\(b : Bool) → ite (Vec 8 Bool)
b (bvNat 8 0) (error (Vec 8 Bool) \"unreachable\")"` emits the
expected `ite`-with-error shape and elaborates.

Estimated cost: ~1 day.

### β.4 — re-validate the 33 failing tests

Run the suite. For each test that comes back online, refresh
`.lean.good`. For each still failing, investigate.

Estimated cost: ~2-3 days.

### Phase ε (orthogonal)

Prove the `vecToBitVec_bitVecToVec` / `bitVecToVec_vecToBitVec`
round-trip "axioms" as theorems. Closes the last hand-library
axioms beyond Lean stdlib. ~1 day, can run alongside β.

## Total

~7-9 days for β.1 through β.4. End state: 33 tests back online,
hand library and auto-emit prelude axiom-clean, translator output
is Lean-idiomatic do/applicative-style code.

## What this plan does NOT do

These were the wrong abstractions I built earlier in this session
and that we deliberately don't do this time:

* No `Cryptol α` wrapper type. We use `Except String α` directly
  from Lean stdlib.
* No parallel `Cryptol.bvAdd`/`Cryptol.bvNat`/etc. hand-library
  mirrors. The translator does the lifting at call sites; the hand
  library has one version of each op.
* No `cryptolMode :: Bool` flag in `TranslationConfiguration`. The
  translator's wrap rule is type-directed, applied uniformly.
* No post-translation rewrite pass to monadify. The translator emits
  the right shape directly.
* No vanity-named anything. Use stdlib names.

## What we will revisit if it bites

* Cryptol code that actually errors at `Nat` type. Currently
  rejected. If Phase β.4 surfaces a real test case, extend.
* SAW Prelude ops that are control-flow rather than data-flow
  (`ite`, recursors). Applicative `<*>` doesn't naturally handle
  conditional evaluation. May need per-op handling in β.2.
* Performance of nested `<$>`/`<*>` chains. Lean's elaborator
  handles them but they can be hard to read. May want a
  `cryptol_eq` discharge tactic later (deferred).
