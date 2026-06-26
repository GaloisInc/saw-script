# saw-core-lean status

Last updated: 2026-06-26

## Purpose

`saw-core-lean` is a SAW proof backend. Its job is to translate SAWCore
terms, Cryptol-module definitions, and SAW proof obligations into Lean 4
source so Lean can discharge or check those obligations in its kernel.

Operationally, it fills the same slot as a solver backend in a SAW
workflow: SAW emits a verification condition, the backend presents that
condition to another trusted engine, and success means the obligation is
closed. The difference is that Lean checking is proof-kernel based, so
the emitted artifact should remain inspectable and replayable.

## Current Strategy

The current active design is Phase beta: value-domain SAW expressions
translate to Lean expressions at `Except String T`, where `T` is the
Lean translation of the SAW type. Type-level expressions translate raw.

Informally:

- If `e : tau` and `tau : sort 0`, then `e` emits as
  `Except String [[tau]]`.
- If `e` is a type expression, sort expression, motive, or proposition,
  it emits raw.
- Function application binds wrapped value arguments with `Bind.bind`,
  passes type/index arguments raw, and wraps value results with
  `Pure.pure`.
- Recursor scrutinees are unwrapped before elimination when the recursor
  produces a value; recursor case binders stay raw because Lean's
  recursor signatures require raw constructor arguments.
- SAW `error` routes to `saw_throw_error`, preserving user-visible
  errors. Fix-shape unreachable defaults route to
  `saw_unreachable_default`, which is a residual trust point tied to
  Cryptol productivity.

This is the intended soundness shape. Any implementation exception should
be documented as either a type-position exception, a Lean signature
adapter, or an explicit residual-trust item.

## Known State

Passing:

- The handwritten Lean support library builds with `lake build`.
- `cabal test saw-core-lean-smoketest` passes.
- The support-library negative shape probes reject as intended.

Not yet passing:

- The full `otherTests/saw-core-lean` suite still fails broadly.
- Many `.lean.good` files predate Phase beta and need regeneration after
  emitted Lean elaborates.
- Most proof scripts are still written against raw, pre-Phase-beta goals.
- Some emitted Lean does not elaborate yet. The main semantic gaps are:
  Nat value positions, constructor-argument lambdas, and variable-headed
  value types around `Eq.rec` / `coerce`.

## Next Repair Order

1. Fix emitted Lean elaboration before refreshing golden files.
2. Implement Nat-at-value-position wrapping/binding.
3. Add constructor/lambda adapters for wrapped-output lambdas used where
   Lean constructors expect raw-output functions.
4. Revisit variable-headed value-type wrapping once the first two gaps are
   closed.
5. Add proof-side simp lemmas for the Phase-beta helpers.
6. Update proof scripts and regenerate `.lean.good` files.
7. Re-sync architecture and trust docs to the implementation.
