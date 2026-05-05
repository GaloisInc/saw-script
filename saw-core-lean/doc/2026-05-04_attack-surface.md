# Attack-surface inventory (saw-core-lean)

**Date:** 2026-05-04
**Status:** Living doc; update whenever a new attack vector is found
or an existing residual is closed.

## Purpose

The L-17 incident showed that example-driven attack tests
(`error False ""`) miss structurally-different routes to the same
goal (`Empty.elim ∘ error Empty`). This doc inventories every
known route a hostile prover could take to derive `False` (or
populate an uninhabited type) using **only** the support-library
axioms exposed to user code. Each route is classified as:

- **B (blocked)** — elaboration rejects this attack. Pinned by a
  `*.shouldfail.lean` probe.
- **R (residual)** — currently *not* blocked; documented as a
  known soundness trade-off. Should NOT be added as a `shouldfail`
  probe — it would fail the test.
- **N (not applicable)** — the attack route doesn't exist (e.g.,
  required symbol isn't exposed to user code).

The audit is **non-exhaustive** in principle (a hostile prover
can compose axioms in unbounded ways), but it covers every route
we have explicitly considered.

## Surface enumeration

### Routes via `error.{u}`

`error.{u} : (α : Sort (u+1)) → String → α` (post-L-17-revert).

| Route | Status | Pin / note |
|-------|--------|-----------|
| `error False "" : False` | **B** | `Sort (u+1)` excludes `Prop`; `False : Prop`. Pinned by `shape/error_prop/attack.shouldfail.lean`. |
| `Empty.elim (error Empty "boom")` → `False` | **R** | `Empty : Type 0 = Sort 1` fits `Sort (u+1)`. Documented as L-17 residual. Proper fix tracked as task #137 (translator-emitted Inhabited evidence). |
| `@Inhabited.default _ (error (Inhabited Empty) "")` → `Empty` → `False` | **R** | Generalization of the Empty route via the `Inhabited` typeclass. `Inhabited Empty : Type 0` is uninhabited, but `error (Inhabited Empty) "..."` typechecks. Same residual class as L-17. Same fix unlocks both. |
| `error α "..."` for any other uninhabited type α : Type u | **R** | Universal version of the L-17 residual. Includes `Fin 0`, `PEmpty`, etc. |

### Routes via `unsafeAssert`

`unsafeAssert : (α : Type) → (x y : α) → @Eq α x y`.

| Route | Status | Pin / note |
|-------|--------|-----------|
| `unsafeAssert (Type 1) _ _` (or higher) | **B** | Signature caps α at `Type` = `Type 0`. Pinned by `shape/unsafe_assert_prop/attack.shouldfail.lean`. |
| `unsafeAssert Prop False True` | **B** | `Prop : Sort 0`, not a `Type`; α : Type. |
| `unsafeAssert Bool true false` → `Bool.noConfusion` → `False` | **R** | unsafeAssert is *intentionally unsound* by SAW design. SAW uses it for type-arithmetic coercions where the equality is assumed (not proven). Documented as faithful translation of SAW's residual trust. |
| `unsafeAssert (Vec n α) v1 v2` for v1 ≠ v2 | **R** | Same residual class as Bool. Generic unsafeAssert misuse. |
| `unsafeAssert Type Bool Empty` then `coerce` | **R** | Universe-level mismatch (`Eq.{1}` vs `Eq.{2}`) blocks the *most direct* combination, but a determined attacker with bumped universes can chain it. Same residual class as Bool. |

### Routes via `coerce`

`coerce : (α β : Type) → @Eq Type α β → α → β`.

| Route | Status | Pin / note |
|-------|--------|-----------|
| `coerce (Type 1) _ _ _` | **B** | α, β : Type = Type 0. Higher universes rejected. Pinned by `shape/coerce/attack.shouldfail.lean`. |
| `coerce α β (unsafeAssert _ α β) x` | **R** | Composition of coerce + unsafeAssert = same residual class as unsafeAssert misuse. |

### Routes via `fix` (translator-rejected)

| Route | Status | Pin / note |
|-------|--------|-----------|
| `fix τ body` for any τ | **N** | `fix` is rejected at SAW translation boundary (L-5). Not exposed in CryptolToLean. User can't construct it. |

### Routes via recursors over uninhabited types

| Route | Status | Pin / note |
|-------|--------|-----------|
| Translator emits `Nat__rec` / `Pos__rec` / etc. | **B** | L-3 auto-derives opacity for all 5 unsound recursor types, so they don't reach user surface. Pinned by smoketest `discoverNatRecReachers` (line 396 of `smoketest/SmokeTest.hs`). |
| User-side attempt to call `Nat__rec` directly | **N** | Not exposed in CryptolToLean's user-facing namespace. User would have to import a different module. |
| Translator emits bare `Bool#rec` (case order inversion) | **B** | L-16 keeps the Bool ops opaque so they don't unfold to bare `Bool#rec1`. Pinned by smoketest `Bool#rec doesn't surface bare in translated output (L-16)` (line 600). |

### Routes via `Vec` constructor / recursor

| Route | Status | Pin / note |
|-------|--------|-----------|
| Pattern-match on `Vec.mk` directly | **R** | L-4: documented but never enforced. Open task to seal Vec via opaque structure. |

## Status summary

- **Blocked** (probed, currently rejected): 6 routes.
- **Residual** (documented, currently *not* rejected): 6+ routes
  in two clusters (L-17 family, unsafeAssert family).
- **Not applicable** (symbol unreachable): 2 routes.

## How the cluster of "residual" attacks gets closed

- **L-17 family** (everything via `error` at uninhabited type):
  closed once task #137 ships — translator emits `[Inhabited a]`
  evidence at every `(a : Type)` binder, support library
  re-tightens `error.{u}` to require `[Inhabited α]`, every
  uninhabited-type instantiation fails synthesis. Probes for
  `error Empty`, `error (Inhabited Empty)`, `error PEmpty`, etc.
  can then be added to `shape/`.

- **unsafeAssert family** (everything that exploits unsafeAssert's
  intentional unsoundness): cannot be closed without changing
  SAW's semantics. SAW uses unsafeAssert as the sole mechanism for
  type-arithmetic coercions (e.g., `unsafeAssert Num (TCNum n)
  (TCNum m)` for size equalities). Removing it would require
  proving every Cryptol size identity, which is impractical.
  Mitigation: ensure unsafeAssert is *only* applied at types the
  SAW translator emits, not at attacker-chosen types. Currently
  enforced by sort restriction (Type, not Prop, not higher).

## Adding new attack vectors

When you discover a new combinational attack:

1. Reproduce it as a Lean snippet in this doc, with `#print
   axioms` showing the dependency.
2. If blocked: add a probe at `otherTests/saw-core-lean/shape/`.
3. If residual: add a row to the table above with a clear note
   on which fix would close it.
4. If unreachable: add a row noting why.

## See also

- `2026-04-24_soundness-boundaries.md` — L-1 through L-17 catalog.
- `2026-05-02_residual-trust.md` — broader trust assumptions.
- task #137 — translator-emitted Inhabited evidence (closes L-17
  family).
- task #133 — this audit (the doc you're reading).
