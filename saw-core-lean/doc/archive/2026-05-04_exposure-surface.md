# Exposure-surface inventory (saw-core-lean)

**Date:** 2026-05-04
**Status:** Living doc; update whenever a new Check vector is found
or an existing residual is closed.

## Purpose

The L-17 incident showed that example-driven Check tests
(`error False ""`) miss structurally-different routes to the same
goal (`Empty.elim ∘ error Empty`). This doc inventories every
known route a hostile prover could take to derive `False` (or
populate an uninhabited type) using **only** the support-library
axioms exposed to user code. Each route is classified as:

- **B (blocked)** — elaboration rejects this probe. Pinned by a
  `*.shouldfail.lean` probe.
- **R (residual)** — currently *not* blocked; documented as a
  known soundness trade-off. Should NOT be added as a `shouldfail`
  probe — it would fail the test.
- **N (not applicable)** — the probe route doesn't exist (e.g.,
  required symbol isn't exposed to user code).

The audit is **non-exhaustive** in principle (a hostile prover
can compose axioms in unbounded ways), but it covers every route
we have explicitly considered.

## Surface enumeration

### Routes via `error` (two-tier design after L-17 mitigation)

The support library exposes two error symbols:
* `error_unrestricted.{u} : (α : Sort (u+1)) → String → α` —
  unsafe axiom, translator emission target only.
* `error.{u} (α : Type u) [Inhabited α] (msg : String) : α` —
  user-facing constrained def. Unqualified `error` resolves
  here in user discharges.

| Route | Status | Pin / note |
|-------|--------|-----------|
| `error False ""` (user-facing) | **B** | `error : Type u → ...` excludes `Prop` directly. Pinned by `negative/error_prop/rejection.shouldfail.lean`. |
| `error_unrestricted False ""` | **B** | `Sort (u+1)` excludes `Prop`. Same probe also covers this since the Sort restriction matches. |
| `Empty.elim (error Empty "boom")` → `False` | **B** | User-facing `error` requires `[Inhabited α]`; `Inhabited Empty` does not exist. Pinned by `negative/error_prop/rejection_empty.shouldfail.lean`. |
| `@Inhabited.default _ (error (Inhabited Empty) "")` → `Empty` → `False` | **B** | Same blocker — `Inhabited (Inhabited Empty)` does not exist. |
| `error α "..."` (user-facing) for any uninhabited α : Type u | **B** | Universal — Inhabited synthesis fails on every uninhabited type. |
| `Empty.elim (error_unrestricted Empty "boom")` → `False` | **R** | The user explicitly opts out by writing the long unsafe name. Same residual class as `unsafeAssert` generic unsoundness. Translator never emits it at uninhabited types (Cryptol surface has no Empty). Faithful binding of SAW's actual error semantics. |

### Routes via `unsafeAssert`

`unsafeAssert : (α : Type) → (x y : α) → @Eq α x y`.

| Route | Status | Pin / note |
|-------|--------|-----------|
| `unsafeAssert (Type 1) _ _` (or higher) | **B** | Signature caps α at `Type` = `Type 0`. Pinned by `negative/unsafe_assert_prop/rejection.shouldfail.lean`. |
| `unsafeAssert Prop False True` | **B** | `Prop : Sort 0`, not a `Type`; α : Type. |
| `unsafeAssert Bool true false` → `Bool.noConfusion` → `False` | **R** | unsafeAssert is *intentionally unsound* by SAW design. SAW uses it for type-arithmetic coercions where the equality is assumed (not proven). Documented as faithful translation of SAW's residual trust. |
| `unsafeAssert (Vec n α) v1 v2` for v1 ≠ v2 | **R** | Same residual class as Bool. Generic unsafeAssert misuse. |
| `unsafeAssert Type Bool Empty` then `coerce` | **R** | Universe-level mismatch (`Eq.{1}` vs `Eq.{2}`) blocks the *most direct* combination, but a determined proof author with bumped universes can chain it. Same residual class as Bool. |

### Routes via `coerce`

`coerce : (α β : Type) → @Eq Type α β → α → β`.

| Route | Status | Pin / note |
|-------|--------|-----------|
| `coerce (Type 1) _ _ _` | **B** | α, β : Type = Type 0. Higher universes rejected. Pinned by `negative/coerce/rejection.shouldfail.lean`. |
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

- **Blocked** (probed, currently rejected): 9 routes.
- **Residual** (documented, currently *not* rejected): 3+ routes
  — all in the unsafeAssert family or via the `error_unrestricted`
  explicit-opt-out form.
- **Not applicable** (symbol unreachable): 2 routes.

## How the cluster of "residual" checks gets closed

- **L-17 family** (user-side `error` at uninhabited type):
  **CLOSED** by the two-tier design (2026-05-04). User-facing
  `error` is constrained to `[Inhabited α]`, blocking every Empty,
  PEmpty, Fin 0, Inhabited Empty, etc. instantiation at synthesis
  time. Phase 9's earlier finding (translator-wide Inhabited
  binder injection breaks recursor application) is sidestepped:
  the translator routes to `error_unrestricted` (separate name,
  no Inhabited constraint), so emission still works for free
  type variables in dead-branch typeclass elaborations. The
  residual is "user explicitly writes the unsafe name" — same
  class as unsafeAssert misuse, faithful to SAW.

- **unsafeAssert family** (everything that unsound paths unsafeAssert's
  intentional unsoundness): cannot be closed without changing
  SAW's semantics. SAW uses unsafeAssert as the sole mechanism for
  type-arithmetic coercions (e.g., `unsafeAssert Num (TCNum n)
  (TCNum m)` for size equalities). Removing it would require
  proving every Cryptol size identity, which is impractical.
  Mitigation: ensure unsafeAssert is *only* applied at types the
  SAW translator emits, not at proof author-chosen types. Currently
  enforced by sort restriction (Type, not Prop, not higher).

## Adding new Check vectors

When you discover a new combinational probe:

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
