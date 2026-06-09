# Phase 2.4 hand-library universe audit

**Date**: 2026-05-11
**Question**: With Phase 2.2's per-binder-fresh universe machinery
now live, which hand-library defs in
`saw-core-lean/lean/CryptolToLean/` need to become
universe-polymorphic to receive translator-emitted calls correctly?

## Finding: hand-library needs *no* changes

The hand-library covers SAWCore *primitives* (constants without
SAWCore bodies). SAW's primitives have **fixed** sort signatures:

| SAW primitive   | SAW signature                       | Hand-library shape           |
|-----------------|-------------------------------------|------------------------------|
| `coerce`        | `(a b : sort 0) → Eq … → a → b`     | `(α β : Type) → @Eq Type α β → α → β` |
| `unsafeAssert`  | `(a : sort 1) → x y → Eq a x y`     | `(α : Type) → … → @Eq α x y` |
| `error`         | `(a : isort 1) → String → a`        | `error_unrestricted.{u} : Sort (u+1) → String → α` |
| `fix`           | `(a : sort 1) → (a → a) → a`        | (rejected — recursion design blocker) |

`sort 0` and `sort 1` in SAW correspond to Lean's concrete `Type 0`
(= `Type` = `Sort 1`) and `Type 1` (= `Sort 2`) under the
sort-shift convention. **They are not polymorphic.** The hand-library
correctly mirrors them at concrete universes.

`error_unrestricted` is the lone exception. It is polymorphic in
the hand-library because Cryptol's typeclass elaboration emits
`error <SomeUninhabitedType> "invalid instance"` in dead branches
across an arbitrary mix of universes (incl. `Sort 1`, `Sort 2` for
nested vector types). The polymorphism is faithful to the
*advisory* nature of SAW's `isort` flag — see the existing comment
block at `SAWCorePrimitives.lean:725`.

## Where universe polymorphism *does* live

In **defined** SAWCore Prelude constants that have sort-k binders
in their bodies — `Eq__rec`, `eq_cong`, `sym`, `trans`, `sawLet`,
etc. These are not in the hand-library because they have
SAWCore bodies that the auto-emit machinery (Phase 3) will
translate. The Phase 2.2 translator emits `Sort u_n` for those
binders correctly; Phase 3 packages the result as a Lean `def`
with explicit universe binders (`def Eq__rec.{u₁, u₂} …`).

## L-2 shape tests stay valid

`otherTests/saw-core-lean/shape/coerce/attack.shouldfail.lean` and
`otherTests/saw-core-lean/shape/unsafe_assert_prop/` pin the
hand-library's monomorphic shapes. With this audit's conclusion
(no hand-library changes), those tests stay valid as-is. They
become *more* important post-Phase 3: they pin the asymmetry
between fixed-sort primitives (hand-library) and polymorphic
defined constants (auto-emitted).

## Phase 2.4 outcome

**No code changes required.** This document records the audit's
conclusion so future work doesn't re-litigate.
