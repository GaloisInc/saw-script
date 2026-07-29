/-
F-1 pin (audit-2, 2026-07-24; probe landed 2026-07-28). The
under-applied partial-op path (`lowerPartialOpRuntimeWrapper`)
annotates the emitted definition RAW for a `Nat -> Nat` SAW type
while the body is the Except-level runtime wrapper — its single
pinned golden emission is ILL-TYPED, and the F-1 disposition rests
on that failure being LOUD: Lean rejects the artifact, and `adaptTo`
ensures nothing downstream silently absorbs the stray `Except`.

This probe makes the loudness a TESTED property instead of an
assumption. It reproduces the golden's emission shape
(`saw-boundary/partial_operation_obligations/under_applied_partial`).
It must FAIL with a type mismatch. If this file ever compiles clean
— an implicit coercion, a library instance, or a signature change
absorbing the Except level — the under-applied path's failure mode
has become SILENT, and that is a soundness event, not a fix:
re-audit the path before touching this pin (the honest fixes are a
wrapped-convention signature or deleting the lowering; see
doc/2026-07-18_underapplied-partial-op-wrapper.md, correction of
2026-07-25).
-/

-- Imports must match the ARTIFACT's (`import CryptolToLean`, the
-- whole library), not just the module the wrapper lives in
-- (2026-07-29, session audit). Instance resolution is
-- import-closure-scoped: with the narrower import, an absorbing
-- coercion added in any of the other five library modules would make
-- the real emission compile silently while this probe stayed red and
-- the row reported OK — the exact silent-absorption event the probe
-- exists to catch.
import CryptolToLean
open CryptolToLean.SAWCorePrimitives

noncomputable def UnderAppliedPartialProbe : Nat -> Nat :=
  divNat_runtimeM (Pure.pure (natPos_macro one_macro))
