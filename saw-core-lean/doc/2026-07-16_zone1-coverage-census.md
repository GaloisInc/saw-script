# Zone-1 coverage census (2026-07-16)

**Status**: LIVE ARTIFACT — the explicit membership list behind the
zone anatomy's Zone-1 claim (see
2026-07-16_fragment-semantics-scoping.md). Re-run the census when the
emitter surface changes. Produced by a read-only census pass over
SpecialTreatment.hs + Term.hs dispatches vs Prelude.sawcore vs the
differential rows' emitted observed.lean artifacts; spot-verified
independently (boolean row folds to `Pure.pure Bool.true` — confirmed;
cryptol_bv_sext is a non-emitting known-gap — confirmed).

## The methodological finding (matters more than the list)

`write_lean_term` runs `scNormalizeForLean` BEFORE emission, so on
CONCRETE inputs any combinator not in `leanOpaqueBuiltins`
constant-folds away — several rows nominally "about" an operation
(boolean, nat_scalar, …) actually compare a pre-folded constant, and
the Lean realization under test never executes. Differential coverage
below is measured STRICTLY: a name counts only if its realization
appears in the compared observed.lean.

**Closure design for the exposure list**: differential rows need
concrete VALUES to compare, but folding needs an OPEN term to be
blocked. Emit a FUNCTION (`write_lean_term {{ \x -> op x c }}` — an
open body survives normalization), then apply it to concrete
arguments inside the row's hand-written lean-observe.lean and compare
against SAW's evaluation at the same arguments. Fits the existing
differential harness with no support changes.

## Summary

~150 emittable names; ~95 with genuine differential coverage; ~55
with NONE (exposure list below). Frontier (partiality) = 20 names,
every one behind a checked/obligation-carrying realization; the rest
total. Realizations documented against Prelude.sawcore essentially
throughout.

## Zone-1 exposure list (total-zone, NO genuine differential coverage)

Value-carrying (close these first, via the open-term pattern):
expNat, doubleNat, pred, leNat; intSub, intMul, intLe, intLt;
rationalZero; **bvUExt, bvSExt** (dedicated row is a known-gap
non-emitting row — highest priority); not, and, or, xor, boolEq
(every boolean row pre-folds; symbolic uses route through iteM so the
named ops are never directly observed); if0Nat, natCase; Either/Left/
Right; PairType1/PairValue1; seq/Bit/bitvector (aliases);
Float/mkFloat/Double/mkDouble (stubs — unobservable by construction,
SAW has no ops either).

Proof/type-level infra (total, not observationally testable — the
harness only reduces value terms): id, sawLet, Eq__rec, sym, trans,
eq_cong, trans2, trans4, eq_inv_map, coerce__def, coerce__def_trans,
rcoerce, piCong0, piCong1, inverse_eta_rule, not__eq, and__eq,
ite_eq_iteDep, iteDep, iteDep_True, iteDep_False.

## Flags (spots to read carefully — none concluded as bugs)

1. **mkDouble : Integer -> Integer -> Float** — faithful to an
   apparent UPSTREAM Prelude.sawcore typo (Prelude.sawcore:2163
   declares mkDouble returning Float). The realization preserves the
   quirk deliberately (no silent corrections). Unobservable (no ops).
2. **IntMod n = Int (representative-based)** — sound only because
   every operation and intModEq re-applies Int.fmod; the reducible
   alias would let an un-normalized representative escape a raw Int
   comparison silently if any future realization skipped the fmod
   discipline. Keep the discipline in review scope for any new IntMod
   op.
3. **Float/Double = Int x Int vs SAW's opaque primitives** — strictly
   more concrete than SAW; sound while SAW exposes no operations;
   revisit if SAW ever adds any.

## Frontier set (all obligation-carrying; for completeness)

divNat, modNat, divModNat, intDiv, intMod, ratio, rationalRecip,
bvUDiv, bvURem, bvSDiv, bvSRem, at, gen, error, unsafeAssert, fix,
MkStream, streamScanl, Stream (productivity), + checked cousins.

Full per-name table (zone / Prelude status / realization-doc /
covering row) lives in the census transcript; regenerate on demand —
this doc records the exposure list, flags, and method, which are the
actionable parts.
