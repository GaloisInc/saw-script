# Under-applied partial-op function wrappers (W1: the intDiv blocker)

2026-07-18. Status: DESIGN — pre-audit. Unblocks rev.cry whole-module
translation (PIntegral dictionary fields carry partial ops
UNAPPLIED; pinned by saw-boundary/polymorphic_seq_module_rejection).

## Problem

Partial-op contracts (Contracts.hs) lower APPLIED occurrences at
exactly contract arity, wiring per-application checked evidence
(h_nonzero). A partial op in FUNCTION-VALUE position (dictionary
field `div = intDiv`; partial application) has no application site
to attach evidence to, and an eta-expanded obligation over the
lambda-bound divisor would be universally quantified — unprovable
(the OP-3 lesson: never emit obligations where they cannot be
proved). Today: named rejection.

## Semantics ground truth (the zero points)

- `intDiv`/`intMod`: SAW concrete simulator = Haskell div/mod
  (Concrete.hs:213 `bpIntDiv = pure2 div`) — divisor 0 CRASHES
  (⊥). Lean support `intDiv := Int.fdiv` is TOTAL (x/0 = 0). The
  zero points DIVERGE; equating them unguarded would be silent
  0-vs-⊥ unsoundness. The checked contract's `Not (y = pure 0)`
  hypothesis exists precisely to exclude this point.
- `divNat`/`modNat`: check SAW semantics per-op before design
  freeze (differential/nat_division_defined suggests SAW Nat
  division at 0 is DEFINED and agrees with Lean's total Nat.div —
  if confirmed, the under-applied wrapper for these is the PLAIN
  total function, no check).
- bv division family: zero-point semantics were pinned in the
  earlier zero-divisor work; per-op table entry required.

## Design: runtime-checked wrapper values (the OP-2 pattern lifted
to function position)

For each partial op the contract table gains an
`underAppliedWrapper` field naming a support-library RUNTIME
wrapper, e.g.

    def intDiv_runtimeM (x y : Except String Int) :
        Except String Int := do
      let x' <- x; let y' <- y
      if y' = 0 then throw "intDiv: division by zero"
      else pure (intDiv x' y')

Lowering rule: a contract-bearing partial op at LESS than contract
arity lowers to its wrapper (partially applied to the available
actuals under the wrapper's wrapped-formal convention —
phaseBetaFunctionValueModesFor family). Zero new recognizer
surface; the dispatch already knows the arity mismatch (the
current reject site). APPLIED sites keep the proof-carrying path
(evidence ⇒ provably error-free, raw-capable results).

Soundness: value semantics identical away from the zero point; AT
the zero point SAW is ⊥/crash and the wrapper is an Except error —
the calculus's standard error-effect mapping (fix_error_elem
precedent: escaping SAW runtime error vs Lean Except error =
agreeing outcome). For ops whose SAW zero point is DEFINED (Nat
family, if confirmed) the wrapper is the plain total lift and the
zero check is OMITTED — a per-op table decision, never a global
rule.

## Audit questions (for the pre-implementation audit)

1. Per-op zero-point table: verify EVERY partial-op contract's SAW
   concrete/symbolic semantics at the excluded point (intDiv,
   intMod, divNat, modNat, divModNat, bvUDiv, bvURem, bvSDiv,
   bvSRem, Cryptol signed family) against the proposed wrapper.
   Symbolic backends (What4/SBV) may define division at 0 (SMT
   semantics: bvudiv x 0 = ones!) — if SAW's SYMBOLIC zero point
   differs from concrete, which is "SAW semantics"? (Likely
   resolution: the backend translates SAWCore's own semantics =
   the simulator's; document.)
2. Error-message policy: SAW concrete CRASHES (no message) — is a
   canonical wrapper message acceptable under the differential
   error-outcome contract (currently unimplemented comparison)?
3. Convention fit: the wrapper value's type must match what
   phaseBetaFunctionValueModesFor declares for a var-headed/known
   function slot at the use site (dictionary field positions).
4. Interaction with OVER-application (contract arity < spine):
   currently also rejected — same wrapper + residual application?
5. No new obligations anywhere (the design emits ZERO proof
   obligations for wrapped values) — confirm no path smuggles an
   eta-local h_nonzero back in.
