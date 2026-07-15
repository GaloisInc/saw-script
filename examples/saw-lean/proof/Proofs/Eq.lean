/-
Discharge for `impl_eq_spec` (rev.cry / demo.saw):
`implRev xs == specRev xs` over `[4][8]`.

`Proofs/EqEmitted.lean` is the namespace-wrapped verbatim copy of
the `offline_lean`-emitted `out/eq_spec_prove0.lean`. Under the
OP-1/OP-2 obligation-placement program every embedded evidence chain
closes at emission, so the only `sorry` in the emitted copy is its
`goal_holds` stub — the theorem below replaces it.

Discharge (same proof as the raw-artifact demo discharge): same
reduction plan as the involution proof — unfold the checked helpers
and the literal Int sign-split arithmetic, collapse the
double-reverse index identity, and the size-4 pointwise `bvEq` fold
evaluates.
-/
import Proofs.EqEmitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

namespace EqDemo

theorem goal_closed : goal := by
  intro xs
  have h_double_rev_idx : ∀ i : Fin 4, 3 - (3 - (i : Nat)) = (i : Nat) := by
    intro i
    omega
  have hfin0 : ((0 : Fin 4) : Nat) = 0 := rfl
  have hfin1 : ((1 : Fin 4) : Nat) = 1 := rfl
  have hfin2 : ((2 : Fin 4) : Nat) = 2 := rfl
  have hfin3 : ((3 : Fin 4) : Nat) = 3 := rfl
  simp +decide [genWithBoundsM, atWithProof_checkedM, atRuntimeCheckedM,
    foldrM, subNat, vecSequenceM, Vector.ofFnM_succ, Vector.ofFnM_zero,
    intLe, intSub, intNeg, intToNat, natToInt,
    hfin0, hfin1, hfin2, hfin3,
    CryptolToLean.SAWCorePreludeExtra.iteM, h_double_rev_idx, bvEq_refl,
    Pure.pure, Bind.bind, Except.pure, Except.bind]

end EqDemo
