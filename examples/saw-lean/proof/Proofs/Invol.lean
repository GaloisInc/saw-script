/-
Discharge for `revInvolutive` (rev.cry / demo.saw):
`implRev (implRev xs) == xs` over `[4][8]`.

`Proofs/InvolEmitted.lean` is the namespace-wrapped verbatim copy of
the `offline_lean`-emitted `out/invol_prove0.lean`. Under the
OP-1/OP-2 obligation-placement program every embedded evidence chain
closes at emission, so the only `sorry` in the emitted copy is its
`goal_holds` stub — the theorem below replaces it.

Discharge (same proof as the raw-artifact demo discharge): unfold the
checked helpers and the concrete Int sign-split index arithmetic
(`xs @ (3 - i)` computes through `natToInt`/`intSub`/`intToNat` under
an `intLe` test — all literals here), collapse the double reverse
with `3 - (3 - i) = i`, and the size-4 fold of `bvEq xs[i] xs[i]`
reduces away.
-/
import Proofs.InvolEmitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

namespace InvolDemo

theorem goal_closed : goal := by
  intro xs
  have h_double_rev_idx : ∀ i : Fin 4, 3 - (3 - (i : Nat)) = (i : Nat) := by
    intro i
    omega
  -- simp does not rewrite `((k : Fin 4) : Nat)` numeral casts in
  -- place (rfl/decide close them, but no simp lemma fires); feed the
  -- reductions explicitly so the concrete list lookups the sign-split
  -- leaves behind can evaluate.
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

end InvolDemo
