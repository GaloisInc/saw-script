
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.xor_swap_gen.
Import xor_swap.


Definition xor_swap_spec x1 x2 :
  CompM (bitvector 64 * bitvector 64) :=
  returnM (x2, x1).
Arguments xor_swap_spec /.

Lemma no_errors_xor_swap : refinesFun xor_swap (fun _ _ => noErrorsSpec).
Proof.
  unfold xor_swap, xor_swap__tuple_fun, noErrorsSpec.
  time "no_errors_xor_swap" prove_refinement.
Qed.


Lemma bvXor_twice_r n x y :
  SAWCorePrelude.bvXor n (SAWCorePrelude.bvXor n x y) y = x.
Proof.
  rewrite <- bvXor_assoc. rewrite bvXor_same. rewrite bvXor_zero. reflexivity.
Qed.

Lemma bvXor_twice_l n x y :
  SAWCorePrelude.bvXor n (SAWCorePrelude.bvXor n y x) y = x.
Proof.
  rewrite bvXor_comm. rewrite bvXor_assoc.
  rewrite bvXor_same. rewrite bvXor_comm. rewrite bvXor_zero. reflexivity.
Qed.

Lemma xor_swap_correct : refinesFun xor_swap xor_swap_spec.
Proof.
  prove_refinement.
  rewrite bvXor_twice_r. rewrite bvXor_twice_l.
  reflexivity.
Qed.
