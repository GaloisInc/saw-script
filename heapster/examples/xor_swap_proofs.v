From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From EnTree  Require Import Automation.

Require Import Examples.common.
Require Import Examples.xor_swap_gen.
Import xor_swap.

Set Bullet Behavior "Strict Subproofs".

Definition xor_swap_spec (x1 x2: bitvector 64) := (x2, x1).
Arguments xor_swap_spec /.


(* First prove safety (i.e. no errors) *)
Lemma xor_swap_not_error (x y: bitvector 64) :
    spec_refines_eq (xor_swap x y) (safety_spec (x,y)).
Proof. solve_trivial_spec 0 0. Qed.
      
Local Hint Extern 10 (spec_refines eqPreRel eqPostRel eq (xor_swap _ _) _) =>
        simple apply xor_swap_not_error: refine_proofs.


(* | Nice notation for better reading in this file*)
Local Infix "^^" := (SAWCorePrelude.bvXor 64) (at level 30).
Lemma bvXor_twice_l:
  forall x1 x2 : bitvector 64, x2 ^^ (x2 ^^ x1) = x1.
Proof.
  intros; rewrite bvXor_assoc, bvXor_same, bvXor_comm, bvXor_zero.
  reflexivity.
Qed.

Lemma bvXor_twice_r:
  forall x1 x2 : bitvector 64, (x1 ^^ x2) ^^ x2 = x1.
Proof.
  intros; rewrite <- bvXor_assoc, bvXor_same, bvXor_zero.
  reflexivity.
Qed.    

(* | Now we can prove correctness *)
Lemma xor_swap_spec_ref (x y: bitvector 64) :
  spec_refines_eq (xor_swap x y)
    (total_spec (fun _ =>  True) (fun xy r => r = xor_swap_spec (fst xy) (snd xy))
       (x,y)).
Proof. solve_trivial_spec 0 0.
    - apply bvXor_twice_r.
    - apply bvXor_twice_l.
Qed.
      
Local Hint Extern 10 (spec_refines eqPreRel eqPostRel eq (xor_swap _ _) _) =>
       simple apply xor_swap_spec_ref: refine_proofs.
