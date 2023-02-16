
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
(* From CryptolToCoq Require Import CompMExtra. *)
From CryptolToCoq Require Import SpecMExtra.
From EnTree  Require Import Automation.

Require Import Examples.xor_swap_gen.
Import xor_swap.

Set Bullet Behavior "Strict Subproofs".

Definition xor_swap_spec (x1 x2: bitvector 64) := (x2, x1).
Arguments xor_swap_spec /.


(* First prove safety (i.e. no errors) *)
Lemma xor_swap_not_error (x y: bitvector 64) :
  spec_refines eqPreRel eqPostRel eq
    (xor_swap x y)
    (total_spec (fun _ =>  True) (fun xy r => True ) (x,y)).
Proof.
  intros.
  unfold xor_swap, xor_swap__bodies.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0.
    + exact (x0 = x2 /\ x1 = x3).
    + exact (r_x = r_x1 /\ r_x0 = r_x2).
    + prepost_exclude_remaining.
  - prove_refinement_continue.
Qed.
      
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
  spec_refines eqPreRel eqPostRel eq
    (xor_swap x y)
    (total_spec
       (fun _ =>  True)
       (fun xy r => r = xor_swap_spec (fst xy) (snd xy))
       (x,y)).
Proof.
  intros.
  unfold xor_swap, xor_swap__bodies.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0.
    + exact (x0 = x2 /\ x1 = x3).
    + exact (r_x = r_x1 /\ r_x0 = r_x2).
    + prepost_exclude_remaining.
  - prove_refinement_continue.
    + apply bvXor_twice_l.
    + apply bvXor_twice_r.
Qed.
      
Local Hint Extern 10 (spec_refines eqPreRel eqPostRel eq (xor_swap _ _) _) =>
       simple apply xor_swap_spec_ref: refine_proofs.
