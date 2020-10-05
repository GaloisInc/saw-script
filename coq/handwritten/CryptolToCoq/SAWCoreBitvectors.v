(***
 *** Lemmas about the bitvectors from SAWCoreVectorsAsCoqVectors
 ***)

From Coq Require Import Program.Basics.
From Coq Require Import Vectors.Vector.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

Import SAWCorePrelude.


(** Bitvector maximum and minimum values **)

Definition bvsmax w : bitvector w :=
  match w with
  | O => nil _
  | S w => cons _ false _ (gen w _ (fun _ => true))
  end.
Definition bvsmin w : bitvector w :=
  match w with
  | O => nil _
  | S w => cons _ true _ (gen w _ (fun _ => false))
  end.

Definition bvumax w : bitvector w := gen w _ (fun _ => true).
Definition bvumin w : bitvector w := gen w _ (fun _ => false).


(** Bitvector inquality propositions, and their preorders **)

Definition isBvsle w a b : Prop := bvsle w a b = true.
Definition isBvsle_def w a b : bvsle w a b = true <-> isBvsle w a b := reflexivity _.
Definition isBvsle_def_opp w a b : bvslt w a b = false <-> isBvsle w b a. Admitted.
Instance PreOrder_isBvsle w : PreOrder (isBvsle w). Admitted.

Definition isBvslt w a b : Prop := bvslt w a b = true.
Definition isBvslt_def w a b : bvslt w a b = true <-> isBvslt w a b := reflexivity _.
Definition isBvslt_def_opp w a b : bvsle w a b = false <-> isBvslt w b a. Admitted.
Instance PreOrder_isBvslt w : PreOrder (isBvslt w). Admitted.

Definition isBvule w a b : Prop := bvule w a b = true.
Definition isBvule_def w a b : bvule w a b = true <-> isBvule w a b := reflexivity _.
Definition isBvule_def_opp w a b : bvult w a b = false <-> isBvule w b a. Admitted.
Instance PreOrder_isBvule w : PreOrder (isBvule w). Admitted.

Definition isBvult w a b : Prop := bvult w a b = true.
Definition isBvult_def w a b : bvult w a b = true <-> isBvult w a b := reflexivity _.
Definition isBvult_def_opp w a b : bvule w a b = false <-> isBvult w b a. Admitted.
Instance PreOrder_isBvult w : PreOrder (isBvult w). Admitted.

(** Converting between bitvector inqualities **)

Definition isBvslt_to_isBvsle w a b : isBvslt w a b -> isBvsle w a b. Admitted.
Instance Proper_isBvslt_isBvsle w : Proper (isBvsle w --> isBvsle w ==> impl) (isBvslt w). Admitted.

Definition isBvult_to_isBvule w a b : isBvult w a b -> isBvule w a b. Admitted.
Instance Proper_isBvult_isBvule w : Proper (isBvule w --> isBvule w ==> impl) (isBvult w). Admitted.

Definition isBvslt_to_isBvsle_suc w a b : isBvslt w a b ->
                                          isBvsle w (bvAdd w a (bvLit w 1)) b.
Admitted.

Definition isBvult_to_isBvslt_pos w a b : isBvsle w (bvLit w 0) a ->
                                          isBvsle w (bvLit w 0) b ->
                                          isBvult w a b -> isBvslt w a b.
Admitted.

(** Other lemmas about bitvector inequalities **)

Definition isBvsle_suc_r w (a : bitvector w) : isBvsle w a (bvsmax w) ->
                                               isBvsle w a (bvAdd w a (bvLit w 1)).
Admitted.

Definition isBvslt_antirefl w a : ~ isBvslt w a a.
Admitted.

Definition isBvule_n_zero w a : isBvule w a (bvLit w 0) <-> a = bvLit w 0.
Admitted.

Definition isBvult_n_zero w a : ~ isBvult w a (bvLit w 0).
Admitted.


(** Lemmas about bitvector equality **)

Lemma bvEq_wrapped_bool (b : bool)
  : not (bvEq 1 (if b then bvLit 1 1 else bvLit 1 0) (bvLit 1 0)) = b.
Proof. destruct b; reflexivity. Qed.


(** Lemmas about bitvector addition **)

Lemma bvAdd_id_l w a : bvAdd w (bvLit w 0) a = a. Admitted.
Lemma bvAdd_id_r w a : bvAdd w a (bvLit w 0) = a. Admitted.
Lemma bvAdd_comm w a b : bvAdd w a b = bvAdd w b a. Admitted.
Lemma bvAdd_assoc w a b c : bvAdd w (bvAdd w a b) c = bvAdd w a (bvAdd w b c). Admitted.
