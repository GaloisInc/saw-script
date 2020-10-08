(***
 *** Lemmas about the bitvectors from SAWCoreVectorsAsCoqVectors
 ***)

From Coq Require Import Program.Basics.
From Coq Require Import Vectors.Vector.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

Import SAWCorePrelude.

Create HintDb SAWCoreBitvectors.


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
Hint Rewrite isBvsle_def isBvsle_def_opp : SAWCoreBitvectors.
Instance PreOrder_isBvsle w : PreOrder (isBvsle w). Admitted.

Definition isBvslt w a b : Prop := bvslt w a b = true.
Definition isBvslt_def w a b : bvslt w a b = true <-> isBvslt w a b := reflexivity _.
Definition isBvslt_def_opp w a b : bvsle w a b = false <-> isBvslt w b a. Admitted.
Hint Rewrite isBvslt_def isBvslt_def_opp : SAWCoreBitvectors.
Instance PreOrder_isBvslt w : PreOrder (isBvslt w). Admitted.

Definition isBvule w a b : Prop := bvule w a b = true.
Definition isBvule_def w a b : bvule w a b = true <-> isBvule w a b := reflexivity _.
Definition isBvule_def_opp w a b : bvult w a b = false <-> isBvule w b a. Admitted.
Hint Rewrite isBvule_def isBvule_def_opp : SAWCoreBitvectors.
Instance PreOrder_isBvule w : PreOrder (isBvule w). Admitted.

Definition isBvult w a b : Prop := bvult w a b = true.
Definition isBvult_def w a b : bvult w a b = true <-> isBvult w a b := reflexivity _.
Definition isBvult_def_opp w a b : bvule w a b = false <-> isBvult w b a. Admitted.
Hint Rewrite isBvult_def isBvult_def_opp : SAWCoreBitvectors.
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

Lemma bvEq_eq  w a b : bvEq w a b = true <-> a = b. Admitted.
Lemma bvEq_neq w a b : bvEq w a b = false <-> a <> b. Admitted.
Hint Rewrite bvEq_eq bvEq_neq : SAWCoreBitvectors.

Lemma bv_eq_if_true (b : bool) : (if b then bvLit 1 1 else bvLit 1 0) = bvLit 1 1 <-> b = true.
Proof. split; intro H; destruct b; reflexivity || inversion H. Qed.
Lemma bv_eq_if_false (b : bool) : (if b then bvLit 1 1 else bvLit 1 0) = bvLit 1 0 <-> b = false.
Proof. split; intro H; destruct b; reflexivity || inversion H. Qed.

Hint Rewrite bv_eq_if_true bv_eq_if_false : SAWCoreBitvectors.

Lemma bv_neq_if_true (b : bool) : (if b then bvLit 1 1 else bvLit 1 0) <> bvLit 1 1 <-> b = false.
Proof.
  split; intro H; destruct b; try reflexivity || inversion H.
  - pose (H0 := H (reflexivity _)); inversion H0.
  - intro H0; inversion H0.
Qed.

Lemma bv_neq_if_false (b : bool) : (if b then bvLit 1 1 else bvLit 1 0) <> bvLit 1 0 <-> b = true.
Proof.
  split; intro H; destruct b; try reflexivity || inversion H.
  - pose (H0 := H (reflexivity _)); inversion H0.
  - intro H0; inversion H0.
Qed.

Hint Rewrite bv_neq_if_true bv_neq_if_false : SAWCoreBitvectors.


(** Lemmas about bitvector addition **)

Lemma bvAdd_id_l w a : bvAdd w (bvLit w 0) a = a. Admitted.
Lemma bvAdd_id_r w a : bvAdd w a (bvLit w 0) = a. Admitted.
Lemma bvAdd_comm w a b : bvAdd w a b = bvAdd w b a. Admitted.
Lemma bvAdd_assoc w a b c : bvAdd w (bvAdd w a b) c = bvAdd w a (bvAdd w b c). Admitted.


(** Other rewriting hints not directly imvolving bitvectors **)

Lemma and_bool_eq_true_lemma (b c : bool) : and b c = true <-> (b = true) /\ (c = true).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.

Lemma and_bool_eq_false_lemma (b c : bool) : and b c = false <-> (b = false) \/ (c = false).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.

Hint Rewrite and_bool_eq_true_lemma and_bool_eq_false_lemma : SAWCoreBitvectors.

Lemma or_bool_eq_true_lemma (b c : bool) : or b c = true <-> (b = true) \/ (c = true).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.

Lemma or_bool_eq_false_lemma (b c : bool) : or b c = false <-> (b = false) /\ (c = false).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.

Hint Rewrite or_bool_eq_true_lemma or_bool_eq_false_lemma : SAWCoreBitvectors.

Lemma not_bool_eq_true_lemma (b : bool) : not b = true <-> b = false.
Proof. split; destruct b; auto. Qed.

Lemma not_bool_eq_false_lemma (b : bool) : not b = false <-> b = true.
Proof. split; destruct b; auto. Qed.

Hint Rewrite not_bool_eq_true_lemma not_bool_eq_false_lemma : SAWCoreBitvectors.

(* Lemma sym_bool_true_eq_lemma (b : bool) : true = b <-> b = true. *)
(* Proof. split; auto. Qed. *)

(* Lemma sym_bool_false_eq_lemma (b : bool) : false = b <-> b = false. *)
(* Proof. split; auto. Qed. *)

(* Hint Rewrite sym_bool_true_eq_lemma sym_bool_false_eq_lemma : SAWCoreBitvectors. *)
