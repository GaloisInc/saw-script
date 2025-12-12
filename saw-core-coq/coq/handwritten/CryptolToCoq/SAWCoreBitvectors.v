(***
 *** Lemmas about the bitvectors from SAWCoreVectorsAsCoqVectors
 ***)

From Stdlib Require Import Program.Basics.
From Stdlib Require        Program.Equality.
#[local] Set Warnings "-stdlib-vector".
From Stdlib Require Import Vectors.Vector.
#[local] Set Warnings "stdlib-vector".
From Stdlib Require Import Logic.Eqdep.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import ZArith.BinInt.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

Import SAWCorePrelude.
Import VectorNotations.

(* A duplicate from `Program.Equality`, because importing that
   module directly gives us a conflict with the `~=` notation... *)
Tactic Notation "dependent" "destruction" ident(H) :=
  Equality.do_depelim' ltac:(fun hyp => idtac) ltac:(fun hyp => Equality.do_case hyp) H.

(* like the `easy` tactic, but tries out branches *)
Ltac easy_branch :=
  match goal with
  | |- _ \/ _ => (left; easy_branch) || (right; easy_branch)
  | |- _ => easy
  end.

Create HintDb SAWCoreBitvectors_eqs.


(* Computing opaque bitvector functions *)

Ltac compute_bv_binrel_in_goal H f w1 w2 a b :=
  let e := eval vm_compute in (f w1 (intToBv w2 a) (intToBv w2 b)) in
  replace (f w1 (intToBv w2 a) (intToBv w2 b)) with e by reflexivity.
Ltac compute_bv_binrel_in H f w1 w2 a b :=
  let e := eval vm_compute in (f w1 (intToBv w2 a) (intToBv w2 b)) in
  replace (f w1 (intToBv w2 a) (intToBv w2 b)) with e in H by reflexivity.

Ltac compute_bv_binop_in_goal H f w1 w2 w3 a b :=
  let e := eval vm_compute in (sbvToInt w2 (f w1 (intToBv w2 a) (intToBv w2 b))) in
  try (replace (f w1 (intToBv w2 a) (intToBv w2 b)) with (intToBv w2 e) by reflexivity).
Ltac compute_bv_binop_in H f w1 w2 a b :=
  let e := eval vm_compute in (sbvToInt w2 (f w1 (intToBv w2 a) (intToBv w2 b))) in
  try (replace (f w1 (intToBv w2 a) (intToBv w2 b)) with (intToBv w2 e) in H by reflexivity).

Ltac compute_bv_unrel_in_goal H f w1 w2 a :=
  let e := eval vm_compute in (f w1 (intToBv w2 a)) in
  try (replace (f w1 (intToBv w2 a)) with e by reflexivity).
Ltac compute_bv_unrel_in H f w1 w2 a :=
  let e := eval vm_compute in (f w1 (intToBv w2 a)) in
  try (replace (f w1 (intToBv w2 a)) with e in H by reflexivity).

Ltac compute_bv_unop_in_goal H f w1 w2 a :=
  let e := eval vm_compute in (sbvToInt w2 (f w1 (intToBv w2 a))) in
  try (replace (f w1 (intToBv w2 a)) with (intToBv w2 e) by reflexivity).
Ltac compute_bv_unop_in H f w1 w2 a :=
  let e := eval vm_compute in (sbvToInt w2 (f w1 (intToBv w2 a))) in
  try (replace (f w1 (intToBv w2 a)) with (intToBv w2 e) in H by reflexivity).

Ltac compute_bv_funs_tac H t compute_bv_binrel compute_bv_binop
                             compute_bv_unrel compute_bv_unop :=
  match t with
  | context [?f ?w1 (intToBv ?w2 ?a) (intToBv ?w2 ?b)] =>
    match f with
    | bvsle => compute_bv_binrel H bvsle w1 w2 a b
    | bvslt => compute_bv_binrel H bvslt w1 w2 a b
    | bvule => compute_bv_binrel H bvule w1 w2 a b
    | bvult => compute_bv_binrel H bvult w1 w2 a b
    | bvEq  => compute_bv_binrel H bvEq w1 w2 a b
    | bvAdd => compute_bv_binop H bvAdd w1 w2 a b
    | bvSub => compute_bv_binop H bvSub w1 w2 a b
    | bvMul => compute_bv_binop H bvMul w1 w2 a b
    end
  | context [?f ?w1 (intToBv ?w2 ?a)] =>
    match f with
    | msb   => compute_bv_unrel H msb w1 w2 a
    | bvNeg => compute_bv_unop H bvNeg w1 w2 a
    end
  end.

Ltac unfold_bv_funs := unfold bvNat,
                              bvsge, bvsgt, bvuge, bvugt, bvSCarry, bvSBorrow,
                              xorb.

Tactic Notation "compute_bv_funs" :=
  unfold_bv_funs;
  repeat match goal with
         | |- ?t => let H := fresh "H" in
                    try (compute_bv_funs_tac H t compute_bv_binrel_in_goal compute_bv_binop_in_goal compute_bv_unrel_in_goal compute_bv_unop_in_goal)
         end.

Tactic Notation "compute_bv_funs" "in" ident(H) :=
  unfold_bv_funs;
  repeat match goal with
         | H': ?t |- _ => match H' with
                          | H => try (compute_bv_funs_tac H t compute_bv_binrel_in compute_bv_binop_in compute_bv_unrel_in compute_bv_unop_in)
                          end
         end.


(** Bitvector maximum and minimum values **)

Definition bvsmax w : bitvector w :=
  match w with
  | O => Vector.nil _
  | S w => Vector.cons _ false _ (gen w _ (fun _ => true))
  end.
Definition bvsmin w : bitvector w :=
  match w with
  | O => Vector.nil _
  | S w => Vector.cons _ true _ (gen w _ (fun _ => false))
  end.

Definition bvumax w : bitvector w := gen w _ (fun _ => true).
Definition bvumin w : bitvector w := gen w _ (fun _ => false).


(* FIXME For now, we say a bitvector lemma holds if it holds up to 3 or 4 bits.
         This is better than just having `Admitted`s for every lemma, but
         eventually this should be replaced with proper proofs. *)

Axiom holds_up_to_3 : forall (P : nat -> Prop),
                      P 0 -> P 1 -> P 2 -> P 3 ->
                      forall n, P n.

Axiom holds_up_to_4 : forall (P : nat -> Prop),
                      P 0 -> P 1 -> P 2 -> P 3 -> P 4 ->
                      forall n, P n.

(* A tactic which tries to prove that the current goal holds up to a certain
   number of bits (see `holds_for_bits_up_to_3` and `holds_for_bits_up_to_4`) *)
Ltac holds_for_bits_up_to n axiom :=
  repeat match goal with
         | H : _ |- _ => revert H
         end;
  match goal with
  | |- ?G =>
    compute;
    match goal with
    | |- forall w, @?P w =>
      idtac "Warning: Admitting the bitvector proposition below if it holds for" w "<=" n;
      idtac G;
      apply (axiom P); intros;
      (* completely destruct every bitvector argument, then try `easy` *)
      repeat match goal with
             | a : VectorDef.t bool _  |- _ => repeat dependent destruction a
             | b : bool |- _ => destruct b
             end; try easy_branch
    end
  end.

(* The tactics to use to "prove" a bitvector lemma by showing it holds up to
   either 3 or 4 bits. Use the latter when coming up with a lemma for some extra
   assurance, but use the former when finished for better performance. *)
Ltac holds_for_bits_up_to_3 := holds_for_bits_up_to 3 holds_up_to_3.
Ltac holds_for_bits_up_to_4 := holds_for_bits_up_to 4 holds_up_to_4.


(** Bitvector inquality propositions, and their preorders **)

Definition isBvsle w a b : Prop := bvsle w a b = true.
Definition isBvsle_def w a b : bvsle w a b = true <-> isBvsle w a b := reflexivity _.
Definition isBvsle_def_opp w a b : bvslt w a b = false <-> isBvsle w b a.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvslt w a b : Prop := bvslt w a b = true.
Definition isBvslt_def w a b : bvslt w a b = true <-> isBvslt w a b := reflexivity _.
Definition isBvslt_def_opp w a b : bvsle w a b = false <-> isBvslt w b a.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvule w a b : Prop := bvule w a b = true.
Definition isBvule_def w a b : bvule w a b = true <-> isBvule w a b := reflexivity _.
Definition isBvule_def_opp w a b : bvult w a b = false <-> isBvule w b a.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvult w a b : Prop := bvult w a b = true.
Definition isBvult_def w a b : bvult w a b = true <-> isBvult w a b := reflexivity _.
Definition isBvult_def_opp w a b : bvule w a b = false <-> isBvult w b a.
Proof. holds_for_bits_up_to_3. Qed.

Instance Reflexive_isBvsle w : Reflexive (isBvsle w).
Proof. holds_for_bits_up_to_3. Qed.

Instance Reflexive_isBvule w : Reflexive (isBvule w).
Proof. holds_for_bits_up_to_3. Qed.

Instance Transitive_isBvsle w : Transitive (isBvsle w).
Proof. holds_for_bits_up_to_3. Qed.

Instance Transitive_isBvslt w : Transitive (isBvslt w).
Proof. holds_for_bits_up_to_3. Qed.

Instance Transitive_isBvule w : Transitive (isBvule w).
Proof. holds_for_bits_up_to_3. Qed.

Instance Transitive_isBvult w : Transitive (isBvult w).
Proof. holds_for_bits_up_to_3. Qed.


(** Converting between bitvector inqualities **)

Definition isBvslt_to_isBvsle w a b : isBvslt w a b -> isBvsle w a b.
Proof. holds_for_bits_up_to_3. Qed.
Instance Proper_isBvslt_isBvsle w :
  Proper (isBvsle w --> isBvsle w ==> impl) (isBvslt w).
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvult_to_isBvule w a b : isBvult w a b -> isBvule w a b.
Proof. holds_for_bits_up_to_3. Qed.
Instance Proper_isBvult_isBvule w : Proper (isBvule w --> isBvule w ==> impl) (isBvult w).
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvule_to_isBvult_or_eq w a b : isBvule w a b -> isBvult w a b \/ a = b.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvslt_to_isBvsle_suc w a b : isBvslt w a b ->
                                          isBvsle w (bvAdd w a (intToBv w 1)) b.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvult_to_isBvule_suc w a b : isBvult w a b ->
                                          isBvule w (bvAdd w a (intToBv w 1)) b.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvult_to_isBvslt_pos w a b : isBvsle w (intToBv w 0) a ->
                                          isBvsle w (intToBv w 0) b ->
                                          isBvult w a b <-> isBvslt w a b.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvule_to_isBvsle_pos w a b : isBvsle w (intToBv w 0) a ->
                                          isBvsle w (intToBv w 0) b ->
                                          isBvule w a b <-> isBvsle w a b.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvslt_to_bvEq_false w a b : isBvslt w a b -> bvEq w a b = false.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvult_to_bvEq_false w a b : isBvult w a b -> bvEq w a b = false.
Proof. holds_for_bits_up_to_3. Qed.


(** Other lemmas about bitvector equalities **)

(** DEPRECATED: Use [bvNat_bvToNat] instead. *)
Definition bvNat_bvToNat_id w a : bvNat w (bvToNat w a) = a :=
  bvNat_bvToNat w a.


(** Other lemmas about bitvector inequalities **)

Definition not_isBvslt_bvsmin w a : ~ isBvslt w a (bvsmin w).
Proof. holds_for_bits_up_to_3. Qed.

Definition not_isBvslt_bvsmax w a : ~ isBvslt w (bvsmax w) a.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvslt_pred_l w a : isBvslt w (bvsmin w) a ->
                                isBvslt w (bvSub w a (intToBv w 1)) a.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvsle_pred_l w a : isBvslt w (bvsmin w) a ->
                                isBvsle w (bvSub w a (intToBv w 1)) a.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvsle_suc_r w a : isBvslt w a (bvsmax w) ->
                               isBvsle w a (bvAdd w a (intToBv w 1)).
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvslt_suc_r w a : isBvslt w a (bvsmax w) ->
                               isBvslt w a (bvAdd w a (intToBv w 1)).
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvslt_antirefl w a : ~ isBvslt w a a.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvule_zero_n w a : isBvule w (intToBv w 0) a.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvule_n_zero w a : isBvule w a (intToBv w 0) <-> a = intToBv w 0.
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvult_n_zero w a : ~ isBvult w a (intToBv w 0).
Proof. holds_for_bits_up_to_3. Qed.

Definition isBvsle_antisymm w a b : isBvsle w a b -> isBvsle w b a -> a = b.
Proof. holds_for_bits_up_to_3. Qed.


(** Lemmas about bitvector addition **)

Lemma bvAdd_id_l w a : bvAdd w (intToBv w 0) a = a.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvAdd_id_r w a : bvAdd w a (intToBv w 0) = a.
Proof. holds_for_bits_up_to_3. Qed.

Hint Rewrite bvAdd_id_l bvAdd_id_r : SAWCoreBitvectors_eqs.

Lemma bvAdd_comm w a b : bvAdd w a b = bvAdd w b a.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvAdd_assoc w a b c : bvAdd w (bvAdd w a b) c = bvAdd w a (bvAdd w b c).
Proof. holds_for_bits_up_to_3. Qed.


(** Lemmas about bitvector subtraction, negation, and sign bits **)

Lemma bvSub_n_zero w a : bvSub w a (intToBv w 0) = a.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvSub_zero_n w a : bvSub w (intToBv w 0) a = bvNeg w a.
Proof. holds_for_bits_up_to_3. Qed.

Hint Rewrite bvSub_zero_n : SAWCoreBitvectors_eqs.

Lemma msb_true_iff_bvslt w a :
  msb w a = true <-> isBvslt (Succ w) a (intToBv (Succ w) 0).
Proof. holds_for_bits_up_to_3. Qed.

Lemma msb_false_iff_bvsle w a :
  msb w a = false <-> isBvsle (Succ w) (intToBv (Succ w) 0) a.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvNeg_bvslt_zero_iff w a : isBvslt w (bvsmin w) a ->
  isBvslt w a (intToBv w 0) <-> isBvslt w (intToBv w 0) (bvNeg w a).
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvNeg_bvAdd_distrib w a b : bvNeg w (bvAdd w a b) = bvAdd w (bvNeg w a) (bvNeg w b).
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvslt_bvSub_l w a b : bvSubOverflow w a b = false ->
                            isBvslt w (bvSub w a b) (intToBv w 0) -> isBvslt w a b.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvslt_bvSub_r w a b : bvSubOverflow w b a = false ->
                            isBvslt w (intToBv w 0) (bvSub w b a) -> isBvslt w a b.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvEq_bvSub_r w a b : a = b <-> intToBv w 0 = bvSub w b a.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvEq_bvSub_l w a b : a = b <-> bvSub w a b = intToBv w 0.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvSub_eq_bvAdd_neg w a b : bvSub w a b = bvAdd w a (bvNeg w b).
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvule_to_bvslt_zero w a b : isBvule w a b ->
                                  isBvslt w a (intToBv w 0) ->
                                  isBvslt w b (intToBv w 0).
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvule_to_zero_bvsle w a b : isBvule w a b ->
                                  isBvsle w (intToBv w 0) b ->
                                  isBvsle w (intToBv w 0) a.
Proof. holds_for_bits_up_to_3. Qed.


(** Lemmas about bitvector xor **)

Lemma bvXor_same n x :
  SAWCorePrelude.bvXor n x x = SAWCorePrelude.replicate n bool false.
Proof.
  unfold SAWCorePrelude.bvXor, SAWCorePrelude.bvZipWith, SAWCorePrelude.zipWith, SAWCorePrelude.replicate.
  induction x; auto; simpl; f_equal; auto.
  rewrite SAWCorePrelude.xor_same; auto.
Qed.

Lemma bvXor_zero n x :
  SAWCorePrelude.bvXor n x (SAWCorePrelude.replicate n bool false) = x.
Proof.
  unfold SAWCorePrelude.bvXor, SAWCorePrelude.bvZipWith, SAWCorePrelude.zipWith, SAWCorePrelude.replicate.
  induction x; auto; simpl. f_equal; auto; cbn.
  rewrite SAWCorePrelude.xor_False2; auto.
Qed.

Lemma bvXor_assoc n x y z :
  SAWCorePrelude.bvXor n x (SAWCorePrelude.bvXor n y z) =
  SAWCorePrelude.bvXor n (SAWCorePrelude.bvXor n x y) z.
Proof.
  unfold SAWCorePrelude.bvXor, SAWCorePrelude.bvZipWith, SAWCorePrelude.zipWith.
  induction n; auto; simpl. f_equal; auto; cbn.
  rewrite Bool.xorb_assoc_reverse. reflexivity.
  remember (S n).
  destruct x; try solve [inversion Heqn0; clear Heqn0; subst]. injection Heqn0.
  destruct y; try solve [inversion Heqn0; clear Heqn0; subst]. injection Heqn0.
  destruct z; try solve [inversion Heqn0; clear Heqn0; subst]. injection Heqn0.
  intros. subst. clear Heqn0. cbn. apply IHn.
Qed.

Lemma bvXor_comm n x y :
  SAWCorePrelude.bvXor n x y = SAWCorePrelude.bvXor n y x.
Proof.
  unfold SAWCorePrelude.bvXor, SAWCorePrelude.bvZipWith, SAWCorePrelude.zipWith.
  induction n; auto; simpl. f_equal; auto; cbn.
  apply Bool.xorb_comm.
  remember (S n).
  destruct x; try solve [inversion Heqn0; clear Heqn0; subst]. injection Heqn0.
  destruct y; try solve [inversion Heqn0; clear Heqn0; subst]. injection Heqn0.
  intros. subst. clear Heqn0. cbn. apply IHn.
Qed.


(** Some general lemmas about boolean equality **)

Lemma boolEq_eq a b : boolEq a b = true <-> a = b.
Proof. split; destruct a, b; easy. Qed.

Lemma boolEq_neq a b : boolEq a b = false <-> a <> b.
Proof. split; destruct a, b; easy. Qed.

Lemma boolEq_refl a : boolEq a a = true.
Proof. destruct a; easy. Qed.

Lemma and_bool_eq_true b c : andb b c = true <-> (b = true) /\ (c = true).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.

Lemma and_bool_eq_false b c : andb b c = false <-> (b = false) \/ (c = false).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.

Lemma or_bool_eq_true b c : orb b c = true <-> (b = true) \/ (c = true).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.

Lemma or_bool_eq_false b c : orb b c = false <-> (b = false) /\ (c = false).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.

Lemma not_bool_eq_true b : negb b = true <-> b = false.
Proof. split; destruct b; auto. Qed.

Lemma not_bool_eq_false b : negb b = false <-> b = true.
Proof. split; destruct b; auto. Qed.


(** Lemmas about bitvector equality **)

Lemma bvEq_cons w h0 h1 a0 a1 :
  bvEq (S w) (VectorDef.cons _ h0 w a0) (VectorDef.cons _ h1 w a1) =
  andb (boolEq h0 h1) (bvEq w a0 a1).
Proof. reflexivity. Qed.

Lemma bvEq_refl w a : bvEq w a a = true.
Proof.
  induction a; eauto.
  rewrite bvEq_cons, boolEq_refl, IHa; eauto.
Qed.

Lemma bvEq_sym w a b : bvEq w a b = bvEq w b a.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvEq_eq  w a b : bvEq w a b = true <-> a = b.
Proof.
  split; intro; induction a; dependent destruction b; eauto.
  - rewrite bvEq_cons, and_bool_eq_true in H.
    destruct H; rewrite boolEq_eq in H; apply IHa in H0.
    subst; reflexivity.
  - injection H as; apply inj_pair2 in H0; subst.
    rewrite bvEq_cons, and_bool_eq_true; split.
    + apply boolEq_refl.
    + apply bvEq_refl.
Qed.

(* the other direction only holds if we assume LEM *)
Lemma bvEq_neq w a b : bvEq w a b = false -> a <> b.
Proof.
  intro; induction a; dependent destruction b; eauto.
  intro; injection H0 as; apply inj_pair2 in H1.
  rewrite bvEq_cons, and_bool_eq_false in H.
  destruct H; [ rewrite boolEq_neq in H | apply IHa in H ].
  all: contradiction.
Qed.


(** Proof automation - computing and rewriting bv funs **)

(* FIXME: update to include support for the new refinement automation whenever
that is defined... *)
(*
Hint Extern 1 (StartAutomation _) => progress compute_bv_funs: refinesFun.

Ltac FreshIntroArg_bv_eq T :=
  let e := fresh in
    IntroArg_intro e;
    compute_bv_funs in e;
    match T with
    | bool => (* try rewrite e; *)
              autorewrite with SAWCoreBitvectors_eqs in e;
              simpl in e; try fold true in e; try fold false in e
    end;
    apply (IntroArg_fold If _ _ e); clear e.

Hint Extern 1 (FreshIntroArg _ (@eq ?T _ _) _) =>
  progress (FreshIntroArg_bv_eq T) : refinesFun.


(** Proof automation - IntroArg rules **)

Lemma IntroArg_bvEq_eq n w a b goal :
  IntroArg n (a = b) (fun _ => goal) ->
  IntroArg n (SAWCorePrelude.bvEq w a b = true) (fun _ => goal).
Proof. intros H eq; apply H, bvEq_eq; eauto. Qed.
Lemma IntroArg_bvEq_neq n w a b goal :
  IntroArg n (a <> b) (fun _ => goal) ->
  IntroArg n (SAWCorePrelude.bvEq w a b = false) (fun _ => goal).
Proof. intros H eq; apply H, bvEq_neq; eauto. Qed.

(* Hint Extern 1 (IntroArg _ (SAWCorePrelude.bvEq _ _ _ = true) _) => *)
(*    simple apply IntroArg_bvEq_eq : refinesFun. *)
(* Hint Extern 1 (IntroArg _ (SAWCorePrelude.bvEq _ _ _ = false) _) => *)
(*    simple apply IntroArg_bvEq_neq : refinesFun. *)

Lemma IntroArg_bv_eq_if_true n (b : bool) goal :
  IntroArg n (b = true) (fun _ => goal) ->
  IntroArg n ((if b then intToBv 1 1 else intToBv 1 0) = intToBv 1 1) (fun _ => goal).
Proof. intros H eq; apply H; destruct b; easy. Qed.
Lemma IntroArg_bv_eq_if_false n (b : bool) goal :
  IntroArg n (b = false) (fun _ => goal) ->
  IntroArg n ((if b then intToBv 1 1 else intToBv 1 0) = intToBv 1 0) (fun _ => goal).
Proof. intros H eq; apply H; destruct b; easy. Qed.
Lemma IntroArg_bv_neq_if_true n (b : bool) goal :
  IntroArg n (b = false) (fun _ => goal) ->
  IntroArg n ((if b then intToBv 1 1 else intToBv 1 0) <> intToBv 1 1) (fun _ => goal).
Proof. intros H eq; apply H; destruct b; easy. Qed.
Lemma IntroArg_bv_neq_if_false n (b : bool) goal :
  IntroArg n (b = true) (fun _ => goal) ->
  IntroArg n ((if b then intToBv 1 1 else intToBv 1 0) <> intToBv 1 0) (fun _ => goal).
Proof. intros H eq; apply H; destruct b; easy. Qed.

(* Hint Extern 1 (IntroArg _ ((if _ then intToBv 1 (-1) else intToBv 1 0) = intToBv 1 1) _) => *)
(*    simple apply IntroArg_bv_eq_if_true : refinesFun. *)
(* Hint Extern 1 (IntroArg _ ((if _ then intToBv 1 (-1) else intToBv 1 0) = intToBv 1 0) _) => *)
(*    simple apply IntroArg_bv_eq_if_false : refinesFun. *)
(* Hint Extern 1 (IntroArg _ ((if _ then intToBv 1 (-1) else intToBv 1 0) <> intToBv 1 1) _) => *)
(*    simple apply IntroArg_bv_neq_if_true : refinesFun. *)
(* Hint Extern 1 (IntroArg _ ((if _ then intToBv 1 (-1) else intToBv 1 0) <> intToBv 1 0) _) => *)
(*    simple apply IntroArg_bv_neq_if_false : refinesFun. *)

Lemma IntroArg_and_bool_eq_true n (b c : bool) goal :
  IntroArg n (b = true) (fun _ => FreshIntroArg n (c = true) (fun _ => goal)) ->
  IntroArg n (andb b c = true) (fun _ => goal).
Proof.
  intros H eq; apply H; apply and_bool_eq_true in eq; destruct eq; eauto.
Qed.
Lemma IntroArg_and_bool_eq_false n (b c : bool) goal :
  IntroArg n (b = false) (fun _ => goal) ->
  IntroArg n (c = false) (fun _ => goal) ->
  IntroArg n (andb b c = false) (fun _ => goal).
Proof.
  intros Hl Hr eq; apply and_bool_eq_false in eq.
  destruct eq; [ apply Hl | apply Hr ]; eauto.
Qed.

(* Hint Extern 1 (IntroArg _ (and _ _ = true) _) => *)
(*    simple apply IntroArg_and_bool_eq_true : refinesFun. *)
(* Hint Extern 1 (IntroArg _ (and _ _ = false) _) => *)
(*    simple apply IntroArg_and_bool_eq_false : refinesFun. *)

Lemma IntroArg_or_bool_eq_true n (b c : bool) goal :
  IntroArg n (b = true) (fun _ => goal) ->
  IntroArg n (c = true) (fun _ => goal) ->
  IntroArg n (orb b c = true) (fun _ => goal).
Proof.
  intros Hl Hr eq; apply or_bool_eq_true in eq.
  destruct eq; [ apply Hl | apply Hr ]; eauto.
Qed.
Lemma IntroArg_or_bool_eq_false n (b c : bool) goal :
  IntroArg n (b = false) (fun _ => FreshIntroArg n (c = false) (fun _ => goal)) ->
  IntroArg n (orb b c = false) (fun _ => goal).
Proof.
  intros H eq; apply H; apply or_bool_eq_false in eq; destruct eq; eauto.
Qed.

(* Hint Extern 1 (IntroArg _ (or _ _ = true) _) => *)
(*    simple apply IntroArg_or_bool_eq_true : refinesFun. *)
(* Hint Extern 1 (IntroArg _ (or _ _ = false) _) => *)
(*    simple apply IntroArg_or_bool_eq_false : refinesFun. *)

Lemma IntroArg_not_bool_eq_true n (b : bool) goal :
  IntroArg n (b = false) (fun _ => goal) ->
  IntroArg n (negb b = true) (fun _ => goal).
Proof. intros H eq; apply H, not_bool_eq_true; eauto. Qed.
Lemma IntroArg_not_bool_eq_false n (b : bool) goal :
  IntroArg n (b = true) (fun _ => goal) ->
  IntroArg n (negb b = false) (fun _ => goal).
Proof. intros H eq; apply H, not_bool_eq_false; eauto. Qed.

(* Hint Extern 1 (IntroArg _ (not _ = true) _) => *)
(*    simple apply IntroArg_not_bool_eq_true : refinesFun. *)
(* Hint Extern 1 (IntroArg _ (not _ = false) _) => *)
(*    simple apply IntroArg_not_bool_eq_false : refinesFun. *)

Lemma IntroArg_boolEq_eq n a b goal :
  IntroArg n (a = b) (fun _ => goal) ->
  IntroArg n (boolEq a b = true) (fun _ => goal).
Proof. intros H eq; apply H, boolEq_eq; eauto. Qed.
Lemma IntroArg_boolEq_neq n a b goal :
  IntroArg n (a <> b) (fun _ => goal) ->
  IntroArg n (boolEq a b = false) (fun _ => goal).
Proof. intros H eq; apply H, boolEq_neq; eauto. Qed.

(* Hint Extern 1 (IntroArg _ (boolEq _ _ = true) _) => *)
(*    simple apply IntroArg_boolEq_eq : refinesFun. *)
(* Hint Extern 1 (IntroArg _ (boolEq _ _ = false) _) => *)
(*    simple apply IntroArg_boolEq_neq : refinesFun. *)

Lemma IntroArg_bool_eq_if_true n (b : bool) goal :
  IntroArg n (b = true) (fun _ => goal) ->
  IntroArg n ((if b then true else false) = true) (fun _ => goal).
Proof. intros H eq; apply H; destruct b; eauto. Qed.
Lemma IntroArg_bool_eq_if_false n (b : bool) goal :
  IntroArg n (b = false) (fun _ => goal) ->
  IntroArg n ((if b then true else false) = false) (fun _ => goal).
Proof. intros H eq; apply H; destruct b; eauto. Qed.
Lemma IntroArg_bool_eq_if_inv_true n (b : bool) goal :
  IntroArg n (b = false) (fun _ => goal) ->
  IntroArg n ((if b then false else true) = true) (fun _ => goal).
Proof. intros H eq; apply H; destruct b; eauto. Qed.
Lemma IntroArg_bool_eq_if_inv_false n (b : bool) goal :
  IntroArg n (b = true) (fun _ => goal) ->
  IntroArg n ((if b then false else true) = false) (fun _ => goal).
Proof. intros H eq; apply H; destruct b; eauto. Qed.

(* Hint Extern 1 (IntroArg _ ((if _ then true else false) = true) _) => *)
(*    simple apply IntroArg_bool_eq_if_true : refinesFun. *)
(* Hint Extern 1 (IntroArg _ ((if _ then true else false) = false) _) => *)
(*    simple apply IntroArg_bool_eq_if_false : refinesFun. *)
(* Hint Extern 1 (IntroArg _ ((if _ then false else true) = true) _) => *)
(*    simple apply IntroArg_bool_eq_if_inv_true : refinesFun. *)
(* Hint Extern 1 (IntroArg _ ((if _ then false else true) = false) _) => *)
(*    simple apply IntroArg_bool_eq_if_inv_false : refinesFun. *)

Hint Extern 1 (IntroArg _ (@eq bool ?x ?y) _) =>
  lazymatch y with
  | true => lazymatch x with
    | SAWCorePrelude.bvEq _ _ _ => simple apply IntroArg_bvEq_eq
    | andb _ _ => simple apply IntroArg_and_bool_eq_true
    | orb _ _ => simple apply IntroArg_or_bool_eq_true
    | negb _ => simple apply IntroArg_not_bool_eq_true
    | boolEq _ _ => simple apply IntroArg_boolEq_eq
    | if _ then true   else false  => simple apply IntroArg_bool_eq_if_true
    | if _ then 1%bool else 0%bool => simple apply IntroArg_bool_eq_if_true
    | if _ then false  else true   => simple apply IntroArg_bool_eq_if_inv_true
    | if _ then 0%bool else 1%bool => simple apply IntroArg_bool_eq_if_inv_true
    end
  | false => lazymatch x with
    | SAWCorePrelude.bvEq _ _ _ => simple apply IntroArg_bvEq_neq
    | andb _ _ => simple apply IntroArg_and_bool_eq_false
    | orb _ _ => simple apply IntroArg_or_bool_eq_false
    | negb _ => simple apply IntroArg_not_bool_eq_false
    | boolEq _ _ => simple apply IntroArg_boolEq_neq
    | if _ then true   else false  => simple apply IntroArg_bool_eq_if_false
    | if _ then 1%bool else 0%bool => simple apply IntroArg_bool_eq_if_false
    | if _ then false  else true   => simple apply IntroArg_bool_eq_if_inv_false
    | if _ then 0%bool else 1%bool => simple apply IntroArg_bool_eq_if_inv_false
    end
  end : refinesFun.

Hint Extern 1 (IntroArg _ (@eq (bitvector _) ?x ?y) _) =>
  lazymatch constr:(x = y) with
  | (if _ then intToBv 1 (-1) else intToBv 1 0) = intToBv 1 1 => simple apply IntroArg_bv_eq_if_true
  | (if _ then intToBv 1 (-1) else intToBv 1 0) = intToBv 1 0 => simple apply IntroArg_bv_eq_if_false
  end : refinesFun.

Hint Extern 1 (IntroArg _ (~ (@eq (bitvector _) ?x ?y)) _) =>
  lazymatch constr:(x <> y) with
  | (if _ then intToBv 1 (-1) else intToBv 1 0) <> intToBv 1 1 => simple apply IntroArg_bv_neq_if_true
  | (if _ then intToBv 1 (-1) else intToBv 1 0) <> intToBv 1 0 => simple apply IntroArg_bv_neq_if_false
  end : refinesFun.

(* these show up as the unfolded versions of `bvultWithProof` and `bvuleWithProof` *)
Lemma IntroArg_iteDep_Maybe_Eq_true n t f x (goal : Prop)
  : IntroArg n (t = x) (fun _ => goal) ->
    IntroArg n (iteDep (fun b => Maybe (b = true)) true t f = x) (fun _ => goal).
Proof. intros H eq; apply H; eauto. Qed.
Lemma IntroArg_iteDep_Maybe_Eq_false n t f x (goal : Prop)
  : IntroArg n (f = x) (fun _ => goal) ->
    IntroArg n (iteDep (fun b => Maybe (b = true)) false t f = x) (fun _ => goal).
Proof. intros H eq; apply H; eauto. Qed.

Hint Extern 1 (IntroArg _ (iteDep (fun _ => Maybe (Eq _ _ _)) true _ _ = _) _) =>
   simple apply IntroArg_iteDep_Maybe_Eq_true : refinesFun.
Hint Extern 1 (IntroArg _ (iteDep (fun _ => Maybe (Eq _ _ _)) false _ _ = _) _) =>
   simple apply IntroArg_iteDep_Maybe_Eq_false : refinesFun.

Lemma IntroArg_isBvsle_def n w a b goal
  : IntroArg n (isBvsle w a b) (fun _ => goal) ->
    IntroArg n (bvsle w a b = true) (fun _ => goal).
Proof. intros H eq; apply H, isBvsle_def; eauto. Qed.
Lemma IntroArg_isBvsle_def_opp n w a b goal
  : IntroArg n (isBvsle w b a) (fun _ => goal) ->
    IntroArg n (bvslt w a b = false) (fun _ => goal).
Proof. intros H eq; apply H, isBvsle_def_opp; eauto. Qed.

(* Hint Extern 3 (IntroArg _ (bvsle _ _ _ = true) _) => *)
(*    simple apply IntroArg_isBvsle_def : refinesFun. *)
(* Hint Extern 3 (IntroArg _ (bvslt _ _ _ = false) _) => *)
(*    simple apply IntroArg_isBvsle_def_opp : refinesFun. *)

Lemma IntroArg_isBvslt_def n w a b goal
  : IntroArg n (isBvslt w a b) (fun _ => goal) ->
    IntroArg n (bvslt w a b = true) (fun _ => goal).
Proof. intros H eq; apply H, isBvslt_def; eauto. Qed.
Lemma IntroArg_isBvslt_def_opp n w a b goal
  : IntroArg n (isBvslt w b a) (fun _ => goal) ->
    IntroArg n (bvsle w a b = false) (fun _ => goal).
Proof. intros H eq; apply H, isBvslt_def_opp; eauto. Qed.

(* Hint Extern 3 (IntroArg _ (bvslt  _ _ = true) _) => *)
(*    simple apply IntroArg_isBvslt_def : refinesFun. *)
(* Hint Extern 3 (IntroArg _ (bvsle _ _ _ = false) _) => *)
(*    simple apply IntroArg_isBvslt_def_opp : refinesFun. *)

Lemma IntroArg_isBvule_def n w a b goal
  : IntroArg n (isBvule w a b) (fun _ => goal) ->
    IntroArg n (bvule w a b = true) (fun _ => goal).
Proof. intros H eq; apply H, isBvule_def; eauto. Qed.
Lemma IntroArg_isBvule_def_opp n w a b goal
  : IntroArg n (isBvule w b a) (fun _ => goal) ->
    IntroArg n (bvult w a b = false) (fun _ => goal).
Proof. intros H eq; apply H, isBvule_def_opp; eauto. Qed.

(* Hint Extern 3 (IntroArg _ (bvule _ _ _ = true) _) => *)
(*    simple apply IntroArg_isBvule_def : refinesFun. *)
(* Hint Extern 3 (IntroArg _ (bvult _ _ _ = false) _) => *)
(*    simple apply IntroArg_isBvule_def_opp : refinesFun. *)

Lemma IntroArg_isBvult_def n w a b goal
  : IntroArg n (isBvult w a b) (fun _ => goal) ->
    IntroArg n (bvult w a b = true) (fun _ => goal).
Proof. intros H eq; apply H, isBvult_def; eauto. Qed.
Lemma IntroArg_isBvult_def_opp n w a b goal
  : IntroArg n (isBvult w b a) (fun _ => goal) ->
    IntroArg n (bvule w a b = false) (fun _ => goal).
Proof. intros H eq; apply H, isBvult_def_opp; eauto. Qed.

(* Hint Extern 3 (IntroArg _ (bvult _ _ _ = true) _) => *)
(*    simple apply IntroArg_isBvult_def : refinesFun. *)
(* Hint Extern 3 (IntroArg _ (bvule _ _ _ = false) _) => *)
(*    simple apply IntroArg_isBvult_def_opp : refinesFun. *)

Lemma IntroArg_msb_true_iff_bvslt n w a goal :
  IntroArg n (isBvslt (Succ w) a (intToBv (Succ w) 0)) (fun _ => goal) ->
  IntroArg n (msb w a = true) (fun _ => goal).
Proof. intros H eq; rewrite msb_true_iff_bvslt in eq; eauto. Qed.

Lemma IntroArg_msb_false_iff_bvsle n w a goal :
  IntroArg n (isBvsle (Succ w) (intToBv (Succ w) 0) a) (fun _ => goal) ->
  IntroArg n (msb w a = false) (fun _ => goal).
Proof. intros H eq; rewrite msb_false_iff_bvsle in eq; eauto. Qed.

(* Hint Extern 3 (IntroArg _ (msb _ _ = true) _) => *)
(*    simple apply IntroArg_msb_true_iff_bvslt : refinesFun. *)
(* Hint Extern 3 (IntroArg _ (msb _ _ = false) _) => *)
(*    simple apply IntroArg_msb_false_iff_bvsle : refinesFun. *)

Hint Extern 3 (IntroArg _ (@eq bool ?x ?y) _) =>
  lazymatch y with
  | true => lazymatch x with
    | bvsle _ _ _ => simple apply IntroArg_isBvsle_def
    | bvslt _ _ _ => simple apply IntroArg_isBvslt_def
    | bvule _ _ _ => simple apply IntroArg_isBvule_def
    | bvult _ _ _ => simple apply IntroArg_isBvult_def
    | msb _ _ => simple apply IntroArg_msb_true_iff_bvslt
    end
  | false => lazymatch x with
    | bvsle _ _ _ => simple apply IntroArg_isBvslt_def_opp
    | bvslt _ _ _ => simple apply IntroArg_isBvsle_def_opp
    | bvule _ _ _ => simple apply IntroArg_isBvult_def_opp
    | bvult _ _ _ => simple apply IntroArg_isBvule_def_opp
    | msb _ _ => simple apply IntroArg_msb_false_iff_bvsle
    end
  end : refinesFun.
*)


(* Tactics for solving bitvector inequalities *)

(* FIXME: these axioms should be easy to prove... *)

(* 0 <= x for any x *)
Axiom bvule_zero_any : forall n x, bvule n (intToBv n 0) x = true.

(* x = y implies x <= y *)
Axiom eq_implies_bvule : forall n x y, x = y -> bvule n x y = true.

Ltac solveUnsafeAssertBVULt := reflexivity.
Ltac solveUnsafeAssertBVULe :=
  try reflexivity; try (apply bvule_zero_any);
  try (apply eq_implies_bvule; reflexivity).
