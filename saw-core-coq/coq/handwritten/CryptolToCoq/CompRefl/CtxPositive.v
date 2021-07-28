
From Coq          Require Import Bool.
From Coq          Require Import Equalities.
From Coq          Require Import Logic.Eqdep.
From Coq          Require Import Program.Equality.
From Coq          Require Import PArith.BinPos.
From Coq          Require Import FSets.FMapInterface.
From Coq          Require Import FSets.FMapFacts.
From Coq          Require Import OrderedTypeEx.
From Coq          Require Import Logic.Eqdep_dec.
From Coq          Require Import Logic.EqdepFacts.
From Coq          Require Import Classes.RelationClasses.
From Coq          Require Import Classes.Morphisms.
From CryptolToCoq Require Import CompRefl.Utils.
From CryptolToCoq Require Import CompRefl.CtxInterface.

Import EqNotations.

Lemma lt_impl_pred {m n} : Pos.lt m n -> m = Pos.pred n \/ Pos.lt m (Pos.pred n).
Proof.
  destruct (Pos.succ_pred_or n); subst; intro.
  - apply Pos.nlt_1_r in H; destruct H.
  - rewrite <- H in H0.
    apply Pos.lt_succ_r, Pos.le_nlt in H0.
    destruct (Pos.lt_total m (Pos.pred n)) as [|[]]; tauto.
Qed.

Module PositiveCtx (type : UsualDecidableType)
                   (Map : Sfun PositiveOrderedTypeBits) <: Ctx type.

  Module MapFacts := WFacts_fun PositiveOrderedTypeBits Map.
  Module MapProps := WProperties_fun PositiveOrderedTypeBits Map.

  Definition MapForall {A} (ck : positive -> A -> bool) (m : Map.t A) : Prop :=
    MapProps.for_all ck m = true.

  Lemma MapForall_iff {A ck m} `{Proper _ (eq ==> eq ==> eq) ck} :
    @MapForall A ck m <-> (forall i x, Map.MapsTo i x m -> ck i x = true).
  Proof.
    unfold MapForall; apply MapProps.for_all_iff; eauto.
  Qed.

  Lemma MapForall_empty {A ck} `{Proper _ (eq ==> eq ==> eq) ck} :
    @MapForall A ck (Map.empty _).
  Proof.
    apply MapForall_iff; intros.
    apply Map.empty_1 in H0; easy.
  Qed.

  Lemma MapForall_add {A ck m i x} `{Proper _ (eq ==> eq ==> eq) ck} :
    ck i x = true -> MapForall ck m ->
    @MapForall A ck (Map.add i x m).
  Proof.
    intros; apply MapForall_iff; intros.
    rewrite MapForall_iff in H1.
    apply MapFacts.add_mapsto_iff in H2; destruct H2 as [[]|[]]; subst; eauto.
  Qed.

  Lemma MapForall_remove {A ck m i} `{Proper _ (eq ==> eq ==> eq) ck} :
    MapForall (fun i' x => Pos.eqb i i' || ck i' x) m ->
    @MapForall A ck (Map.remove i m).
  Proof.
    intros; apply MapForall_iff; intros.
    rewrite MapForall_iff in H0.
    apply MapFacts.remove_mapsto_iff in H1; destruct H1.
    specialize (H0 _ _ H2).
    apply orb_true_iff in H0; destruct H0; eauto.
    destruct H1; apply Pos.eqb_eq; eauto.
  Qed.

  Lemma MapForall_impl {A ck ck' m} `{Proper _ (eq ==> eq ==> eq) ck}
                                    `{Proper _ (eq ==> eq ==> eq) ck'} :
    (forall i a, ck i a = true -> ck' i a = true) ->
    @MapForall A ck m -> @MapForall A ck' m.
  Proof.
    intros; apply MapForall_iff; intros.
    rewrite MapForall_iff in H2.
    apply H1, H2; eauto.
  Qed.

  Definition name (_ : type.t) : Type := positive.

  Definition nameEq {t t'} : name t -> name t' -> bool := Pos.eqb.

  Definition tnameEq {t t'} (n : name t) (n' : name t') : bool :=
    match type.eq_dec t t' with
    | left _ => nameEq n n'
    | right _ => false
    end.

  Record t (F : type.t -> Type) : Type :=
    { max : positive;
      pmap : Map.t { t : type.t & option (F t) };
      ltPf : MapForall (fun n _ => Pos.ltb n max) pmap
    }.
  Arguments max {F}.
  Arguments pmap {F}.
  Arguments ltPf {F}.

  Definition ctx := t.

  Lemma ctx_eq {F} {c c' : ctx F} :
    c.(max) = c'.(max) -> c.(pmap) = c'.(pmap) -> c = c'.
  Proof.
    destruct c, c'; simpl; intros.
    destruct H, H0.
    assert (ltPf0 = ltPf1) by (apply UIP_dec; apply bool_dec).
    destruct H; reflexivity.
  Qed.

  Lemma ctx_eq_inv {F} {c c' : ctx F} :
    c = c' -> c.(max) = c'.(max) /\ c.(pmap) = c'.(pmap).
  Proof.
    destruct c, c'; intros; injection H; eauto.
  Qed.

  Section Operations.

    Context {F : type.t -> Type}.

    Definition isFresh {t} (n : name t) (c : ctx F) : bool :=
      negb (Map.mem n c.(pmap)).

    Definition find {t} (n : name t) (c : ctx F) : bool + F t :=
      match Map.find n c.(pmap) with
      | Some (existT t' (Some x)) => match type.eq_dec t t' with
                                     | left e => inr (eq_rect_r _ x e)
                                     | right _ => inl true
                                     end
      | Some _ => inl true
      | None => inl false
      end.

    Definition mem {t} (n : name t) (c : ctx F) : bool :=
      match find n c with
      | inr _ => true
      | inl _ => false
      end.

    Definition empty : ctx F := {| max := 1;
                                   pmap := Map.empty _;
                                   ltPf := MapForall_empty |}.

    Lemma extWith_ltPf {t} {n : name t} {x} {c : ctx F} :
      MapForall (fun n' _ => Pos.ltb n' (Pos.succ (Pos.max n c.(max))))
                (Map.add n x c.(pmap)).
    Proof.
      apply MapForall_add.
      - apply Pos.ltb_lt, Pos.lt_succ_r, Pos.le_max_l.
      - eapply MapForall_impl; [| exact c.(ltPf) ]; simpl; intros.
        apply Pos.ltb_lt in H; apply Pos.ltb_lt.
        apply Pos.lt_lt_succ, Pos.max_lt_iff; eauto.
    Qed.

    Definition extWith (c : ctx F) {t} (n : name t) (pf : isFresh n c = true) o : ctx F :=
      {| max := Pos.succ (Pos.max n c.(max));
         pmap := Map.add n (existT _ t o) c.(pmap);
         ltPf := extWith_ltPf |}.

    Lemma ext_ltPf {x} {c : ctx F} :
      MapForall (fun n' _ => Pos.ltb n' (Pos.succ c.(max)))
                (Map.add c.(max) x c.(pmap)).
    Proof.
      apply MapForall_add.
      - apply Pos.ltb_lt, Pos.lt_succ_r, Pos.le_refl.
      - eapply MapForall_impl; [| exact c.(ltPf) ]; simpl; intros.
        apply Pos.ltb_lt in H; apply Pos.ltb_lt.
        apply Pos.lt_lt_succ; eauto.
    Qed.

    Definition extCtx (c : ctx F) (t : type.t) o : ctx F :=
      {| max := Pos.succ c.(max);
         pmap := Map.add c.(max) (existT _ t o) c.(pmap);
         ltPf := ext_ltPf |}.

    Definition ext (c : ctx F) (t : type.t) o : name t * ctx F :=
      (c.(max), extCtx c t o).

    Lemma forget_ltPf1 {c : ctx F} :
      MapForall (fun n' _ => Pos.ltb n' (Pos.pred c.(max)))
                (Map.remove (Pos.pred c.(max)) c.(pmap)).
    Proof.
      eapply MapForall_remove.
      eapply MapForall_impl; [| exact c.(ltPf) ]; simpl; intros.
      apply orb_true_iff; rewrite Pos.ltb_lt, Pos.eqb_eq.
      apply Pos.ltb_lt, lt_impl_pred in H.
      destruct H; [ left | right ]; eauto.
    Qed.

    Lemma forget_ltPf2 {c : ctx F} {t} {n : name t} :
      MapForall (fun n' _ => Pos.ltb n' c.(max))
                (Map.remove n c.(pmap)).
    Proof.
      eapply MapForall_remove.
      eapply MapForall_impl; [| exact c.(ltPf) ]; simpl; intros.
      apply orb_true_iff.
      right; eauto.
    Qed.

    Definition forget (c : ctx F) {t} (n : name t) : ctx F :=
      match mem n c with
      | true =>
        match Pos.eqb n (Pos.pred c.(max)) with
        | true  => {| max := Pos.pred (c.(max));
                      pmap := Map.remove (Pos.pred c.(max)) c.(pmap);
                      ltPf := forget_ltPf1 |}
        | false => {| max := c.(max);
                      pmap := Map.remove n c.(pmap);
                      ltPf := forget_ltPf2 |}
        end
      | false => c
      end.

  End Operations.

  Section NameEqSpec.

    Lemma nameEq_refl {t1} {n1 : name t1} : nameEq n1 n1 = true.
    Proof. apply Pos.eqb_refl. Qed.

    Lemma nameEq_sym {t1 t2} {n1 : name t1} {n2 : name t2} :
      nameEq n1 n2 = nameEq n2 n1.
    Proof. apply Pos.eqb_sym. Qed.

    Lemma nameEq_trans {t1 t2 t3} {n1 : name t1} {n2 : name t2} {n3 : name t3} :
      nameEq n1 n2 = true -> nameEq n2 n3 = true -> nameEq n1 n3 = true.
    Proof. intro; rewrite (proj1 (Pos.eqb_eq _ _) H); eauto. Qed.

    Lemma nameEq_to_eq {t1} {n1 n1' : name t1} :
      nameEq n1 n1' = true -> n1 = n1'.
    Proof. apply Pos.eqb_eq. Qed.

    Lemma tnameEq_refl {t1} {n1 : name t1} : tnameEq n1 n1 = true.
    Proof.
      unfold tnameEq.
      destruct (type.eq_dec t1 t1); try easy.
      apply Pos.eqb_refl.
    Qed.

    Lemma tnameEq_sym {t1 t2} {n1 : name t1} {n2 : name t2} :
      tnameEq n1 n2 = tnameEq n2 n1.
    Proof.
      unfold tnameEq.
      destruct (type.eq_dec t1 t2), (type.eq_dec t2 t1); subst; try easy.
      apply Pos.eqb_sym.
    Qed.

    Lemma tnameEq_trans {t1 t2 t3} {n1 : name t1} {n2 : name t2} {n3 : name t3} :
      tnameEq n1 n2 = true -> tnameEq n2 n3 = true -> tnameEq n1 n3 = true.
    Proof.
      unfold tnameEq.
      destruct (type.eq_dec t1 t2), (type.eq_dec t2 t3), (type.eq_dec t1 t3); subst; try easy.
      repeat rewrite Pos.eqb_eq.
      intros; rewrite H; eauto.
    Qed.

    Lemma tnameEq_to_nameEq {t1 t2} {n1 : name t1} {n2 : name t2} :
      tnameEq n1 n2 = true -> nameEq n1 n2 = true.
    Proof.
      unfold tnameEq; destruct (type.eq_dec t1 t2); easy.
    Qed.

    Lemma tnameEq_to_teq {t1 t2} {n1 : name t1} {n2 : name t2} :
      tnameEq n1 n2 = true -> t1 = t2.
    Proof.
      unfold tnameEq; destruct (type.eq_dec t1 t2); easy.
    Qed.

  End NameEqSpec.

  Section Spec.

    Definition MapsTo {F t} (n : name t) x (c : ctx F) : Prop :=
      Map.MapsTo n (existT _ t (Some x)) c.(pmap).

    Definition HasValue {F t} (n : name t) (c : ctx F) := exists x, MapsTo n x c.

    Record Equiv {F G} (c : ctx F) (c' : ctx G) (P : forall {t}, F t -> G t -> Prop) : Prop := {
      equiv_HasValue : forall t (n : name t), HasValue n c <-> HasValue n c';
      equiv_isFresh  : forall t (n : name t), isFresh n c = true <-> isFresh n c' = true;
      equiv_vals : forall t (n : name t) x x', MapsTo n x c -> MapsTo n x' c' -> P x x' }.

    Definition SameShape {F G} (c : ctx F) (c' : ctx G) := Equiv c c' (fun _ _ _ => True).

    Lemma MapsTo_1 {F t1 t2 n1 n2} {x1 : F t1} {x2 : F t2} {c : ctx F} :
      forall (p : tnameEq n1 n2 = true),
        rew (tnameEq_to_teq p) in x1 = x2 ->
        MapsTo n1 x1 c -> MapsTo n2 x2 c.
    Proof.
      intros; unfold MapsTo, tnameEq in *.
      symmetry in H; eapply eq_dep1_intro in H;
        apply eq_dep1_dep in H; apply eq_dep_sym in H.
      destruct (eq_dep_eq1 H); apply eq_dep_eq in H.
      destruct (type.eq_dec t1 t1); [|contradiction].
      apply nameEq_to_eq in p.
      destruct p, H; eauto.
    Qed.

    Lemma isFresh_1 {F t1 t2} {n1 : name t1} {n2 : name t2} {c : ctx F} :
      nameEq n1 n2 = true -> isFresh n1 c = isFresh n2 c.
    Proof.
      intros; unfold isFresh, nameEq in *.
      apply Pos.eqb_eq in H.
      destruct H; reflexivity.
    Qed.

    Lemma isFresh_2 {F t1} {n1 : name t1} {c : ctx F} :
      HasValue n1 c -> isFresh n1 c = false.
    Proof.
      intros [?o ?]; unfold MapsTo, isFresh in *.
      apply negb_false_iff, MapFacts.mem_in_iff.
      eexists; eauto.
    Qed.

    Definition contra_isFresh_2 {F t1} {n1 : name t1} {c : ctx F} :
      isFresh n1 c = true -> ~ HasValue n1 c :=
      fun H1 H2 => eq_true_false_abs _ H1 (isFresh_2 H2).

    Lemma find_1 {F t1} {n1 : name t1} {x1} {c : ctx F} :
      MapsTo n1 x1 c -> find n1 c = inr x1.
    Proof.
      intros; unfold MapsTo, find in *.
      apply Map.find_1 in H; rewrite H.
      destruct (type.eq_dec t1 t1); [|contradiction].
      f_equal; symmetry.
      apply eq_rect_eq_dec; exact type.eq_dec.
    Qed.

    Lemma find_2 {F t1} {n1 : name t1} {x1} {c : ctx F} :
      find n1 c = inr x1 -> MapsTo n1 x1 c.
    Proof.
      intros; unfold MapsTo, find in *.
      apply Map.find_2.
      destruct (Map.find n1 c.(pmap)) as [[?t []]|]; try easy.
      destruct (type.eq_dec t1 t0); try easy.
      f_equal; apply eq_existT_uncurried.
      exists (symmetry e).
      destruct e; unfold eq_rect_r, eq_sym in H; simpl in *.
      injection H; intro; rewrite H0; reflexivity.
    Qed.

    Lemma find_3 {F t1} {n1 : name t1} {c : ctx F} :
      isFresh n1 c = true -> find n1 c = inl false.
    Proof.
      intro; unfold isFresh, find in *.
      apply negb_true_iff, MapFacts.not_mem_in_iff in H.
      apply MapFacts.not_find_in_iff in H.
      rewrite H; reflexivity.
    Qed.

    Lemma find_4 {F t1} {n1 : name t1} {c : ctx F} :
      find n1 c = inl false -> isFresh n1 c = true.
    Proof.
      intro; unfold isFresh, find in *.
      apply negb_true_iff, MapFacts.not_mem_in_iff.
      apply MapFacts.not_find_in_iff.
      destruct (Map.find n1 (pmap c)); eauto.
      destruct s, o; [ destruct (type.eq_dec t1 x) |].
      all: discriminate H.
    Qed.

    Lemma mem_1 {F t1} {n1 : name t1} {c : ctx F} :
      HasValue n1 c -> mem n1 c = true.
    Proof.
      intros []; unfold MapsTo, mem in *.
      apply find_1 in H; rewrite H; eauto.
    Qed.

    Lemma mem_2 {F t1} {n1 : name t1} {c : ctx F} :
      mem n1 c = true -> HasValue n1 c.
    Proof.
      intros; unfold MapsTo, mem in *.
      remember (find n1 c) as o; destruct o; [easy|].
      eexists; apply find_2; eauto.
    Qed.

    Lemma empty_1 {F t1} {n1 : name t1} : isFresh n1 (@empty F) = true.
    Proof.
      unfold isFresh, empty; simpl.
      apply negb_true_iff, MapFacts.not_mem_in_iff.
      destruct 1; eapply Map.empty_1; eauto. 
    Qed.

    Lemma extWith_1 {F t1} {n1 : name t1} {x1} {c : ctx F} {pf1} :
      MapsTo n1 x1 (extWith c n1 pf1 (Some x1)).
    Proof.
      unfold MapsTo, extWith in *; simpl in *.
      apply Map.add_1; reflexivity.
    Qed.

    Lemma extWith_2 {F t1 t2} {n1 : name t1} {n2 : name t2} {x2 o1} {c : ctx F} {pf1} :
      MapsTo n2 x2 c -> MapsTo n2 x2 (extWith c n1 pf1 o1).
    Proof.
      intros; assert (isFresh n2 c = false) by (apply isFresh_2; eexists; eauto).
      unfold isFresh, MapsTo, extWith in *; simpl in *.
      apply Map.add_2; eauto.
      destruct 1; rewrite pf1 in H0; discriminate H0.
    Qed.

    Lemma extWith_3 {F t1 t2} {n1 : name t1} {n2 : name t2} {x1 x2} {c : ctx F} {pf1} :
      MapsTo n2 x2 (extWith c n1 pf1 (Some x1)) -> tnameEq n1 n2 = true \/ MapsTo n2 x2 c.
    Proof.
      unfold MapsTo, extWith, tnameEq in *; simpl in *; intros.
      apply MapFacts.add_mapsto_iff in H.
      destruct H as [[]|[]]; [ left | right ]; eauto.
      destruct (type.eq_dec t1 t2).
      - apply Pos.eqb_eq; eauto.
      - apply False_ind, n, (projT1_eq H0).
    Qed.

    Lemma extWith_4 {F t1 t2} {n1 : name t1} {n2 : name t2} {x2} {c : ctx F} {pf1} :
      MapsTo n2 x2 (extWith c n1 pf1 None) -> MapsTo n2 x2 c.
    Proof.
      unfold MapsTo, extWith in *; simpl in *; intros.
      apply MapFacts.add_mapsto_iff in H.
      destruct H as [[]|[]]; eauto.
      discriminate H0.
    Qed.

    Lemma extWith_5 {F t1 t2} {n1 : name t1} {n2 : name t2} {o1} {c : ctx F} {pf1} :
      isFresh n2 c = true -> nameEq n1 n2 = true \/ isFresh n2 (extWith c n1 pf1 o1) = true.
    Proof.
      unfold isFresh, extWith in *; simpl in *; intro.
      apply negb_true_iff in pf1; apply negb_true_iff in H.
      (* repeat rewrite <- MapFacts.not_mem_in_iff in *. *)
      remember (Pos.eqb n1 n2); destruct b; [ left; eauto | right ].
      apply negb_true_iff; rewrite MapFacts.add_neq_b; eauto.
      apply Pos.eqb_neq; eauto.
    Qed.

    Lemma extWith_6 {F t1 t2} {n1 : name t1} {n2 : name t2} {o1} {c : ctx F} {pf1} :
      isFresh n2 (extWith c n1 pf1 o1) = true -> isFresh n2 c = true.
    Proof.
      unfold isFresh, extWith in *; simpl in *; intro.
      apply negb_true_iff in H; apply negb_true_iff.
      repeat rewrite <- MapFacts.not_mem_in_iff in *.
      intro; apply H; clear H.
      apply MapFacts.add_in_iff.
      right; eauto.
    Qed.

    Lemma forget_1 {F t1} {n1 : name t1} {c : ctx F} :
      ~ HasValue n1 (forget c n1).
    Proof.
      unfold HasValue, MapsTo, forget; destruct 1 as [o].
      remember (mem n1 c) as b; symmetry in Heqb; destruct b.
      1: remember (Pos.eqb n1 (Pos.pred c.(max))) as b0;
           symmetry in Heqb0; destruct b0; simpl in *.
      - apply Pos.eqb_eq in Heqb0; symmetry in Heqb0.
        eapply Map.remove_1; eauto.
        eexists; eauto.
      - eapply Map.remove_1; try reflexivity.
        eexists; eauto.
      - assert (mem n1 c = true) by (apply mem_1; econstructor; eauto).
        rewrite H0 in Heqb; discriminate Heqb.
    Qed.

    Lemma forget_2 {F t1 t2} {n1 : name t1} {n2 : name t2} {x2} {c : ctx F} :
      MapsTo n2 x2 (forget c n1) -> MapsTo n2 x2 c.
    Proof.
      unfold MapsTo, forget in *; intro.
      remember (mem n1 c) as b; symmetry in Heqb; destruct b; eauto.
      remember (Pos.eqb n1 (Pos.pred c.(max))) as b0;
        symmetry in Heqb0; destruct b0; simpl in *; eauto.
      all: apply Map.remove_3 in H; eauto.
    Qed.

    Lemma forget_3 {F t1 t2} {n1 : name t1} {n2 : name t2} {x2} {c : ctx F} :
      MapsTo n2 x2 c -> tnameEq n1 n2 = true \/ MapsTo n2 x2 (forget c n1).
    Proof.
      unfold MapsTo, forget, nameEq in *; intro.
      remember (mem n1 c) as b; symmetry in Heqb; destruct b; eauto.
      remember (tnameEq n1 n2) as b1;
        symmetry in Heqb1; destruct b1; simpl in *; eauto.
      eapply Map.remove_2 in H.
      - remember (Pos.eqb n1 (Pos.pred c.(max))) as b0;
          symmetry in Heqb0; destruct b0; simpl in *.
        + apply Pos.eqb_eq in Heqb0; destruct Heqb0; eauto.
        + eauto.
      - destruct 1; try destruct (proj1 (Pos.eqb_eq _ _) Heqb0).
        destruct (mem_2 Heqb); unfold MapsTo in *.
        apply Map.find_1 in H; apply Map.find_1 in H0.
        rewrite H0 in H; injection H; intros.
        destruct H2; rewrite tnameEq_refl in Heqb1.
        discriminate Heqb1.
    Qed.

    Lemma forget_4 {F t1} {n1 : name t1} {c : ctx F} :
      HasValue n1 c -> isFresh n1 (forget c n1) = true.
    Admitted.

    Lemma forget_5 {F t1 t2} {n1 : name t1} {n2 : name t2} {c : ctx F} :
      isFresh n2 (forget c n1) = true -> nameEq n1 n2 = true \/ isFresh n2 c = true.
    Admitted.

    Lemma forget_6 {F t1 t2} {n1 : name t1} {n2 : name t2} {c : ctx F} :
      isFresh n2 c = true -> isFresh n2 (forget c n1) = true.
    Admitted.

    Lemma ext_1 {F t1 x1} {c : ctx F} :
      MapsTo (fst (ext c t1 (Some x1))) x1 (snd (ext c t1 (Some x1))).
    Proof.
      intros; unfold MapsTo, ext in *; simpl in *.
      apply Map.add_1; reflexivity.
    Qed.

    Lemma ext_2 {F t1 t2} {n2 : name t2} {x2 o1} {c : ctx F} :
      MapsTo n2 x2 c -> MapsTo n2 x2 (snd (ext c t1 o1)).
    Proof.
      intro; unfold MapsTo, ext in *; simpl in *.
      apply Map.add_2; eauto.
      destruct c; simpl in *.
      rewrite MapForall_iff in ltPf0.
      specialize (ltPf0 _ _ H).
      apply Pos.ltb_lt, Pos.lt_nle in ltPf0.
      intro; apply ltPf0; rewrite H0; apply Pos.le_refl.
    Qed.

    Lemma ext_3 {F t1 t2} {n2 : name t2} {x1 x2} {c : ctx F} :
      MapsTo n2 x2 (snd (ext c t1 (Some x1))) ->
      tnameEq (fst (ext c t1 (Some x1))) n2 = true \/ MapsTo n2 x2 c.
    Proof.
      unfold MapsTo, ext, tnameEq in *; simpl in *; intros.
      apply MapFacts.add_mapsto_iff in H.
      destruct H as [[]|[]]; [ left | right ]; eauto.
      destruct (type.eq_dec t1 t2).
      - apply Pos.eqb_eq; eauto.
      - apply False_ind, n, (projT1_eq H0).
    Qed.

    Lemma ext_4 {F t1 t2} {n2 : name t2} {x2} {c : ctx F} :
      MapsTo n2 x2 (snd (ext c t1 None)) -> MapsTo n2 x2 c.
    Proof.
      unfold MapsTo, ext, nameEq in *; simpl in *; intros.
      apply MapFacts.add_mapsto_iff in H.
      destruct H as [[]|[]]; eauto.
      discriminate H0.
    Qed.

    Lemma ext_5 {F t1 o1} {c : ctx F} :
      isFresh (fst (ext c t1 o1)) c = true.
    Proof.
      unfold isFresh, ext; simpl.
      apply negb_true_iff, MapFacts.not_mem_in_iff.
      intros []; destruct c; simpl in *.
      rewrite MapForall_iff in ltPf0.
      specialize (ltPf0 max0 _ H).
      apply Pos.ltb_lt, Pos.le_nlt in ltPf0; eauto.
      apply Pos.le_refl.
    Qed.

    Lemma ext_6 {F t1 t2} {n2 : name t2} {x1 : F t1} {c : ctx F} :
      isFresh n2 c = true -> nameEq (fst (ext c t1 (Some x1))) n2 = true
                             \/ isFresh n2 (snd (ext c t1 (Some x1))) = true.
    Admitted.

    Lemma ext_7 {F t1 o1} {c : ctx F} {t2} {n2 : name t2} :
      isFresh n2 (snd (ext c t1 o1)) = true -> isFresh n2 c = true.
    Proof.
      unfold isFresh, extWith in *; simpl in *; intro.
      apply negb_true_iff in H; apply negb_true_iff.
      repeat rewrite <- MapFacts.not_mem_in_iff in *.
      intro; apply H; clear H.
      apply MapFacts.add_in_iff.
      right; eauto.
    Qed.

    Lemma ext_8 {F t1 o1} {c : ctx F} :
      snd (ext c t1 o1) = extWith c (fst (ext c t1 o1)) ext_5 o1.
    Proof.
      unfold ext, extWith; simpl.
      apply ctx_eq; eauto; simpl.
      rewrite Pos.max_l; [| apply Pos.le_refl ]; eauto.
    Qed.

    Lemma ext_9 {F G t1 o1 o1'} {c : ctx F} {c' : ctx G} :
      SameShape c c' -> nameEq (fst (ext c t1 o1)) (fst (ext c' t1 o1')) = true.
    Admitted.

    (* Lemma ext_8 {F t1 t2 x2 o1} {c : ctx F} : *)
    (*   fst (ext c t1 o1) = fst (ext (forget (snd (ext c t2 (Some x2))) (fst (ext c t2 (Some x2)))) t1 o1). *)
    (* Proof. *)
    (*   unfold forget. *)
    (*   remember (mem (fst (ext c t2 (Some x2))) (snd (ext c t2 (Some x2)))) as b; *)
    (*     symmetry in Heqb; destruct b; eauto. *)
    (*   1: remember (Pos.eqb (fst (ext c t2 (Some x2))) (Pos.pred (max (snd (ext c t2 (Some x2)))))) as b0; *)
    (*        symmetry in Heqb0; destruct b0; simpl in *; eauto; simpl. *)
    (*   - symmetry; apply Pos.pred_succ. *)
    (*   - elimtype False. *)
    (*     apply (proj1 (Pos.eqb_neq _ _) Heqb0). *)
    (*     symmetry; apply Pos.pred_succ. *)
    (*   - elimtype False. *)
    (*     assert (mem (fst (ext c t2 (Some x2))) (snd (ext c t2 (Some x2))) = true) *)
    (*       by (apply mem_1; eexists; apply ext_1). *)
    (*     rewrite H in Heqb; discriminate Heqb. *)
    (* Qed. *)

  End Spec.

  (* Section Map. *)

  (*   Context {F G : type.t -> Type}. *)

  (*   Lemma map_ltPf {f : forall t, option (F t) -> option (G t)} {c : ctx F} : *)
  (*     MapForall (fun n' _ => Pos.ltb n' c.(max)) *)
  (*                       (Map.map (fun '(existT _ t o) => existT _ t (f t o)) c.(pmap)). *)
  (*   Proof. *)
  (*     apply MapForall_iff; intros. *)
  (*     apply MapFacts.map_mapsto_iff in H; destruct H as [?x [?eq ?]]. *)
  (*     pose proof (proj1 MapForall_iff c.(ltPf)); eauto. *)
  (*   Qed. *)

  (*   Definition map (f : forall t, option (F t) -> option (G t)) (c : ctx F) : ctx G := *)
  (*     {| max := c.(max); *)
  (*        pmap := Map.map (fun '(existT _ t o) => existT _ t (f t o)) c.(pmap); *)
  (*        ltPf := map_ltPf |}. *)

  (*   Section MapSpec. *)

  (*     Lemma map_1 {t} {n : name t} {o} {f : forall t, option (F t) -> option (G t)} {c} : *)
  (*       MapsTo n o c -> MapsTo n (f t o) (map f c). *)
  (*     Admitted. *)

  (*     Lemma map_2 {t} {n : name t} {o'} {f : forall t, option (F t) -> option (G t)} {c} : *)
  (*       MapsTo n o' (map f c) -> exists o, f t o = o' /\ MapsTo n o c. *)
  (*     Admitted. *)

  (*   End MapSpec. *)

  (* End Map. *)

  Global Arguments name : simpl never.
  Global Arguments nameEq : simpl never.
  Global Arguments tnameEq : simpl never.
  Global Arguments ctx : simpl never.
  Global Arguments isFresh : simpl never.
  Global Arguments mem : simpl never.
  Global Arguments find : simpl never.
  Global Arguments empty : simpl never.
  Global Arguments extWith : simpl never.
  Global Arguments extCtx : simpl never.
  Global Arguments forget : simpl never.

End PositiveCtx.

Module PositiveMapCtx (type : UsualDecidableType) <: Ctx type.
  From Coq Require Import FSets.FMapPositive.
  Include (PositiveCtx type PositiveMap).
  Global Opaque isFresh empty extWith ext forget find mem.
End PositiveMapCtx.

Module PositiveListCtx (type : UsualDecidableType) <: Ctx type.
  From Coq Require Import FSets.FMapList.
  Module PositiveList := Make PositiveOrderedTypeBits.
  Include (PositiveCtx type PositiveList).
  Global Opaque isFresh empty extWith find mem.
End PositiveListCtx.
