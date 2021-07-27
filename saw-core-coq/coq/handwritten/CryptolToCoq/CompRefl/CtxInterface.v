
From Coq          Require Import Lists.List.
From Coq          Require Import Bool.Bool.
From Coq          Require Import Equalities.
From CryptolToCoq Require Import CompRefl.Utils.

Import EqNotations.

Module Type Ctx (type : UsualDecidableType).

  Parameter name : type.t -> Type.
  (** the abstract type of names *)

  Parameter nameEq : forall {t t'}, name t -> name t' -> bool.
  (** decidable equality of names, independent of their types *)

  Parameter tnameEq : forall {t t'}, name t -> name t' -> bool.
  (** decidable equality of names with types *)

  Parameter ctx : (type.t -> Type) -> Type.
  (** the abstract type of contexts *)

  Section Operations.

    Context {F : type.t -> Type}.

    Parameter isFresh : forall {t}, name t -> ctx F -> bool.
    (** Decide whether a name is fresh in a context, independent of the given type. *)

    Parameter mem : forall {t}, name t -> ctx F -> bool.
    (** Check whether a name with a given type has a value in a context. *)

    Parameter find : forall {t}, name t -> ctx F -> bool + F t.
    (** Try to find the value of a name with a given type in a context. Returns
        `inr x` if the name with the given type has the value `x` in the given
        context, `inl false` if the name (independent of the given type) is
        fresh in the given context, or `inl true` otherwise.  *)

    Parameter empty : ctx F.
    (** The empty context. *)

    Parameter extWith : forall (c : ctx F) {t} (n : name t), isFresh n c = true -> option (F t) -> ctx F.
    (** Extend a context with a given fresh name. *)

    Parameter ext : ctx F -> forall (t : type.t), option (F t) -> name t * ctx F.
    (** Extend a context with an automatically generated fresh name, returning the new name. *)

    Parameter forget : ctx F -> forall {t}, name t -> ctx F.
    (** Forget a name in a context, the inverse of extWith/ext. *)

  End Operations.

  Section NameEqSpec.
    Set Implicit Arguments.
    Unset Strict Implicit.

    Variable t1 t2 t3 : type.t.
    Variable n1 n1' : name t1.
    Variable n2 : name t2.
    Variable n3 : name t3.

    Parameter nameEq_refl : nameEq n1 n1 = true.
    Parameter nameEq_sym : nameEq n1 n2 = nameEq n2 n1.
    Parameter nameEq_trans : nameEq n1 n2 = true -> nameEq n2 n3 = true -> nameEq n1 n3 = true.
    Parameter nameEq_to_eq : nameEq n1 n1' = true -> n1 = n1'.

    Parameter tnameEq_refl : tnameEq n1 n1 = true.
    Parameter tnameEq_sym : tnameEq n1 n2 = tnameEq n2 n1.
    Parameter tnameEq_trans : tnameEq n1 n2 = true -> tnameEq n2 n3 = true -> tnameEq n1 n3 = true.
    Parameter tnameEq_to_nameEq : tnameEq n1 n2 = true -> nameEq n1 n2 = true.
    Parameter tnameEq_to_teq : tnameEq n1 n2 = true -> t1 = t2.

  End NameEqSpec.

  Section Spec.
    Set Implicit Arguments.
    Unset Strict Implicit.

    Variable F G : type.t -> Type.
    Variable t1 t2 : type.t.
    Variable n1 : name t1.
    Variable n2 : name t2.
    Variable x1 x1' : F t1.
    Variable x2 : F t2.
    Variable o1 : option (F t1).
    Variable o1' : option (G t1).
    Variable c : ctx F.
    Variable c' : ctx G.
    Variable pf1 : isFresh n1 c = true.

    Parameter MapsTo : forall {F t}, name t -> F t -> ctx F -> Prop.
    (** The proposition that a name with a given type has a given value in a context. *)

    Definition HasValue {F t} (n : name t) (c : ctx F) := exists x, MapsTo n x c.
    (** The proposition that a name with a given type has some value in a context. *)

    Record Equiv (P : forall {t}, F t -> G t -> Prop) : Prop := {
      equiv_HasValue : forall t (n : name t), HasValue n c <-> HasValue n c';
      equiv_isFresh  : forall t (n : name t), isFresh n c = true <-> isFresh n c' = true;
      equiv_vals : forall t (n : name t) x x', MapsTo n x c -> MapsTo n x' c' -> P x x' }.
    (** Equivalence of contexts w.r.t. some predicate. *)

    Definition SameShape := Equiv (fun _ _ _ => True).
    (** The proposition that two contexts have the same shape. *)

    (** Specification of [MapsTo] *)
    Parameter MapsTo_1 : forall (p : tnameEq n1 n2 = true),
                           rew (tnameEq_to_teq p) in x1 = x2 ->
                           MapsTo n1 x1 c -> MapsTo n2 x2 c.

    (** Specification of [isFresh] *)
    Parameter isFresh_1 : nameEq n1 n2 = true -> isFresh n1 c = isFresh n2 c.
    Parameter isFresh_2 : HasValue n1 c -> isFresh n1 c = false.
    Definition contra_isFresh_2 : isFresh n1 c = true -> ~ HasValue n1 c :=
      fun H1 H2 => eq_true_false_abs _ H1 (isFresh_2 H2).

    (** Specification of [mem] *)
    Parameter mem_1 : HasValue n1 c -> mem n1 c = true.
    Parameter mem_2 : mem n1 c = true -> HasValue n1 c.

    (** Specification of [find] *)
    Parameter find_1 : MapsTo n1 x1 c -> find n1 c = inr x1.
    Parameter find_2 : find n1 c = inr x1 -> MapsTo n1 x1 c.
    Parameter find_3 : isFresh n1 c = true -> find n1 c = inl false.
    Parameter find_4 : find n1 c = inl false -> isFresh n1 c = true.

    (** Specification of [empty] *)
    Parameter empty_1 : isFresh n1 (@empty F) = true.

    (** Specification of [extWith] *)
    Parameter extWith_1 : MapsTo n1 x1 (extWith c n1 pf1 (Some x1)).
    Parameter extWith_2 : MapsTo n2 x2 c -> MapsTo n2 x2 (extWith c n1 pf1 o1).
    Parameter extWith_3 : MapsTo n2 x2 (extWith c n1 pf1 (Some x1)) -> tnameEq n1 n2 = true \/ MapsTo n2 x2 c.
    Parameter extWith_4 : MapsTo n2 x2 (extWith c n1 pf1 None) -> MapsTo n2 x2 c.
    Parameter extWith_5 : isFresh n2 c = true -> nameEq n1 n2 = true \/ isFresh n2 (extWith c n1 pf1 o1) = true.
    Parameter extWith_6 : isFresh n2 (extWith c n1 pf1 o1) = true -> isFresh n2 c = true.

    (** Specification of [forget] *)
    Parameter forget_1 : ~ HasValue n1 (forget c n1).
    Parameter forget_2 : MapsTo n2 x2 (forget c n1) -> MapsTo n2 x2 c.
    Parameter forget_3 : MapsTo n2 x2 c -> tnameEq n1 n2 = true \/ MapsTo n2 x2 (forget c n1).
    Parameter forget_4 : HasValue n1 c -> isFresh n1 (forget c n1) = true.
    Parameter forget_5 : isFresh n2 (forget c n1) = true -> nameEq n1 n2 = true \/ isFresh n2 c = true.
    Parameter forget_6 : isFresh n2 c = true -> isFresh n2 (forget c n1) = true.

    (** Specification of [ext] *)
    Parameter ext_1 : MapsTo (fst (ext c t1 (Some x1))) x1 (snd (ext c t1 (Some x1))).
    Parameter ext_2 : MapsTo n2 x2 c -> MapsTo n2 x2 (snd (ext c t1 o1)).
    Parameter ext_3 : MapsTo n2 x2 (snd (ext c t1 (Some x1))) ->
                      tnameEq (fst (ext c t1 (Some x1))) n2 = true \/ MapsTo n2 x2 c.
    Parameter ext_4 : MapsTo n2 x2 (snd (ext c t1 None)) -> MapsTo n2 x2 c.
    Parameter ext_5 : isFresh (fst (ext c t1 o1)) c = true.
    Parameter ext_6 : isFresh n2 c = true -> nameEq (fst (ext c t1 (Some x1))) n2 = true
                                             \/ isFresh n2 (snd (ext c t1 (Some x1))) = true.
    Parameter ext_7 : forall {t2} {n2 : name t2},
                      isFresh n2 (snd (ext c t1 o1)) = true -> isFresh n2 c = true.
    Parameter ext_8 : snd (ext c t1 o1) = extWith c (fst (ext c t1 o1)) ext_5 o1.
    Parameter ext_9 : SameShape -> nameEq (fst (ext c t1 o1)) (fst (ext c' t1 o1')) = true.

  End Spec.

End Ctx.

Module CtxExtras (type : UsualDecidableType) (C : Ctx type).
  Open Scope type_scope.
  Import ListNotations.
  Import C.

  Definition tnameEq_to_eq {t1} {n1 n1' : name t1} :
    tnameEq n1 n1' = true -> n1 = n1' :=
    fun p => nameEq_to_eq (tnameEq_to_nameEq p).

  Lemma nameEq_to_tnameEq {t1} {n1 n1' : name t1} :
    nameEq n1 n1' = true -> tnameEq n1 n1' = true.
  Proof.
    intro; apply nameEq_to_eq in H.
    destruct H; apply tnameEq_refl.
  Qed.

  (** Specification of [HasValue] *)
  Definition HasValue_1 {F t1 t2} {n1 : name t1} {n2 : name t2} {c : ctx F} :
    tnameEq n1 n2 = true -> HasValue n1 c -> HasValue n2 c :=
    fun p '(ex_intro _ x1 H) => ex_intro _ (rew (tnameEq_to_teq p) in x1)
                                           (MapsTo_1 eq_refl H).

  (** Properties of [MapsTo] *)
  Lemma MapsTo_fun {F t1 n1} {x1 x1' : F t1} {c} :
    MapsTo n1 x1 c -> MapsTo n1 x1' c -> x1 = x1'.
  Proof.
    intros; apply find_1 in H.
    rewrite (find_1 H0) in H.
    injection H; eauto.
  Qed.



  (** ** Additional functions for adding to a context *)

  Definition addWith {F} (c : ctx F) {t} (n : name t) (pf : isFresh n c = true) (x : F t) : ctx F :=
    extWith c n pf (Some x).
  (** Add a value to a context with a given fresh name. *)
  Hint Transparent addWith : core.
  Hint Unfold addWith : core.

  Definition add {F} (c : ctx F) {t} (x : F t) : name t * ctx F :=
    ext c t (Some x).
  (** Add a value to a context with an automatically generated fresh name, returning the new name. *)
  Hint Transparent add : core.
  Hint Unfold add : core.

  Definition fresh {F} (c : ctx F) (t : type.t) : name t * ctx F :=
    ext c t None.
  (** Generate a fresh name, returning the updated context. *)
  Hint Transparent fresh : core.
  Hint Unfold fresh : core.

  Definition inExt {F B} (c : ctx F) {t} (g : name t -> ctx F -> B) (f : F t) : B :=
    g (fst (add c f)) (snd (add c f)).
  (** Continuation in an extended context (using [add]) *)

  Definition withFreshName {F B} (c : ctx F) {t} (g : name t -> ctx F -> B) : B :=
    g (fst (fresh c t)) (snd (fresh c t)).
  (** Continuation with a fresh name (using [fresh]) *)


  (** ** Pure and assignment contexts *)

  Definition pctx := ctx (fun _ => unit).
  (** A pure context, i.e. a context with no values for names. *)

  Definition pext (p : pctx) (t : type.t) := add p (t:=t) tt.
  (** Extend a pure context. *)

  Record actx (p : pctx) F :=
    { innerCtx : ctx F; actxPf : SameShape p innerCtx }.
  (** A context which assigns a value to all the names in a pure context. *)
  Arguments innerCtx {p F}.
  Arguments actxPf {p F}.

  Lemma actx_empty_pf {F} : SameShape (@empty (fun _ => unit)) (@empty F).
  Proof.
    split; intros; eauto.
    - split; intro; apply isFresh_2 in H; rewrite empty_1 in H; discriminate H.
    - do 2 rewrite empty_1; tauto.
  Qed.

  Definition actx_empty {F} : actx empty F :=
    {| innerCtx := empty; actxPf := actx_empty_pf |}.
  (** An empty assignment context. *)

  Definition actx_tail_pf {p : pctx} {F t} {c : ctx F} :
    SameShape (snd (pext p t)) c -> SameShape p (forget c (fst (pext p t))).
  Proof.
    intro; destruct H as [?H ?H ?H]; clear H1;
      split; split; intro.
    - assert (HasValue n (snd (pext p t)))
        by (destruct H1; eapply ext_2 in H1; eexists; eauto).
      apply H in H2; destruct H2.
      eapply forget_3 in H2; destruct H2; [| eexists; eauto ].
      eapply HasValue_1; eauto.
      eapply HasValue_1 in H1; [| rewrite tnameEq_sym ]; eauto.
      apply isFresh_2 in H1.
      unfold pext, add in H1; erewrite ext_5 in H1.
      discriminate H1.
    - assert (HasValue n c)
        by (destruct H1; eapply forget_2 in H1; eexists; eauto).
      apply H in H2; destruct H2 as [[]].
      eapply ext_3 in H2; destruct H2; [| eexists; eauto ].
      eapply HasValue_1; eauto.
      eapply HasValue_1 in H1; [| rewrite tnameEq_sym ]; eauto.
      apply isFresh_2 in H1.
      erewrite forget_4 in H1; try discriminate H1.
      apply H; eexists; apply ext_1.
    - eapply ext_6 in H1; destruct H1.
      2: { apply H0 in H1; apply forget_6; eauto. }
      change (nameEq (fst (pext p t)) n = true) in H1.
      erewrite <- isFresh_1; eauto.
      apply forget_4, H.
      eexists; apply ext_1.
    - apply forget_5 in H1; destruct H1.
      + erewrite <- isFresh_1; eauto.
        eapply ext_5.
      + apply H0, ext_7 in H1; eauto.
  Qed.

  Definition actx_tail {p F t} (c : actx (snd (pext p t)) F) : actx p F :=
    {| innerCtx := forget c.(innerCtx) (fst (pext p t));
       actxPf := actx_tail_pf c.(actxPf) |}.
  (** The tail of an assignment context in an extended pure context. *)

  Lemma actx_head_lemma_helper {p F t} (c : actx (snd (pext p t)) F) b :
    find (fst (pext p t)) c.(innerCtx) <> inl b.
  Proof.
    intro; destruct c as [?c [?H ?H ?H]]; simpl in H.
    assert (HasValue (fst (pext p t)) (snd (pext p t)))
      by (eexists; apply ext_1).
    apply H0 in H3; destruct H3; apply find_1 in H3.
    rewrite H3 in H; discriminate H.
  Qed.

  Definition actx_head_lemma {p F t} (c : actx (snd (pext p t)) F) : F t.
  Proof.
    remember (find (fst (pext p t)) c.(innerCtx)) as o;
      destruct o; symmetry in Heqo; eauto.
    destruct (actx_head_lemma_helper c b); eauto.
  Qed.

  Definition actx_head {p F t} (c : actx (snd (pext p t)) F) : F t :=
    match find (fst (pext p t)) c.(innerCtx) with
    | inr x => x
    | inl _ => actx_head_lemma c
    end.
  (** The head of an assignment context in an extended pure context. *)

  Definition actx_head_MapsTo {p F t} {c : actx (snd (pext p t)) F} :
    MapsTo (fst (pext p t)) (actx_head c) c.(innerCtx).
  Proof.
    unfold actx_head; apply find_2; symmetry.
    remember (find (fst (pext p t)) c.(innerCtx)) as o;
      destruct o; symmetry in Heqo; eauto.
    destruct (actx_head_lemma_helper c b); eauto.
  Qed.

  Lemma actx_add_isFresh_pf {p F t} (c : actx p F) {x : F t} :
    isFresh (fst (pext p t)) c.(innerCtx) = true.
  Proof.
    destruct c as [c [?H ?H ?H]]; simpl.
    eapply H0, ext_5.
  Qed.

  Lemma actx_add_pf {p F t} {x : F t} {c : ctx F} :
    SameShape p c -> SameShape (snd (pext p t)) (snd (add c x)).
  Proof.
    intro; pose proof H; destruct H0 as [?H ?H ?H]; clear H2;
      split; split; intros.
    - destruct H2.
      apply ext_3 in H2; destruct H2.
      + assert (tnameEq (fst (add c x)) n = true).
        * eapply tnameEq_trans; eauto; rewrite tnameEq_sym.
          apply nameEq_to_tnameEq, ext_9; eauto.
        * eapply HasValue_1; eauto.
          eexists; eapply ext_1.
      + assert (HasValue n p) by (eexists; eauto).
        apply H0 in H3; destruct H3.
        eexists; apply ext_2; eauto.
    - destruct H2.
      apply ext_3 in H2; destruct H2.
      + assert (tnameEq (fst (pext p t)) n = true).
        * eapply tnameEq_trans; eauto.
          apply nameEq_to_tnameEq, ext_9; eauto.
        * eapply HasValue_1; eauto.
          eexists; eapply ext_1.
      + assert (HasValue n c) by (eexists; eauto).
        apply H0 in H3; destruct H3.
        eexists; apply ext_2; eauto.
    - pose proof H2.
      eapply ext_7, H1, ext_6 in H3; destruct H3; eauto.
      eapply nameEq_trans in H3; [| eapply ext_9; eauto ].
      erewrite <- isFresh_1 in H2; eauto.
      rewrite isFresh_2 in H2; try discriminate H2.
      eexists; apply ext_1.
    - pose proof H2.
      eapply ext_7, H1, ext_6 in H3; destruct H3; eauto.
      eapply nameEq_trans in H3; [| rewrite nameEq_sym; eapply ext_9; eauto ].
      erewrite <- isFresh_1 in H2; eauto.
      rewrite isFresh_2 in H2; try discriminate H2.
      eexists; apply ext_1.
  Qed.

  Definition actx_add {p F t} (c : actx p F) (x : F t) : actx (snd (pext p t)) F :=
    {| innerCtx := snd (add c.(innerCtx) x); actxPf := actx_add_pf c.(actxPf) |}.
  (** [add] for assignment contexts. *)

  Lemma actx_head_add {p F t} (c : actx p F) (x : F t) : actx_head (actx_add c x) = x.
  Proof.
    unfold actx_head, actx_add, pext, add; simpl.
    rewrite (nameEq_to_eq (ext_9 (Some tt) (Some x) c.(actxPf))).
    rewrite (find_1 (ext_1 _ _)).
    reflexivity.
  Qed.

  Lemma actx_fst_add_eq {F p t x} {c : actx p F} :
    fst (add c.(innerCtx) x) = fst (pext p t).
  Proof.
    symmetry; apply nameEq_to_eq, ext_9, c.(actxPf).
  Qed.


  (** ** Adding multiple things to a context *)

  Fixpoint HasFreshNames {F} (xs : list { t & name t * F t }) (c : ctx F) : Prop :=
    match xs with
    | [] => True
    | existT _ _ (n,x) :: xs =>
      { pf : isFresh n c = true | HasFreshNames xs (addWith c n pf x) }
    end.

  Fixpoint append {F} (c : ctx F) (xs : list { t & name t * F t }) : HasFreshNames xs c -> ctx F :=
    match xs with
    | [] => fun _ => c
    | existT _ _ (n,x) :: xs => fun pfs => append (addWith c n (proj1_sig pfs) x) xs (proj2_sig pfs)
    end.

  Lemma HasFreshNames_unfold_r {F} {c : ctx F} {xs : list { t & name t * F t }} {t} {n : name t} {x} :
    HasFreshNames (xs ++ [existT _ _ (n,x)]) c ->
    { pfs : HasFreshNames xs c | isFresh n (append c xs pfs) = true }.
  Proof.
    revert c; induction xs as [|[?t [?n ?s]]]; simpl; intros;
      destruct H; eauto.
    destruct (IHxs _ h).
    repeat (unshelve eexists); eauto.
  Defined.

  Lemma HasFreshNames_fold_r {F} {c : ctx F} {xs : list { t & name t * F t }} {t} {n : name t} {x} :
    { pfs : HasFreshNames xs c | isFresh n (append c xs pfs) = true } ->
    HasFreshNames (xs ++ [existT _ _ (n,x)]) c.
  Proof.
    destruct 1; revert c x0 e; induction xs as [|[?t [?n ?s]]]; simpl; intros; eauto.
  Defined.

  Lemma append_unfold_r {F} {c : ctx F} {xs : list { t & name t * F t }} {t} {n : name t} {x pfs} :
    append c (xs ++ [existT _ _ (n,x)]) pfs =
    addWith (append c xs (proj1_sig (HasFreshNames_unfold_r pfs))) n
            (proj2_sig (HasFreshNames_unfold_r pfs)) x.
  Proof.
    induction xs as [|[?t [?n ?s]]]; cbn [ List.app HasFreshNames ] in *; intros.
    - simpl; destruct pfs; eauto.
    - (* rewrite (app_comm_cons xs [existT _ _ (n,x)] (existT _ _ (n0,s))). *)
  Admitted.

  Lemma HasFreshNames_drop_l {F} {c : ctx F} {s} {xs : list { t & name t * F t }} :
    HasFreshNames (s :: xs) c -> HasFreshNames xs c.
  Proof.
    destruct s as [t0 [n0 s0]].
    rewrite <- (rev_involutive xs); generalize (rev xs); intro xs'; clear xs.
    induction xs' as [|[?t [?n ?s]]]; simpl rev; intros; try easy.
    rewrite app_comm_cons in H.
    apply HasFreshNames_fold_r; eapply HasFreshNames_unfold_r in H.
    destruct H as [?pfs ?pf]; unshelve eexists; eauto.
    destruct pfs as [?pf ?pfs]; simpl append in pf.
  Admitted.


  Lemma append_1 {F} {c : ctx F} {t} {n : name t} {x xs pfs} :
    List.In (existT _ _ (n,x)) xs -> MapsTo n x (append c xs pfs).
  Admitted.

  Lemma append_2 {F} {c : ctx F} {t} {n : name t} {x xs pfs} :
    MapsTo n x c -> MapsTo n x (append c xs pfs).
  Admitted.

  Lemma append_3 {F} {c : ctx F} {t} {n : name t} {x xs pfs} :
    MapsTo n x (append c xs pfs) ->
    MapsTo n x c \/ List.In (existT _ _ (n,x)) xs.
  Proof.
    revert pfs.
    rewrite <- (rev_involutive xs); generalize (rev xs); intro xs'; clear xs.
    induction xs' as [|[?t [?n ?s]]]; simpl; intros; eauto.
    rewrite append_unfold_r in H.
    destruct (extWith_3 H).
    - right.
      destruct (tnameEq_to_teq H0); destruct (tnameEq_to_eq H0).
      replace x with s by (eapply MapsTo_fun; eauto; apply extWith_1).
      apply in_or_app; right; apply in_eq.
    - specialize (IHxs' _ H0); destruct IHxs'; [ left | right ]; eauto.
      apply in_or_app; left; eauto.
  Qed.

  Lemma append_cons_1 {F} {c : ctx F} {t} {n : name t} {pf} {t'} {n' : name t'} {x' xs pfs} :
    MapsTo n' x' (append c xs (HasFreshNames_drop_l pfs)) ->
    MapsTo n' x' (append c (existT _ _ (n,pf) :: xs) pfs).
  Admitted.

  (* Fixpoint hasFreshNames {F} (c : ctx F) (xs : list { t & name t * F t }) : bool := *)
  (*   match xs with *)
  (*   | [] => true *)
  (*   | existT _ _ (n,x) :: xs => *)
  (*     match bool_dec (isFresh n c) true with *)
  (*     | left pf => hasFreshNames (addWith c n pf x) xs *)
  (*     | right _ => false *)
  (*     end *)
  (*   end. *)

  (* Definition unfold_hasFreshNames {F c t} {n : name t} {x xs} : *)
  (*   hasFreshNames c (existT _ _ (n,x) :: xs) = true -> *)
  (*   { pf : isFresh n c = true | hasFreshNames (addWith c n pf x) xs = true }. *)
  (* Proof. *)
  (*   simpl; destruct (bool_dec (isFresh n c) true); eauto; easy. *)
  (* Qed. *)

  (* Fixpoint append {F} (c : ctx F) (xs : list { t & name t * F t }) : *)
  (*   hasFreshNames c xs = true -> ctx F := *)
  (*   match xs with *)
  (*   | [] => fun _ => c *)
  (*   | existT _ _ (n,x) :: xs => fun pfs => *)
  (*     let (pf,pfs') := unfold_hasFreshNames pfs *)
  (*      in append (addWith c n pf x) xs pfs' *)
  (*     (* match bool_dec (isFresh n c) true as pf *) *)
  (*     (*       return (match pf with *) *)
  (*     (*               | left pf => hasFreshNames (addWith c n pf x) xs *) *)
  (*     (*               | right _ => false *) *)
  (*     (*               end = true -> ctx F) with *) *)
  (*     (* | left pf => fun pfs => append (addWith c n pf x) xs pfs *) *)
  (*     (* | right _ => fun bad => False_rect _ (diff_false_true bad) *) *)
  (*     (* end *) *)
  (*   end. *)

  (* Lemma hasFreshNames_drop_r {F} (c : ctx F) (xs : list { t & name t * F t }) s : *)
  (*   hasFreshNames c (xs ++ [s]) = true -> hasFreshNames c xs = true. *)
  (* Proof. *)
  (*   revert c s; induction xs as [|[t [n x]]]; simpl; intros; eauto. *)
  (*   destruct (bool_dec (isFresh n c) true) as [pf|]; eauto. *)
  (* Qed. *)

  (* Lemma hope {F} (c : ctx F) (xs : list { t & name t * F t }) {t} (n : name t) x : *)
  (*   hasFreshNames c (xs ++ [existT _ _ (n,x)]) = true *)
  (*     <-> { pfs : hasFreshNames c xs = true | isFresh n (append c xs pfs) = true }. *)
  (* Proof. *)
  (*   split; [ intro pf | destruct 1 ]. *)
  (*   - pose (pf' := hasFreshNames_drop_r _ _ _ pf); exists pf'. *)
  (*     induction xs as [|[?t [?n ?s]]]; simpl in *. *)
  (*     + destruct (bool_dec (isFresh n c) true); try easy. *)
  (*     + destruct (bool_dec (isFresh n0 c) true); try easy. *)
  (*       specialize (IHxs H). *)

  (* Lemma hasFreshNames_drop_l {F} (c : ctx F) s (xs : list { t & name t * F t }) : *)
  (*   hasFreshNames c (s :: xs) = true -> hasFreshNames c xs = true. *)
  (* Proof. *)
  (*   destruct s as [t0 [n0 x0]]; simpl. *)
  (*   destruct (bool_dec (isFresh n0 c) true) as [pf0|]; try easy. *)
  (*   rewrite <- (rev_involutive xs) in *. *)
  (*   remember (rev xs) as xs'. *)
  (*   induction xs' as [|[?t [?n ?x]]]; simpl; intros; eauto. *)

  (*   revert c t0 n0 pf0 x0; induction xs as [|[?t [?n ?x]]]; simpl; intros; eauto. *)
  (*   destruct (bool_dec (isFresh n (addWith c n0 pf0 x0)) true); try easy. *)
  (*   pose proof (extWith_4 e). *)
  (*   destruct (bool_dec (isFresh n c) true); try easy. *)
  (* Admitted. *)

  (* Lemma hasFreshNames_unappend {F} (c : ctx F) (xs : list { t & name t * F t }) s ys : *)
  (*   hasFreshNames (append c (xs ++ [s])) ys = true -> hasFreshNames (append c xs) ys. *)


  (** ** Lemmas about [mem] and [extWith] *)

  Lemma mem_extWith_1 {F t1} {n1 : name t1} {x1} {c : ctx F} {pf1} :
    mem n1 (extWith c n1 pf1 (Some x1)) = true.
  Proof. apply mem_1; eexists; apply extWith_1. Qed.

  Lemma mem_extWith_2 {F t1 t2 } {n1 : name t1} {n2 : name t2} {x1} {c : ctx F} {pf1} :
    mem n2 c = true -> mem n2 (extWith c n1 pf1 (Some x1)) = true.
  Proof.
    intro; apply mem_1; apply mem_2 in H.
    destruct H; eexists; apply extWith_2; eauto.
  Qed.

  Lemma mem_ext_1 {F t1} {n1 : name t1} {x1} {c : ctx F} :
    mem (fst (ext c t1 (Some x1))) (snd (ext c t1 (Some x1))) = true.
  Proof. apply mem_1; eexists; apply ext_1. Qed.

  Lemma mem_ext_2 {F t1 t2} {n1 : name t1} {n2 : name t2} {x1} {c : ctx F} :
    mem n2 c = true -> mem n2 (snd (ext c t1 (Some x1))) = true.
  Proof.
    intro; apply mem_1; apply mem_2 in H.
    destruct H; eexists; apply ext_2; eauto.
  Qed.

End CtxExtras.
