
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Logic.Eqdep.
From Coq          Require Import Logic.FunctionalExtensionality.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import CompM.
From CryptolToCoq Require Import CompRefl.Utils.
From CryptolToCoq Require Import CompRefl.CompRefl.

Import ListNotations.
Import EqNotations.


(** * Ensuring a bool is true using typeclasses *)

Class IsTrue (b : bool) : Prop :=
  isTrue_eq : b = true.

Instance IsTrue_true : IsTrue true.
Proof. reflexivity. Qed.


(** * Finding/adding to a list using typeclasses *)

Class InList A (l : list A) (i : nat) (a : A) :=
  inList_eq : nth_error l i = Some a.

Instance InList_here {A} (l : list A) (a : A) :
  InList A (a :: l) 0 a | 1 := reflexivity _.

Instance InList_there {A} (l : list A) (i : nat) (a a' : A)
  `(H : InList A l i a) : InList A (a' :: l) (S i) a | 2 := H.


(** * Abstracting out a name using typeclasses *)

Class AbstractVar {t} A (n : name t) (x : A) (lam : name t -> A) : Prop :=
  abstractVar_eq : x = lam n.

Fixpoint prods (Ts : list Type) (A : Type) : Type :=
  match Ts with
  | T :: Ts => T * prods Ts A
  | nil => A
  end.

Fixpoint lastProds {Ts A} : prods Ts A -> A :=
  match Ts with
  | T :: Ts => fun ts => lastProds (snd ts)
  | nil => fun a => a
  end.

Fixpoint mapLastProds {Ts A B} (f : A -> B) : prods Ts A -> prods Ts B :=
  match Ts with
  | T :: Ts => fun ts => (fst ts, mapLastProds f (snd ts))
  | nil => f
  end.

Lemma lastProds_mapLastProds {Ts A B} {f : A -> B} {ts : prods Ts A} :
  lastProds (mapLastProds f ts) = f (lastProds ts).
Proof. induction Ts; simpl; eauto. Qed.

Lemma mapLastProds_comp {Ts A B C} {f : A -> B} {g : B -> C} {ts : prods Ts A} :
  mapLastProds g (mapLastProds f ts) = mapLastProds (fun a => g (f a)) ts.
Proof.
  induction Ts; simpl; eauto.
  rewrite IHTs; eauto.
Qed.

Lemma mapLastProds_id {Ts A f} {ts : prods Ts A} :
  (forall a, f a = a) -> mapLastProds f ts = ts.
Proof.
  induction Ts; simpl; intro; eauto.
  rewrite IHTs; destruct ts; eauto.
Qed.

Class AbstractVarInCtx {t} Ts A (n : name t) (x : prods Ts unit -> A)
                                             (lam : prods Ts (name t) -> A) : Prop :=
  abstractVarInCtx_eq : forall ts, x ts = lam (mapLastProds (fun _ => n) ts).

Instance AbstractVar_ctx {t A n x lam}
  `(AbstractVarInCtx t nil A n (fun _ => x) lam) :
  @AbstractVar t A n x lam.
Proof.
  unfold AbstractVarInCtx, AbstractVar in *.
  rewrite (H tt); reflexivity.
Qed.

Instance AbstractVarInCtx_var {t Ts n1 n2}
  `(IsTrue (Ctx.nameEq n1 n2)) :
  @AbstractVarInCtx t Ts (name t) n1 (fun _ => n2) (fun ts => lastProds ts) | 1.
Proof.
  unfold AbstractVarInCtx, IsTrue in *; intro.
  rewrite lastProds_mapLastProds; symmetry.
  apply Ctx.nameEq_to_eq; eauto.
Qed.

Instance AbstractVarInCtx_fun {t Ts T1 A n f lam}
  `(@AbstractVarInCtx t (T1 :: Ts) A n (fun ts => f (Datatypes.snd ts) (Datatypes.fst ts)) lam) :
  @AbstractVarInCtx t Ts (T1 -> A) n f (fun ts t1 => lam (t1, ts)) | 2.
Proof.
  unfold AbstractVarInCtx in *; intro.
  apply functional_extensionality; intro t1.
  specialize (H (t1, ts)); simpl in H; eauto.
Qed.

Instance AbstractVarInCtx_ap4 {t Ts T1 T2 T3 T4 A n f t1 t2 t3 t4 lam1 lam2 lam3 lam4}
  `(@AbstractVarInCtx t Ts T1 n t1 lam1) `(@AbstractVarInCtx t Ts T2 n t2 lam2)
  `(@AbstractVarInCtx t Ts T3 n t3 lam3) `(@AbstractVarInCtx t Ts T4 n t4 lam4) :
  @AbstractVarInCtx t Ts A n (fun ts => f (t1 ts) (t2 ts) (t3 ts) (t4 ts))
                             (fun ts => f (lam1 ts) (lam2 ts) (lam3 ts) (lam4 ts)) | 3.
Proof.
  unfold AbstractVarInCtx in *; intro.
  rewrite H, H0, H1, H2; reflexivity.
Qed.

Instance AbstractVarInCtx_ap3 {t Ts T1 T2 T3 A n f t1 t2 t3 lam1 lam2 lam3}
  `(@AbstractVarInCtx t Ts T1 n t1 lam1) `(@AbstractVarInCtx t Ts T2 n t2 lam2)
  `(@AbstractVarInCtx t Ts T3 n t3 lam3) :
  @AbstractVarInCtx t Ts A n (fun ts => f (t1 ts) (t2 ts) (t3 ts))
                             (fun ts => f (lam1 ts) (lam2 ts) (lam3 ts)) | 4.
Proof.
  unfold AbstractVarInCtx in *; intro.
  rewrite H, H0, H1; reflexivity.
Qed.

Instance AbstractVarInCtx_ap2 {t Ts T1 T2 A n f t1 t2 lam1 lam2}
  `(@AbstractVarInCtx t Ts T1 n t1 lam1) `(@AbstractVarInCtx t Ts T2 n t2 lam2) :
  @AbstractVarInCtx t Ts A n (fun ts => f (t1 ts) (t2 ts))
                             (fun ts => f (lam1 ts) (lam2 ts)) | 5.
Proof.
  unfold AbstractVarInCtx in *; intro.
  rewrite H, H0; reflexivity.
Qed.

Instance AbstractVarInCtx_ap1 {t Ts T1 A n f t1 lam1}
  `(@AbstractVarInCtx t Ts T1 n t1 lam1) :
  @AbstractVarInCtx t Ts A n (fun ts => f (t1 ts))
                             (fun ts => f (lam1 ts)) | 6.
Proof.
  unfold AbstractVarInCtx in *; intro.
  rewrite H; reflexivity.
Qed.

Instance AbstractVarInCtx_const {t Ts A n x} :
  @AbstractVarInCtx t Ts A n x (fun ts => x (mapLastProds (fun _ => tt) ts)) | 7.
Proof.
  unfold AbstractVarInCtx in *; intro.
  rewrite mapLastProds_comp, mapLastProds_id; eauto.
  intros []; reflexivity.
Qed.

(* Lemma abstractVar {A} a T (P : T -> Prop) x lam *)
(*   `(@AbstractVar A T a x lam) : *)
(*   P (lam a) -> P x. *)
(* Proof. rewrite H; eauto. Qed. *)


(** * Reifying types *)

Class ReifyType (tEnv : list Set) (t : type) (A : Set) :=
  reifyType_eq : typeD tEnv t = A.

Definition reifyType_rew {tEnv t A} `{H : ReifyType tEnv t A} : A -> typeD tEnv t :=
  fun a => rew <- H in a.

Instance ReifyType_unit {tEnv} :
  ReifyType tEnv unitT unit | 1.
Proof. reflexivity. Defined.

Instance ReifyType_bool {tEnv} :
  ReifyType tEnv boolT bool | 1.
Proof. reflexivity. Defined.

Instance ReifyType_Either {tEnv tl tr Al Ar}
  `(ReifyType tEnv tl Al) `(ReifyType tEnv tr Ar) :
  ReifyType tEnv (EitherT tl tr) (SAWCorePrelude.Either Al Ar) | 1.
Proof.
  unfold ReifyType in *; simpl.
  rewrite H, H0; reflexivity.
Defined.

Instance ReifyType_prod {tEnv tl tr Al Ar}
  `(ReifyType tEnv tl Al) `(ReifyType tEnv tr Ar) :
  ReifyType tEnv (prodT tl tr) (prod Al Ar) | 1.
Proof.
  unfold ReifyType in *; simpl.
  rewrite H, H0; reflexivity.
Defined.

Instance ReifyType_list {tEnv t A}
  `(ReifyType tEnv t A) :
  ReifyType tEnv (listT t) (list A) | 1.
Proof.
  unfold ReifyType in *; simpl.
  rewrite H; reflexivity.
Defined.

Instance ReifyType_unknown {tEnv i A}
  `(InList _ tEnv i A) :
  ReifyType tEnv (TypeT i) A | 2.
Proof.
  unfold InList, ReifyType in *; simpl; unfold nthTypeEnv.
  revert tEnv H; induction i; intros;
    destruct tEnv; simpl in *;
    try discriminate H; try injection H; eauto.
Defined.

Class ReifyFMType (tEnv : list Set) (fmt : fmtype) (lrt : LetRecType) :=
  reifyFMType_eq : fmtypeD tEnv fmt = lrt.

Instance ReifyFMType_FunMT {tEnv t fmt A lrt}
  `(ReifyType tEnv t A)
  `(ReifyFMType tEnv fmt lrt) :
  ReifyFMType tEnv (FunMT t fmt) (LRT_Fun A (fun _ => lrt)).
Proof.
  unfold ReifyType, ReifyFMType in *; simpl.
  rewrite H, H0; reflexivity.
Defined.

Instance ReifyFMType_CompMT {tEnv t A}
  `(ReifyType tEnv t A) :
  ReifyFMType tEnv (CompMT t) (LRT_Ret A).
Proof.
  unfold ReifyType, ReifyFMType in *; simpl.
  rewrite H; reflexivity.
Defined.


(** * Reifying variables *)

Class ReifyVar tEnv p p' (f : Ctx.actx p (typeD tEnv) -> Ctx.actx p' (typeD tEnv)) :=
  reifyVar_impl : forall c t (n : name t) x,
    Ctx.MapsTo n x (Ctx.innerCtx (f c)) -> Ctx.MapsTo n x (Ctx.innerCtx c).

Instance ReifyVar_base {tEnv p t} :
  ReifyVar tEnv (Datatypes.snd (Ctx.pext p t))
                (Datatypes.snd (Ctx.pext p t)) (fun c => c).
Proof. intro; eauto. Qed.

Instance ReifyVar_step {tEnv p p' t f}
  `(ReifyVar tEnv p (Datatypes.snd (Ctx.pext p' t)) f) :
  ReifyVar tEnv p p' (fun c => Ctx.actx_tail (f c)).
Proof.
  unfold ReifyVar, Ctx.actx_tail in *; simpl; intros.
  apply Ctx.forget_2 in H0; eauto.
Qed.

Definition var0 {F : type -> Set} {A : Set} p t :
  Ctx.actx (Datatypes.snd (Ctx.pext p t)) F -> F t = A -> A :=
  fun c eq =>rew eq in @Ctx.actx_head p _ _ c.


(** * Reifying expressions *)

Class ReifyExpr (tEnv : list Set) p
                (t : type) (e : expr tEnv t)
                (A : Set) (x : Ctx.actx p (typeD tEnv) -> A) :=
  reifyExpr_eq : forall c, eq_dep Set (sum String) (typeD tEnv t) (exprD tEnv (Ctx.innerCtx c) e) A (inr (x c)).

Definition reifyExpr_teq {tEnv p t e A x} `{ReifyExpr tEnv p t e A x} :
  Ctx.actx p (typeD tEnv) -> typeD tEnv t = A :=
  fun c => eq_dep_eq1 (reifyExpr_eq c).

Instance ReifyExpr_var {tEnv p p' t A f eq}
  `(ReifyVar tEnv p (Datatypes.snd (Ctx.pext p' t)) f) :
  ReifyExpr tEnv p t (varE _ (Datatypes.fst (Ctx.pext p' t)))
                   A (fun c => var0 p' t (f c) (eq c)) | 1.
Proof.
  unfold ReifyExpr, ReifyVar, var0, Ctx.actx_head in *; cbn - [Ctx.ext]; intro.
  assert (Ctx.HasValue (Datatypes.fst (Ctx.pext p' t)) (Ctx.innerCtx (f c))).
  - apply (Ctx.actxPf (f c)).
    econstructor; apply Ctx.ext_1.
  - destruct H0; pose proof (H _ _ _ _ H0).
    apply Ctx.find_1 in H0; apply Ctx.find_1 in H1.
    rewrite H0, H1; simpl.
    destruct eq; simpl.
    reflexivity.
Qed.

Instance ReifyExpr_tt {tEnv p} :
  ReifyExpr tEnv p _ (ttE _) _ (fun _ => tt) | 1.
Proof. intro; reflexivity. Qed.

Instance ReifyExpr_true {tEnv p} :
  ReifyExpr tEnv p _ (trueE _) _ (fun _ => true) | 1.
Proof. intro; reflexivity. Qed.

Instance ReifyExpr_false {tEnv p} :
  ReifyExpr tEnv p _ (falseE _) _ (fun _ => false) | 1.
Proof. intro; reflexivity. Qed.

Instance ReifyExpr_Left {tEnv p tl tr Al Ar e x}
  `(ReifyType tEnv tr Ar) `(ReifyExpr tEnv p tl e Al x) :
  ReifyExpr tEnv p _ (LeftE _ tl tr e) _ (fun c => SAWCorePrelude.Left Al Ar (x c)) | 1.
Proof.
  unfold ReifyExpr, ReifyType in *; simpl; intro.
  rewrite H, (H0 c).
  reflexivity.
Qed.

Instance ReifyExpr_Right {tEnv p tl tr Al Ar e x}
  `(ReifyType tEnv tl Al) `(ReifyExpr tEnv p tr e Ar x) :
  ReifyExpr tEnv p _ (RightE _ tl tr e) _ (fun c => SAWCorePrelude.Right Al Ar (x c)) | 1.
Proof.
  unfold ReifyExpr, ReifyType in *; simpl; intro.
  rewrite H, (H0 c).
  reflexivity.
Qed.

Instance ReifyExpr_fst {tEnv p tl tr Al Ar e x}
  `(ReifyType tEnv tl Al) `(ReifyType tEnv tr Ar)
  `(ReifyExpr tEnv p (prodT tl tr) e (prod Al Ar) x) :
  ReifyExpr tEnv p _ (fstE tEnv e) _ (fun c => fst (x c)) | 1.
Proof.
  unfold ReifyExpr, ReifyType in *; simpl in *; intro.
  destruct H, H0.
  enough (fmapSumR fst (exprD tEnv (Ctx.innerCtx c) e) = inr (fst (x c)))
    by (rewrite H; reflexivity).
  specialize (H1 c); apply eq_dep_eq in H1.
  rewrite H1; reflexivity.
Qed.

Instance ReifyExpr_snd {tEnv p tl tr Al Ar e x}
  `(ReifyType tEnv tl Al) `(ReifyType tEnv tr Ar)
  `(ReifyExpr tEnv p (prodT tl tr) e (prod Al Ar) x) :
  ReifyExpr tEnv p _ (sndE tEnv e) _ (fun c => snd (x c)) | 1.
Proof.
  unfold ReifyExpr, ReifyType in *; simpl in *; intro.
  destruct H, H0.
  enough (fmapSumR snd (exprD tEnv (Ctx.innerCtx c) e) = inr (snd (x c)))
    by (rewrite H; reflexivity).
  specialize (H1 c); apply eq_dep_eq in H1.
  rewrite H1; reflexivity.
Qed.

Instance ReifyExpr_pair {tEnv p tl tr Al Ar e1 e2 x1 x2}
  `(ReifyExpr tEnv p tl e1 Al x1)
  `(ReifyExpr tEnv p tr e2 Ar x2) :
  ReifyExpr tEnv p _ (pairE tEnv e1 e2) _ (fun c => (x1 c, x2 c)) | 1.
Proof.
  unfold ReifyExpr, ReifyType in *; simpl in *; intro.
  rewrite H, H0; reflexivity.
Qed.

Instance ReifyExpr_nil {tEnv p t A}
  `(ReifyType tEnv t A) :
  ReifyExpr tEnv p _ (@nilE tEnv t) _ (fun _ => @nil A) | 1.
Proof.
  unfold ReifyType in *; simpl in *; intro.
  destruct H; reflexivity.
Qed.

Instance ReifyExpr_cons {tEnv p t A e1 e2 x1 x2}
  `(ReifyExpr tEnv p t e1 A x1)
  `(ReifyExpr tEnv p (listT t) e2 (list A) x2) :
  ReifyExpr tEnv p _ (consE tEnv e1 e2) _ (fun c => (x1 c) :: (x2 c)) | 1.
Proof.
  unfold ReifyExpr, ReifyType in *; simpl in *; intro.
  destruct (eq_dep_eq1 (H c)).
  specialize (H c); apply eq_dep_eq in H.
  specialize (H0 c); apply eq_dep_eq in H0.
  enough (apSumR (fmapSumR cons (exprD tEnv (Ctx.innerCtx c) e1)) (exprD tEnv (Ctx.innerCtx c) e2) = inr (x1 c :: x2 c))
    by (rewrite H1; reflexivity).
  rewrite H, H0; reflexivity.
Qed.

Instance ReifyExpr_unfoldList {tEnv p t A e x}
  `(ReifyType tEnv t A) `(ReifyExpr tEnv p _ e _ x) :
  ReifyExpr tEnv p _ (@unfoldListE tEnv t e)
                   _ (fun c => @SAWCorePrelude.unfoldList A (x c)) | 1.
Proof.
  unfold ReifyExpr, ReifyType in *; simpl in *; intro.
  destruct H.
  enough (fmapSumR (SAWCorePrelude.unfoldList (typeD tEnv t)) (exprD tEnv (Ctx.innerCtx c) e) = inr (SAWCorePrelude.unfoldList (typeD tEnv t) (x c)))
    by (rewrite H; reflexivity).
  specialize (H0 c); apply eq_dep_eq in H0.
  rewrite H0; reflexivity.
Qed.

Instance ReifyExpr_foldList {tEnv p t A e x}
  `(ReifyType tEnv t A) `(ReifyExpr tEnv p _ e _ x) :
  ReifyExpr tEnv p _ (@foldListE tEnv t e)
                   _ (fun c => @SAWCorePrelude.foldList A (x c)) | 1.
Proof.
  unfold ReifyExpr, ReifyType in *; simpl in *; intro.
  destruct H.
  enough (fmapSumR (SAWCorePrelude.foldList (typeD tEnv t)) (exprD tEnv (Ctx.innerCtx c) e) = inr (SAWCorePrelude.foldList (typeD tEnv t) (x c)))
    by (rewrite H; reflexivity).
  specialize (H0 c); apply eq_dep_eq in H0.
  rewrite H0; reflexivity.
Qed.

Instance ReifyExpr_unknown {tEnv p t A x}
  `(ReifyType tEnv t A) :
  ReifyExpr tEnv p _ (termE _ (reifyType_rew x)) A (fun _ => x) | 2.
Proof.
  unfold ReifyExpr, ReifyType, reifyType_eq in *; simpl; intro.
  destruct H; vm_compute reifyType_rew.
  reflexivity.
Qed.


(** * Reifying monadic expressions *)

Class ReifyMExpr (tEnv : list Set) p
                 (t : type) (me : mexpr tEnv t)
                 (A : Set) (m : Ctx.actx p (typeD tEnv) -> CompM A) :=
  reifyMExpr_eq : forall c, eq_dep Set CompM (typeD tEnv t) (mexprD tEnv (Ctx.innerCtx c) me) A (m c).

Definition reifyMExpr_teq {tEnv p t me A m} `{ReifyMExpr tEnv p t me A m} :
  Ctx.actx p (typeD tEnv) -> typeD tEnv t = A :=
  fun c => eq_dep_eq1 (reifyMExpr_eq c).

Instance ReifyMExpr_returnM {tEnv p t e A x}
  `(ReifyExpr tEnv p t e A x) :
  ReifyMExpr tEnv p t (returnE _ _ e) A (fun c => returnM (x c)).
Proof.
  unfold ReifyExpr, ReifyMExpr in *; simpl; intros.
  rewrite H; simpl.
  reflexivity.
Qed.

(* This is false for CtxPositive! *)
Axiom actx_tail_add : forall {p F t} (c : Ctx.actx p F) (x : F t),
  Ctx.actx_tail (Ctx.actx_add c x) = c.

Instance ReifyMExpr_bindE {tEnv p t t' me ke' ke A B m k}
  `(ReifyType tEnv t A)
  `(ReifyMExpr tEnv p t' me B m)
  `(ReifyMExpr tEnv (Datatypes.snd (Ctx.pext p t'))
               t ke'
               A (fun c => k (Ctx.actx_tail c) (var0 p t' c (reifyMExpr_teq (Ctx.actx_tail c)))))
  `(AbstractVar _ _ (Datatypes.fst (Ctx.pext p t')) ke' ke) :
  ReifyMExpr tEnv p t (bindE _ _ me ke) A (fun c => bindM (m c) (k c)).
Proof.
  unfold ReifyType, ReifyMExpr in *; cbn - [Ctx.ext]; unfold Ctx.inExt; intro.
  apply (eq_dep_bindM (H0 c)); [eauto | intros].
  unfold reifyMExpr_teq, reifyMExpr_eq, var0 in H1.
  replace ke' with (ke (Datatypes.fst (Ctx.pext p t'))) in H1.
  rewrite Ctx.actx_fst_add_eq.
  specialize (H1 (Ctx.actx_add c a)); cbn - [Ctx.ext] in H1.
  rewrite H1, Ctx.actx_head_add.
  enough ((k (Ctx.actx_tail (Ctx.actx_add c a))
             (rew [fun x : Set => x] eq_dep_eq1 (H0 (Ctx.actx_tail (Ctx.actx_add c a))) in a)) = (k c (rew [fun x : Set => x] eq_dep_eq1 (H0 c) in a))).
  - rewrite <- H3; reflexivity.
  - rewrite (actx_tail_add c a); reflexivity.
Qed.

Instance ReifyMExpr_errorE {tEnv p t s A}
  `(ReifyType tEnv t A) :
  ReifyMExpr tEnv p t (errorE _ _ s) A (fun _ => errorM s).
Proof.
  unfold ReifyMExpr, ReifyType in *; cbn; intros.
  rewrite H; reflexivity.
Qed.

Instance ReifyMExpr_iteE {tEnv p} {t e me1 me2 A b x1 x2}
  `(ReifyExpr tEnv p boolT e bool b)
  `(ReifyMExpr tEnv p t me1 A x1)
  `(ReifyMExpr tEnv p t me2 A x2) :
  ReifyMExpr tEnv p t (iteE _ _ e me1 me2)
                    A (fun c => if b c then x1 c else x2 c).
Proof.
  unfold ReifyMExpr, ReifyExpr in *; cbn; intro.
  specialize (H c); apply eq_dep_eq in H; rewrite H; cbn.
  eapply f_eq_dep_2 with (f := fun A x1 x2 => if b c then x1 else x2); eauto.
Qed.

Instance ReifyMExpr_eitherE {tEnv p} {t tl tr fe fe' ge ge' e A Al Ar f g x}
  `(ReifyType tEnv tl Al) `(ReifyType tEnv tr Ar) `(ReifyType tEnv t A)
  `(ReifyExpr tEnv p (EitherT tl tr) e (SAWCorePrelude.Either Al Ar) x)
  `(ReifyMExpr tEnv (Datatypes.snd (Ctx.pext p tl))
               t fe'
               A (fun c => f (Ctx.actx_tail c) (var0 p tl c reifyType_eq)))
  `(AbstractVar _ _ (Datatypes.fst (Ctx.pext p tl)) fe' fe)
  `(ReifyMExpr tEnv (Datatypes.snd (Ctx.pext p tr))
               t ge'
               A (fun c => g (Ctx.actx_tail c) (var0 p tr c reifyType_eq)))
  `(AbstractVar _ _ (Datatypes.fst (Ctx.pext p tr)) ge' ge) :
  ReifyMExpr tEnv p t (eitherE _ _ fe ge e)
                    A (fun c => SAWCorePrelude.either _ _ _ (f c) (g c) (x c)).
Proof.
  unfold ReifyMExpr, ReifyType, ReifyExpr in *;
    cbn - [Ctx.ext]; unfold Ctx.inExt; intro.
  unfold reifyMExpr_teq, reifyMExpr_eq, var0 in H2, H3.
  destruct H, H0.
  specialize (H2 c); apply eq_dep_eq in H2.
  rewrite H2; cbn - [Ctx.ext].
  eapply f_eq_dep_2 with (U := Set) (f := fun A l r => SAWCorePrelude.either (typeD tEnv tl) (typeD tEnv tr) (CompM A) l r (x c));
    apply @eq_dep_fun_ext with (U := Set) (P := CompM); eauto; intro.
  - specialize (H3 (Ctx.actx_add c x0)); cbn - [Ctx.ext] in H3.
    replace fe' with (fe (Datatypes.fst (Ctx.pext p tl))) in H3.
    rewrite Ctx.actx_fst_add_eq, H3, Ctx.actx_head_add.
    rewrite (actx_tail_add c x0); reflexivity.
  - specialize (H5 (Ctx.actx_add c x0)); cbn - [Ctx.ext] in H5.
    replace ge' with (ge (Datatypes.fst (Ctx.pext p tr))) in H5.
    rewrite Ctx.actx_fst_add_eq, H5, Ctx.actx_head_add.
    rewrite (actx_tail_add c x0); reflexivity.
Qed.

Instance ReifyMExpr_existsE {tEnv p t t' Pe Pe' A A' P}
  `(ReifyType tEnv t A)  `(ReifyType tEnv t' A')
  `(ReifyMExpr tEnv (Datatypes.snd (Ctx.pext p t'))
               t Pe'
               A (fun c => P (Ctx.actx_tail c) (var0 p t' c reifyType_eq)))
  `(AbstractVar _ _ (Datatypes.fst (Ctx.pext p t')) Pe' Pe) :
  ReifyMExpr tEnv p t (existsE _ _ _ Pe) A (fun c => existsM (P c)).
Proof.
  unfold ReifyType, ReifyMExpr in *; cbn - [Ctx.ext]; unfold Ctx.inExt; intro.
  unfold reifyType_eq in H1; destruct H0; cbn in H1.
  eapply f_eq_dep with (U := Set) (f := fun A P => existsM P).
  apply @eq_dep_fun_ext with (U := Set) (P := CompM); eauto; intro.
  specialize (H1 (Ctx.actx_add c x)); cbn - [Ctx.ext] in H1.
  replace Pe' with (Pe (Datatypes.fst (Ctx.pext p t'))) in H1.
  rewrite Ctx.actx_fst_add_eq, H1, Ctx.actx_head_add.
  rewrite (actx_tail_add c x); reflexivity.
Qed.


(** * Reifying monadic functions *)

Class ReifyFMExpr (tEnv : list Set) (p : Ctx.pctx)
                  (fmt : fmtype) (fme : fmexpr tEnv fmt)
                  (lrt : LetRecType) (f : Ctx.actx p (typeD tEnv) -> lrtToType lrt) :=
  reifyFMExpr_eq : forall c, eq_dep _ lrtToType (fmtypeD tEnv fmt) (fmexprD tEnv (Ctx.innerCtx c) fme) lrt (f c).

Instance ReifyFMExpr_CompMT {tEnv p t me A m}
  `(ReifyMExpr tEnv p t me A m) :
  ReifyFMExpr tEnv p (CompMT t) me (LRT_Ret A) m.
Proof.
  unfold ReifyFMExpr, ReifyMExpr in *; cbn - [Ctx.ext]; intro.
  rewrite H; reflexivity.
Qed.

Instance ReifyFMExpr_FunMT {tEnv p t fmt fme fme'} {A : Set} {lrt f}
  `(ReifyType tEnv t A) `(ReifyFMType tEnv fmt lrt)
  `(ReifyFMExpr tEnv (Datatypes.snd (Ctx.pext p t))
                fmt fme'
                lrt (fun c => f (Ctx.actx_tail c) (var0 p t c reifyType_eq)))
  `(AbstractVar _ _ (Datatypes.fst (Ctx.pext p t)) fme' fme) :
  ReifyFMExpr tEnv p (FunMT t fmt) fme (LRT_Fun A (fun _ => lrt)) f.
Proof.
  unfold ReifyFMExpr, ReifyType in *;
    cbn - [Ctx.ext]; unfold Ctx.inExt; intro.
  unfold reifyMExpr_teq, reifyMExpr_eq, var0 in H1.
  replace fme' with (fme (Datatypes.fst (Ctx.pext p t))) in H1.
  destruct H.
  enough (eq_dep LetRecType (fun lrt => typeD tEnv t -> lrtToType lrt)
                 (fmtypeD tEnv fmt) (fun x => fmexprD tEnv (Datatypes.snd (Ctx.add (Ctx.innerCtx c) x))
                                                      (fme (Datatypes.fst (Ctx.add (Ctx.innerCtx c) x))))
                 lrt (f c))
    by (rewrite H; reflexivity).
  apply eq_dep_fun_ext; eauto; intro.
  specialize (H1 (Ctx.actx_add c x)); cbn - [Ctx.ext] in H1.
  rewrite Ctx.actx_fst_add_eq, H1, Ctx.actx_head_add.
  rewrite(actx_tail_add c x); reflexivity.
Qed.


(** * Tactics for reifying *)

Ltac reifyTac lemma :=
  unshelve (eapply lemma);
  [try exact []|];
  cbn [prods lastProds mapLastProds fst Datatypes.fst].

Lemma reifyType_lemma {tEnv t A} (P : Type -> Prop)
  `{ReifyType tEnv t A} :
  P (typeD tEnv t) -> P A.
Proof. rewrite reifyType_eq; eauto. Qed.

Ltac reifyType := reifyTac reifyType_lemma.

(* Lemma reifyExpr_lemma {tEnv p t e x} {P : string + typeD tEnv t -> Prop} *)
(*   `{ReifyExpr tEnv p t e x} c : *)
(*   P (exprD tEnv (Ctx.innerCtx c) e) -> P (inr (x c)). *)
(* Proof. rewrite reifyExpr_eq; eauto. Qed. *)

Lemma reifyExpr_lemma {tEnv t e A x} {P : forall (A : Set), string + A -> Prop}
  `{ReifyExpr tEnv Ctx.empty t e A (fun _ => x)} :
  P (typeD tEnv t) (exprD tEnv (Ctx.innerCtx Ctx.actx_empty) e) -> P A (inr x).
Proof. rewrite (H Ctx.actx_empty); eauto. Qed.

Ltac reifyExpr := reifyTac reifyExpr_lemma.

Lemma reifyMExpr_lemma {tEnv t me A m} {P : forall (A : Set), CompM A -> Prop}
  `{ReifyMExpr tEnv Ctx.empty t me A (fun _ => m)} :
  P (typeD tEnv t) (mexprD tEnv (Ctx.innerCtx Ctx.actx_empty) me) -> P A m.
Proof. rewrite (H Ctx.actx_empty); eauto. Qed.

Ltac reifyMExpr := reifyTac reifyMExpr_lemma.

Lemma reifyMExpr_refinesM_lemma {tEnv t me1 me2 A m1 m2}
  `{ReifyMExpr tEnv Ctx.empty t me1 A (fun _ => m1)}
  `{ReifyMExpr tEnv Ctx.empty t me2 A (fun _ => m2)} :
  refinesM (mexprD tEnv (Ctx.innerCtx Ctx.actx_empty) me1)
           (mexprD tEnv (Ctx.innerCtx Ctx.actx_empty) me2) ->
  refinesM m1 m2.
Proof.
  unfold ReifyMExpr in *; intro.
  specialize (H Ctx.actx_empty); specialize (H0 Ctx.actx_empty).
  destruct (eq_dep_eq1 H).
  apply eq_dep_eq in H; apply eq_dep_eq in H0.
  rewrite H, H0 in H1; eauto.
Qed.

Ltac reifyMExpr_refinesM := (* reifyTac reifyMExpr_refinesM_lemma. *)
  unshelve (eapply reifyMExpr_refinesM_lemma);
  [try exact []|];
  cbn [prods lastProds mapLastProds fst Datatypes.fst].

Lemma reifyFMExpr_lemma {tEnv fmt fme lrt f} {P : forall (lrt : LetRecType), lrtToType lrt -> Prop}
  `{ReifyFMExpr tEnv Ctx.empty fmt fme lrt (fun _ => f)} :
  P (fmtypeD tEnv fmt) (fmexprD tEnv (Ctx.innerCtx Ctx.actx_empty) fme) -> P lrt f.
Proof. rewrite (H Ctx.actx_empty); eauto. Qed.

Ltac reifyFMExpr := reifyTac reifyFMExpr_lemma.

Lemma reifyFMExpr_refinesFun_lemma {tEnv fmt fme1 fme2 lrt f1 f2}
  `{ReifyFMExpr tEnv Ctx.empty fmt fme1 lrt (fun _ => f1)}
  `{ReifyFMExpr tEnv Ctx.empty fmt fme2 lrt (fun _ => f2)} :
  refinesFun (fmexprD tEnv (Ctx.innerCtx Ctx.actx_empty) fme1)
             (fmexprD tEnv (Ctx.innerCtx Ctx.actx_empty) fme2) ->
  refinesFun f1 f2.
Proof.
  unfold ReifyFMExpr in *; intro.
  specialize (H Ctx.actx_empty); specialize (H0 Ctx.actx_empty).
  destruct (eq_dep_eq1 H).
  apply eq_dep_eq in H; apply eq_dep_eq in H0.
  rewrite H, H0 in H1; eauto.
Qed.

Ltac reifyFMExpr_refinesFun := (* reifyTac reifyFMExpr_refinesFun_lemma. *)
  unshelve (eapply reifyFMExpr_refinesFun_lemma);
  [try exact []|];
  cbn [prods lastProds mapLastProds fst Datatypes.fst].

(* Inductive test := hi. *)

(* Goal forall {P : Type -> Prop}, P (SAWCorePrelude.Either bool (SAWCorePrelude.Either bool test)). *)
(*   intro. *)
(*   reifyType P. *)

(* Lemma reifyType_lemma2 {tEnv t} A *)
(*   `(ReifyType tEnv t A) : *)
(*   typeD tEnv t = A. *)
(* Proof. rewrite reifyType_eq; eauto. Qed. *)

(* Goal refinesM (returnM (SAWCorePrelude.Left bool bool true)) (returnM (SAWCorePrelude.Left bool bool true)). *)

(*   reifyMExpr_refinesM. *)

(* Goal forall {P : forall (A : Set), CompM A -> Prop}, *)
(*     P _ (returnM tt >>= (fun u => returnM u)). *)

(*   Opaque bindM. *)

(*   intros. *)
(*   eapply reifyMExpr_lemma. *)
(*   unshelve typeclasses eauto;  *)
(*   apply  *)
(*   Set Typeclasses Debug. *)
(*   try typeclasses eauto. *)
(*   (* typeclasses eauto. *) *)
(*   - eapply ReifyMExpr_bindE. *)
(*     + eapply ReifyMExpr_returnM. *)
(*       eapply ReifyExpr_var. *)
(*       typeclasses eauto. *)
(*   Unshelve. 2: exact []. *)
(*       Check @ReifyExpr_var0. *)
(*       eapply (@ReifyExpr_var _ (Datatypes.snd (Ctx.pext Ctx.empty unitT)) Ctx.empty unitT unit). *)

(*   intros. *)
(*   reifyMExpr P. *)
(*   match goal with *)
(*   | |- P ?t ?x =>  *)
(*   end. *)
(*   reifyExpr P. *)
(*   assert (SAWCorePrelude.Either bool bool = typeD [bool] (EitherT (TypeT 0) (TypeT 0))). *)
(*   - symmetry; eapply reifyType_lemma2. *)
(*     typeclasses eauto. *)
(*   - pattern (SAWCorePrelude.Either bool bool). *)

(* Goal forall {P : forall (lrt : LetRecType), lrtToType lrt -> Prop}, *)
(*     P (LRT_Fun (SAWCorePrelude.Either unit unit) (fun _ => LRT_Ret unit)) *)
(*       (fun _ => returnM tt). *)

(*   intros. *)
(*   eapply reifyFMExpr_lemma. *)
(*   - eapply ReifyFMExpr_FunMT; [typeclasses eauto|]. *)
(*     eapply ReifyFMExpr_CompMT. Print fmexpr. Print fmtype_rect. *)
(*     Unshelve. 4: simpl. *)
(*     eapply ReifyMExpr_returnM. *)
(*     Set Typeclasses Debug. *)
(*   try timeout 5 reifyFMExpr P. *)

(* Goal forall {P : forall (lrt : LetRecType), lrtToType lrt -> Prop}, *)
(*     P (LRT_Fun (SAWCorePrelude.Either unit unit) (fun _ => LRT_Ret unit)) *)
(*       (fun x => SAWCorePrelude.either _ _ _ returnM returnM x). *)


(*   intros. *)
(*   reifyFMExpr P. *)

(*   intro; eapply reifyFMExpr_lemma. *)
(*   Set Typeclasses Debug. *)
(*   try typeclasses eauto. *)

(*   reifyFMExpr P. *)











(* Inductive test := hi. *)

(* Goal forall {P : Type -> Prop}, P (SAWCorePrelude.Either bool (SAWCorePrelude.Either bool test)). *)

(* intro. Set Typeclasses Debug Verbosity 1. *)
(* unshelve eapply reifyType; [ exact [] |]. *)

(* Class ReifyExpr (tEnv : list Set) (t : type) (e : expr tEnv t) (A : Set) (x : A) := *)
(*   reifyExpr_eq : forall c, eq_dep Set (sum String) (typeD tEnv t) (exprD tEnv c e) A (inr x). *)

(* Instance ReifyExpr_tt {tEnv} : *)
(*   ReifyExpr tEnv _ (ttE _) _ tt | 1. *)
(* Proof. intro; reflexivity. Qed. *)

(* Instance ReifyExpr_Left {tEnv tl tr Al Ar e x} *)
(*   `(ReifyType tEnv tr Ar) `(ReifyExpr tEnv tl e Al x) : *)
(*   ReifyExpr tEnv _ (LeftE _ tl tr e) _ (SAWCorePrelude.Left Al Ar x) | 1. *)
(* Proof. *)
(*   unfold ReifyExpr, ReifyType in *; simpl; intro. *)
(*   rewrite H, (H0 c). *)
(*   reflexivity. *)
(* Qed. *)

(* Instance ReifyExpr_Right {tEnv tl tr Al Ar e x} *)
(*   `(ReifyType tEnv tl Al) `(ReifyExpr tEnv tr e Ar x) : *)
(*   ReifyExpr tEnv _ (RightE _ tl tr e) _ (SAWCorePrelude.Right Al Ar x) | 1. *)
(* Proof. *)
(*   unfold ReifyExpr, ReifyType in *; simpl; intro. *)
(*   rewrite H, (H0 c). *)
(*   reflexivity. *)
(* Qed. *)

(* Instance ReifyExpr_unknown {tEnv A i x} *)
(*   `(ReifyType tEnv (TypeT i) A) : *)
(*   ReifyExpr tEnv _ (termE _ i (reifyType_rew x)) A x | 2. *)
(* Proof. *)
(*   unfold ReifyExpr, ReifyType, reifyType_eq in *; simpl; intro. *)
(*   destruct H; vm_compute reifyType_rew. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma reifyExpr {P : forall (A : Set), Ctx.actx p (typeD tEnv) string + A -> Prop} *)
(*                 {tEnv p t e A x} `{ReifyExpr tEnv p t e A x} : *)
(*   forall c, P (typeD tEnv t) (exprD tEnv (Ctx.innerCtx c) e) -> P A (inr (x c)). *)
(* Proof. intro; rewrite (H c); eauto. Qed. *)

(* Inductive test := hi. *)

(* Goal forall {P : forall (A : Set), string + A -> Prop} (c : Ctx.actx () (typeD)), *)
(*     P _ (inr (SAWCorePrelude.Left bool bool true)). *)

(* intro. (* Set Typeclasses Debug Verbosity 2. *) *)
(* unshelve eapply reifyExpr; try exact Ctx.empty; try exact []. *)





(* (** Test whether two terms are unifiable *) *)
(* Ltac unifies a b := *)
(*   match goal with *)
(*     | [ |- _ ] => let z := constr:(refl_equal _ : a = b) in constr:(true) *)
(*     | [ |- _ ] => constr:(false) *)
(*   end. *)

(* (** Tries to find the index of an element in a list, using [unifies] *) *)
(* Ltac indexOf x l := *)
(*   let rec indexOf' l i := *)
(*     match l with *)
(*     | nil => constr:(@None nat) *)
(*     | ?y :: ?l' => *)
(*       match unifies x y with *)
(*       | true => constr:(Some i) *)
(*       | false => indexOf' l' (S i) *)
(*       end *)
(*     end in *)
(*   indexOf' l O. *)

(* (** For context (i.e. map) represented by a list of pairs, tries to look up a value *) *)
(* Ltac lookupInCtx x c := *)
(*   match c with *)
(*   | nil => match type of c with *)
(*            | list (prod _ ?A) => constr:(@None A) *)
(*            end *)
(*   | (pair ?y ?v) :: ?c' => *)
(*     match unifies x y with *)
(*     | true => constr:(v) *)
(*     | false => lookupInCtx x c' *)
(*     end *)
(*   end. *)


(* (** * Reifying types *) *)

(* Ltac reifyType typeEnv A := *)
(*   match A with *)
(*   | unit => constr:(pair typeEnv unitT) *)
(*   | SAWCorePrelude.Either ?Al ?Ar => *)
(*     match reifyType typeEnv Al with *)
(*     | pair ?typeEnv' ?tl => *)
(*       match reifyType typeEnv' Ar with *)
(*       | pair ?typeEnv'' ?tr => *)
(*         constr:(pair typeEnv'' (EitherT tl tr)) *)
(*       end *)
(*     end *)
(*   | _ => *)
(*     match indexOf A typeEnv with *)
(*     | Some ?i => constr:(pair typeEnv (TypeT i)) *)
(*     | None => let i := eval compute in (length typeEnv) in *)
(*               let typeEnv' := eval simpl app in (typeEnv ++ (A :: nil)) in *)
(*               constr:(pair typeEnv' (TypeT i)) *)
(*     end *)
(*   end. *)

(* Local Example ex_reifyType : *)
(*   ltac:(let e := reifyType (@nil Set) (SAWCorePrelude.Either bool unit) in exact e) *)
(*     = ([bool], EitherT (TypeT 0) unitT) := *)
(*   reflexivity _. *)


(* (** * Reifying expressions *) *)

(* Ltac typeEnvOfExpr typeEnv x := *)
(*   match x with *)
(*   | tt => typeEnv *)
(*   | SAWCorePrelude.Left ?Al ?Ar ?x => *)
(*     match reifyType typeEnv Al with *)
(*     | pair ?typeEnv' _ => *)
(*       match reifyType typeEnv' Ar with *)
(*       | pair ?typeEnv'' _ => *)
(*         typeEnvOfExpr typeEnv'' x *)
(*       end *)
(*     end *)
(*   | SAWCorePrelude.Right ?Al ?Ar ?x => *)
(*     match reifyType typeEnv Al with *)
(*     | pair ?typeEnv' _ => *)
(*       match reifyType typeEnv' Ar with *)
(*       | pair ?typeEnv'' _ => *)
(*         typeEnvOfExpr typeEnv'' x *)
(*       end *)
(*     end *)
(*   | _ => *)
(*     let A := type of x in *)
(*     match reifyType typeEnv A with *)
(*     | pair ?typeEnv' _ => *)
(*       typeEnv' *)
(*     end *)
(*   end. *)

(* Ltac reifyExpr' typeEnv' x := *)
(*   match x with *)
(*   | tt => constr:(ttE typeEnv') *)
(*   | SAWCorePrelude.Left ?Al ?Ar ?x => *)
(*     match reifyType typeEnv' Al with *)
(*     | pair _ ?tl => *)
(*       match reifyType typeEnv' Ar with *)
(*       | pair _ ?tr => *)
(*         let e := reifyExpr' typeEnv' x in *)
(*         constr:(LeftE typeEnv' tl tr e) *)
(*       end *)
(*     end *)
(*   | SAWCorePrelude.Right ?Al ?Ar ?x => *)
(*     match reifyType typeEnv' Al with *)
(*     | pair _ ?tl => *)
(*       match reifyType typeEnv' Ar with *)
(*       | pair _ ?tr => *)
(*         let e := reifyExpr' typeEnv' x in *)
(*         constr:(RightE typeEnv' tl tr e) *)
(*       end *)
(*     end *)
(*   | _ => *)
(*     let A := type of x in *)
(*     match indexOf A typeEnv' with *)
(*     | Some ?i => *)
(*       constr:(termE typeEnv' i x) *)
(*     end *)
(*   end. *)

(* Ltac reifyExpr typeEnv x := *)
(*   let typeEnv' := typeEnvOfExpr typeEnv x in *)
(*   let e := reifyExpr' typeEnv' x in *)
(*   constr:(pair typeEnv' e). *)

(* Local Example ex_reifyExpr : *)
(*   ltac:(let e := reifyExpr (@nil Set) (SAWCorePrelude.Left bool unit true) in exact e) *)
(*     = ([bool], LeftE [bool] (TypeT 0) unitT (termE [bool] 0 true)) := *)
(*   reflexivity _. *)


(* (** * Reifying monadic expressions *) *)

(* Print mexpr. *)

(* (* Goal forall {A} (f : A -> A), True. *) *)
(* (*   intros. *) *)

(* (*   match constr:(fun (a : unit) => tt) with *) *)
(* (*   | fun _ => ?b => idtac b *) *)
(* (*   | _ => idtac "nope" *) *)
(* (*   end. *) *)

(* (*   lazymatch constr:(fun r => f r) with *) *)
(* (*   | fun a => @?b a => idtac a; idtac b; *) *)
(* (*                      match b with *) *)
(* (*                      | f ?c => idtac c *) *)
(* (*                      | _ => idtac "??" *) *)
(* (*                      end *) *)
(* (*   | _ => idtac "nope" *) *)
(* (*   end. *) *)

(* Ltac typeEnvOfMExpr typeEnv ctx x := *)
(*   match x with *)
(*   | fun a => returnM (@?x a) => typeEnvOfExpr typeEnv x *)
(*   | @bindM _ _ ?A ?A' ?mx ?f => *)
(*     match reifyType typeEnv A with *)
(*     | pair ?typeEnv' _ => *)
(*       match reifyType typeEnv' A' with *)
(*       | pair ?typeEnv'' _ => *)
(*         let typeEnv''' := typeEnvOfMExpr typeEnv'' ?mx in *)
(*         let ctx' := eval simpl app in (ctx ++ tt :: nil) in *)
(*         let f' :=  *)
(*   | SAWCorePrelude.Left ?Al ?Ar ?x => *)
(*     match reifyType typeEnv Al with *)
(*     | pair ?typeEnv' _ => *)
(*       match reifyType typeEnv' Ar with *)
(*       | pair ?typeEnv'' _ => *)
(*         typeEnvOfMExpr typeEnv'' x *)
(*       end *)
(*     end *)
(*   | SAWCorePrelude.Right ?Al ?Ar ?x => *)
(*     match reifyType typeEnv Al with *)
(*     | pair ?typeEnv' _ => *)
(*       match reifyType typeEnv' Ar with *)
(*       | pair ?typeEnv'' _ => *)
(*         typeEnvOfMExpr typeEnv'' x *)
(*       end *)
(*     end *)
(*   | _ => *)
(*     let A := type of x in *)
(*     match reifyType typeEnv A with *)
(*     | pair ?typeEnv' _ => *)
(*       typeEnv' *)
(*     end *)
(*   end. *)

(* Ltac reifyExpr' typeEnv' x := *)
(*   match x with *)
(*   | tt => constr:(ttE typeEnv') *)
(*   | SAWCorePrelude.Left ?Al ?Ar ?x => *)
(*     match reifyType typeEnv' Al with *)
(*     | pair _ ?tl => *)
(*       match reifyType typeEnv' Ar with *)
(*       | pair _ ?tr => *)
(*         let e := reifyExpr' typeEnv' x in *)
(*         constr:(LeftE typeEnv' tl tr e) *)
(*       end *)
(*     end *)
(*   | SAWCorePrelude.Right ?Al ?Ar ?x => *)
(*     match reifyType typeEnv' Al with *)
(*     | pair _ ?tl => *)
(*       match reifyType typeEnv' Ar with *)
(*       | pair _ ?tr => *)
(*         let e := reifyExpr' typeEnv' x in *)
(*         constr:(RightE typeEnv' tl tr e) *)
(*       end *)
(*     end *)
(*   | _ => *)
(*     let A := type of x in *)
(*     match indexOf A typeEnv' with *)
(*     | Some ?i => *)
(*       constr:(termE typeEnv' i x) *)
(*     end *)
(*   end. *)

(* Ltac reifyExpr typeEnv x := *)
(*   let typeEnv' := typeEnvOfExpr typeEnv x in *)
(*   let e := reifyExpr' typeEnv' x in *)
(*   constr:(pair typeEnv' e). *)
