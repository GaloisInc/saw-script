
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Logic.Eqdep.
From Coq          Require Import Logic.FunctionalExtensionality.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import CompM.
From CryptolToCoq Require Import CompRefl.CompRefl.

Import ListNotations.
Import EqNotations.

Definition eq_dep_eq1 {U P p x q y} (eq : eq_dep U P p x q y) : p = q :=
  match eq with
  | eq_dep_intro => eq_refl
  end.

Lemma f_eq_dep_2 :
  forall U (P Q : U -> Type) R p q x y z w (f : forall p, P p -> Q p -> R p),
    eq_dep U P p x q y -> eq_dep U Q p z q w -> eq_dep U R p (f p x z) q (f q y w).
Admitted.

Lemma eq_dep_fun_ext {U A} {P : U -> Type} {p q} {f : A -> P p} {g : A -> P q} :
  (forall x, eq_dep U P p (f x) q (g x)) -> eq_dep U (fun i => A -> P i) p f q g.
Admitted.

Lemma eq_dep_bindM {A B C D : Set} {m1 m2} {k1 : A -> CompM C} {k2 : B -> CompM D} :
  forall (H : eq_dep Set CompM A m1 B m2),
  (forall a, eq_dep Set CompM C (k1 a) D (k2 (rew eq_dep_eq1 H in a))) ->
  eq_dep Set CompM C (m1 >>= k1) D (m2 >>= k2).
Admitted.


(** * Finding/adding to a list using typeclasses *)

Class InList A (l : list A) (i : nat) (a : A) :=
  inList_eq : nth_error l i = Some a.

Instance InList_here {A} (l : list A) (a : A) :
  InList A (a :: l) 0 a | 1 := reflexivity _.

Instance InList_there {A} (l : list A) (i : nat) (a a' : A)
  `(H : InList A l i a) : InList A (a' :: l) (S i) a | 2 := H.


(** * Reifying types *)

Class ReifyType (tEnv : list Set) (t : type) (A : Set) :=
  reifyType_eq : typeD tEnv t = A.

Definition reifyType_rew {tEnv t A} `{H : ReifyType tEnv t A} : A -> typeD tEnv t :=
  match H with eq_refl => fun a => a end.

Instance ReifyType_unit {tEnv} :
  ReifyType tEnv unitT unit | 1.
Proof. reflexivity. Qed.

Instance ReifyType_Either {tEnv tl tr Al Ar}
  `(ReifyType tEnv tl Al) `(ReifyType tEnv tr Ar) :
  ReifyType tEnv (EitherT tl tr) (SAWCorePrelude.Either Al Ar) | 1.
Proof.
  unfold ReifyType in *; simpl.
  rewrite H, H0; reflexivity.
Qed.

Instance ReifyType_unknown {tEnv i A}
  `(InList _ tEnv i A) :
  ReifyType tEnv (TypeT i) A | 2.
Proof.
  unfold InList, ReifyType in *; simpl; unfold nthTypeEnv.
  apply nth_error_nth; eauto.
Qed.


(** * Reifying variables *)

Class ReifyVar tEnv p p' (t : type) (n n' : name t)
      (f : Ctx.actx p (typeD tEnv) -> Ctx.actx p' (typeD tEnv)) :=
  reifyVar_impl : forall c x, Ctx.MapsTo n' x (Ctx.innerCtx (f c)) ->
                              Ctx.MapsTo n  x (Ctx.innerCtx c).

Instance ReifyVar_base {tEnv p t n} :
  ReifyVar tEnv p p t n n (fun c => c).
Proof. intro; eauto. Qed.

Instance ReifyVar_step {tEnv p p' t n n' f}
  `(ReifyVar tEnv p (Datatypes.snd (Ctx.pext p' t)) t n n' f) :
  ReifyVar tEnv p p' t n n' (fun c => Ctx.actx_tail (f c)).
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

Instance ReifyExpr_var {tEnv p t n A f eq}
  `(ReifyVar tEnv p _ t n (Datatypes.fst (Ctx.pext p t)) f) :
  ReifyExpr tEnv p t (varE _ n) A (fun c => var0 p t (f c) eq) | 1.
Proof.
  unfold ReifyExpr, ReifyVar, var0, Ctx.actx_head in *; cbn - [Ctx.ext]; intro.
  assert (Ctx.HasValue (Datatypes.fst (Ctx.pext p t)) (Ctx.innerCtx (f c))).
  - apply (Ctx.actxPf (f c)).
    econstructor; apply Ctx.ext_1.
  - destruct H0; pose proof (H _ _ H0).
    apply Ctx.find_1 in H0; apply Ctx.find_1 in H1.
    rewrite H0, H1; simpl.
    destruct eq; simpl.
    reflexivity.
Qed.

Instance ReifyExpr_tt {tEnv p} :
  ReifyExpr tEnv p _ (ttE _) _ (fun _ => tt) | 1.
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

Instance ReifyExpr_unknown {tEnv p A i x}
  `(ReifyType tEnv (TypeT i) A) :
  ReifyExpr tEnv p _ (termE _ i (reifyType_rew x)) A (fun _ => x) | 2.
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

Instance ReifyMExpr_bindE {tEnv p t t' me ke A B m k}
  `(ReifyMExpr tEnv p t' me B m)
  `(ReifyMExpr tEnv (Datatypes.snd (Ctx.pext p t'))
               t (ke (Datatypes.fst (Ctx.pext p t')))
               A (fun c => k (Ctx.actx_tail c) (var0 p t' c (reifyMExpr_teq (Ctx.actx_tail c))))) :
  ReifyMExpr tEnv p t (bindE _ _ me ke) A (fun c => bindM (m c) (k c)).
Proof.
  unfold ReifyMExpr in *; cbn - [Ctx.ext]; unfold Ctx.inExt; intro.
  apply (eq_dep_bindM (H c)); intros.
  unfold reifyMExpr_teq, reifyMExpr_eq, var0 in H0.
  rewrite Ctx.actx_fst_add_eq.
  specialize (H0 (Ctx.actx_add c a)); cbn - [Ctx.ext] in H0.
  rewrite H0, Ctx.actx_head_add.
  enough ((k (Ctx.actx_tail (Ctx.actx_add c a))
             (rew [fun x : Set => x] eq_dep_eq1 (H (Ctx.actx_tail (Ctx.actx_add c a))) in a)) = (k c (rew [fun x : Set => x] eq_dep_eq1 (H c) in a))).
  - rewrite <- H1; reflexivity.
  - rewrite (actx_tail_add c a); reflexivity.
Qed.

Instance ReifyMExpr_errorE {tEnv p t s A}
  `(ReifyType tEnv t A) :
  ReifyMExpr tEnv p t (errorE _ _ s) A (fun _ => errorM s).
Proof.
  unfold ReifyMExpr, ReifyType in *; cbn; intros.
  rewrite H; reflexivity.
Qed.

Instance ReifyMExpr_eitherE {tEnv p} {t tl tr fe ge e A Al Ar f g x}
  `(ReifyType tEnv tl Al) `(ReifyType tEnv tr Ar)
  `(ReifyExpr tEnv p (EitherT tl tr) e (SAWCorePrelude.Either Al Ar) x)
  `(ReifyMExpr tEnv (Datatypes.snd (Ctx.pext p tl))
               t (fe (Datatypes.fst (Ctx.pext p tl)))
               A (fun c => f (Ctx.actx_tail c) (var0 p tl c reifyType_eq)))
  `(ReifyMExpr tEnv (Datatypes.snd (Ctx.pext p tr))
               t (ge (Datatypes.fst (Ctx.pext p tr)))
               A (fun c => g (Ctx.actx_tail c) (var0 p tr c reifyType_eq))) :
  ReifyMExpr tEnv p t (eitherE _ _ fe ge e)
                    A (fun c => SAWCorePrelude.either _ _ _ (f c) (g c) (x c)).
Proof.
  unfold ReifyMExpr, ReifyType, ReifyExpr in *;
    cbn - [Ctx.ext]; unfold Ctx.inExt; intro.
  unfold reifyMExpr_teq, reifyMExpr_eq, var0 in H2, H3.
  destruct H, H0.
  specialize (H1 c); apply eq_dep_eq in H1.
  rewrite H1; cbn - [Ctx.ext].
  eapply f_eq_dep_2 with (U := Set) (f := fun A l r => SAWCorePrelude.either (typeD tEnv tl) (typeD tEnv tr) (CompM A) l r (x c));
    apply @eq_dep_fun_ext with (U := Set) (P := CompM); intro.
  - specialize (H2 (Ctx.actx_add c x0)); cbn - [Ctx.ext] in H2.
    rewrite Ctx.actx_fst_add_eq, H2, Ctx.actx_head_add.
    rewrite (actx_tail_add c x0); reflexivity.
  - specialize (H3 (Ctx.actx_add c x0)); cbn - [Ctx.ext] in H3.
    rewrite Ctx.actx_fst_add_eq, H3, Ctx.actx_head_add.
    rewrite (actx_tail_add c x0); reflexivity.
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

Instance ReifyFMExpr_FunMT {tEnv p t fmt fe} {A : Set} {lrt f}
  `(ReifyType tEnv t A)
  `(ReifyFMExpr tEnv (Datatypes.snd (Ctx.pext p t))
                fmt (fe (Datatypes.fst (Ctx.pext p t)))
                lrt (fun c => f (Ctx.actx_tail c) (var0 p t c reifyType_eq))) :
  ReifyFMExpr tEnv p (FunMT t fmt) fe (LRT_Fun A (fun _ => lrt)) f.
Proof.
  unfold ReifyFMExpr, ReifyType in *;
    cbn - [Ctx.ext]; unfold Ctx.inExt; intro.
  unfold reifyMExpr_teq, reifyMExpr_eq, var0 in H0.
  destruct H.
  enough (eq_dep LetRecType (fun lrt => typeD tEnv t -> lrtToType lrt)
                 (fmtypeD tEnv fmt) (fun x => fmexprD tEnv (Datatypes.snd (Ctx.add (Ctx.innerCtx c) x))
                                                      (fe (Datatypes.fst (Ctx.add (Ctx.innerCtx c) x))))
                 lrt (f c))
    by (rewrite H; reflexivity).
  apply eq_dep_fun_ext; intro.
  specialize (H0 (Ctx.actx_add c x)); cbn - [Ctx.ext] in H0.
  rewrite Ctx.actx_fst_add_eq, H0, Ctx.actx_head_add.
  rewrite(actx_tail_add c x); reflexivity.
Qed.


(** * Tactics for reifying *)

Ltac reifyTac lemma P :=
  unshelve (eapply lemma; [typeclasses eauto|]); [try exact []|].

Lemma reifyType_lemma {tEnv t A} (P : Type -> Prop)
  `(ReifyType tEnv t A) :
  P (typeD tEnv t) -> P A.
Proof. rewrite reifyType_eq; eauto. Qed.

Ltac reifyType P := reifyTac reifyType_lemma P.

(* Lemma reifyExpr_lemma {tEnv p t e x} {P : string + typeD tEnv t -> Prop} *)
(*   `(ReifyExpr tEnv p t e x) c : *)
(*   P (exprD tEnv (Ctx.innerCtx c) e) -> P (inr (x c)). *)
(* Proof. rewrite reifyExpr_eq; eauto. Qed. *)

Lemma reifyExpr_lemma {tEnv t e A x} {P : forall (A : Set), string + A -> Prop}
  `(ReifyExpr tEnv Ctx.empty t e A (fun _ => x)) :
  P (typeD tEnv t) (exprD tEnv (Ctx.innerCtx Ctx.actx_empty) e) -> P A (inr x).
Proof. rewrite (H Ctx.actx_empty); eauto. Qed.

Ltac reifyExpr P := reifyTac reifyExpr_lemma P.

Lemma reifyMExpr_lemma {tEnv t me A m} {P : forall (A : Set), CompM A -> Prop}
  `(ReifyMExpr tEnv Ctx.empty t me A (fun _ => m)) :
  P (typeD tEnv t) (mexprD tEnv (Ctx.innerCtx Ctx.actx_empty) me) -> P A m.
Proof. rewrite (H Ctx.actx_empty); eauto. Qed.

Ltac reifyMExpr P := reifyTac reifyMExpr_lemma P.

Lemma reifyMExpr_refinesM_lemma {tEnv t me1 me2 A m1 m2}
  `(ReifyMExpr tEnv Ctx.empty t me1 A (fun _ => m1))
  `(ReifyMExpr tEnv Ctx.empty t me2 A (fun _ => m2)) :
  refinesM (mexprD tEnv (Ctx.innerCtx Ctx.actx_empty) me1)
           (mexprD tEnv (Ctx.innerCtx Ctx.actx_empty) me2) ->
  refinesM m1 m2.
Admitted.

Ltac reifyMExpr_refinesM :=
  unshelve (eapply reifyMExpr_refinesM_lemma;
            [ typeclasses eauto | typeclasses eauto |]);
  [try exact []|].

Lemma reifyFMExpr_lemma {tEnv fmt fme lrt f} {P : forall (lrt : LetRecType), lrtToType lrt -> Prop}
  `(ReifyFMExpr tEnv Ctx.empty fmt fme lrt (fun _ => f)) :
  P (fmtypeD tEnv fmt) (fmexprD tEnv (Ctx.innerCtx Ctx.actx_empty) fme) -> P lrt f.
Proof. rewrite (H Ctx.actx_empty); eauto. Qed.

Ltac reifyFMExpr P := reifyTac reifyFMExpr_lemma P.

Lemma reifyFMExpr_refinesFun_lemma {tEnv fmt fme1 fme2 lrt f1 f2}
  `(ReifyFMExpr tEnv Ctx.empty fmt fme1 lrt (fun _ => f1))
  `(ReifyFMExpr tEnv Ctx.empty fmt fme2 lrt (fun _ => f2)) :
  refinesFun (fmexprD tEnv (Ctx.innerCtx Ctx.actx_empty) fme1)
             (fmexprD tEnv (Ctx.innerCtx Ctx.actx_empty) fme2) ->
  refinesFun f1 f2.
Admitted.

Ltac reifyFMExpr_refinesFun :=
  unshelve (eapply reifyFMExpr_refinesFun_lemma;
            [ typeclasses eauto | typeclasses eauto |]);
  [try exact []|].

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
(*     P _ (returnM tt >>= (fun u => returnM u >>= (fun v => returnM v))). *)

(*   Opaque bindM. *)

(*   intros. *)
(*   eapply reifyMExpr_lemma. *)
(*   - eapply ReifyMExpr_bindE. *)

(*     + eapply ReifyExpr_Left. *)
(*       * typeclasses eauto. *)
(*       * eapply ReifyExpr_unknown. *)
(*     + eapply ReifyMExpr_returnM. *)
(*   Set Typeclasses Debug. *)
(*   try timeout 1 reifyMExpr P. *)

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
