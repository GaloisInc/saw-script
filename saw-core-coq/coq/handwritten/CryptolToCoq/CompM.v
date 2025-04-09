(***
 *** A version of the computation monad using the option-set monad
 ***)

From Coq Require Import Program.Basics.
From Coq Require Export Morphisms Setoid.
From Coq Require Import Strings.String.

(***
 *** The Monad Typeclasses
 ***)

(* The monad equivalence relation *)
Class MonadEqOp (M:Type -> Type) : Type :=
  eqM : forall {A}, M A -> M A -> Prop.

Infix "~=" := eqM (at level 70, no associativity).

(* The class for the monadic return operation *)
Class MonadReturnOp (M:Type -> Type) : Type :=
  returnM : forall {A}, A -> M A.

(* The class for the monadic bind operation *)
Class MonadBindOp (M:Type -> Type) : Type :=
  bindM : forall {A B}, M A -> (A -> M B) -> M B.

Infix ">>=" := bindM (at level 58, left associativity).
Notation "m1 >> m2" := (m1 >>= fun _ => m2) (at level 58, left associativity).

(* A monad is a collection of monad operations that satisfy the monad laws *)
Class Monad M `{MonadEqOp M} `{MonadReturnOp M} `{MonadBindOp M} : Prop :=
  { Equivalence_eqM :> forall A, Equivalence (eqM (A:=A));
    Proper_bindM :> forall A B,
        Proper (eqM (A:=A) ==> (pointwise_relation A (eqM (A:=B))) ==> eqM) bindM;
    returnM_bindM : forall A B a (f:A -> M B), returnM a >>= f ~= f a;
    bindM_returnM : forall A (m:M A), m >>= (fun x => returnM x) ~= m;
    bindM_bindM : forall A B C (m:M A) (f:A -> M B) (g:B -> M C),
        (m >>= f) >>= g ~= m >>= (fun x => f x >>= g) }.

(* This is not strictly necessary, but it speed up rewriting w.r.t. eq *)
Instance Proper_eq_bindM A B `{Monad} :
  Proper (eq ==> (pointwise_relation A (@eq (M B))) ==> eqM) bindM.
Proof.
  intros m1 m2 e_m; rewrite e_m.
  intros f1 f2 ef; eapply Proper_bindM; [ reflexivity | ].
  intros a; rewrite (ef _). reflexivity.
Qed.


(** Monads with Errors **)

(* The error operation *)
Class MonadErrorOp (M:Type -> Type) : Type :=
  errorM : forall {A}, string -> M A.

(* A monad with errors *)
Class MonadError M `{Monad M} `{MonadErrorOp M} : Prop :=
  { errorM_bindM : forall A B str (f:A -> M B), errorM str >>= f ~= errorM str }.


(** Monads with Fixed-points **)

(* The domain ordering for a fixed-point monad *)
Class MonadLeqOp (M:Type -> Type) : Type :=
  leqM : forall {A}, M A -> M A -> Prop.

(* The class for the fixed-point operation *)
Class MonadFixOp (M:Type -> Type) : Type :=
  fixM : forall {A B}, ((forall (a:A), M (B a)) -> (forall (a:A), M (B a))) ->
                       (forall (a:A), M (B a)).

(* Typeclass for dependent functions that respect the domain order *)
(* FIXME: this doesn't need to be a typeclass *)
Class ProperFixFun {A B M} `{MonadLeqOp M}
      (F:(forall (a:A), M (B a)) -> (forall (a:A), M (B a))) : Prop :=
  { properFixFun : forall f1 f2, (forall a, leqM (f1 a) (f2 a)) ->
                                 (forall a, leqM (F f1 a) (F f2 a)) }.

Class MonadFix M `{Monad M} `{MonadLeqOp M} `{MonadFixOp M} : Prop :=
  { PreOrder_leqM :> forall A, PreOrder (leqM (A:=A));
    (* FIXME: does this need Properness of F?
    Proper_fixM :> forall A B,
        Proper (((eq ==> eqM) ==> eq ==> eqM) ==> eq ==> eqM) (fixM (A:=A) (B:=B)); *)
    eqM_leqM : forall A (m1 m2:M A), m1 ~= m2 <-> leqM m1 m2 /\ leqM m2 m1;
    fixM_F_fixM : forall A (B:A -> Type) (F:(forall a, M (B a)) -> (forall a, M (B a)))
                         {prp:ProperFixFun F} a,
        eqM (fixM F a) (F (fixM F) a)
  }.


(***
 *** The Set Monad
 ***)

(* The set monad = the sets over a given type *)
Definition SetM (A:Type) : Type := A -> Prop.

(* Equivalence of two sets = they contain the same elements *)
Instance MonadEqOp_SetM : MonadEqOp SetM :=
  fun A m1 m2 => forall a, m1 a <-> m2 a.

Instance Equivalence_SetM_eqM A : Equivalence (@eqM SetM _ A).
Proof.
  split.
  { intros m a; reflexivity. }
  { intros m1 m2 eq_m a. symmetry. apply eq_m. }
  { intros m1 m2 m3 eq12 eq23 a. transitivity (m2 a); [ apply eq12 | apply eq23 ]. }
Qed.

(* Return for the set monad = the set with a single element *)
Instance MonadReturnOp_SetM : MonadReturnOp SetM :=
  fun A a a' => a = a'.

(* Bind for the set monad = set map + union *)
Instance MonadBindOp_SetM : MonadBindOp SetM :=
  fun A B m f b => exists2 a, m a & f a b.

Instance Monad_SetM : Monad SetM.
Proof.
  split; intros.
  { typeclasses eauto. }
  { intros m1 m2 Rm f1 f2 Rf b; split; unfold bindM; intros [ a in_m in_fa ];
      exists a; try (apply Rm; assumption);
        try apply (Rf a); assumption. }
  { split; unfold bindM, returnM; intro.
    { destruct H as [ x in_a in_fa ]. rewrite in_a. assumption. }
    { exists a; [ reflexivity | assumption ]. } }
  { split; unfold bindM, returnM; intro.
    { destruct H as [ x in_a in_fa ]. rewrite <- in_fa. assumption. }
    { exists a; [ assumption | reflexivity ]. } }
  { split; unfold bindM; intro.
    { destruct H as [ y [ x in_m in_fx ] in_gy ]. exists x; try assumption.
      exists y; assumption. }
    { destruct H as [ x in_m [ y in_fx in_gy ]]. exists y; try assumption.
      exists x; assumption. } }
Qed.


Instance MonadLeqOp_SetM : MonadLeqOp SetM :=
  fun A m1 m2 => forall a, m1 a -> m2 a.

(* The class for the fixed-point operation *)
Instance MonadFixOp_SetM : MonadFixOp SetM :=
  fun A B F a b => forall f, (forall a', leqM (F f a') (f a')) -> f a b.

(* Helper for splitting eqM on SetM into to leqM requirements *)
Lemma split_SetM_eqM A (m1 m2:SetM A) : leqM m1 m2 -> leqM m2 m1 -> eqM m1 m2.
Proof.
  intros l12 l21 a; split; [ apply l12 | apply l21 ].
Qed.

(* Helper for proving that fixM is a fixed-point: that fixM F is F-closed *)
Lemma SetM_fixM_F_closed {A B} F {prp:ProperFixFun (A:=A) (B:=B) F} a :
  leqM (F (fixM F) a) (fixM F a).
Proof.
  intros b in_F_fixM f f_F_closed. apply f_F_closed.
  refine (properFixFun (F:=F) (fixM F) f _ a _ in_F_fixM).
  intros a' b' in_fixM_b'. apply (in_fixM_b' f f_F_closed).
Qed.

(* Helper for proving that fixM is a fixed-point: that fixM F is <= any F-closed f *)
Lemma SetM_fixM_leq_F_closed A B (F:(forall (a:A), SetM (B a)) -> forall a, SetM (B a)) f :
  (forall a, leqM (F f a) (f a)) -> forall a, leqM (fixM F a) (f a).
Proof.
  intros f_F_closed a b fixM_ab. apply (fixM_ab f f_F_closed).
Qed.


Instance MonadFix_SetM : MonadFix SetM.
Proof.
  split.
  { intro A; split.
    { intros m a m_a; assumption. }
    { intros m1 m2 m3 l12 l23 a m1_a. apply l23. apply l12. assumption. } }
  (* FIXME: finish proving that fixM is Proper
  { intros A B F1 F2 RF a1 a2 Ra b. rewrite Ra.
    split; intro Fab; apply Fab; intros a' b' F_fixM_a'b'.
    { apply Fab. *)
  { intros A m1 m2; split.
    { intros eq12; split; intro a; destruct (eq12 a); assumption. }
    { intros [leq12 leq21] a; split; [ apply leq12 | apply leq21 ]. } }
  { intros A B F prp a. apply split_SetM_eqM.
    { revert a. apply SetM_fixM_leq_F_closed. intro a.
      apply properFixFun. intro a'. apply SetM_fixM_F_closed. assumption. }
    { apply SetM_fixM_F_closed. assumption. } }
Qed.


(***
 *** The Option Monad Transformer
 ***)

(* The option transformer just adds "option" around the type A *)
Definition OptionT (M:Type -> Type) (A:Type) : Type := M (option A).

(* Equivalence in OptionT is just the underlying equivlence *)
Instance MonadEqOp_OptionT M `{MonadEqOp M} : MonadEqOp (OptionT M) :=
  fun A m1 m2 => eqM (A:=option A) m1 m2.

(* Return for the option monad = underlying return of Some *)
Instance MonadReturnOp_OptionT M `{MonadReturnOp M} : MonadReturnOp (OptionT M) :=
  fun A a => returnM (Some a).

(* Bind for the option monad = pattern-match *)
Instance MonadBindOp_OptionT M `{MonadReturnOp M} `{MonadBindOp M} : MonadBindOp (OptionT M) :=
  fun A B m f =>
    bindM (A:=option A) m
          (fun opt_a =>
             match opt_a with
             | Some a => f a
             | None => returnM None
             end).

Instance Monad_OptionT M `{Monad M} : Monad (OptionT M).
Proof.
  split.
  { intro A; apply (Equivalence_eqM (option A)). }
  { intros A B m1 m2 Rm f1 f2 Rf.
    apply (Proper_bindM (M:=M)); [ assumption | ].
    intros opt_a; destruct opt_a; [ apply Rf | ]; reflexivity. }
  { intros.
    unfold returnM, MonadReturnOp_OptionT, bindM, MonadBindOp_OptionT.
    unfold eqM, MonadEqOp_OptionT.
    rewrite (returnM_bindM (M:=M)). reflexivity. }
  { intros.
    unfold returnM, MonadReturnOp_OptionT, bindM, MonadBindOp_OptionT.
    unfold eqM, MonadEqOp_OptionT.
    etransitivity; [ | apply (bindM_returnM (M:=M)) ].
    apply Proper_bindM; [ reflexivity | ].
    intros opt; destruct opt; reflexivity. }
  { intros.
    unfold returnM, MonadReturnOp_OptionT, bindM, MonadBindOp_OptionT;
      unfold eqM, MonadEqOp_OptionT.
    rewrite (bindM_bindM (M:=M)).
    apply Proper_bindM; [ reflexivity | ].
    intros opt_a; destruct opt_a.
    { apply Proper_bindM; [ reflexivity | ].
      intros opt_b; destruct opt_b; reflexivity. }
    { rewrite returnM_bindM. reflexivity. } }
Qed.


Instance MonadErrorOp_OptionT M `{MonadReturnOp M} : MonadErrorOp (OptionT M) :=
  fun A _ => returnM None.

Instance MonadError_OptionT M `{Monad M} : MonadError (OptionT M).
Proof.
  split.
  { intros.
    unfold errorM, MonadErrorOp_OptionT, bindM, MonadBindOp_OptionT.
    rewrite returnM_bindM. reflexivity. }
Qed.


Instance MonadLeqOp_OptionT M `{MonadLeqOp M} : MonadLeqOp (OptionT M) :=
  fun A m1 m2 => leqM (M:=M) m1 m2.

Instance MonadFixOp_OptionT M `{MonadFixOp M} : MonadFixOp (OptionT M) :=
  fun A B F a => fixM (M:=M) F a.

Instance MonadFix_OptionT M `{MonadFix M} : MonadFix (OptionT M).
Proof.
  split.
  { intros A; apply (PreOrder_leqM (M:=M)). }
  { intros. apply (eqM_leqM (M:=M)). }
  { intros. apply (fixM_F_fixM (M:=M) _ (fun a => option (B a))).
    constructor. apply (properFixFun (ProperFixFun:=prp)). }
Qed.


(***
 *** The Set of Sets Monad
 ***)

(*
FIXME: can we get this to work as a predicate monad for SetM?
- The hard part is defining bindM: the current version fails associativity
  because it requires finding a choice function
- I could imagine P >> Q is the union over all Q a for any a in mA in P, or the
  union_(s in P) (intersection_(a in s) (Q a))
- But all of these have issues!
- e.g., if P contains the empty set, so should P >>= Q!

(* A SetSetM computation is a set of subsets of a type *)
Definition SetSetM (A:Type) := SetM A -> Prop.

(* Close off a SetSetM under extensional equivalence *)
Definition inSetSetM {A} (P:SetSetM A) : SetSetM A :=
  fun m => exists2 m', m' ~= m & P m'.

(* Equivalence of two sets = they contain the same elements *)
Instance MonadEqOp_SetSetM : MonadEqOp SetSetM :=
  fun A P1 P2 => forall m, inSetSetM P1 m <-> inSetSetM P2 m.

Instance Proper_eqM_inSetSetM {A} :
  Proper (eqM ==> eqM ==> iff) (inSetSetM (A:=A)).
Proof.
  intros P1 P2 eqP m1 m2 eqm.
  split; intros [ m' eq_m' in_m' ]; apply eqP; exists m'; try assumption.
  - transitivity m1; assumption.
  - transitivity m2; [ | symmetry ]; assumption.
Qed.

Instance Equivalence_SetSetM_eqM A : Equivalence (eqM (M:=SetSetM) (A:=A)).
Proof.
  split.
  { intros m a; reflexivity. }
  { intros m1 m2 eq_m a. symmetry. apply eq_m. }
  { intros m1 m2 m3 eq12 eq23 a. etransitivity; [ apply eq12 | apply eq23 ]. }
Qed.

Instance MonadReturnOp_SetSetM : MonadReturnOp SetSetM :=
  fun A a m => m ~= returnM a.

Lemma SetSetM_returnM A (m:SetM A) a :
  inSetSetM (returnM a) m <-> m ~= returnM a.
Proof.
  split.
  - intros [ m' eq_m' in_P ]. transitivity m'; [ symmetry; assumption | apply in_P ].
  - intro e_m; exists (returnM a); [ symmetry; assumption | intro; reflexivity ].
Qed.

Instance MonadBindOp_SetSetM : MonadBindOp SetSetM :=
  fun A B P Q m =>
    exists2 mA, inSetSetM P mA &
                exists2 f, (forall a, mA a -> inSetSetM (Q a) (f a)) &
                           m ~= mA >>= f.

Lemma SetSetM_bindM_elim {A B P} {Q:A -> SetSetM B} {m} :
  inSetSetM (P >>= Q) m ->
  exists2 mA, inSetSetM P mA &
              exists2 f, (forall a, mA a -> inSetSetM (Q a) (f a)) & m ~= mA >>= f.
Proof.
  intros [ m' eq_m [ mA in_P_mA [ f in_Q_f eq_m' ]]].
  exists mA; [ assumption | ].
  exists f; [ apply in_Q_f | ].
  rewrite <- eq_m; assumption.
Qed.


Lemma SetSetM_bindM_intro {A B P} {Q:A -> SetSetM B} {m} mA f :
  inSetSetM P mA -> (forall a, mA a -> inSetSetM (Q a) (f a)) -> m ~= mA >>= f ->
  inSetSetM (P >>= Q) m.
Proof.
  intros [ mA' eq_mA in_mA' ] in_Q_f eq_m.
  exists (mA >>= f); [ symmetry; assumption | ].
  exists mA; [ exists mA'; assumption | ].
  exists f; [ | reflexivity ]. apply in_Q_f.
Qed.

Instance Monad_SetSetM : Monad SetSetM.
Proof.
  split; intros.
  { typeclasses eauto. }
  { intros P1 P2 RP Q1 Q2 RQ m; split;
      intros [ m' eq_m [ mA in_P_mA [ f in_Q_f eq_m' ] ] ];
      exists m'; try assumption; exists mA; try (apply RP; assumption);
        exists f; try assumption;
          intros a in_mA; apply (RQ a a eq_refl); apply in_Q_f; assumption. }
  { intro m; split.
    { intro in_m.
      destruct (SetSetM_bindM_elim in_m) as [ mA in_mA [ g in_g eq_m ]].
      rewrite eq_m.
      rewrite SetSetM_returnM in in_mA. rewrite in_mA. rewrite returnM_bindM.
      apply in_g. rewrite (in_mA a). apply eq_refl. }
    { intro in_m. apply (SetSetM_bindM_intro (returnM a) (fun _ => m)).
      - apply SetSetM_returnM; reflexivity.
      - intros a' eq_a_a'; compute in eq_a_a'. rewrite <- eq_a_a'. assumption.
      - rewrite returnM_bindM. reflexivity. } }
  { intro s; split.
    { intro in_s.
      destruct (SetSetM_bindM_elim in_s) as [ mA in_mA [ g in_g eq_s ]].
      assert (eq_s_mA : s ~= mA); [ | rewrite eq_s_mA; assumption ].
      transitivity (mA >>= g); [ assumption | ].
      transitivity (mA >>= returnM); [ | apply bindM_returnM ].
      intro a; split; intros [ a' in_a' in_f_a' ]; exists a'; try assumption.
      - destruct (in_g a' in_a') as [ s' eq_s' in_s'].
        rewrite <- (in_s' a). rewrite (eq_s' a). assumption.
      - destruct (in_g a' in_a')  as [ s' eq_s' in_s'].
        rewrite <- (eq_s' a). apply in_s'. assumption. }
    { intros [ s' eq_s' in_m_s' ]. exists s'; [ assumption | ].
      exists s'; [ exists s'; [ reflexivity | assumption ] | ].
      exists returnM; [ | symmetry; apply bindM_returnM ].
      intros a in_s'. exists (returnM a); [ reflexivity | ].
      intro a'; reflexivity. } }
  { intro sC; split; intro in_sC.
    { destruct (SetSetM_bindM_elim in_sC) as [ sB in_sB [ sg in_sg eq_sC ]].
      destruct (SetSetM_bindM_elim in_sB) as [ sA in_sA [ sf in_sf eq_sB ]].
      apply (SetSetM_bindM_intro sA (fun x => sf x >>= sg)); try assumption;
        [ | rewrite eq_sC; rewrite eq_sB; rewrite bindM_bindM; reflexivity ].
      intros a in_a.
      apply (SetSetM_bindM_intro (sf a) sg); [ apply in_sf; assumption | | reflexivity ].
      intros b in_b. apply in_sg. rewrite (eq_sB b).
      exists a; assumption. }
    { destruct (SetSetM_bindM_elim in_sC) as [ sA in_sA [ sfg in_sfg eq_sC ]].
      apply (SetSetM_bindM_intro sA sfg).


      admit. } }

      apply (SetSetM_bindM_intro sA sfg); try assumption.

      destruct (SetSetM_bindM_elim in_sB) as [ sA in_sA [ sf in_sf eq_sB ]].

    intros [ sC' eq_sC' [ sB [ sB' eq_sB' [ sA eq_sA in_sA ] ] eq_sB ] ]. destruct in_sC'.
 *)


(***
 *** The Computation Monad = the Option-Set Monad
 ***)

Definition CompM : Type -> Type := OptionT SetM.


(***
 *** Letrec and Mutual Fixed-points in CompM
 ***)

(* An inductive description of a type A1 -> A2 -> ... -> An -> CompM B *)
Inductive LetRecType : Type :=
| LRT_Ret (B:Type) : LetRecType
| LRT_Fun (A:Type) (lrtF:A -> LetRecType) : LetRecType
.

(* Convert a LetRecType to the type it represents *)
Fixpoint lrtToType (lrt:LetRecType) : Type :=
  match lrt with
  | LRT_Ret B => CompM B
  | LRT_Fun A lrtF => forall a, lrtToType (lrtF a)
  end.

(* Convert the argument types of a LetRecType to their "flat" version of the
form { x1:A1 & { x2:A2 & ... { xn:An & unit } ... }} *)
Fixpoint lrtToFlatArgs (lrt:LetRecType) : Type :=
  match lrt with
  | LRT_Ret _ => unit
  | LRT_Fun A lrtF => sigT (fun (a:A) => lrtToFlatArgs (lrtF a))
  end.

(* Get the dependent return type fun (args:lrtToFlatArgs) => B x.1 ... of
a LetRecType in terms of the flat arguments *)
Fixpoint lrtToFlatRet (lrt:LetRecType) : lrtToFlatArgs lrt -> Type :=
  match lrt return lrtToFlatArgs lrt -> Type with
  | LRT_Ret B => fun _ => B
  | LRT_Fun A lrtF =>
    fun args => lrtToFlatRet (lrtF (projT1 args)) (projT2 args)
  end.

(* Extract out the "flat" version of a LetRecType *)
Definition lrtToFlatType lrt :=
  forall (args:lrtToFlatArgs lrt), CompM (lrtToFlatRet lrt args).

(* "Flatten" a function described by a LetRecType *)
Fixpoint flattenLRTFun lrt : lrtToType lrt -> lrtToFlatType lrt :=
  match lrt return lrtToType lrt -> lrtToFlatType lrt with
  | LRT_Ret _ => fun f _ => f
  | LRT_Fun A lrtF =>
    fun f args => flattenLRTFun (lrtF (projT1 args)) (f (projT1 args)) (projT2 args)
  end.

(* "Unflatten" a function described by a LetRecType *)
Fixpoint unflattenLRTFun lrt : lrtToFlatType lrt -> lrtToType lrt :=
  match lrt return lrtToFlatType lrt -> lrtToType lrt with
  | LRT_Ret _ => fun f => f tt
  | LRT_Fun A lrtF =>
    fun f a => unflattenLRTFun (lrtF a) (fun args => f (existT _ a args))
  end.

(* A list of types (FIXME: use a Coq list?) *)
Inductive LetRecTypes : Type :=
| LRT_Nil : LetRecTypes
| LRT_Cons : LetRecType -> LetRecTypes -> LetRecTypes
.

(* Construct type type (F1, (F2, ... (Fn, unit) .. )) from a LetRecTypes list of
descriptions of the types F1, ..., Fn *)
Fixpoint lrtTupleType (lrts:LetRecTypes) : Type :=
  match lrts with
  | LRT_Nil => unit
  | LRT_Cons lrt lrts' => prod (lrtToType lrt) (lrtTupleType lrts')
  end.

(* Construct type type F1 -> ... -> Fn -> B from a LetRecTypes list of
descriptions of the types F1, ..., Fn *)
Fixpoint lrtPi (lrts:LetRecTypes) (B:Type) : Type :=
  match lrts with
  | LRT_Nil => B
  | LRT_Cons lrt lrts' => lrtToType lrt -> lrtPi lrts' B
  end.

(* Construct a multi-arity function of type lrtPi lrts B from one of type
lrtTupleType lrts -> B *)
Fixpoint lrtLambda {lrts B} : (lrtTupleType lrts -> B) -> lrtPi lrts B :=
  match lrts return (lrtTupleType lrts -> B) -> lrtPi lrts B with
  | LRT_Nil => fun F => F tt
  | LRT_Cons _ lrts' => fun F f => lrtLambda (fun fs => F (f, fs))
  end.

(* Apply a multi-arity function of type lrtPi lrts B to an lrtTupleType lrts *)
Fixpoint lrtApply {lrts B} : lrtPi lrts B -> lrtTupleType lrts -> B :=
  match lrts return lrtPi lrts B -> lrtTupleType lrts -> B with
  | LRT_Nil => fun F _ => F
  | LRT_Cons _ lrts' => fun F fs => lrtApply (F (fst fs)) (snd fs)
  end.

(* Build a multi-argument fixed-point of type A1 -> ... -> An -> CompM B *)
Definition multiArgFixM (lrt:LetRecType) (F:lrtToType lrt ->
                                            lrtToType lrt) : lrtToType lrt :=
  unflattenLRTFun
    lrt
    (fixM (fun f => flattenLRTFun lrt (F (unflattenLRTFun lrt f)))).

(* Construct a mutual fixed-point over tuples of LRT functions *)
Fixpoint multiTupleFixM (lrts:LetRecTypes) : (lrtTupleType lrts -> lrtTupleType lrts) ->
                                             lrtTupleType lrts :=
  match lrts return (lrtTupleType lrts -> lrtTupleType lrts) -> lrtTupleType lrts with
  | LRT_Nil => fun _ => tt
  | LRT_Cons lrt lrts' =>
    fun F =>
      let f1 := multiArgFixM lrt (fun f => fst (F (f, multiTupleFixM lrts' (fun fs => snd (F (f, fs)))))) in
      (f1, multiTupleFixM lrts' (fun fs => snd (F (f1, fs))))
  end.

(* A nicer version of multiTupleFixM that abstracts the functions one at a time *)
Definition multiFixM {lrts:LetRecTypes}
           (F:lrtPi lrts (lrtTupleType lrts)) : lrtTupleType lrts :=
  multiTupleFixM lrts (fun fs => lrtApply F fs).

(* A letrec construct for binding 0 or more mutually recursive functions *)
Definition letRecM (lrts : LetRecTypes) {B} (F: lrtPi lrts (lrtTupleType lrts))
           (body:lrtPi lrts (CompM B)) : CompM B :=
  lrtApply body (multiFixM F).


(***
 *** Refinement Proofs
 ***)

Definition refinesM {A} (m1 m2:CompM A) : Prop := forall a, m1 a -> m2 a.

Infix "|=" := refinesM (at level 70, no associativity).

Instance PreOrder_refinesM A : PreOrder (refinesM (A:=A)).
Proof.
  split.
  { intros m a in_a; assumption. }
  { intros m1 m2 m3 R12 R23 a in_m1. apply R23. apply R12. assumption. }
Qed.

Instance Proper_eqM_refinesM A : Proper (eqM ==> eqM ==> iff) (refinesM (A:=A)).
Proof.
  intros m1 m1' e1 m2 m2' e2.
  split; intros R12 a in_a; apply e2; apply R12; apply e1; assumption.
Qed.

Instance Proper_refinesM_bindM A B :
  Proper (refinesM ==> (pointwise_relation A refinesM) ==> refinesM) (bindM (A:=A) (B:=B)).
Proof.
  intros m1 m2 Rm f1 f2 Rf opt_b [ opt_a in_opt_a in_opt_b ].
  exists opt_a; [ apply Rm; assumption | ].
  destruct opt_a; [ | assumption ].
  apply (Rf a); assumption.
Qed.

Lemma refinesM_returnM A (a1 a2:A) : a1 = a2 -> returnM a1 |= returnM a2.
Proof.
  intro e; rewrite e. reflexivity.
Qed.

Lemma refinesM_errorM_returnM A s (a:A) : ~ errorM s |= returnM a.
Proof.
  intro H; vm_compute in H.
  apply (fun H => H None eq_refl) in H.
  discriminate H.
Qed.

Lemma refinesM_returnM_errorM A (a:A) s : ~ returnM a |= errorM s.
Proof.
  intro H; vm_compute in H.
  apply (fun H => H (Some a) eq_refl) in H.
  discriminate H.
Qed.

(* If a monadic function f is F-closed w.r.t. the refinement relation, then the
least fixed-point of F refines f *)
Lemma refinesM_fixM_l A B (F : (forall (a:A), CompM (B a)) ->
                             (forall (a:A), CompM (B a))) f :
  (forall a, F f a |= f a) -> forall a, fixM F a |= f a.
Proof.
  intros F_closed a opt_b in_fix.
  apply in_fix. intros a' opt_b' in_F. apply F_closed. apply in_F.
Qed.

Lemma refinesM_fixM_lr A B (F G : (forall (a:A), CompM (B a)) ->
                                  (forall (a:A), CompM (B a))) :
  (forall f a, F f a |= G f a) -> forall a, fixM F a |= fixM G a.
Proof.
  intros leq_FG a opt_b in_fixF f G_closed.
  apply (refinesM_fixM_l _ _ F); [ | assumption ].
  intros a' opt_b' in_F. apply G_closed. apply leq_FG. assumption.
Qed.

(* Lift refinesM to monadic functions *)
Fixpoint refinesFun {lrt} : relation (lrtToType lrt) :=
  match lrt return relation (lrtToType lrt) with
  | LRT_Ret B => refinesM
  | LRT_Fun A lrtF => forall_relation (fun a => @refinesFun (lrtF a))
  end.

Instance PreOrder_refinesFun lrt : PreOrder (@refinesFun lrt).
Proof.
  induction lrt.
  - apply PreOrder_refinesM.
  - split.
    { intros f a. reflexivity. }
    { intros f1 f2 f3 H1 H2 a. transitivity (f2 a); [ apply H1 | apply H2 ]. }
Qed.

Instance subrelation_forall_const_pointwise A B (R : relation B)
  : subrelation (forall_relation (fun _ => R)) (pointwise_relation A R).
Proof. vm_compute; auto. Qed.

(* A convenient specialization of refinesFun *)
Definition refinesFun1 {A} {B:A -> Type} : (forall a, CompM (B a)) -> (forall a, CompM (B a)) -> Prop :=
  refinesFun (lrt:=LRT_Fun _ (fun _ => LRT_Ret _)).

(* Lift refinesM to tuples of monadic functions *)
Fixpoint refinesFunTuple {lrts} : relation (lrtTupleType lrts) :=
  match lrts return relation (lrtTupleType lrts) with
  | LRT_Nil => fun _ _ => True
  | LRT_Cons lrt lrts' =>
    fun tup1 tup2 => refinesFun (fst tup1) (fst tup2) /\
                     refinesFunTuple (snd tup1) (snd tup2)
  end.

Fixpoint respectfulLRTPi {lrts} {B} : relation (lrtPi lrts (CompM B)) :=
  match lrts with
  | LRT_Nil => refinesM
  | LRT_Cons _ _ => respectful refinesFun respectfulLRTPi
  end.

(* `ProperLRTFun F` is just `Proper (refinesFun ==> ... ==> refinesFun ==> refinesM) F` *)
Class ProperLRTFun {lrts} {B} (F : lrtPi lrts (CompM B)) : Prop :=
  { properLRTFun : Proper respectfulLRTPi F }.

(* All constant functions are proper *)
Instance ProperLRTFun_const lrts B b : @ProperLRTFun lrts B (lrtLambda (fun _ => b)).
Proof.
  split; induction lrts; vm_compute; intros; assumption.
Qed.

(* FIXME Get rid of this *)
Instance ProperLRTFun_any lrts B F : @ProperLRTFun lrts B F.
Proof.
  admit. (* FIXME *)
Admitted.

Instance Proper_lrtApply lrts B
  : Proper (respectfulLRTPi ==> refinesFunTuple ==> refinesM) (@lrtApply lrts (CompM B)).
Proof.
  unfold Proper, respectful; intros F G H1 fs gs H2.
  induction lrts; simpl in F,G,H1,fs,gs,H2; simpl.
  - exact H1.
  - destruct fs as [f fs]; destruct gs as [g gs]; destruct H2 as [H2 H3]; simpl in *.
    apply IHlrts.
    + unfold respectful in H1.
      apply H1.
      assumption.
    + assumption.
Qed.

Lemma refinesFunTuple_multiFixM lrts (F:lrtPi lrts (lrtTupleType lrts)) tup :
  refinesFunTuple (lrtApply F tup) tup -> refinesFunTuple (multiFixM F) tup.
Proof.
  admit. (* FIXME *)
Admitted.

Lemma refinesFun_multiFixM_fst lrt (F:lrtPi (LRT_Cons lrt LRT_Nil)
                                            (lrtTupleType (LRT_Cons lrt LRT_Nil))) f
      (ref_f:refinesFun (fst (F f)) f) :
  refinesFun (fst (multiFixM F)) f.
Proof.
  refine (proj1 (refinesFunTuple_multiFixM (LRT_Cons lrt LRT_Nil) _ (f, tt) _)).
  split; [ | constructor ].
  apply ref_f.
Qed.

Lemma letRecM_Nil B F P : @letRecM LRT_Nil B F P = P.
Proof.
  reflexivity.
Qed.

Lemma refinesM_letRecM_Nil_l B F P Q : P |= Q -> @letRecM LRT_Nil B F P |= Q.
Proof.
  rewrite letRecM_Nil. trivial.
Qed.

Lemma multiFixM_const lrts fs
  : multiFixM (lrts:=lrts) (lrtLambda (fun _ => fs)) = fs.
Proof.
  admit. (* FIXME *)
Admitted.

Lemma refinesM_letRecM_const_r lrts B (F : lrtPi lrts (lrtTupleType lrts))
                               (G : lrtTupleType lrts) (P Q : lrtPi lrts (CompM B))
                               `{ProperLRTFun _ _ P} `{ProperLRTFun _ _ Q}
  : refinesFunTuple (multiFixM F) G ->
    lrtApply P G |= lrtApply Q G ->
    @letRecM lrts B F P |= @letRecM lrts B (lrtLambda (fun _ => G)) Q.
Proof.
  destruct H as [ProperP]; destruct H0 as [ProperQ].
  intros.
  unfold letRecM.
  rewrite H, H0, multiFixM_const.
  reflexivity.
Qed.

Lemma lrtApply_const lrts B (b : B) (F : lrtTupleType lrts)
  : lrtApply (lrts:=lrts) (lrtLambda (fun _ => b)) F = b.
Proof.
  induction lrts.
  - reflexivity.
  - destruct F as [ F0 F1 ].
    simpl; rewrite (IHlrts F1).
    reflexivity.
Qed.

Lemma refinesM_letRecM_match_r lrts B F P Q `{ProperLRTFun _ _ P}
  : forall (G : lrtTupleType lrts),
    @letRecM lrts B F P |= @letRecM lrts B (lrtLambda (fun _ => G)) (lrtLambda (fun _ => Q)) ->
    @letRecM lrts B F P |= Q.
Proof.
  intros.
  rewrite H0.
  unfold letRecM.
  rewrite lrtApply_const.
  reflexivity.
Qed.

Lemma refinesM_if_l {A} (m1 m2:CompM A) b P :
  (b = true -> m1 |= P) -> (b = false -> m2 |= P) ->
  (if b then m1 else m2) |= P.
Proof.
  intros ref1 ref2; destruct b; [ apply ref1 | apply ref2 ]; reflexivity.
Qed.

Lemma refinesM_if_r {A} (m1 m2:CompM A) b P :
  (b = true -> P |= m1) -> (b = false -> P |= m2) ->
  P |= (if b then m1 else m2).
Proof.
  intros ref1 ref2; destruct b; [ apply ref1 | apply ref2 ]; reflexivity.
Qed.

Lemma simpl_letRecM0 B F body : @letRecM LRT_Nil B F body = body.
Proof.
  reflexivity.
Qed.

Lemma refinesM_sigT_rect_l {A1 A2 B} F P (s: {x:A1 & A2 x}) :
  (forall a1 a2, s = existT _ a1 a2 -> F a1 a2 |= P) ->
  sigT_rect (fun _ => CompM B) F s |= P.
Proof.
  destruct s; intros.
  apply H. reflexivity.
Qed.

Lemma refinesM_sigT_rect_r {A1 A2 B} F P (s: {x:A1 & A2 x}) :
  (forall a1 a2, s = existT _ a1 a2 -> P |= F a1 a2) ->
  P |= sigT_rect (fun _ => CompM B) F s.
Proof.
  destruct s; intros.
  apply H. reflexivity.
Qed.


(** Existential Specifications **)

Definition existsM {A B} (P: A -> CompM B) : CompM B :=
  fun b => exists a, P a b.

Lemma refinesM_existsM_r {A B} (P: A -> CompM B) m a :
  m |= (P a) -> m |= (existsM P).
Proof.
  intros r b in_b. exists a. apply r. assumption.
Qed.

Lemma refinesM_existsM_l A B (P: A -> CompM B) Q :
  (forall a, P a |= Q) -> existsM P |= Q.
Proof.
  intros r b [ a in_b ]. apply (r a). assumption.
Qed.

Lemma refinesM_existsM_lr A B (P Q : A -> CompM B) :
  (forall a, P a |= Q a) -> existsM P |= existsM Q.
Proof.
  intros r b [ a in_b ]. exists a. apply r. assumption.
Qed.

Lemma existsM_bindM A B C (P: A -> CompM B) (Q: B -> CompM C) :
  (existsM P) >>= Q ~= existsM (fun x => P x >>= Q).
Proof.
  intros c; split.
  - intros [ opt_b [ a in_b ] in_c ]. exists a. exists opt_b; assumption.
  - intros [ a [ opt_b in_b in_c ] ]. exists opt_b; [ | assumption ].
    exists a; assumption.
Qed.

Definition noErrorsSpec {A} : CompM A := existsM (fun a => returnM a).
Arguments noErrorsSpec /.


(** Universal Specifications **)

Definition forallM {A B} (P: A -> CompM B) : CompM B :=
  fun b => forall a, P a b.

Lemma refinesM_forallM_r {A B} P (Q: A -> CompM B) :
  (forall a, P |= (Q a)) -> P |= (forallM Q).
Proof.
  intros r b in_b a. apply r. assumption.
Qed.

Lemma refinesM_forallM_l {A B} (P: A -> CompM B) Q a :
  P a |= Q -> forallM P |= Q.
Proof.
  intros r b in_b. apply r. apply in_b.
Qed.

(* NOTE: the other direction does not hold *)
Lemma forallM_bindM A B C (P: A -> CompM B) (Q: B -> CompM C) :
  refinesM ((forallM P) >>= Q) (forallM (fun x => P x >>= Q)).
Proof.
  intros c [ opt_b H ] a. exists opt_b; [ apply (H _) | assumption ].
Qed.


(** Conjuctive and disjunctive specifications **)

Definition orM {A} (m1 m2 : CompM A) : CompM A :=
  fun b => m1 b \/ m2 b.

Lemma refinesM_orM_r {A} (m1 m2 : CompM A) P :
  P |= m1 \/ P |= m2 -> P |= (orM m1 m2).
Proof.
  intros r b in_b; destruct r; [ left | right ]; apply H; assumption.
Qed.

Lemma refinesM_orM_l {A} (m1 m2 : CompM A) P :
  m1 |= P -> m2 |= P -> orM m1 m2 |= P.
Proof.
  intros r1 r2 b in_b; destruct in_b; [ apply r1 | apply r2 ]; assumption.
Qed.

Lemma orM_bindM A B (m1 m2 : CompM A) (P : A -> CompM B) :
  (orM m1 m2) >>= P ~= orM (m1 >>= P) (m2 >>= P).
Proof.
  intros c; split.
  - intros [ opt_b [ r1 | r2 ] in_c ]; [ left | right ]; exists opt_b; assumption.
  - intros [ [ opt_b in_b in_c ] | [ opt_b in_b in_c ] ]; (exists opt_b; [ | assumption ]);
    [ left | right ]; assumption.
Qed.

Definition andM {A} (m1 m2:CompM A) : CompM A :=
  fun b => m1 b /\ m2 b.

Lemma refinesM_andM_r {A} (m1 m2 : CompM A) P :
  P |= m1 -> P |= m2 -> P |= andM m1 m2.
Proof.
  intros r1 r2 b in_b. split; [ apply r1 | apply r2 ]; assumption.
Qed.

Lemma refinesM_andM_l {A} (m1 m2 : CompM A) P :
  m1 |= P \/ m2 |= P -> andM m1 m2 |= P.
Proof.
  intros r b in_b; destruct r; destruct in_b; apply H; assumption.
Qed.

Lemma andM_bindM A B (m1 m2 : CompM A) (P : A -> CompM B) :
  refinesM ((andM m1 m2) >>= P) (andM (m1 >>= P) (m2 >>= P)).
Proof.
  intros c [ opt_b [ r1 r2 ] in_c ]; split; exists opt_b; assumption.
Qed.


(** Assertions and Assumptions **)

Definition assertM (P:Prop) : CompM unit :=
  existsM (fun pf:P => returnM tt).

Definition assertingM {A} (P:Prop) (m:CompM A) : CompM A :=
  assertM P >> m.

Definition assertM_eq (P:Prop) (pf:P) : assertM P ~= returnM tt.
Proof.
  intro opt_a; split.
  - intros [ _ H ]; assumption.
  - intros H. exists pf. assumption.
Qed.

Lemma refinesM_bindM_assertM_r {A} (P:Prop) (m1 m2: CompM A) :
  P -> m1 |= m2 -> m1 |= assertM P >> m2.
Proof.
  intro pf; rewrite (assertM_eq P pf). rewrite returnM_bindM. intro; assumption.
Qed.

Lemma refinesM_bindM_assertM_l {A} (P:Prop) (m1 m2: CompM A) :
  (P -> m1 |= m2) -> assertM P >> m1 |= m2.
Proof.
  intro H. unfold assertM; rewrite existsM_bindM.
  apply refinesM_existsM_l.
  rewrite returnM_bindM; assumption.
Qed.

Definition assumingM {A} (P:Prop) (m:CompM A) : CompM A :=
  forallM (fun pf:P => m).

Lemma refinesM_assumingM_r {A} (P:Prop) (m1 m2: CompM A) :
  (P -> m1 |= m2) -> m1 |= assumingM P m2.
Proof.
  apply refinesM_forallM_r.
Qed.

Lemma refinesM_assumingM_l {A} (P:Prop) (m1 m2 : CompM A) :
  P -> m1 |= m2 -> assumingM P m1 |= m2.
Proof.
  apply refinesM_forallM_l.
Qed.

(* NOTE: the other direction does not hold *)
Lemma assumingM_bindM {A B} (P:Prop) (m: CompM A) (Q: A -> CompM B) :
  refinesM ((assumingM P m) >>= Q) (assumingM P (m >>= Q)).
Proof.
  apply forallM_bindM.
Qed.
