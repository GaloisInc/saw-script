(***
 *** A version of the computation monad using the option-set monad
 ***)

From Coq Require Export Morphisms Setoid.

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

(* A monad is a collection of monad operations that satisfy the monad laws *)
Class Monad M `{MonadEqOp M} `{MonadReturnOp M} `{MonadBindOp M} : Prop :=
  { Equivalence_eqM :> forall A, Equivalence (eqM (A:=A));
    Proper_bindM :> forall A B,
        Proper (eqM (A:=A) ==> (eq ==> eqM (A:=B)) ==> eqM) bindM;
    returnM_bindM : forall A B a (f:A -> M B), returnM a >>= f ~= f a;
    bindM_returnM : forall A (m:M A), m >>= returnM ~= m;
    bindM_bindM : forall A B C (m:M A) (f:A -> M B) (g:B -> M C),
        (m >>= f) >>= g ~= m >>= (fun x => f x >>= g) }.


(** Monads with Errors **)

(* The error operation *)
Class MonadErrorOp (M:Type -> Type) : Type :=
  errorM : forall {A}, M A.

(* A monad with errors *)
Class MonadError M `{Monad M} `{MonadErrorOp M} : Prop :=
  { errorM_bindM : forall A B (f:A -> M B), errorM >>= f ~= errorM }.


(** Monads with Fixed-points **)

(* The domain ordering for a fixed-point monad *)
Class MonadLeqOp (M:Type -> Type) : Type :=
  leqM : forall {A}, M A -> M A -> Prop.

(* The class for the fixed-point operation *)
Class MonadFixOp (M:Type -> Type) : Type :=
  fixM : forall {A B}, ((forall (a:A), M (B a)) -> (forall (a:A), M (B a))) ->
                       (forall (a:A), M (B a)).

(* Typeclass for dependent functions that respect the domain order *)
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
        try apply (Rf a a); try reflexivity; assumption. }
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
    intros opt_a1 opt_a2 eq12; rewrite eq12.
    destruct opt_a2; [ apply Rf | ]; reflexivity. }
  { intros.
    unfold returnM, MonadReturnOp_OptionT, bindM, MonadBindOp_OptionT.
    unfold eqM, MonadEqOp_OptionT.
    rewrite (returnM_bindM (M:=M)). reflexivity. }
  { intros.
    unfold returnM, MonadReturnOp_OptionT, bindM, MonadBindOp_OptionT.
    unfold eqM, MonadEqOp_OptionT.
    etransitivity; [ | apply (bindM_returnM (M:=M)) ].
    apply Proper_bindM; [ reflexivity | ].
    intros opt1 opt2 eq12. rewrite eq12.
    destruct opt2; reflexivity. }
  { intros.
    unfold returnM, MonadReturnOp_OptionT, bindM, MonadBindOp_OptionT;
      unfold eqM, MonadEqOp_OptionT.
    rewrite (bindM_bindM (M:=M)).
    apply Proper_bindM; [ reflexivity | ].
    intros opt_a1 opt_a2 eq_a12; rewrite eq_a12.
    destruct opt_a2.
    { apply Proper_bindM; [ reflexivity | ].
      intros opt_b1 opt_b2 eq_b12; rewrite eq_b12.
      destruct opt_b2; reflexivity. }
    { rewrite returnM_bindM. reflexivity. } }
Qed.


Instance MonadErrorOp_OptionT M `{MonadReturnOp M} : MonadErrorOp (OptionT M) :=
  fun A => returnM None.

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
Definition letRecM {lrts : LetRecTypes} {B} (F: lrtPi lrts (lrtTupleType lrts))
           (body:lrtPi lrts (CompM B)) : CompM B :=
  lrtApply body (multiFixM F).
