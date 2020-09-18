(***
 *** Extra Proofs for CompM that Rely on SAWCorePrelude
 ***)

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Export CompM.

(***
 *** Extra lemmas about refinement that rely on SAWCorePrelude
 ***)

Lemma refinesM_either_l {A B C} (f:A -> CompM C) (g:B -> CompM C) eith P :
  (forall a, eith = SAWCorePrelude.Left _ _ a -> f a |= P) ->
  (forall b, eith = SAWCorePrelude.Right _ _ b -> g b |= P) ->
  SAWCorePrelude.either _ _ _ f g eith |= P.
Proof.
  destruct eith; intros; simpl.
  - apply H; reflexivity.
  - apply H0; reflexivity.
Qed.

Lemma refinesM_either_r {A B C} (f:A -> CompM C) (g:B -> CompM C) eith P :
  (forall a, eith = SAWCorePrelude.Left _ _ a -> P |= f a) ->
  (forall b, eith = SAWCorePrelude.Right _ _ b -> P |= g b) ->
  P |= SAWCorePrelude.either _ _ _ f g eith.
Proof.
  destruct eith; intros; simpl.
  - apply H; reflexivity.
  - apply H0; reflexivity.
Qed.

Lemma returnM_if A (b : bool) (x y : A) :
  @returnM CompM _ A (if b then x else y) ~= if b then returnM x else returnM y.
Proof. destruct b. setoid_reflexivity. setoid_reflexivity. Qed.

Lemma refinesM_returnM_if_l A (b : bool) (x y : A) P :
  ((if b then returnM x else returnM y) |= P) ->
  (returnM (if b then x else y) |= P).
Proof. rewrite returnM_if. trivial. Qed.

Lemma refinesM_returnM_if_r A (b : bool) (x y : A) P :
  (P |= (if b then returnM x else returnM y)) ->
  (P |= returnM (if b then x else y)).
Proof. rewrite returnM_if. trivial. Qed.

Lemma returnM_injective : forall (A : Type) (x y : A),
    returnM (M:=CompM) x ~= returnM y -> x = y.
Proof.
  intros. unfold returnM in H. unfold MonadReturnOp_OptionT in H.
  unfold eqM in H. unfold MonadEqOp_OptionT in H. unfold eqM in H. unfold MonadEqOp_SetM in H.
  assert (Some x = Some y) as Hxy.
  { rewrite H. reflexivity. }
  inversion Hxy; subst. reflexivity.
Qed.


(***
 *** Automation for proving refinement
 ***)

Create HintDb refinesM.

(*
Hint Extern 2 (refinesFun _ _) => (apply refinesFun_multiFixM_fst;
                                     simpl; intros) : refinesFun.
*)

Hint Extern 999 (_ |= _) => shelve : refinesM.
Hint Resolve refinesM_letRecM0 : refinesM.

(*
Hint Resolve refinesM_either_l : refinesM.
Hint Resolve refinesM_either_r : refinesM.
Hint Resolve refinesM_sigT_rect_l : refinesM.
Hint Resolve refinesM_sigT_rect_r : refinesM.
Hint Resolve refinesM_if_l : refinesM.
Hint Resolve refinesM_if_r : refinesM.

Hint Resolve refinesM_existsM_l : refinesM.
Hint Resolve refinesM_forallM_r : refinesM.
Hint Resolve refinesM_existsM_r | 10 : refinesM.
Hint Resolve refinesM_forallM_l | 10 : refinesM.
Hint Resolve refinesM_returnM : refinesM.
*)

Hint Extern 1 (SAWCorePrelude.either _ _ _ _ _ _ |= _) =>
  apply refinesM_either_l;
    let e := fresh "e_either" in
    let e' := fresh "e_either_arg" in
    (intro; intro e; try discriminate e; try rewrite e;
    try (injection e; intro e'; try rewrite <- e')) : refinesM.
Hint Extern 1 (_ |= SAWCorePrelude.either _ _ _ _ _ _) =>
  apply refinesM_either_r;
    let e := fresh "e_either" in
    let e' := fresh "e_either_arg" in
    (intro; intro e; try discriminate e; try rewrite e;
    try (injection e; intro e'; try rewrite <- e')) : refinesM.
Hint Extern 1 (sigT_rect _ _ _ |= _) =>
  apply refinesM_sigT_rect_l;
    let e := fresh "e_sigT_rect" in
    (intro; intro; intro e; try rewrite e) : refinesM.
Hint Extern 1 (_ |= sigT_rect _ _ _) =>
  apply refinesM_sigT_rect_r;
    let e := fresh "e_sigT_rect" in
    (intro; intro; intro e; try rewrite e) : refinesM.
Hint Extern 1 ((if _ then _ else _) |= _) =>
  apply refinesM_if_l;
    let e := fresh "e_if" in
    (intro e; try discriminate e; try rewrite e) : refinesM.
Hint Extern 1 (_ |= (if _ then _ else _)) =>
  apply refinesM_if_r;
    let e := fresh "e_if" in
    (intro e; try discriminate e; try rewrite e) : refinesM.
Hint Extern 1 (returnM (if _ then _ else _) |= _) =>
  apply refinesM_returnM_if_l : refinesM.
Hint Extern 1 (_ |= returnM (if _ then _ else _)) =>
  apply refinesM_returnM_if_r : refinesM.

Hint Extern 1 (existsM _ |= _) => apply refinesM_existsM_l; intros : refinesM.
Hint Extern 1 (_ |= forallM _) => apply refinesM_forallM_r; intros : refinesM.
Hint Extern 2 (_ |= existsM _) => eapply refinesM_existsM_r; shelve : refinesM.
Hint Extern 2 (forallM _ |= _) => eapply refinesM_forallM_l; shelve : refinesM.
(* Hint Extern 2 (returnM _ |= returnM _) => apply refinesM_returnM; intros; *)
(*                                              (reflexivity || shelve) : refinesM. *)

Hint Extern 1 ((returnM _ >>= _) |= _) => rewrite returnM_bindM : refinesM.
Hint Extern 1 (_ |= (returnM _ >>= _)) => rewrite returnM_bindM : refinesM.
Hint Extern 1 ((existsM _ >>= _) |= _) => rewrite existsM_bindM : refinesM.
Hint Extern 1 (_ |= (existsM _ >>= _)) => rewrite existsM_bindM : refinesM.
Hint Extern 1 ((errorM _ >>= _) |= _) => rewrite errorM_bindM : refinesM.
Hint Extern 1 (_ |= (errorM _ >>= _)) => rewrite errorM_bindM : refinesM.
Hint Extern 1 (((_ >>= _) >>= _) |= _) => rewrite bindM_bindM : refinesM.
Hint Extern 1 (_ |= ((_ >>= _) >>= _)) => rewrite bindM_bindM : refinesM.


(***
 *** Rewriting rules
 ***)

Lemma existT_eta A (B:A -> Type) (s: {a:A & B a}) :
  existT B (projT1 s) (projT2 s) = s.
Proof.
  destruct s; reflexivity.
Qed.

Lemma existT_eta_unit A (s: {_:A & unit}) : existT (fun _ => unit) (projT1 s) tt = s.
Proof.
  destruct s; destruct u; reflexivity.
Qed.

Hint Rewrite existT_eta existT_eta_unit : refinesM.

(*
Lemma function_eta A B (f:A -> B) : pointwise_relation A eq (fun x => f x) f.
Proof.
  intro; reflexivity.
Qed.
*)

(* Specialized versions of monad laws for CompM to make rewriting faster,
probably because Coq doesn't have to search for the instances...? *)

Definition returnM_bindM_CompM A B (a:A) (f:A -> CompM B) : returnM a >>= f ~= f a :=
  returnM_bindM (M:=CompM) A B a f.

Definition bindM_returnM_CompM A (m:CompM A) : m >>= (fun x => returnM x) ~= m :=
  bindM_returnM (M:=CompM) A m.

Definition bindM_bindM_CompM A B C (m : CompM A) (f : A -> CompM B) (g : B -> CompM C) :
  m >>= f >>= g ~= m >>= (fun x : A => f x >>= g) :=
  bindM_bindM (M:=CompM) A B C m f g.

Hint Rewrite returnM_bindM_CompM bindM_returnM_CompM bindM_bindM_CompM : refinesM.

(*
FIXME: do we need these rules?

Lemma bvEq_sym n x y : bvEq n x y = bvEq n y x.
  admit.
Admitted.

From Coq Require Import Nat.

Lemma bvEq_eqb n x y : bvEq n (bvNat n x) (bvNat n y) = eqb x y.
  admit.
Admitted.
*)


(***
 *** Automation for proving function refinement
 ***)

Create HintDb refinesFun.
Hint Extern 999 (_ |= _) => shelve : refinesFun.
Hint Extern 999 (refinesFun _ _) => shelve : refinesFun.

Definition MaybeDestructArg A (a:A) (goal:Type) : Type := goal.
Definition noDestructArg A a goal : goal -> MaybeDestructArg A a goal := fun g => g.
Definition noDestructArg_bv n a goal :
  goal -> MaybeDestructArg (SAWCorePrelude.bitvector n) a goal := fun g => g.

Definition refinesFun_multiFixM_fst' lrt (F:lrtPi (LRT_Cons lrt LRT_Nil)
                                                  (lrtTupleType (LRT_Cons lrt LRT_Nil))) f
      (ref_f:refinesFun (SAWCoreScaffolding.fst (F f)) f) :
  refinesFun (fst (multiFixM F)) f := refinesFun_multiFixM_fst lrt F f ref_f.

Definition refinesFun_fst lrt B f1 (fs:B) f2 (r:@refinesFun lrt f1 f2) :
  refinesFun (SAWCoreScaffolding.fst (f1, fs)) f2 := r.

Hint Resolve refinesFun_fst | 1 : refinesFun.
Hint Resolve refinesFun_multiFixM_fst' | 1 : refinesFun.
Hint Resolve noDestructArg | 5 : refinesFun.
(* Hint Resolve noDestructArg_bv | 5 : refinesFun. *)

(*
Hint Extern 1 (MaybeDestructArg _ _ _) =>
  (lazymatch goal with
  | |- MaybeDestructArg ?W64list ?l ?g =>
    match g with
    | context [W64List_rect _ _ _ l] => destruct l; simpl; apply noDestructArg
    end
  end) : refiesFun.
Print HintDb refinesFun.
 *)

Ltac get_last_hyp tt :=
  match goal with H: _ |- _ => constr:(H) end.

(* If a goal contains W64List_rect applied to l, then destruct l *)
Ltac destructArg_W64List :=
  (lazymatch goal with
  | |- MaybeDestructArg ?W64list ?l ?g =>
    match g with
    | context [SAWCorePrelude.W64List_rect _ _ _ l] =>
      induction l; let IH := get_last_hyp tt in
      try simpl in IH; try unfold MaybeDestructArg in IH;
      simpl; apply noDestructArg
    end
  end).
Hint Extern 1 (MaybeDestructArg _ _ _) => destructArg_W64List :refinesFun.

(* If a goal contains list_rect applied to l, then destruct l *)
Ltac destructArg_list :=
  (lazymatch goal with
  | |- MaybeDestructArg (list _) ?l ?g =>
    match g with
    | context [Datatypes.list_rect _ _ _ l] =>
      induction l; let IH := get_last_hyp tt in
      try simpl in IH; try unfold MaybeDestructArg in IH;
      simpl; apply noDestructArg
    end
   end).
Hint Extern 1 (MaybeDestructArg _ _ _) => destructArg_list :refinesFun.

Definition refinesFunBase B m1 m2 (r: m1 |= m2) : @refinesFun (LRT_Ret B) m1 m2 := r.
Definition refinesFunStep A lrtF f1 f2
           (r: forall a:A, MaybeDestructArg A a (@refinesFun (lrtF a) (f1 a) (f2 a))) :
  @refinesFun (LRT_Fun A lrtF) f1 f2 := r.

Hint Resolve refinesFunBase refinesFunStep | 5 : refinesFun.


(***
 *** Top-level tactics to put it all together
 ***)

Ltac prove_refinement :=
  compute_bvLits;
  unshelve (typeclasses eauto with refinesM refinesFun);
  try (unshelve (rewrite_strat (bottomup (hints refinesM))));
  try reflexivity.

Ltac prove_refinesFun := unshelve (typeclasses eauto with refinesFun).

(*
Ltac rewrite_refinesM :=
  try ((rewrite returnM_bindM || rewrite bindM_returnM || rewrite bindM_bindM ||
        rewrite errorM_bindM || rewrite existsM_bindM); rewrite_refinesM).
*)


(*** FIXME: old stuff below ***)

Ltac old_prove_refinesM :=
  lazymatch goal with
  (* Bind cases *)
  | |- (returnM _ >>= _) |= _ => rewrite returnM_bindM; old_prove_refinesM
  | |- _ |= (returnM _ >>= _) => rewrite returnM_bindM; old_prove_refinesM
  | |- (existsM _ >>= _) |= _ => rewrite existsM_bindM; old_prove_refinesM
  | |- _ |= (existsM _ >>= _) => rewrite existsM_bindM; old_prove_refinesM
  | |- (errorM >>= _) |= _ => rewrite errorM_bindM; old_prove_refinesM
  | |- _ |= (errorM >>= _) => rewrite errorM_bindM; old_prove_refinesM
  | |- ((_ >>= _) >>= _) |= _ => rewrite bindM_bindM; old_prove_refinesM
  | |- _ |= ((_ >>= _) >>= _) => rewrite bindM_bindM; old_prove_refinesM

  (* letRecM cases *)
  | |- letRecM tt _ |= _ => apply refinesM_letRecM0; old_prove_refinesM

  (* either *)
  | |- SAWCorePrelude.either _ _ _ _ _ _ |= _ =>
    apply refinesM_either_l; intros; old_prove_refinesM
  | |- _ |= SAWCorePrelude.either _ _ _ _ _ _ =>
    apply refinesM_either_r; intros; old_prove_refinesM
  | |- sigT_rect _ _ _ |= _ =>

  (* sigT_rect *)
    apply refinesM_sigT_rect_l; intros; old_prove_refinesM
  | |- _ |= sigT_rect _ _ _ =>
    apply refinesM_sigT_rect_r; intros; old_prove_refinesM

  (* if *)
  | |- (if _ then _ else _) |= _ =>
    apply refinesM_if_l; intros; old_prove_refinesM
  | |- _ |= (if _ then _ else _) =>
    apply refinesM_if_r; intros; old_prove_refinesM

  (* quantifiers *)
  | |- existsM _ |= _ => apply refinesM_existsM_l; intros; old_prove_refinesM
  | |- _ |= forallM _ => apply refinesM_forallM_r; intros; old_prove_refinesM
  | |- _ |= existsM _ => eapply refinesM_existsM_r; old_prove_refinesM
  | |- forallM _ |= _ => eapply refinesM_forallM_l; old_prove_refinesM
  | |- returnM _ |= returnM _ => apply refinesM_returnM; intros; try reflexivity

  (* default: give up! *)
  | _ => idtac (* try (progress (autorewrite with refinesM) ; old_prove_refinesM) *)
  end.

Ltac old_prove_refinesFun :=
  apply refinesFun_multiFixM_fst; simpl; intros; old_prove_refinesM.
