(***
 *** Extra Proofs for CompM that Rely on SAWCorePrelude
 ***)

From Coq          Require Import Logic.
From Coq          Require Import Strings.String.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Export CompM.

(***
 *** Some useful Ltac
 ***)

Ltac get_last_hyp tt :=
  match goal with H: _ |- _ => constr:(H) end.

Tactic Notation "unfold_projs" :=
  unfold SAWCoreScaffolding.fst;
  cbn [ Datatypes.fst Datatypes.snd projT1 ].

Tactic Notation "unfold_projs" "in" constr(N) :=
  unfold SAWCoreScaffolding.fst in N;
  cbn [ Datatypes.fst Datatypes.snd projT1 ] in N.

Tactic Notation "unfold_projs" "in" "*" :=
  unfold SAWCoreScaffolding.fst in *;
  cbn [ Datatypes.fst Datatypes.snd projT1 ] in *.

Ltac destruct_prods_sums_in H :=
  match type of H with
  | _ /\ _        => let H0 := fresh H in
                     let H1 := fresh H in
                     destruct H as [ H0 H1 ];
                     destruct_prods_sums_in H0;
                     destruct_prods_sums_in H1
  | { _ : _ & _ } => let H0 := fresh H in
                     let H1 := fresh H in
                     destruct H as [ H0 H1 ];
                     destruct_prods_sums_in H0;
                     destruct_prods_sums_in H1
  | prod _ _      => let H0 := fresh H in
                     let H1 := fresh H in
                     destruct H as [ H0 H1 ];
                     destruct_prods_sums_in H0;
                     destruct_prods_sums_in H1
  | unit          => destruct H
  | _ \/ _        => destruct H as [ H | H ];
                     [ destruct_prods_sums_in H
                     | destruct_prods_sums_in H ]
  | _ => idtac
  end.

Tactic Notation "destruct_prods_sums" "in" hyp(H) :=
  destruct_prods_sums_in H.

Ltac intro_destruct_prods_sums :=
  intro; match goal with H: _ |- _ => destruct_prods_sums in H end.

Ltac split_prod_goal :=
  repeat match goal with
         | |- _ /\ _        => split
         | |- { _ : _ & _ } => split
         | |- _ * _         => split
         | |- unit          => exact tt
         | |- True          => trivial
         end.


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

Lemma refinesM_maybe_l {A B} (x : CompM B) (f : A -> CompM B) mb P :
  (mb = SAWCorePrelude.Nothing _ -> x |= P) ->
  (forall a, mb = SAWCorePrelude.Just _ a -> f a |= P) ->
  SAWCorePrelude.maybe _ _ x f mb |= P.
Proof.
  destruct mb; intros; simpl.
  - apply H; reflexivity.
  - apply H0; reflexivity.
Qed.

Lemma refinesM_maybe_r {A B} (x : CompM B) (f : A -> CompM B) mb P :
  (mb = SAWCorePrelude.Nothing _ -> P |= x) ->
  (forall a, mb = SAWCorePrelude.Just _ a -> P |= f a) ->
  P |= SAWCorePrelude.maybe _ _ x f mb.
Proof.
  destruct mb; intros; simpl.
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

Hint Resolve refinesM_letRecM_Nil_l : refinesM.
(* Hint Extern 1 (@letRecM LRT_Nil _ _ _ |= @letRecM LRT_Nil _ _ _) => *)
(*   apply refinesM_letRecM0 : refinesM. *)

Hint Extern 1 (@letRecM ?lrts _ _ _ |= @letRecM ?lrts _ (lrtLambda (fun _ => _)) _) =>
  (* idtac "prove_refinement: refinesM_letRecM_const_r"; *)
  apply refinesM_letRecM_const_r; try apply ProperLRTFun_any;
  try (apply refinesFunTuple_multiFixM; unfold refinesFunTuple; split_prod_goal);
  unfold lrtApply, lrtLambda; unfold_projs : refinesM.

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
  (* idtac "prove_refinement: refinesM_either_l"; *)
  apply refinesM_either_l;
    let e := fresh "e_either" in
    let e' := fresh "e_either_arg" in
    (intro_destruct_prods_sums;
      intro e; unfold_projs in e; (* autorewrite with SAWCoreBitvectors in e; *)
      try discriminate e; unfold_projs; try rewrite e;
      try (injection e; intro e'; try rewrite <- e')) : refinesM.
Hint Extern 1 (_ |= SAWCorePrelude.either _ _ _ _ _ _) =>
  (* idtac "prove_refinement: refinesM_either_r"; *)
  apply refinesM_either_r;
    let e := fresh "e_either" in
    let e' := fresh "e_either_arg" in
    (intro_destruct_prods_sums;
      intro e; unfold_projs in e; (* autorewrite with SAWCoreBitvectors in e; *)
      try discriminate e; unfold_projs; try rewrite e;
      try (injection e; intro e'; try rewrite <- e')) : refinesM.

Hint Extern 1 (SAWCorePrelude.maybe _ _ _ _ _ |= _) =>
  (* idtac "prove_refinement: refinesM_maybe_l"; *)
  let e := fresh "e_maybe" in
  let e' := fresh "e_maybe_arg" in
    apply refinesM_maybe_l;
    [ intro e; (* autorewrite with SAWCoreBitvectors in e; *)
      try discriminate e; try rewrite e
    | intro_destruct_prods_sums;
      intro e; unfold_projs in e; (* autorewrite with SAWCoreBitvectors in e; *)
      try discriminate e; unfold_projs; try rewrite e;
      try (injection e; intro e'; try rewrite <- e') ] : refinesM.
Hint Extern 1 (_ |= SAWCorePrelude.maybe _ _ _ _ _) =>
  (* idtac "prove_refinement: refinesM_maybe_r"; *)
  let e := fresh "e_maybe" in
  let e' := fresh "e_maybe_arg" in
    apply refinesM_maybe_r;
    [ intro e; (* autorewrite with SAWCoreBitvectors in e; *)
      try discriminate e; try rewrite e
    | intro_destruct_prods_sums;
      intro e; unfold_projs in e; (* autorewrite with SAWCoreBitvectors in e; *)
      try discriminate e; unfold_projs; try rewrite e;
      try (injection e; intro e'; try rewrite <- e') ] : refinesM.

Hint Extern 1 (sigT_rect _ _ _ |= _) =>
  (* idtac "prove_refinement: refinesM_sigT_rect_l"; *)
  apply refinesM_sigT_rect_l;
    let e := fresh "e_sigT_rect" in
    let e' := fresh "e_sigT_arg0" in
    let e'' := fresh "e_sigT_arg1" in
    (intro_destruct_prods_sums; intro_destruct_prods_sums;
     intro e; unfold_projs in e; unfold_projs; try rewrite e;
     try (injection e; intros e' e''; try rewrite <- e'; try rewrite <- e'')) : refinesM.
Hint Extern 1 (_ |= sigT_rect _ _ _) =>
  (* idtac "prove_refinement: refinesM_sigT_rect_r"; *)
  apply refinesM_sigT_rect_r;
    let e := fresh "e_sigT_rect" in
    let e' := fresh "e_sigT_arg0" in
    let e'' := fresh "e_sigT_arg1" in
    (intro_destruct_prods_sums; intro_destruct_prods_sums;
     intro e; unfold_projs in e; unfold_projs; try rewrite e;
     try (injection e; intros e' e''; try rewrite <- e'; try rewrite <- e'')) : refinesM.

Hint Extern 1 ((if _ then _ else _) |= _) =>
  (* idtac "prove_refinement: refinesM_if_l"; *)
  apply refinesM_if_l;
    let e := fresh "e_if" in
    (intro e; (* let p := type of e in idtac p; time "bv rewrite (if_l)" *)
              (autorewrite with SAWCoreBitvectors in e);
              destruct_prods_sums in e;
     try discriminate e; try rewrite e) : refinesM.
Hint Extern 1 (_ |= (if _ then _ else _)) =>
  (* idtac "prove_refinement: refinesM_if_r"; *)
  apply refinesM_if_r;
    let e := fresh "e_if" in
    (intro e; (* let p := type of e in idtac p; time "bv rewrite (if_r)" *)
              (autorewrite with SAWCoreBitvectors in e);
              destruct_prods_sums in e;
     try discriminate e; try rewrite e) : refinesM.
Hint Extern 1 (returnM (if _ then _ else _) |= _) =>
  apply refinesM_returnM_if_l : refinesM.
Hint Extern 1 (_ |= returnM (if _ then _ else _)) =>
  apply refinesM_returnM_if_r : refinesM.

Hint Extern 1 (assertM _ >> _ |= _) =>
  (* idtac "prove_refinement: refinesM_assertM_l"; *)
  apply refinesM_bindM_assertM_l;
    let e := fresh "e_assert" in
     (intro e; autorewrite with SAWCoreBitvectors in e;
      destruct_prods_sums in e): refinesM.
Hint Extern 1 (_ |= assumingM _ _) =>
  (* idtac "prove_refinement: refinesM_assumingM_r"; *)
  apply refinesM_assumingM_r;
    let e := fresh "e_assuming" in
     (intro e; autorewrite with SAWCoreBitvectors in e;
      destruct_prods_sums in e) : refinesM.
Hint Extern 2 (_ |= assertM _ >> _) =>
  (* idtac "prove_refinement: refinesM_assertM_r"; *)
  eapply refinesM_bindM_assertM_r; shelve : refinesM.
Hint Extern 2 (assumingM _ _ |= _) =>
  (* idtac "prove_refinement: refinesM_assumingM_l"; *)
  eapply refinesM_assumingM_l; shelve : refinesM.

Hint Extern 2 (existsM _ |= _) => apply refinesM_existsM_l; intro_destruct_prods_sums : refinesM.
Hint Extern 2 (_ |= forallM _) => apply refinesM_forallM_r; intro_destruct_prods_sums : refinesM.
Hint Extern 3 (_ |= existsM _) => eapply refinesM_existsM_r; shelve : refinesM.
Hint Extern 3 (forallM _ |= _) => eapply refinesM_forallM_l; shelve : refinesM.

Hint Extern 3 (returnM _ |= returnM _) =>
  apply refinesM_returnM; (reflexivity || shelve) : refinesM.

Hint Extern 1 (orM _ _ |= _) => apply refinesM_orM_l : refinesM.
Hint Extern 1 (_ |= andM _ _) => apply refinesM_andM_r : refinesM.
(* Hint Extern 99 (_ |= orM _ _) => apply refinesM_orM_r : refinesM. *)
(* Hint Extern 99 (andM _ _ |= _) => apply refinesM_andM_l : refinesM. *)

Hint Extern 1 ((returnM _ >>= _) |= _) => rewrite returnM_bindM : refinesM.
Hint Extern 1 (_ |= (returnM _ >>= _)) => rewrite returnM_bindM : refinesM.
Hint Extern 1 ((existsM _ >>= _) |= _) => rewrite existsM_bindM : refinesM.
Hint Extern 1 (_ |= (existsM _ >>= _)) => rewrite existsM_bindM : refinesM.
Hint Extern 1 ((orM _ _ >>= _) |= _)   => rewrite orM_bindM : refinesM.
Hint Extern 1 (_ |= (orM _ _ >>= _))   => rewrite orM_bindM : refinesM.
Hint Extern 1 ((errorM _ >>= _) |= _)  => rewrite errorM_bindM : refinesM.
Hint Extern 1 (_ |= (errorM _ >>= _))  => rewrite errorM_bindM : refinesM.
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

Hint Extern 5 (@refinesFun (LRT_Ret _) _ _) =>
  (* idtac "prove_refinement: refinesFunBase"; *)
  simple apply refinesFunBase; unfold_projs : refinesFun.

Hint Extern 5 (@refinesFun (LRT_Fun _ _) _ _) =>
  (* idtac "prove_refinement: refinesFunStep"; *)
  simple apply refinesFunStep; intro_destruct_prods_sums : refinesFun.


(***
 *** Top-level tactics to put it all together
 ***)

Ltac prove_refinement_core :=
  unshelve (typeclasses eauto with refinesM refinesFun);
  try (unshelve (rewrite_strat (bottomup (hints refinesM))));
  unfold_projs in *; split_prod_goal;
  try reflexivity || contradiction.

Ltac prove_refinement :=
  (* idtac "prove_refinement: start"; *)
  unfold_projs; compute_bv_funs;
  prove_refinement_core.

(* Giving user input as to which disjunctive branch to continue proof automation in *)
Ltac continue_prove_refinement_left :=
  match goal with
  | |- _ |= orM _ _ => apply refinesM_orM_r; left; prove_refinement_core
  | |- andM _ _ |= _ => apply refinesM_andM_l; left; prove_refinement_core
  end.
Ltac continue_prove_refinement_right :=
  match goal with
  | |- _ |= orM _ _ => apply refinesM_orM_r; right; prove_refinement_core
  | |- andM _ _ |= _ => apply refinesM_andM_l; right; prove_refinement_core
  end.

Ltac prove_refinement_match_letRecM_l :=
  unshelve (typeclasses eauto with refinesM refinesFun);
  unshelve (eapply refinesM_letRecM_match_r);
  [ unfold lrtTupleType, lrtToType; repeat split | apply ProperLRTFun_any | ].

(* Ltac prove_refinesFun := unshelve (typeclasses eauto with refinesFun). *)

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
  | |- letRecM tt _ |= _ => apply refinesM_letRecM_Nil_l; old_prove_refinesM

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
