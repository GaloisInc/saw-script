From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SpecMExtra.
From EnTree       Require Import Automation.
Import SAWCorePrelude.
Import SpecMNotations.
Local Open Scope entree_scope.

Require Import Examples.linked_list_gen.
Import linked_list.


(* FIXME move to EnTree.Automation *)

Lemma spec_refines_either_l (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  RR A B f g eith (P : SpecM E2 Γ2 R2) :
  (forall a, eith = Left _ _ a -> spec_refines RPre RPost RR (f a) P) ->
  (forall b, eith = Right _ _ b -> spec_refines RPre RPost RR (g b) P) ->
  spec_refines RPre RPost RR (either A B (SpecM E1 Γ1 R1) f g eith) P.
Proof. destruct eith; intros; eauto. Qed.

Lemma spec_refines_either_r (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  RR (P : SpecM E1 Γ1 R1) A B f g eith :
  (forall a, eith = Left _ _ a -> spec_refines RPre RPost RR P (f a)) ->
  (forall b, eith = Right _ _ b -> spec_refines RPre RPost RR P (g b)) ->
  spec_refines RPre RPost RR P (either A B (SpecM E2 Γ2 R2) f g eith).
Proof. destruct eith; intros; eauto. Qed.

Definition spec_refines_either_l_IntroArg (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  RR A B f g eith (P : SpecM E2 Γ2 R2) :
  (IntroArg Any A (fun a =>
   IntroArg Hyp (eith = Left _ _ a) (fun _ =>
   spec_refines RPre RPost RR (f a) P))) ->
  (IntroArg Any B (fun b =>
   IntroArg Hyp (eith = Right _ _ b) (fun _ =>
   spec_refines RPre RPost RR (g b) P))) ->
  spec_refines RPre RPost RR (either A B (SpecM E1 Γ1 R1) f g eith) P :=
  spec_refines_either_l E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR A B f g eith P.

Definition spec_refines_either_r_IntroArg (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  RR A B f g eith (P : SpecM E1 Γ1 R1) :
  (IntroArg Any A (fun a =>
   IntroArg Hyp (eith = Left _ _ a) (fun _ =>
   spec_refines RPre RPost RR P (f a)))) ->
  (IntroArg Any B (fun b =>
   IntroArg Hyp (eith = Right _ _ b) (fun _ =>
   spec_refines RPre RPost RR P (g b)))) ->
  spec_refines RPre RPost RR P (either A B (SpecM E2 Γ2 R2) f g eith) :=
  spec_refines_either_r E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR P A B f g eith.

#[global] Hint Extern 101 (spec_refines _ _ _ (either _ _ _ _ _ _) _) =>
  simple apply spec_refines_either_l_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ _ (either _ _ _ _ _ _)) =>
  simple apply spec_refines_either_r_IntroArg : refines.

Lemma IntroArg_eq_Left_const n A B (x y : A) (goal : Prop)
  : IntroArg n (x = y) (fun _ => goal) ->
    IntroArg n (Left A B x = Left A B y) (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.
Lemma IntroArg_eq_Right_const n A B (x y : B) (goal : Prop)
  : IntroArg n (x = y) (fun _ => goal) ->
    IntroArg n (Right A B x = Right A B y) (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.
Lemma IntroArg_eq_Left_Right n A B (x : A) (y : B) goal
  : IntroArg n (Left A B x = Right A B y) goal.
Proof. intros eq; discriminate eq. Qed.
Lemma IntroArg_eq_Right_Left n A B (x : A) (y : B) goal
  : IntroArg n (Right A B y = Left A B x) goal.
Proof. intros eq; discriminate eq. Qed.

#[global] Hint Extern 101 (IntroArg _ (Left _ _ _ = Left _ _ _) _) =>
  simple apply IntroArg_eq_Left_const : refines.
#[global] Hint Extern 101 (IntroArg _ (Right _ _ _ = Right _ _ _) _) =>
  simple apply IntroArg_eq_Right_const : refines.
#[global] Hint Extern 101 (IntroArg _ (Left _ _ _ = Right _ _ _) _) =>
  idtac "1hi"; simple apply IntroArg_eq_Left_Right; idtac "1ho?" : refines.
#[global] Hint Extern 101 (IntroArg _ (Right _ _ _ = Left _ _ _) _) =>
  idtac "2hi"; simple apply IntroArg_eq_Right_Left; idtac "2ho?" : refines.

(* List destruction automation *)
Ltac list_destruction l :=
  let l' := fresh l in destruct l as [| ? l'];
  simpl SAWCorePrelude.unfoldList in *.
#[global] Hint Extern 102 (IntroArg ?n (eq (SAWCorePrelude.unfoldList _ ?l)
                                           (Left _ _ _)) _) =>
  list_destruction l : refines.
#[global] Hint Extern 102 (IntroArg ?n (eq (SAWCorePrelude.unfoldList _ ?l)
                                           (Right _ _ _)) _) =>
  list_destruction l : refines.

(* QOL: nicer names for bitvector and list arguments *)
#[local] Hint Extern 901 (IntroArg Any (bitvector _) _) =>
  let e := fresh "x" in IntroArg_intro e : refines prepostcond. 
#[local] Hint Extern 901 (IntroArg Any (list _) _) =>
  let e := fresh "l" in IntroArg_intro e : refines prepostcond. 
#[local] Hint Extern 901 (IntroArg Any (List_def _) _) =>
  let e := fresh "l" in IntroArg_intro e : refines prepostcond. 


Lemma is_elem_spec_ref x l :
  spec_refines eqPreRel eqPostRel eq
    (is_elem x l)
    (total_spec (fun _ => True)
                (fun '(x, l) r => (~ List.In x l /\ r = intToBv 64 0)
                                  \/ (List.In x l /\ r = intToBv 64 1))
                (x, l)).
Proof.
  unfold is_elem, is_elem__bodies.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact (length l0).
  - prepost_case 0 0.
    + exact (x0 = x1 /\ l0 = l1).
    + exact (r = r0).
    + prepost_exclude_remaining.
  - time "is_elem_spec_ref" prove_refinement_continue.
    all: try (left; easy || right; easy).


(* =============== OLD BELOW =============== *)

Lemma no_errors_is_elem x l :
  spec_refines eqPreRel eqPostRel eq (is_elem x l) no_errors_spec.
Proof.
  unfold is_elem, no_errors_spec.
  time "no_errors_is_elem" prove_refinement.
Qed.

Lemma no_errors_is_elem_manual : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun, sawLet_def.
  unfold noErrorsSpec.
  apply refinesFun_multiFixM_fst; intros x l.
  apply refinesM_letRecM_Nil_l.
  apply refinesM_either_l; intros.
  - eapply refinesM_existsM_r. reflexivity.
  - apply refinesM_if_l; intros.
    + eapply refinesM_existsM_r. reflexivity.
    + rewrite existsM_bindM.
      apply refinesM_existsM_l; intros. rewrite returnM_bindM.
      eapply refinesM_existsM_r. reflexivity.
Qed.

(*
Fixpoint is_elem_spec (x:bitvector 64) (l:W64List) : CompM (bitvector 64) :=
  match l with
  | W64Nil => returnM (intToBv 64 0)
  | W64Cons y l' =>
    if bvEq 64 y x then returnM (intToBv 64 1) else
      is_elem_spec x l'
  end.
*)

Definition is_elem_fun (x:bitvector 64) :
  list (bitvector 64) -> CompM (bitvector 64) :=
  list_rect (fun _ => CompM (bitvector 64))
            (returnM (intToBv 64 0))
            (fun y l' rec =>
               if bvEq 64 y x then returnM (intToBv 64 1) else rec).

Arguments is_elem_fun /.

Lemma is_elem_fun_ref : refinesFun is_elem is_elem_fun.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_fun, List_def.
  time "is_elem_fun_ref" prove_refinement.
Qed.

Lemma is_elem_fun_ref_manual : refinesFun is_elem is_elem_fun.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_fun, sawLet_def.
  apply refinesFun_multiFixM_fst; intros x l.
  apply refinesM_letRecM_Nil_l. simpl.
  apply refinesM_either_l; intros [] e_either.
  all: destruct l; cbn [ unfoldList list_rect ] in *.
  all: try (injection e_either; intros; subst); try discriminate e_either.
  - reflexivity.
  - apply refinesM_if_r; intro e_if; unfold_projs; rewrite e_if; simpl.
    + reflexivity.
    + rewrite bindM_returnM_CompM.
      reflexivity.
Qed.

(* The pure version of is_elem *)
Definition is_elem_pure (x:bitvector 64) (l:list (bitvector 64))
  : bitvector 64 :=
  (list_rect (fun _ => bitvector 64)
             (intToBv 64 0)
             (fun y l' rec =>
                if bvEq 64 y x then intToBv 64 1 else rec) l).

Arguments is_elem_pure /.

Definition is_elem_lrt : LetRecType :=
  LRT_Fun (bitvector 64) (fun _ =>
    LRT_Fun (list (bitvector 64)) (fun _ =>
      LRT_Ret (bitvector 64))).

Lemma is_elem_pure_fun_ref : @refinesFun is_elem_lrt is_elem_fun (fun x l => returnM (is_elem_pure x l)).
Proof.
  unfold is_elem_fun, is_elem_lrt, is_elem_pure.
  time "is_elem_pure_fun_ref" prove_refinement.
Qed.

Lemma is_elem_pure_fun_ref_manual : @refinesFun is_elem_lrt is_elem_fun (fun x l => returnM (is_elem_pure x l)).
Proof.
  unfold is_elem_fun, is_elem_pure.
  intros x l; induction l; simpl.
  - reflexivity.
  - apply refinesM_if_l; intro H; rewrite H.
    + reflexivity.
    + exact IHl.
Qed.

Lemma is_elem_pure_ref : refinesFun is_elem (fun x l => returnM (is_elem_pure x l)).
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_pure, List_def.
  time "is_elem_pure_ref" prove_refinement.
Qed.


(* A high-level specification of is_elem *)
Definition is_elem_spec (x:bitvector 64) (l:list (bitvector 64))
  : CompM (bitvector 64) :=
  orM
    (assertM (List.In x l) >> returnM (intToBv 64 1))
    (assertM (~ List.In x l) >> returnM (intToBv 64 0)).

Arguments is_elem_spec /.

Lemma is_elem_spec_ref : refinesFun is_elem is_elem_spec.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_spec.
  time "is_elem_spec_ref" prove_refinement.
  (* The a0 = [] case. *)
  - continue_prove_refinement_right.
    easy.
  (* The a0 = (s1 :: a1) case where a = s1. *)
  - continue_prove_refinement_left.
    now left.
  (* The a0 = (s1 :: a1) case where a <> s1, and we inductively assume
     the left assertion of our specification *)
  - continue_prove_refinement_left.
    now right.
  (* The a0 = (s1 :: a1) case where a <> s1, and we inductively assume
     the right assertion of our specification *)
  - continue_prove_refinement_right.
    now intros [].
Qed.


Section any.

  Lemma refinesM_bind_lr A B (x y : CompM A) (f g : A -> CompM B) :
    refinesM x y -> @refinesFun (LRT_Fun A (fun _ => LRT_Ret B)) f g ->
    refinesM (x >>= f) (y >>= g).
  Proof.
    unfold refinesM, bindM, MonadBindOp_OptionT, bindM, MonadBindOp_SetM.
    intros x_ref f_ref b H.
    destruct H as [ a xa H ].
    exists a.
    - apply x_ref.
      assumption.
    - destruct a.
      + apply f_ref.
        assumption.
      + assumption.
  Qed.

  Hint Resolve refinesM_bind_lr | 0 : refinesM.

  Definition any_fun (f:bitvector 64 -> CompM (bitvector 64)) :
    list (bitvector 64) -> CompM (bitvector 64) :=
    list_rect (fun _ => CompM (bitvector 64))
              (returnM (intToBv 64 0))
              (fun y l' rec =>
                 f y >>= fun call_ret_val =>
                  if not (bvEq 64 call_ret_val (intToBv 64 0))
                  then returnM (intToBv 64 1) else rec).

  Lemma any_fun_ref : refinesFun any any_fun.
  Proof.
    unfold any, any__tuple_fun, any_fun.
    time "any_fun_ref" prove_refinement.
  Qed.

  Local Arguments noErrorsSpec : simpl never.

  Lemma no_errors_any : refinesFun any (fun pred _ => assumingM
                                                     (forall x, refinesM (pred x) noErrorsSpec)
                                                     noErrorsSpec).
  Proof.
    unfold any, any__tuple_fun. (* unfold noErrorsSpec at 1. *)
    time "no_errors_any (1/2)" prove_refinement with NoRewrite.
    - unfold noErrorsSpec; prove_refinement.
    - rewrite (e_assuming v).
      unfold noErrorsSpec at 1.
      time "no_errors_any (2/2)" prove_refinement.
      + unfold noErrorsSpec; prove_refinement.
      + prove_refinement; assumption.
  Qed.

End any.

(*
Arguments sorted_insert__tuple_fun /.
Eval simpl in sorted_insert__tuple_fun.
Print sorted_insert__tuple_fun.
*)

Lemma no_errors_find_elem : refinesFun find_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold find_elem, find_elem__tuple_fun, noErrorsSpec.
  time "no_errors_find_elem" prove_refinement.
Qed.

Definition find_elem_fun (x: bitvector 64) :
  list (bitvector 64) -> CompM (list (bitvector 64)) :=
  list_rect (fun _ => CompM (list (bitvector 64)))
            (returnM List.nil)
            (fun y l' rec =>
               if bvEq 64 y x
               then returnM (y :: l')
               else rec).

Lemma find_elem_fun_ref : refinesFun find_elem find_elem_fun.
Proof.
  unfold find_elem, find_elem__tuple_fun, find_elem_fun.
  time "find_elem_fun_ref" prove_refinement.
Qed.

Lemma no_errors_sorted_insert : refinesFun sorted_insert (fun _ _ => noErrorsSpec).
Proof.
  unfold sorted_insert, sorted_insert__tuple_fun, mallocSpec, noErrorsSpec.
  time "no_errors_sorted_insert" prove_refinement.
Qed.

Definition sorted_insert_fun (x: bitvector 64) :
  list (bitvector 64) -> CompM (list (bitvector 64)) :=
  list_rect (fun _ => CompM (list (bitvector 64)))
            (returnM (x :: List.nil))
            (fun y l' rec =>
               if bvsle 64 x y
               then returnM (x :: y :: l')
               else rec >>= (fun l => returnM (y :: l))).

Lemma sorted_insert_fun_ref : refinesFun sorted_insert sorted_insert_fun.
Proof.
  unfold sorted_insert, sorted_insert__tuple_fun, sorted_insert_fun, mallocSpec.
  time "sorted_insert_fun_ref" prove_refinement.
Qed.

Lemma no_errors_sorted_insert_no_malloc : refinesFun sorted_insert_no_malloc (fun _ _ => noErrorsSpec).
Proof.
  unfold sorted_insert_no_malloc, sorted_insert_no_malloc__tuple_fun, mallocSpec, noErrorsSpec.
  time "no_errors_sorted_insert_no_malloc" prove_refinement.
Qed.

(* Same spec as sorted_insert *)
Lemma sorted_insert_no_malloc_fun_ref : refinesFun sorted_insert_no_malloc sorted_insert_fun.
Proof.
  unfold sorted_insert_no_malloc, sorted_insert_no_malloc__tuple_fun, sorted_insert_fun.
  time "sorted_insert_no_malloc_fun_ref" prove_refinement.
Qed.
