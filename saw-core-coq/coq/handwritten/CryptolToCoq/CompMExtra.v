(***
 *** Extra Proofs for CompM that Rely on SAWCorePrelude
 ***)

From Coq          Require Import Logic.
From Coq          Require        Program.Equality.
From Coq          Require Import Strings.String.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Export CompM.

(* A duplicate from `Program.Equality`, because importing that
   module directly gives us a conflict with the `~=` notation... *)
Tactic Notation "dependent" "destruction" ident(H) := 
  Equality.do_depelim' ltac:(fun hyp => idtac) ltac:(fun hyp => Equality.do_case hyp) H.

(***
 *** Some useful Ltac
 ***)

(* Ltac get_last_hyp tt := *)
(*   match goal with H: _ |- _ => constr:(H) end. *)

Tactic Notation "unfold_projs" :=
  unfold SAWCoreScaffolding.fst, SAWCoreScaffolding.snd;
  cbn [ Datatypes.fst Datatypes.snd projT1 ].

Tactic Notation "unfold_projs" "in" constr(N) :=
  unfold SAWCoreScaffolding.fst, SAWCoreScaffolding.snd in N;
  cbn [ Datatypes.fst Datatypes.snd projT1 ] in N.

Tactic Notation "unfold_projs" "in" "*" :=
  unfold SAWCoreScaffolding.fst, SAWCoreScaffolding.snd in *;
  cbn [ Datatypes.fst Datatypes.snd projT1 ] in *.

Ltac split_prod_hyps :=
  repeat match goal with
         | H: _ /\ _        |- _ => destruct H as [?H ?H]
         | p: { _ : _ & _ } |- _ => destruct p as [?p ?p]
         | p: _ * _         |- _ => destruct p as [?p ?p]
         | u: unit          |- _ => destruct u
         | u: True          |- _ => destruct u
         end.

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
Create HintDb refinesFun.

Hint Extern 999 (_ |= _) => shelve : refinesM.

Hint Resolve refinesM_letRecM_Nil_l : refinesM.

Hint Extern 1 (@letRecM ?lrts _ _ _ |= @letRecM ?lrts _ (lrtLambda (fun _ => _)) _) =>
  apply refinesM_letRecM_const_r; try apply ProperLRTFun_any;
  try (apply refinesFunTuple_multiFixM; unfold refinesFunTuple; split_prod_goal);
  unfold lrtApply, lrtLambda; unfold_projs : refinesM.

Inductive ArgName := Any | Either | Maybe | SigT | If | If0 |
                     Assert | Assuming | Exists | Forall.
Ltac argName n :=
  match n with
  | Any      => fresh "a"
  | Either   => fresh "e_either"
  | Maybe    => fresh "e_maybe"
  | SigT     => fresh "e_either"
  | If       => fresh "e_if"
  | Assert   => fresh "e_assert"
  | Assuming => fresh "e_assuming"
  | Exists   => fresh "e_exists"
  | Forall   => fresh "e_forall"
  end.

Definition IntroArg (n : ArgName) A (goal : A -> Prop) := forall a, goal a.

Hint Opaque IntroArg : refinesM refinesFun.

Definition FreshIntroArg (n : ArgName) A (goal : A -> Prop) := IntroArg n A goal.

Hint Opaque FreshIntroArg : refinesM refinesFun.

Hint Extern 999 (FreshIntroArg _ _ _) => unfold FreshIntroArg : refinesFun.

Lemma IntroArg_fold n A goal : forall a, IntroArg n A goal -> goal a.
Proof. intros a H; exact (H a). Qed.

(* Lemma IntroArg_unfold n A (goal : A -> Prop) : (forall a, goal a) -> IntroArg n A goal. *)
(* Proof. unfold IntroArg; intro H; exact H. Qed. *)

Ltac IntroArg_intro e := intro e; unfold_projs in *.

Ltac IntroArg_forget := let e := fresh in intro e; clear e.

Lemma IntroArg_and n P Q (goal : P /\ Q -> Prop)
  : IntroArg n P (fun p => FreshIntroArg n Q (fun q => goal (conj p q))) -> IntroArg n _ goal.
Proof. intros H [ p q ]; apply H. Qed.

Lemma IntroArg_or n P Q (goal : P \/ Q -> Prop)
  : IntroArg n P (fun p => goal (or_introl p)) ->
    IntroArg n Q (fun q => goal (or_intror q)) -> IntroArg n _ goal.
Proof. intros Hl Hr [ p | q ]; [ apply Hl | apply Hr ]. Qed.

Lemma IntroArg_sigT n A P (goal : {a : A & P a} -> Prop)
  : IntroArg n A (fun a => FreshIntroArg n (P a) (fun p => goal (existT _ a p))) -> IntroArg n _ goal.
Proof. intros H [ a p ]; apply H. Qed.

Lemma IntroArg_prod n P Q (goal : P * Q -> Prop)
  : IntroArg n P (fun p => FreshIntroArg n Q (fun q => goal (pair p q))) -> IntroArg n _ goal.
Proof. intros H [ p q ]; apply H. Qed.

Lemma IntroArg_sum n P Q (goal : P + Q -> Prop)
  : IntroArg n P (fun p => goal (inl p)) ->
    IntroArg n Q (fun q => goal (inr q)) -> IntroArg n _ goal.
Proof. intros Hl Hr [ p | q ]; [ apply Hl | apply Hr ]. Qed.

Lemma IntroArg_unit n (goal : unit -> Prop) : goal tt -> IntroArg n _ goal.
Proof. intros H []. apply H. Qed.

Lemma IntroArg_eq_sigT_const n A B (a a' : A) (b b' : B) (goal : Prop)
  : IntroArg n (a = a') (fun _ => FreshIntroArg n (b = b') (fun _ => goal)) ->
    IntroArg n (existT _ a b = existT _ a' b') (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.

Lemma IntroArg_eq_prod_const n P Q (p p' : P) (q q' : Q) (goal : Prop)
  : IntroArg n (p = p') (fun _ => FreshIntroArg n (q = q') (fun _ => goal)) ->
    IntroArg n (pair p q = pair p' q') (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.

Lemma IntroArg_eq_Left_const n A B (x y : A) (goal : Prop)
  : IntroArg n (x = y) (fun _ => goal) ->
    IntroArg n (SAWCorePrelude.Left A B x = SAWCorePrelude.Left A B y) (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.
Lemma IntroArg_eq_Right_const n A B (x y : B) (goal : Prop)
  : IntroArg n (x = y) (fun _ => goal) ->
    IntroArg n (SAWCorePrelude.Right A B x = SAWCorePrelude.Right A B y) (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.
Lemma IntroArg_eq_Left_Right n A B (x : A) (y : B) goal
  : IntroArg n (SAWCorePrelude.Left A B x = SAWCorePrelude.Right A B y) goal.
Proof. intros eq; discriminate eq. Qed.
Lemma IntroArg_eq_Right_Left n A B (x : A) (y : B) goal
  : IntroArg n (SAWCorePrelude.Right A B y = SAWCorePrelude.Left A B x) goal.
Proof. intros eq; discriminate eq. Qed.

Lemma IntroArg_eq_Just_const n A (x y : A) (goal : Prop)
  : IntroArg n (x = y) (fun _ => goal) ->
    IntroArg n (SAWCorePrelude.Just _ x = SAWCorePrelude.Just _ y) (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.
Lemma IntroArg_eq_Just_Nothing n A (x : A) goal
  : IntroArg n (SAWCorePrelude.Just _ x = SAWCorePrelude.Nothing _) goal.
Proof. intros eq; discriminate eq. Qed.
Lemma IntroArg_eq_Nothing_Just n A (y : A) goal
  : IntroArg n (SAWCorePrelude.Nothing _ = SAWCorePrelude.Just _ y) goal.
Proof. intros eq; discriminate eq. Qed.

(* Hint Resolve IntroArg_and IntroArg_or IntroArg_sigT IntroArg_prod IntroArg_sum *)
(*              IntroArg_unit IntroArg_eq_sigT_const IntroArg_eq_prod_const *)
(*              IntroArg_eq_Left_const IntroArg_eq_Right_const *)
(*              IntroArg_eq_Left_Right IntroArg_eq_Right_Left *)
(*              IntroArg_eq_Just_const IntroArg_eq_Just_Nothing_const *)
(*              IntroArg_eq_Nothing_Just_const | 1 : refinesFun. *)

Ltac IntroArg_intro_dependent_destruction n :=
  let e := argName n in
    IntroArg_intro e; dependent destruction e.

(* Hint Extern 1 (IntroArg ?n (eq (SAWCorePrelude.Nothing _) (SAWCorePrelude.Nothing _)) _) => *)
(*   IntroArg_forget : refinesFun. *)
(* Hint Extern 1 (IntroArg ?n (eq true true) _) => *)
(*   IntroArg_intro_dependent_destruction n : refinesFun. *)
(* Hint Extern 1 (IntroArg ?n (eq false false) _) => *)
(*   IntroArg_intro_dependent_destruction n : refinesFun. *)
(* Hint Extern 1 (IntroArg ?n (eq true false) _) => *)
(*   IntroArg_intro_dependent_destruction n : refinesFun. *)
(* Hint Extern 1 (IntroArg ?n (eq false true) _) => *)
(*   IntroArg_intro_dependent_destruction n : refinesFun. *)
(* Hint Extern 1 (IntroArg ?n (@eq unit _ _) _) => *)
(*   IntroArg_forget : refinesFun. *)

Ltac IntroArg_base_tac n A g :=
  lazymatch A with
  | _ /\ _        => simple apply IntroArg_and
  | _ \/ _        => simple apply IntroArg_or
  (* | { _ : _ & _ } => simple apply IntroArg_sigT *)
  (* | prod _      _ => simple apply IntroArg_prod *)
  | sum _ _       => simple apply IntroArg_sum
  | unit          => simple apply IntroArg_unit
  | existT _ _ _ = existT _ _ _ => simple apply IntroArg_eq_sigT_const
  | pair _ _     = pair _ _     => simple apply IntroArg_eq_prod_const
  | SAWCorePrelude.Left _ _ _  = SAWCorePrelude.Left _ _ _  => simple apply IntroArg_eq_Left_const
  | SAWCorePrelude.Right _ _ _ = SAWCorePrelude.Right _ _ _ => simple apply IntroArg_eq_Right_const
  | SAWCorePrelude.Left _ _ _  = SAWCorePrelude.Right _ _ _ => simple apply IntroArg_eq_Left_Right
  | SAWCorePrelude.Right _ _ _ = SAWCorePrelude.Left _ _ _  => simple apply IntroArg_eq_Right_Left
  | SAWCorePrelude.Just _ _  = SAWCorePrelude.Just _ _  => simple apply IntroArg_eq_Just_const
  | SAWCorePrelude.Just _ _  = SAWCorePrelude.Nothing _ => simple apply IntroArg_eq_Just_Nothing
  | SAWCorePrelude.Nothing _ = SAWCorePrelude.Just _ _  => simple apply IntroArg_eq_Nothing_Just
  | SAWCorePrelude.Nothing _ = SAWCorePrelude.Nothing _ => IntroArg_forget
  | true  = true  => IntroArg_intro_dependent_destruction n
  | false = false => IntroArg_intro_dependent_destruction n
  | true  = false => IntroArg_intro_dependent_destruction n
  | false = true  => IntroArg_intro_dependent_destruction n
  | @eq unit _ _ => IntroArg_forget
  end.

Hint Extern 1 (IntroArg ?n ?A ?g) => IntroArg_base_tac n A g : refinesFun.

Ltac IntroArg_rewrite_bool_eq n :=
  let e := fresh in
    IntroArg_intro e; repeat rewrite e in *;
    apply (IntroArg_fold n _ _ e); clear e.

Hint Extern 2 (IntroArg ?n (@eq bool _ _) _) =>
  progress (IntroArg_rewrite_bool_eq n) : refinesFun.

Hint Extern 4 (IntroArg ?n _ _) =>
  let e := argName n in IntroArg_intro e; subst : refinesFun.

Definition refinesM_either_l_IntroArg {A B C} (f:A -> CompM C) (g:B -> CompM C) eith P :
  (FreshIntroArg Any _ (fun a =>
    FreshIntroArg Either (eith = SAWCorePrelude.Left _ _ a) (fun _ => f a |= P))) ->
  (FreshIntroArg Any _ (fun b =>
    FreshIntroArg Either (eith = SAWCorePrelude.Right _ _ b) (fun _ => g b |= P))) ->
  SAWCorePrelude.either _ _ _ f g eith |= P := refinesM_either_l f g eith P.
Definition refinesM_either_r_IntroArg {A B C} (f:A -> CompM C) (g:B -> CompM C) eith P :
  (FreshIntroArg Any _ (fun a =>
    FreshIntroArg Either (eith = SAWCorePrelude.Left _ _ a) (fun _ => P |= f a))) ->
  (FreshIntroArg Any _ (fun b =>
    FreshIntroArg Either (eith = SAWCorePrelude.Right _ _ b) (fun _ => P |= g b))) ->
  P |= SAWCorePrelude.either _ _ _ f g eith := refinesM_either_r f g eith P.

Hint Extern 1 (SAWCorePrelude.either _ _ _ _ _ _ |= _) =>
  simple apply refinesM_either_l_IntroArg : refinesM.
Hint Extern 1 (_ |= SAWCorePrelude.either _ _ _ _ _ _) =>
  simple apply refinesM_either_r_IntroArg : refinesM.

Definition refinesM_maybe_l_IntroArg {A B} (x : CompM B) (f : A -> CompM B) mb P :
  (FreshIntroArg Maybe (mb = SAWCorePrelude.Nothing _) (fun _ => x |= P)) ->
  (FreshIntroArg Any _ (fun a =>
    FreshIntroArg Maybe (mb = SAWCorePrelude.Just _ a) (fun _ => f a |= P))) ->
  SAWCorePrelude.maybe _ _ x f mb |= P := refinesM_maybe_l x f mb P.
Definition refinesM_maybe_r_IntroArg {A B} (x : CompM B) (f : A -> CompM B) mb P :
  (FreshIntroArg Maybe (mb = SAWCorePrelude.Nothing _) (fun _ => P |= x)) ->
  (FreshIntroArg Any _ (fun a =>
    FreshIntroArg Maybe (mb = SAWCorePrelude.Just _ a) (fun _ => P |= f a))) ->
  P |= SAWCorePrelude.maybe _ _ x f mb := refinesM_maybe_r x f mb P.

Hint Extern 1 (SAWCorePrelude.maybe _ _ _ _ _ |= _) =>
  simple apply refinesM_maybe_l_IntroArg : refinesM.
Hint Extern 1 (_ |= SAWCorePrelude.maybe _ _ _ _ _) =>
  simple apply refinesM_maybe_r_IntroArg : refinesM.

Definition refinesM_sigT_rect_l_IntroArg {A1 A2 B} F P (s: {x:A1 & A2 x}) :
  (FreshIntroArg Any _ (fun a1 => FreshIntroArg Any _ (fun a2 =>
    FreshIntroArg SigT (s = existT _ a1 a2) (fun _ => F a1 a2 |= P)))) ->
  sigT_rect (fun _ => CompM B) F s |= P := refinesM_sigT_rect_l F P s.

Definition refinesM_sigT_rect_r_IntroArg {A1 A2 B} F P (s: {x:A1 & A2 x}) :
  (FreshIntroArg Any _ (fun a1 => FreshIntroArg Any _ (fun a2 =>
    FreshIntroArg SigT (s = existT _ a1 a2) (fun _ => P |= F a1 a2)))) ->
  P |= sigT_rect (fun _ => CompM B) F s := refinesM_sigT_rect_r F P s.

Hint Extern 1 (sigT_rect (fun _ => CompM _) _ _ |= _) =>
  simple apply refinesM_sigT_rect_l_IntroArg : refinesM.
Hint Extern 1 (_ |= sigT_rect (fun _ => CompM _) _ _) =>
  simple apply refinesM_sigT_rect_r_IntroArg : refinesM.

Definition refinesM_if_l_IntroArg {A} (m1 m2:CompM A) b P :
  (FreshIntroArg If (b = true) (fun _ => m1 |= P)) ->
  (FreshIntroArg If (b = false) (fun _ => m2 |= P)) ->
  (if b then m1 else m2) |= P := refinesM_if_l m1 m2 b P.
Definition refinesM_if_r_IntroArg {A} (m1 m2:CompM A) b P :
  (FreshIntroArg If (b = true) (fun _ => P |= m1)) ->
  (FreshIntroArg If (b = false) (fun _ => P |= m2)) ->
  P |= (if b then m1 else m2) := refinesM_if_r m1 m2 b P.

Hint Extern 1 ((if _ then _ else _) |= _) =>
  apply refinesM_if_l_IntroArg : refinesM.
Hint Extern 1 (_ |= (if _ then _ else _)) =>
  apply refinesM_if_r_IntroArg : refinesM.

Hint Extern 1 (returnM (if _ then _ else _) |= _) =>
  simple apply refinesM_returnM_if_l : refinesM.
Hint Extern 1 (_ |= returnM (if _ then _ else _)) =>
  simple apply refinesM_returnM_if_r : refinesM.

Definition refinesM_bindM_assertM_l_IntroArg {A} (P:Prop) (m1 m2: CompM A) :
  (FreshIntroArg Assert P (fun _ => m1 |= m2)) -> assertM P >> m1 |= m2 :=
  refinesM_bindM_assertM_l P m1 m2.
Definition refinesM_assumingM_r_IntroArg {A} (P:Prop) (m1 m2: CompM A) :
  (FreshIntroArg Assuming P (fun _ => m1 |= m2))  -> m1 |= assumingM P m2 :=
  refinesM_assumingM_r P m1 m2.

Hint Extern 1 (assertM _ >> _ |= _) =>
  simple eapply refinesM_bindM_assertM_l_IntroArg : refinesM.
Hint Extern 1 (_ |= assumingM _ _) =>
  simple eapply refinesM_assumingM_r_IntroArg : refinesM.

Hint Extern 2 (_ |= assertM _ >> _) =>
  simple eapply refinesM_bindM_assertM_r; shelve : refinesM.
Hint Extern 2 (assumingM _ _ |= _) =>
  simple eapply refinesM_assumingM_l; shelve : refinesM.

Definition refinesM_existsM_l_IntroArg A B (P: A -> CompM B) Q :
  (FreshIntroArg Exists _ (fun a => P a |= Q)) -> existsM P |= Q :=
  refinesM_existsM_l A B P Q.
Definition refinesM_forallM_r_IntroArg {A B} P (Q: A -> CompM B) :
  (FreshIntroArg Forall _ (fun a => P |= (Q a))) -> P |= (forallM Q) :=
  refinesM_forallM_r P Q.

Hint Extern 2 (existsM _ |= _) =>
  simple apply refinesM_existsM_l_IntroArg : refinesM.
Hint Extern 2 (_ |= forallM _) =>
  simple apply refinesM_forallM_r_IntroArg : refinesM.

Hint Extern 3 (_ |= existsM _) =>
  simple eapply refinesM_existsM_r; shelve : refinesM.
Hint Extern 3 (forallM _ |= _) =>
  simple eapply refinesM_forallM_l; shelve : refinesM.

Hint Extern 3 (returnM _ |= returnM _) =>
  apply refinesM_returnM; (reflexivity || shelve) : refinesM.

Hint Extern 1 (orM _ _ |= _) => simple apply refinesM_orM_l : refinesM.
Hint Extern 1 (_ |= andM _ _) => simple apply refinesM_andM_r : refinesM.
(* Note: For the moment, we don't automatically apply refinesM_orM_r or
   refinesM_andM_l - use continue_prove_refinement_left and
   continue_prove_refinement_right. *)

Lemma refinesM_returnM_bindM_l A B (a:A) (f:A -> CompM B) P :
  f a |= P -> returnM a >>= f |= P.
Proof. rewrite returnM_bindM; eauto. Qed.
Lemma refinesM_returnM_bindM_r A B P (a:A) (f:A -> CompM B) :
  P |= f a -> P |= returnM a >>= f.
Proof. rewrite returnM_bindM; eauto. Qed.

Hint Extern 1 ((returnM _ >>= _) |= _) => simple apply refinesM_returnM_bindM_l : refinesM.
Hint Extern 1 (_ |= (returnM _ >>= _)) => simple apply refinesM_returnM_bindM_r : refinesM.

Lemma refinesM_existsM_bindM_l A B C (P: A -> CompM B) (Q: B -> CompM C) R :
  existsM (fun x => P x >>= Q) |= R -> (existsM P) >>= Q |= R.
Proof. rewrite existsM_bindM; eauto. Qed.
Lemma refinesM_existsM_bindM_r A B C P (Q: A -> CompM B) (R: B -> CompM C) :
  P |= existsM (fun x => Q x >>= R) -> P |= (existsM Q) >>= R.
Proof. rewrite existsM_bindM; eauto. Qed.

Hint Extern 1 ((existsM _ >>= _) |= _) => simple apply refinesM_existsM_bindM_l : refinesM.
Hint Extern 1 (_ |= (existsM _ >>= _)) => simple apply refinesM_existsM_bindM_r : refinesM.

Lemma refinesM_orM_bindM_l A B (m1 m2 : CompM A) (P : A -> CompM B) Q :
  orM (m1 >>= P) (m2 >>= P) |= Q -> (orM m1 m2) >>= P |= Q.
Proof. rewrite orM_bindM; eauto. Qed.
Lemma refinesM_orM_bindM_r A B P (m1 m2 : CompM A) (Q : A -> CompM B) :
  P |= orM (m1 >>= Q) (m2 >>= Q) -> P |= (orM m1 m2) >>= Q.
Proof. rewrite orM_bindM; eauto. Qed.

Hint Extern 1 ((orM _ _ >>= _) |= _) => simple apply refinesM_orM_bindM_l : refinesM.
Hint Extern 1 (_ |= (orM _ _ >>= _)) => simple apply refinesM_orM_bindM_r : refinesM.

Lemma refinesM_errorM_bindM_l A B str (f:A -> CompM B) P :
  errorM str |= P -> errorM str >>= f |= P.
Proof. rewrite errorM_bindM; eauto. Qed.
Lemma refinesM_errorM_bindM_r A B P str (f:A -> CompM B) :
  P |= errorM str -> P |= errorM str >>= f.
Proof. rewrite errorM_bindM; eauto. Qed.

Hint Extern 1 ((errorM _ >>= _) |= _) => simple apply refinesM_errorM_bindM_l : refinesM.
Hint Extern 1 (_ |= (errorM _ >>= _)) => simple apply refinesM_errorM_bindM_r : refinesM.

Lemma refinesM_bindM_bindM_l A B C (m : CompM A) (f : A -> CompM B) (g : B -> CompM C) P :
  m >>= (fun x : A => f x >>= g) |= P -> m >>= f >>= g |= P.
Proof. rewrite bindM_bindM; eauto. Qed.
Lemma refinesM_bindM_bindM_r A B C (m : CompM A) (f : A -> CompM B) (g : B -> CompM C) P :
  P |= m >>= (fun x : A => f x >>= g) -> P |= m >>= f >>= g.
Proof. rewrite bindM_bindM; eauto. Qed.

Hint Extern 1 (((_ >>= _) >>= _) |= _) => simple apply refinesM_bindM_bindM_l : refinesM.
Hint Extern 1 (_ |= ((_ >>= _) >>= _)) => simple apply refinesM_bindM_bindM_r : refinesM.

Lemma refinesM_bindM_returnM_l A (m:CompM A) P :
  m |= P -> m >>= (fun x => returnM x) |= P.
Proof. rewrite bindM_returnM; eauto. Qed.
Lemma refinesM_bindM_returnM_r A P (m:CompM A) :
  P |= m -> P |= m >>= (fun x => returnM x).
Proof. rewrite bindM_returnM; eauto. Qed.

Hint Extern 1 ((_ >>= (fun _ => returnM _)) |= _) => simple apply refinesM_bindM_returnM_l : refinesM.
Hint Extern 1 (_ |= (_ >>= (fun _ => returnM _))) => simple apply refinesM_bindM_returnM_r : refinesM.

Lemma bindM_returnM_sigT_unit A (m:CompM {_:A & unit}) u :
  m >>= (fun x => returnM (existT (fun _ => unit) (projT1 x) u)) ~= m.
Proof.
  assert (forall x u, existT (fun _ => unit) (projT1 x : A) u = x).
  { intros [] []; destruct u0; easy. }
  setoid_rewrite H.
  apply bindM_returnM.
Qed.

Lemma refinesM_bindM_returnM_sigT_unit_l A (m:CompM {_:A & unit}) P :
  m |= P -> m >>= (fun x => returnM (existT (fun _ => unit) (projT1 x) tt)) |= P.
Proof. rewrite bindM_returnM_sigT_unit; eauto. Qed.

Lemma refinesM_bindM_returnM_sigT_unit_r A P (m:CompM {_:A & unit}) :
  P |= m -> P |= m >>= (fun x => returnM (existT (fun _ => unit) (projT1 x) tt)).
Proof. rewrite bindM_returnM_sigT_unit; eauto. Qed.

Hint Extern 1 ((_ >>= (fun _ => returnM (existT _ (projT1 _) _))) |= _) =>
  simple apply refinesM_bindM_returnM_sigT_unit_l : refinesM.
Hint Extern 1 (_ |= (_ >>= (fun _ => returnM  (existT _ (projT1 _) _)))) =>
  simple apply refinesM_bindM_returnM_sigT_unit_r : refinesM.

Lemma refinesM_forallM_bindM_l A B C (P: A -> CompM B) (Q: B -> CompM C) (R : CompM C) :
  forallM (fun a => P a >>= Q) |= R -> (forallM P) >>= Q |= R.
Proof. rewrite forallM_bindM; eauto. Qed.
Lemma refinesM_assumingM_bindM_l A B P (m: CompM A) (Q: A -> CompM B) (R : CompM B) :
  assumingM P (m >>= Q) |= R -> (assumingM P m) >>= Q |= R.
Proof. rewrite assumingM_bindM; eauto. Qed.

Hint Extern 1 (((forallM _) >>= _) |= _) => simple apply refinesM_forallM_bindM_l : refinesM.
Hint Extern 1 (((assumingM _ _) >>= _) |= _) => simple apply refinesM_assumingM_bindM_l : refinesM.

Create HintDb refinement_proofs.
Hint Extern 1 (_ _ >>= _ |= _) =>
  progress (try (rewrite_strat (outermost (hints refinement_proofs)))) : refinesM.

Definition DidInduction {A} (a : A) : Type := unit.

Lemma didInduction {A} (a : A) : DidInduction a.
Proof. exact tt. Qed.

Tactic Notation "doInduction" tactic(ind) tactic(smp) ident(l) :=
  lazymatch goal with
  | H: DidInduction l |- _ => assumption
  | _ => let l' := fresh l in
         ind l l'; try pose proof (didInduction l'); smp
  end.

Tactic Notation "doDestruction" tactic(dst) tactic(smp) ident(l) :=
  let l' := fresh l in dst l l'; smp.

Ltac list_destruct l l' := destruct l as [| ? l'].
Ltac list_induction l l' := induction l as [| ? l'].
Ltac list_simpl := simpl SAWCorePrelude.unfoldList in *; simpl list_rect in *.

Hint Extern 2 (IntroArg ?n (eq (SAWCorePrelude.unfoldList _ ?l)
                               (SAWCorePrelude.Left _ _ _)) _) =>
  doDestruction (list_destruct) (list_simpl) l : refinesFun.
Hint Extern 2 (IntroArg ?n (eq (SAWCorePrelude.unfoldList _ ?l)
                               (SAWCorePrelude.Right _ _ _)) _) =>
  doDestruction (list_destruct) (list_simpl) l : refinesFun.

Hint Extern 9 (list_rect _ _ _ ?l |= _) =>
  doInduction (list_induction) (list_simpl) l : refinesM.
Hint Extern 9 (_ |= list_rect _ _ _ ?l) =>
  doInduction (list_induction) (list_simpl) l : refinesM.

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

Definition errorM_bindM_CompM A B str (f:A -> CompM B) : errorM str >>= f ~= errorM str :=
  errorM_bindM (M:=CompM) A B str f.

Hint Rewrite returnM_bindM_CompM bindM_returnM_CompM bindM_bindM_CompM errorM_bindM_CompM  : refinesM.

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

Definition StartAutomation (goal : Prop) := goal.

Lemma StartAutomation_fold goal : StartAutomation goal -> goal.
Proof. easy. Qed.

Hint Extern 999 (StartAutomation ?A) => unfold StartAutomation : refinesFun.

(* Create HintDb refinesFun. *)
Hint Extern 999 (_ |= _) => shelve : refinesFun.
Hint Extern 999 (refinesFun _ _) => shelve : refinesFun.

(* Definition MaybeDestructArg A (a:A) (goal:Prop) : Prop := goal. *)
(* Definition noDestructArg A a (goal:Prop) : goal -> MaybeDestructArg A a goal := fun g => g. *)

Definition refinesFun_multiFixM_fst' lrt (F:lrtPi (LRT_Cons lrt LRT_Nil)
                                                  (lrtTupleType (LRT_Cons lrt LRT_Nil))) f
      (ref_f:refinesFun (SAWCoreScaffolding.fst (F f)) f) :
  refinesFun (fst (multiFixM F)) f := refinesFun_multiFixM_fst lrt F f ref_f.

Definition refinesFun_fst lrt B f1 (fs:B) f2 (r:@refinesFun lrt f1 f2) :
  refinesFun (SAWCoreScaffolding.fst (f1, fs)) f2 := r.

Hint Resolve refinesFun_fst | 1 : refinesFun.
Hint Resolve refinesFun_multiFixM_fst' | 1 : refinesFun.
(* Hint Resolve noDestructArg | 5 : refinesFun. *)

(* (* If a goal contains W64List_rect applied to l, then destruct l *) *)
(* Ltac destructArg_W64List := *)
(*   (lazymatch goal with *)
(*   | |- MaybeDestructArg ?W64list ?l ?g => *)
(*     match g with *)
(*     | context [SAWCorePrelude.W64List_rect _ _ _ l] => *)
(*       induction l; let IH := get_last_hyp tt in *)
(*       try simpl in IH; try unfold MaybeDestructArg in IH; *)
(*       simpl; apply noDestructArg *)
(*     end *)
(*   end). *)
(* Hint Extern 1 (MaybeDestructArg _ _ _) => destructArg_W64List :refinesFun. *)

(* (* If a goal contains list_rect applied to l, then destruct l *) *)
(* Ltac destructArg_list := *)
(*   (lazymatch goal with *)
(*   | |- MaybeDestructArg (list _) ?l ?g => *)
(*     match g with *)
(*     | context [Datatypes.list_rect _ _ _ l] => *)
(*       induction l; let IH := get_last_hyp tt in *)
(*       try simpl in IH; try unfold MaybeDestructArg in IH; *)
(*       simpl; apply noDestructArg *)
(*     end *)
(*    end). *)
(* Hint Extern 1 (MaybeDestructArg _ _ _) => destructArg_list :refinesFun. *)

Definition refinesFunBase B m1 m2 (r: m1 |= m2) : @refinesFun (LRT_Ret B) m1 m2 := r.
Definition refinesFunStep A lrtF f1 f2
           (r: IntroArg Any _ (fun a => @refinesFun (lrtF a) (f1 a) (f2 a))) :
  @refinesFun (LRT_Fun A lrtF) f1 f2 := r.

Hint Extern 5 (@refinesFun (LRT_Ret _) _ _) =>
  simple apply refinesFunBase; unfold_projs : refinesFun.

Hint Extern 5 (@refinesFun (LRT_Fun _ _) _ _) =>
  simple apply refinesFunStep : refinesFun.


(***
 *** Top-level tactics to put it all together
 ***)

Variant ProveRefOpts := Default | NoRewrite | NoDestructProds | NoRewriteNoDestructProds.

Ltac prove_refinement_eauto :=
  unshelve (typeclasses eauto with refinesM refinesFun).
Ltac prove_refinement_destruct_prod_hyps :=
  split_prod_hyps; unfold_projs in *.
Ltac prove_refinement_rewrite :=
  try unshelve (rewrite_strat (bottomup (hints refinesM))).
Ltac prove_refinement_try_solve :=
  split_prod_goal;
  try reflexivity || contradiction.

Tactic Notation "prove_refinement_core" "with" constr(opts) :=
  prove_refinement_eauto;
  match opts with
  | Default => prove_refinement_destruct_prod_hyps; prove_refinement_rewrite
  | NoRewrite => prove_refinement_destruct_prod_hyps
  | NoDestructProds => prove_refinement_rewrite
  | NoRewriteNoDestructProds => idtac
  end;
  prove_refinement_try_solve.

Ltac prove_refinement_core := prove_refinement_core with Default.

(* Automatically prove refinements of the form `refinesFun F G` or of the
   form` P |= Q`, where P,Q may contain matching calls to `letRecM`. *)

Tactic Notation "prove_refinement" "with" constr(opts) :=
  unfold_projs; unfold Eq, Refl, SAWCoreScaffolding.Bool;
  apply StartAutomation_fold;
  prove_refinement_core with opts.

Ltac prove_refinement := prove_refinement with Default.

(* After a call to `prove_refinement`, give user input as to whether to continue
   proof automation in the left or right branch of an `orM`/`andM`. *)

Tactic Notation "continue_prove_refinement_lr" tactic(tac) "with" constr(opts) :=
  match goal with
  | |- _ |= orM _ _ => apply refinesM_orM_r; tac; prove_refinement_core with opts
  | |- andM _ _ |= _ => apply refinesM_andM_l; tac; prove_refinement_core with opts
  end.

Tactic Notation "continue_prove_refinement_left" "with" constr(opts) :=
  continue_prove_refinement_lr (left) with opts.
Tactic Notation "continue_prove_refinement_right" "with" constr(opts) :=
  continue_prove_refinement_lr (right) with opts.

Ltac continue_prove_refinement_left := continue_prove_refinement_left with Default.
Ltac continue_prove_refinement_right := continue_prove_refinement_right with Default.

(* For refinements of the form `refinesFun F G` or `P |= Q` where a subexpression
   on the left has a call to `letRecM` which does not match one on the right,
   this tactic tries to prove the refinement by transitivity, where the new
   middle expression has a `letRecM` which matches the one on the left as per
   `refinesM_letRecM_match_r`. After giving values for each of the needed
   functions, call `prove_refinement` to continue automation. *)

Ltac prove_refinement_match_letRecM_l :=
  prove_refinement_eauto;
  unshelve (eapply refinesM_letRecM_match_r);
  [ unfold lrtTupleType, lrtToType; repeat split | apply ProperLRTFun_any | ].

(* It's important for the tactic above that `letRecM` is opaque! Otherwise
   `eauto` will unfold it too soon. *)
Hint Opaque letRecM : refinesM refinesFun.

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
