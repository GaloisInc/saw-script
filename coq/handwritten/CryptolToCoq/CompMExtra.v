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

Hint Extern 999 (_ |= _) => shelve : refinesM.

Hint Resolve refinesM_letRecM_Nil_l : refinesM.

Hint Extern 1 (@letRecM ?lrts _ _ _ |= @letRecM ?lrts _ (lrtLambda (fun _ => _)) _) =>
  apply refinesM_letRecM_const_r; try apply ProperLRTFun_any;
  try (apply refinesFunTuple_multiFixM; unfold refinesFunTuple; split_prod_goal);
  unfold lrtApply, lrtLambda; unfold_projs : refinesM.

Inductive ArgName := Any | Either | Maybe | SigT | If | Assert | Assuming | Exists | Forall.
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

Definition IntroArg (_ : ArgName) A (goal : A -> Prop) := forall a, goal a.

Lemma IntroArg_fold n A goal : forall a, IntroArg n A goal -> goal a.
Proof. unfold IntroArg; intros a H; exact (H a). Qed.

Lemma IntroArg_unfold n A (goal : A -> Prop) : (forall a, goal a) -> IntroArg n A goal.
Proof. unfold IntroArg; intro H; exact H. Qed.

Lemma IntroArg_and n P Q (goal : P /\ Q -> Prop)
  : IntroArg n P (fun p => IntroArg n Q (fun q => goal (conj p q))) -> IntroArg n _ goal.
Proof. unfold IntroArg; intros H [ p q ]; apply H. Qed.

Lemma IntroArg_or n P Q (goal : P \/ Q -> Prop)
  : IntroArg n P (fun p => goal (or_introl p)) ->
    IntroArg n Q (fun q => goal (or_intror q)) -> IntroArg n _ goal.
Proof. unfold IntroArg; intros Hl Hr [ p | q ]; [ apply Hl | apply Hr ]. Qed.

Lemma IntroArg_sigT n A P (goal : {a : A & P a} -> Prop)
  : IntroArg n A (fun a => IntroArg n (P a) (fun p => goal (existT _ a p))) -> IntroArg n _ goal.
Proof. unfold IntroArg; intros H [ a p ]; apply H. Qed.

Lemma IntroArg_prod n P Q (goal : P * Q -> Prop)
  : IntroArg n P (fun p => IntroArg n Q (fun q => goal (pair p q))) -> IntroArg n _ goal.
Proof. unfold IntroArg; intros H [ p q ]; apply H. Qed.

Lemma IntroArg_sum n P Q (goal : P + Q -> Prop)
  : IntroArg n P (fun p => goal (inl p)) ->
    IntroArg n Q (fun q => goal (inr q)) -> IntroArg n _ goal.
Proof. unfold IntroArg; intros Hl Hr [ p | q ]; [ apply Hl | apply Hr ]. Qed.

Lemma IntroArg_unit n (goal : unit -> Prop) : goal tt -> IntroArg n _ goal.
Proof. unfold IntroArg; intros H []. apply H. Qed.

Lemma IntroArg_eq_sigT_const n A B (a a' : A) (b b' : B) (goal : Prop)
  : IntroArg n (a = a') (fun _ => IntroArg n (b = b') (fun _ => goal)) ->
    IntroArg n (existT _ a b = existT _ a' b') (fun _ => goal).
Proof.
  unfold IntroArg; intros H eq.
  injection eq; intros.
  apply H; assumption.
Qed.

Hint Resolve IntroArg_and IntroArg_or IntroArg_sigT IntroArg_prod IntroArg_sum
             IntroArg_unit IntroArg_eq_sigT_const | 1 : refinesM.

Hint Extern 2 (IntroArg ?n (@eq bool _ _) _) =>
  let e := fresh in
    apply IntroArg_unfold; intro e; unfold_projs in e;
    progress (compute_bv_funs in e; autorewrite with SAWCoreBitvectors in e);
    apply (IntroArg_fold n _ _ e); clear e : refinesM.

Hint Extern 3 (IntroArg ?n (isBvsle _ _ _) _) =>
  let e := argName n in
  let e' := fresh in
    apply IntroArg_unfold; intro e; assert (e' := e);
    unfold isBvsle in e'; try rewrite e'; clear e' : refinesM.
Hint Extern 3 (IntroArg ?n (isBvslt _ _ _) _) =>
  let e := argName n in
  let e' := fresh in
    apply IntroArg_unfold; intro e; assert (e' := e);
    unfold isBvslt in e'; try rewrite e'; clear e' : refinesM.
Hint Extern 3 (IntroArg ?n (isBvule _ _ _) _) =>
  let e := argName n in
  let e' := fresh in
    apply IntroArg_unfold; intro e; assert (e' := e);
    unfold isBvule in e'; try rewrite e'; clear e' : refinesM.
Hint Extern 3 (IntroArg ?n (isBvult _ _ _) _) =>
  let e := argName n in
  let e' := fresh in
    apply IntroArg_unfold; intro e; assert (e' := e);
    unfold isBvult in e'; try rewrite e'; clear e' : refinesM.

Hint Extern 3 (IntroArg ?n (@eq ?T _ _) _) =>
  let e := argName n in
    apply IntroArg_unfold; intro e; unfold_projs in e;
    (match T with
     | bitvector _ => idtac
     | _ => try discriminate e; unfold_projs; try rewrite e
     end);
    try (match T with
         | Either _ _ => let e' := argName n in injection e; intro e'; try rewrite <- e'
         | Maybe _    => let e' := argName n in injection e; intro e'; try rewrite <- e'
         | {_ : _ & _ } => let e' := argName n in let e'' := argName n in
                             injection e; intros e' e''; clear e'; try rewrite <- e''
         end) : refinesM.

Hint Extern 4 (IntroArg ?n _ _) =>
  let e := argName n in
    apply IntroArg_unfold; intro e; compute_bv_funs in e : refinesM.

Definition refinesM_either_l' {A B C} (f:A -> CompM C) (g:B -> CompM C) eith P :
  (IntroArg Any _ (fun a => IntroArg Either (eith = SAWCorePrelude.Left _ _ a) (fun _ => f a |= P))) ->
  (IntroArg Any _ (fun b => IntroArg Either (eith = SAWCorePrelude.Right _ _ b) (fun _ => g b |= P))) ->
  SAWCorePrelude.either _ _ _ f g eith |= P := refinesM_either_l f g eith P.
Definition refinesM_either_r' {A B C} (f:A -> CompM C) (g:B -> CompM C) eith P :
  (IntroArg Any _ (fun a => IntroArg Either (eith = SAWCorePrelude.Left _ _ a) (fun _ => P |= f a))) ->
  (IntroArg Any _ (fun b => IntroArg Either (eith = SAWCorePrelude.Right _ _ b) (fun _ => P |= g b))) ->
  P |= SAWCorePrelude.either _ _ _ f g eith := refinesM_either_r f g eith P.

Hint Resolve refinesM_either_l' refinesM_either_r' | 1 : refinesM.

Definition refinesM_maybe_l' {A B} (x : CompM B) (f : A -> CompM B) mb P :
  (IntroArg Maybe (mb = SAWCorePrelude.Nothing _) (fun _ => x |= P)) ->
  (IntroArg Any _ (fun a => IntroArg Maybe (mb = SAWCorePrelude.Just _ a) (fun _ => f a |= P))) ->
  SAWCorePrelude.maybe _ _ x f mb |= P := refinesM_maybe_l x f mb P.
Definition refinesM_maybe_r' {A B} (x : CompM B) (f : A -> CompM B) mb P :
  (IntroArg Maybe (mb = SAWCorePrelude.Nothing _) (fun _ => P |= x)) ->
  (IntroArg Any _ (fun a => IntroArg Maybe (mb = SAWCorePrelude.Just _ a) (fun _ => P |= f a))) ->
  P |= SAWCorePrelude.maybe _ _ x f mb := refinesM_maybe_r x f mb P.

Hint Resolve refinesM_maybe_l' refinesM_maybe_r' | 1 : refinesM.

Definition refinesM_sigT_rect_l' {A1 A2 B} F P (s: {x:A1 & A2 x}) :
  (IntroArg Any _ (fun a1 => IntroArg Any _ (fun a2 =>
    IntroArg SigT (s = existT _ a1 a2) (fun _ => F a1 a2 |= P)))) ->
  sigT_rect (fun _ => CompM B) F s |= P := refinesM_sigT_rect_l F P s.

Definition refinesM_sigT_rect_r' {A1 A2 B} F P (s: {x:A1 & A2 x}) :
  (IntroArg Any _ (fun a1 => IntroArg Any _ (fun a2 =>
    IntroArg SigT (s = existT _ a1 a2) (fun _ => P |= F a1 a2)))) ->
  P |= sigT_rect (fun _ => CompM B) F s := refinesM_sigT_rect_r F P s.

Hint Resolve refinesM_sigT_rect_l' refinesM_sigT_rect_r' | 1 : refinesM.

Definition refinesM_if_l' {A} (m1 m2:CompM A) b P :
  (IntroArg If (b = true) (fun _ => m1 |= P)) ->
  (IntroArg If (b = false) (fun _ => m2 |= P)) ->
  (if b then m1 else m2) |= P := refinesM_if_l m1 m2 b P.

Definition refinesM_if_r' {A} (m1 m2:CompM A) b P :
  (IntroArg If (b = true) (fun _ => P |= m1)) ->
  (IntroArg If (b = false) (fun _ => P |= m2)) ->
  P |= (if b then m1 else m2) := refinesM_if_r m1 m2 b P.

Hint Resolve refinesM_if_l' refinesM_if_r' | 1 : refinesM.

Hint Extern 1 (returnM (if _ then _ else _) |= _) =>
  apply refinesM_returnM_if_l : refinesM.
Hint Extern 1 (_ |= returnM (if _ then _ else _)) =>
  apply refinesM_returnM_if_r : refinesM.

Definition refinesM_bindM_assertM_l' {A} (P:Prop) (m1 m2: CompM A) :
  (IntroArg Assert P (fun _ => m1 |= m2)) -> assertM P >> m1 |= m2 :=
  refinesM_bindM_assertM_l P m1 m2.
Definition refinesM_assumingM_r' {A} (P:Prop) (m1 m2: CompM A) :
  (IntroArg Assuming P (fun _ => m1 |= m2))  -> m1 |= assumingM P m2 :=
  refinesM_assumingM_r P m1 m2.

Hint Resolve refinesM_bindM_assertM_l' refinesM_assumingM_r' | 1 : refinesM.

Hint Extern 2 (_ |= assertM _ >> _) =>
  eapply refinesM_bindM_assertM_r; shelve : refinesM.
Hint Extern 2 (assumingM _ _ |= _) =>
  eapply refinesM_assumingM_l; shelve : refinesM.

Definition refinesM_existsM_l' A B (P: A -> CompM B) Q :
  (IntroArg Exists _ (fun a => P a |= Q)) -> existsM P |= Q :=
  refinesM_existsM_l A B P Q.
Definition refinesM_forallM_r' {A B} P (Q: A -> CompM B) :
  (IntroArg Forall _ (fun a => P |= (Q a))) -> P |= (forallM Q) :=
  refinesM_forallM_r P Q.

Hint Resolve refinesM_existsM_l' refinesM_forallM_r' | 2 : refinesM.

(* Hint Extern 2 (existsM _ |= _) => apply refinesM_existsM_l; intro_destruct_prods_sums : refinesM. *)
(* Hint Extern 2 (_ |= forallM _) => apply refinesM_forallM_r; intro_destruct_prods_sums : refinesM. *)
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

Create HintDb refinement_proofs.
Hint Extern 1 (_ _ >>= _ |= _) =>
  progress (try (rewrite_strat (outermost (hints refinement_proofs)))) : refinesM.

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

Definition MaybeDestructArg A (a:A) (goal:Prop) : Prop := goal.
Definition noDestructArg A a (goal:Prop) : goal -> MaybeDestructArg A a goal := fun g => g.

Definition refinesFun_multiFixM_fst' lrt (F:lrtPi (LRT_Cons lrt LRT_Nil)
                                                  (lrtTupleType (LRT_Cons lrt LRT_Nil))) f
      (ref_f:refinesFun (SAWCoreScaffolding.fst (F f)) f) :
  refinesFun (fst (multiFixM F)) f := refinesFun_multiFixM_fst lrt F f ref_f.

Definition refinesFun_fst lrt B f1 (fs:B) f2 (r:@refinesFun lrt f1 f2) :
  refinesFun (SAWCoreScaffolding.fst (f1, fs)) f2 := r.

Hint Resolve refinesFun_fst | 1 : refinesFun.
Hint Resolve refinesFun_multiFixM_fst' | 1 : refinesFun.
Hint Resolve noDestructArg | 5 : refinesFun.

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
           (r: IntroArg Any _ (fun a => MaybeDestructArg A a (@refinesFun (lrtF a) (f1 a) (f2 a)))) :
  @refinesFun (LRT_Fun A lrtF) f1 f2 := r.

Hint Extern 5 (@refinesFun (LRT_Ret _) _ _) =>
  simple apply refinesFunBase; unfold_projs : refinesFun.

Hint Extern 5 (@refinesFun (LRT_Fun _ _) _ _) =>
  simple apply refinesFunStep : refinesFun.


(***
 *** Top-level tactics to put it all together
 ***)

Ltac prove_refinement_core :=
  unshelve (typeclasses eauto with refinesM refinesFun);
  try (unshelve (rewrite_strat (bottomup (hints refinesM))));
  unfold_projs in *; split_prod_goal;
  try reflexivity || contradiction.

(* Automatically prove refinements of the form `refinesFun F G` or of the
   form` P |= Q`, where P,Q may contain matching calls to `letRecM`. *)
Ltac prove_refinement :=
  unfold_projs; compute_bv_funs;
  prove_refinement_core.

(* After a call to `prove_refinement`, give user input as to whether to continue
   proof automation in the left or right branch of an `orM`/`andM`. *)
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

(* For refinements of the form `refinesFun F G` or `P |= Q` where a subexpression
   on the left has a call to `letRecM` which does not match one on the right,
   this tactic tries to prove the refinement by transitivity, where the new
   middle expression has a `letRecM` which matches the one on the left as per
   `refinesM_letRecM_match_r`. After giving values for each of the needed
   functions, call `prove_refinement` to continue automation. *)
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
