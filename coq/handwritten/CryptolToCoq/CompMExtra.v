(***
 *** Extra Proofs for CompM that Rely on SAWCorePrelude
 ***)

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Export CompM.

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


(*
Ltac rewrite_refinesM :=
  try ((rewrite returnM_bindM || rewrite bindM_returnM || rewrite bindM_bindM ||
        rewrite errorM_bindM || rewrite existsM_bindM); rewrite_refinesM).
*)

Ltac prove_refinesM :=
  lazymatch goal with
  (* Bind cases *)
  | |- (returnM _ >>= _) |= _ => rewrite returnM_bindM; prove_refinesM
  | |- _ |= (returnM _ >>= _) => rewrite returnM_bindM; prove_refinesM
  | |- (existsM _ >>= _) |= _ => rewrite existsM_bindM; prove_refinesM
  | |- _ |= (existsM _ >>= _) => rewrite existsM_bindM; prove_refinesM
  | |- (errorM >>= _) |= _ => rewrite errorM_bindM; prove_refinesM
  | |- _ |= (errorM >>= _) => rewrite errorM_bindM; prove_refinesM
  | |- ((_ >>= _) >>= _) |= _ => rewrite bindM_bindM; prove_refinesM
  | |- _ |= ((_ >>= _) >>= _) => rewrite bindM_bindM; prove_refinesM

  (* letRecM cases *)
  | |- letRecM tt _ |= _ => apply refinesM_letRecM0; prove_refinesM

  (* either *)
  | |- SAWCorePrelude.either _ _ _ _ _ _ |= _ =>
    apply refinesM_either_l; intros; prove_refinesM
  | |- _ |= SAWCorePrelude.either _ _ _ _ _ _ =>
    apply refinesM_either_r; intros; prove_refinesM
  | |- sigT_rect _ _ _ |= _ =>

  (* sigT_rect *)
    apply refinesM_sigT_rect_l; intros; prove_refinesM
  | |- _ |= sigT_rect _ _ _ =>
    apply refinesM_sigT_rect_r; intros; prove_refinesM

  (* if *)
  | |- (if _ then _ else _) |= _ =>
    apply refinesM_if_l; intros; prove_refinesM
  | |- _ |= (if _ then _ else _) =>
    apply refinesM_if_r; intros; prove_refinesM

  (* quantifiers *)
  | |- existsM _ |= _ => apply refinesM_existsM_l; intros; prove_refinesM
  | |- _ |= forallM _ => apply refinesM_forallM_r; intros; prove_refinesM
  | |- _ |= existsM _ => eapply refinesM_existsM_r; prove_refinesM
  | |- forallM _ |= _ => eapply refinesM_forallM_l; prove_refinesM
  | |- returnM _ |= returnM _ => apply refinesM_returnM; intros; try reflexivity

  (* default: give up! *)
  | _ => idtac (* try (progress (autorewrite with refinesM) ; prove_refinesM) *)
  end.

Ltac prove_refinesFun :=
  apply refinesFun_multiFixM_fst; simpl; intros; prove_refinesM.


(*
FIXME: it would be nice if we could rewrite under binders, but the sigT_rect
rule requires rewriting under a dependent binder, which I'm not sure how to do...

Instance Proper_either A B C (RC:relation C) :
  Proper ((eq ==> RC) ==> (eq ==> RC) ==> eq ==> RC) (either A B C).
Proof.
  intros f1 f2 Rf g1 g2 Rg eith1 eith2 Reith. rewrite Reith.
  destruct eith2; simpl; [ apply Rf | apply Rg ]; reflexivity.
Qed.

Print is_elem__tuple_fun.
Print sigT_rect.


Instance Proper_sigT_rect A (B:A -> Type) C (RC:relation C) :
  Proper ((eq ==> eq ==> RC) ==> eq ==> RC) (@sigT_rect A B (fun _ => C)).
*)
