(***
 *** Extra Proofs for CompM that Rely on SAWCorePrelude
 ***)

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Export CompM.

Lemma refinesM_either {A B C} (f:A -> CompM C) (g:B -> CompM C) eith P :
  (forall a, eith = SAWCorePrelude.Left _ _ a -> f a |= P) ->
  (forall b, eith = SAWCorePrelude.Right _ _ b -> g b |= P) ->
  SAWCorePrelude.either _ _ _ f g eith |= P.
Proof.
  destruct eith; intros; simpl.
  - apply H; reflexivity.
  - apply H0; reflexivity.
Qed.
