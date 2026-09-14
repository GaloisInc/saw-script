(**
 * This generalizes the default_nan_pl{32,64} definitions from IEEE754.Bits to
 * work over any precision.
 *)

From Stdlib Require Import Lia SpecFloat ZArith.
From Flocq Require Import Core IEEE754.Binary.

Lemma digits2_pos_iter_nat (n : nat) :
  SpecFloat.digits2_pos (Zaux.iter_nat xO n 1%positive) = Pos.of_succ_nat n.
Proof.
induction n.
- easy.
- rewrite Zaux.iter_nat_S.
  simpl.
  now rewrite IHn.
Qed.

Section Binary_Bits_Extra.

Arguments exist {A} {P}.
Arguments B754_nan {prec} {emax}.

(** Number of bits for the fraction and exponent *)
Variable mw ew : positive.

Let prec := Z.pos (Pos.succ mw).
Let emax := Zpower 2 (Z.pos ew - 1).
Notation binary_float := (binary_float prec emax) (only parsing).

Definition default_pl : positive :=
  Zaux.iter_nat xO (Z.to_nat (prec - 2)) 1%positive.

Lemma nan_pl_default_pl :
  nan_pl prec default_pl = true.
Proof.
unfold nan_pl, default_pl, prec'.
rewrite digits2_pos_iter_nat.
rewrite Zpos_P_of_succ_nat.
rewrite (Z2Nat.id (prec - 2)).
- change (prec - 2)%Z with (prec + (-1 + -1))%Z.
  rewrite Z.add_assoc.
  change (prec + -1 + -1)%Z with (Z.pred (prec - 1))%Z.
  rewrite <- (Zsucc_pred (prec - 1)).
  lia.
- lia.
Qed.

Definition default_nan_pl : { nan : binary_float | is_nan prec emax nan = true } :=
  exist (B754_nan false default_pl nan_pl_default_pl) (refl_equal true).

End Binary_Bits_Extra.
