(*
 * Bitvectors.
 * The type is "bitvector w" where "w" is the width (in nat).
 *
 * See the notes at the top of Vector.v for further commentary;
 * these two files are really one component.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith NArith ZArith Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Eqdep.
From Stdlib Require Import Eqdep_dec.
(*From Stdlib Require Import JMeq.*)
(*From Stdlib Require Import FunctionalExtensionality.*)

From CryptolToRocq Require Import Vector.

(*
 * Current state:
 *   - all the things listed in Vector.v
 *   - something is wrong with multiply
 *)


(*************************************************************)
(* bitvector *)

(*
 * Bitvectors are vectors of bool.
 *
 * The least significant bit is at the near (cons) end of the vector.
 *
 * This makes the representation of bitvectors backward if you look
 * at them in list order. Recommendation: just don't do that.
 *)
Notation bitvector n := (Vec bool n).

(*
 * zero.
 *)
Definition bvZero (w: nat) : bitvector w :=
   gen w (fun _ => false).

(*
 * one.
 *)
Definition bvOne (w: nat) : bitvector w :=
   gen w (fun i =>
          match i with
          | 0 => true
          | _ => false
          end).

(*
 * minus one, aka all-bits-1
 *)
Definition bvMinusOne (w: nat) : bitvector w :=
   gen w (fun _ => true).

(* unfolding these if you didn't ask is confusing and messy *)
Arguments bvZero: simpl never.
Arguments bvOne: simpl never.
Arguments bvMinusOne: simpl never.

(*
 * zero isn't one
 *)
Lemma bvZero_not_one: forall w, 0 < w -> bvZero w <> bvOne w.
Proof.
   intros * Hgt.
   destruct w; try lia.
   unfold bvZero. unfold bvOne. unfold gen.
   simpl.
   assert (w - w = 0) as -> by lia.
   congruence.
Qed.

(*
 * zero also isn't minus one
 *)
Lemma bvZero_not_minusOne: forall w, 0 < w -> bvZero w <> bvMinusOne w.
Proof.
   intros * Hgt.
   destruct w; try lia.
   unfold bvZero. unfold bvMinusOne. unfold gen.
   simpl.
   congruence.
Qed.

(*
 * one isn't minus one
 *)
Lemma bvOne_not_minusOne: forall w, 1 < w -> bvOne w <> bvMinusOne w.
Proof.
   intros * Hgt.
   destruct w; try lia.
   destruct w; try lia.
   unfold bvOne. unfold bvMinusOne. unfold gen.
   simpl.
   assert (w - w = 0) as -> by lia.
   destruct w; try congruence.
   assert (S w - w = 1) as -> by lia.
   congruence.
Qed.

(*
 * ...unless the width is 1.
 *)
Lemma bvOne_is_minusOne: bvOne 1 = bvMinusOne 1.
Proof.
   unfold bvOne. unfold bvMinusOne. unfold gen.
   simpl; auto.
Qed.

(*
 * zero of length 0 is nil.
 *)
Lemma bvZero_0: bvZero 0 = NilVec bool.
Proof.
   unfold bvZero. unfold gen.
   simpl; auto.
Qed.

(*
 * one of length 0 is nil.
 * (note that all vectors of length zero are also zero)
 *)
Lemma bvOne_0: bvOne 0 = NilVec bool.
Proof.
   unfold bvOne. unfold gen.
   simpl; auto.
Qed.

(*
 * minusOne of length 0 is nil.
 * (note that all vectors of length zero are also zero)
 *)
Lemma bvMinusOne_0: bvMinusOne 0 = NilVec bool.
Proof.
   unfold bvMinusOne. unfold gen.
   simpl; auto.
Qed.

(*
 * zero of S length is a cons.
 *)
Lemma bvZero_S: forall w, bvZero (S w) = ConsVec false (bvZero w).
Proof.
   intros. unfold bvZero. unfold gen. simpl.
   rewrite gen_visit_S_l; try lia.
   auto.
Qed.

(*
 * one of S length is a cons, and in particular it's a one bit and the
 * rest is zero.
 *)
Lemma bvOne_S: forall w, bvOne (S w) = ConsVec true (bvZero w).
Proof.
   intros. unfold bvOne. unfold bvZero. unfold gen. simpl.
   assert (w - w = 0) as -> by lia.
   rewrite gen_visit_S_l; try lia.
   auto.
Qed.

(*
 * minusone of S length is a cons.
 *)
Lemma bvMinusOne_S: forall w, bvMinusOne (S w) = ConsVec true (bvMinusOne w).
Proof.
   intros. unfold bvMinusOne. unfold gen. simpl.
   rewrite gen_visit_S_l; try lia.
   auto.
Qed.

(*
 * consing false onto zero makes another zero.
 *)
Lemma ConsVec_false_bvZero: forall w, ConsVec false (bvZero w) = bvZero (S w).
Proof.
   intros.
   rewrite bvZero_S; auto.
Qed.

(*
 * consing true onto zero makes one.
 *)
Lemma ConsVec_true_bvZero: forall w, ConsVec true (bvZero w) = bvOne (S w).
Proof.
   intros.
   rewrite bvOne_S.
   auto.
Qed.

(*
 * consing true onto minusone makes another minusone.
 *)
Lemma ConsVec_true_bvMinusOne: forall w,
   ConsVec true (bvMinusOne w) = bvMinusOne (S w).
Proof.
   intros.
   rewrite bvMinusOne_S.
   auto.
Qed.

(*
 * There's only one zero of each length.
 *)
Lemma bvZero_unique: forall w w' pf, coerceVec w pf (bvZero w') = bvZero w.
Proof.
   intros.
   destruct pf.
   simpl; auto.
Qed.

(*
 * There's only one one of each length.
 *)
Lemma bvOne_unique: forall w w' pf, coerceVec w pf (bvOne w') = bvOne w.
Proof.
   intros.
   destruct pf.
   simpl; auto.
Qed.

(*
 * There's only one minusone of each length.
 *)
Lemma bvMinusOne_unique: forall w w' pf,
   coerceVec w pf (bvMinusOne w') = bvMinusOne w.
Proof.
   intros.
   destruct pf.
   simpl; auto.
Qed.

(*
 * head of zero is false
 *)
Lemma head_bvZero: forall w, head (bvZero (S w)) = false.
Proof.
Admitted.

(*
 * head of one is true
 *)
Lemma head_bvOne: forall w, head (bvOne (S w)) = true.
Proof.
Admitted.

(*
 * head of minusone is true
 *)
Lemma head_bvMinusOne: forall w, head (bvMinusOne (S w)) = true.
Proof.
Admitted.

(*
 * tail of zero is zero
 *)
Lemma tail_bvZero: forall w, tail (bvZero (S w)) = bvZero w.
Proof.
Admitted.

(*
 * tail of one is zero
 *)
Lemma tail_bvOne: forall w, tail (bvOne (S w)) = bvZero w.
Proof.
Admitted.

(*
 * tail of minusone is minusone
 *)
Lemma tail_bvMinusOne: forall w, tail (bvMinusOne (S w)) = bvMinusOne w.
Proof.
Admitted.

(*
 * appending zero to zero gives zero
 *)
Lemma append_bvZero_bvZero: forall w1 w2,
   append (bvZero w1) (bvZero w2) = bvZero (w1 + w2).
Proof.
Admitted.

(*
 * appending one to zero gives one
 * (remember, the lowest-order bit is on the left and thus the lowest
 * order subword is on the left of append)
 *)
Lemma append_bvOne_bvZero: forall w1 w2,
   append (bvOne w1) (bvZero w2) = bvOne (w1 + w2).
Proof.
Admitted.

(*
 * appending minusone to minusone gives minusone
 *)
Lemma append_bvMinusOne_bvMinusOne: forall w1 w2,
   append (bvMinusOne w1) (bvMinusOne w2) = bvMinusOne (w1 + w2).
Proof.
Admitted.

(*
 * reversing zero is still zero
 *)
Lemma reverse_bvZero: forall w, reverse (bvZero w) = bvZero w.
Proof.
   intros.
   unfold bvZero.
   rewrite reverse_gen.
   auto.
Qed.

(*
 * reversing minusone is still minusone
 *)
Lemma reverse_bvMinusOne: forall w, reverse (bvMinusOne w) = bvMinusOne w.
Proof.
   intros.
   unfold bvMinusOne.
   rewrite reverse_gen.
   auto.
Qed.

(*
 * All the bits of zero are false.
 *)
Lemma atOption_bvZero: forall w k, k < w -> atOption (bvZero w) k = Some false.
Proof.
   intros * Hlt.
   unfold bvZero.
   rewrite atOption_gen; auto.
Qed.

(*
 * The bottom bit of one is true.
 *)
Lemma atOption_bvOne_0: forall w, 0 < w -> atOption (bvOne w) 0 = Some true.
Proof.
   intros.
   unfold bvOne.
   rewrite atOption_gen; auto.
Qed.

(*
 * The rest of the bits of one are false.
 *)
Lemma atOption_bvOne: forall w k, 0 < k -> k < w ->
   atOption (bvOne w) k = Some false.
Proof.
   intros.
   unfold bvOne.
   rewrite atOption_gen; auto.
   destruct k; auto; lia.
Qed.

(*
 * All the bits of minusone are true.
 *)
Lemma atOption_bvMinusOne: forall w k, k < w ->
   atOption (bvMinusOne w) k = Some true.
Proof.
   intros.
   unfold bvMinusOne.
   rewrite atOption_gen; auto.
Qed.

(*
 * taking from zero gives zero
 *)
Lemma take_bvZero: forall w k, take k (bvZero w) = bvZero (min w k).
Proof.
   intros.
   revert k.
   induction w; intros.
   - rewrite bvZero_0.
     destruct k.
     + rewrite take_0_l. rewrite coerceVec_vacuous; auto.
     + simpl. rewrite coerceVec_vacuous; auto.
   - rewrite bvZero_S.
     destruct k.
     + rewrite take_0_l.
       rewrite coerceVec_vacuous. simpl; auto.
     + simpl. rewrite bvZero_S. rewrite IHw. auto.
Qed.

(*
 * taking from one gives one (assuming you take at least one bit)
 * (remember, the lowest-order bit is on the left and thus the lowest
 * order bit is first out when you take)
 *)
Lemma take_bvOne: forall w k, 0 < k -> take k (bvOne w) = bvOne (min w k).
Proof.
   intros * Hgt.
   revert Hgt.
   revert k.
   destruct w; intros.
   - rewrite bvOne_0. destruct k; try lia. simpl.
     rewrite coerceVec_vacuous; auto.
   - rewrite bvOne_S. destruct k; try lia. simpl.
     rewrite bvOne_S. rewrite take_bvZero. auto.
Qed.

(*
 * taking from minusone gives minusone
 *)
Lemma take_bvMinusOne: forall w k, take k (bvMinusOne w) = bvMinusOne (min w k).
Proof.
   intros.
   revert k.
   induction w; intros.
   - rewrite bvMinusOne_0.
     destruct k.
     + rewrite take_0_l. rewrite coerceVec_vacuous; auto.
     + simpl. rewrite coerceVec_vacuous; auto.
   - rewrite bvMinusOne_S.
     destruct k.
     + rewrite take_0_l.
       rewrite coerceVec_vacuous. simpl; auto.
     + simpl. rewrite bvMinusOne_S. rewrite IHw. auto.
Qed.

(*
 * taking from the end of zero gives zero
 *)
Lemma takeEnd_bvZero: forall w k, takeEnd k (bvZero w) = bvZero (min w k).
Proof.
Admitted.

(*
 * taking from the end of one gives zero (assuming you don't take
 * the whole thing)
 *
 * (remember, the lowest-order bit is on the left when the vector's
 * viewed as a list, and thus the lowest order bit is last out)
 *)
Lemma takeEnd_bvOne: forall w k,
   k < w -> takeEnd k (bvOne w) = bvZero (min w k).
Proof.
Admitted.

(*
 * taking from the end of minusone gives minusone
 *)
Lemma takeEnd_bvMinusOne: forall w k,
   takeEnd k (bvMinusOne w) = bvMinusOne (min w k).
Proof.
Admitted.

(*
 * dropping from zero gives zero
 *)
Lemma drop_bvZero: forall w k, drop k (bvZero w) = bvZero (w - k).
Proof.
Admitted.

(*
 * dropping from one gives zero (assuming you drop at least one bit)
 * (remember, the lowest-order bit is on the left and thus the lowest
 * order bit is first to be dropped)
 *)
Lemma drop_bvOne: forall w k, 0 < k -> drop k (bvOne w) = bvZero (w - k).
Proof.
Admitted.

(*
 * dropping from minusone gives minusone
 *)
Lemma drop_bvMinusOne: forall w k, drop k (bvMinusOne w) = bvMinusOne (w - k).
Proof.
Admitted.

(*
 * dropping from the end of zero gives zero
 *)
Lemma dropEnd_bvZero: forall w k, dropEnd k (bvZero w) = bvZero (w - k).
Proof.
Admitted.

(*
 * dropping from the end of one gives one (assuming you don't drop
 * the whole thing)
 *
 * (remember, the lowest-order bit is on the left when the vector's
 * viewed as a list, and thus the lowest order bit is last to go)
 *)
Lemma dropEnd_bvOne: forall w k, k < w -> dropEnd k (bvOne w) = bvOne (w - k).
Proof.
Admitted.

(*
 * dropping from the end of minusone gives minusone
 *)
Lemma dropEnd_bvMinusOne: forall w k,
   dropEnd k (bvMinusOne w) = bvMinusOne (w - k).
Proof.
Admitted.


(*************************************************************)
(* decidable equality *)

Lemma bv_eq_dec: forall {w} (x y: bitvector w), { x = y } + { x <> y }.
Proof.
   intros.
   destruct (Vec_eq_dec x y); try (left; auto; fail); try (right; auto; fail).
   intros x0 y0.
   destruct x0; destruct y0; try (left; auto; fail); right; discriminate.
Qed.


(*************************************************************)
(* sign *)

(*
 * Extract the sign bit (the w - 1'th bit)
 *)
Definition bvSign {w: nat} (x: bitvector w) :=
   match w with
   | 0 => false
   | S w' =>
        match atOption x w' with
        | None => (* not actually possible *) false
        | Some result => result
        end
   end.

(*
 * bvSign of NilVec is false
 *)
Lemma bvSign_NilVec: bvSign (NilVec bool) = false.
Proof.
   simpl; auto.
Qed.

(*
 * bvSign of ConsVec x0 NilVec is x0
 *)
Lemma bvSign_ConsVecNilVec: forall x0, bvSign (ConsVec x0 (NilVec bool)) = x0.
Proof.
   intros; simpl; auto.
Qed.

(*
 * bvSign of ConsVec ConsVec is bvSign of ConsVec
 *)
Lemma bvSign_ConsVecConsVec: forall w x0 x1 (x: bitvector w),
   bvSign (ConsVec x0 (ConsVec x1 x)) = bvSign (ConsVec x1 x).
Proof.
   intros; simpl; auto.
Qed.

(*
 * general case for bvSign of ConsVec x0 xs
 *)
Lemma bvSign_ConsVec: forall w x0 (x: bitvector w),
   bvSign (ConsVec x0 x) =
      match w with
      | 0 => x0
      | S _ => bvSign x
      end.
Proof.
   intros.
   destruct x.
   - apply bvSign_ConsVecNilVec.
   - apply bvSign_ConsVecConsVec.
Qed.

(*
 * coercions inside bvSign are irrelevant
 *)
Lemma bvSign_coerceVec: forall w w' pf (x: bitvector w),
   bvSign (coerceVec w' pf x) = bvSign x.
Proof.
   intros.
   subst.
   simpl; auto.
Qed.

(*
 * bvSign of a gen is calling the gen function at the last bit
 *)
Lemma bvSign_gen: forall w f, bvSign (gen (S w) f) = f w.
Proof.
   intros.
   unfold bvSign.
   destruct (atOption (gen (S w) f) w) eqn:H.
   - rewrite atOption_gen in H; try lia.
     injection H; intros; auto.
   - rewrite <- atOption_None in H.
     lia.
Qed.

(*
 * bvSign of (nondegenerate) append is bvSign of the RHS
 * (recall the RHS is most significant)
 *)
Lemma bvSign_append: forall w1 w2 (x: bitvector w1) (y: bitvector w2),
   0 < w2 -> bvSign (append x y) = bvSign y.
Proof.
   intros.
   unfold bvSign.
   destruct w2; try lia.
   destruct w1.
   - simpl.
     destruct x using caseVec_0.
     rewrite append_NilVec_l; auto.
   - (* uuugh another case where it munges the implicit arguments *)
     admit.
Admitted.

(*
 * zero is positive
 *)
Lemma bvSign_bvZero: forall w, bvSign (bvZero w) = false.
Proof.
   intros.
   unfold bvSign.
   destruct w; auto.
   rewrite atOption_bvZero; auto.
Qed.

(*
 * one is positive
 *)
Lemma bvSign_bvOne: forall w, 1 < w -> bvSign (bvOne w) = false.
Proof.
   intros.
   unfold bvSign.
   destruct w; auto.
   rewrite atOption_bvOne; auto; lia.
Qed.

(*
 * minusone is negative
 *)
Lemma bvSign_bvMinusOne: forall w, 0 < w -> bvSign (bvMinusOne w) = true.
Proof.
   intros.
   unfold bvSign.
   destruct w; try lia.
   rewrite atOption_bvMinusOne; auto; lia.
Qed.


(*************************************************************)
(* inc/dec *)

(*
 * Increment
 *)
Fixpoint bvInc {w: nat} (x: bitvector w) :=
   match x with
   | NilVec _ => NilVec bool
   | ConsVec b x' =>
        match b with
        | false => ConsVec true x'
        | true => ConsVec false (bvInc x')
        end
   end.

(*
 * increment with carry, which we need to be able to increment over append.
 *)
Fixpoint bvInc_carry {w: nat} (x: bitvector w) : bool * bitvector w :=
   match x with
   | NilVec _ => (true, NilVec bool)
   | ConsVec x0 x' =>
        match x0 with
        | false => (false, ConsVec true x')
        | true =>
             let (carry, x'') := bvInc_carry x' in
             (carry, ConsVec false x'')
        end
   end.

(*
 * Equivalence
 *)
Lemma bvInc_carry_bvInc: forall w (x x': bitvector w) c,
   (c, x') = bvInc_carry x -> x' = bvInc x.
Proof.
   intros * Heq.
   revert Heq.
   revert c x'.
   induction x; intros.
   - destruct x' using caseVec_0.
     simpl; auto.
   - destruct x' using caseVec_S.
     simpl.
     simpl in Heq.
     destruct (bvInc_carry x0) eqn:Hcarry.
     specialize (IHx b v eq_refl).
     subst v.
     destruct x; congruence.
Qed.

(*
 * Unfold lemma for incrementing nil
 *)
Lemma bvInc_NilVec: bvInc (NilVec bool) = NilVec bool.
Proof.
   simpl; auto.
Qed.

(*
 * Unfold lemma for incrementing cons
 *)
Lemma bvInc_ConsVec: forall w x0 (x: bitvector w),
   bvInc (ConsVec x0 x) =
      match x0 with
      | false => ConsVec true x
      | true => ConsVec false (bvInc x)
      end.
Proof.
   intros; simpl; auto.
Qed.

(*
 * Pull a coercion out of bvInc.
 *)
Lemma bvInc_coerceVec: forall w w' (x: bitvector w) pf,
   bvInc (coerceVec w' pf x) = coerceVec w' pf (bvInc x).
Proof.
   intros.
   destruct pf.
   simpl; auto.
Qed.

(*
 * Incrementing zero gives one.
 *)
Lemma bvInc_bvZero: forall w, bvInc (bvZero w) = bvOne w.
Proof.
   intros.
   unfold bvZero.
   unfold bvOne.
   unfold gen.
   induction w; simpl; auto.
   assert (w - w = 0) as -> by lia.
   f_equal.
   do 2 (rewrite gen_visit_S_l; try lia).
   auto.
Qed.

(*
 * Incrementing minusone gives zero.
 *)
Lemma bvInc_bvMinusOne: forall w, bvInc (bvMinusOne w) = bvZero w.
Proof.
   intros.
   unfold bvZero.
   unfold bvMinusOne.
   unfold gen.
   induction w; simpl; auto.
   f_equal.
   do 2 (rewrite gen_visit_S_l; try lia).
   apply IHw.
Qed.

(*
 * Incrementing minusone carries out
 *)
Lemma bvInc_carry_bvMinusOne: forall w,
   bvInc_carry (bvMinusOne w) = (true, bvZero w).
Proof.
   induction w.
   - rewrite bvZero_0. rewrite bvMinusOne_0.
     simpl; auto.
   - rewrite bvZero_S. rewrite bvMinusOne_S.
     (*
      * XXX: we really want a bvInc_carry_ConsVec lemma here; simpl
      * unfolds too far
      *)
     assert (bvInc_carry (ConsVec true (bvMinusOne w)) =
             (let (c, x) := bvInc_carry (bvMinusOne w) in (c, ConsVec false x)))
          as -> by (simpl; auto).
     rewrite IHw. auto.
Qed.

(*
 * incrementing anything else does not carry
 *)
Lemma bvInc_carry_other: forall w (x: bitvector w),
   x <> bvMinusOne w -> bvInc_carry x = (false, bvInc x).
Proof.
   intros * Hneq.
   induction w.
   - destruct x using caseVec_0. contradiction.
   - destruct x using caseVec_S.
     rewrite bvMinusOne_S in Hneq.
     simpl.
     destruct x; auto.
     rewrite IHw; auto.
     congruence.
Qed.

(*
 * increment on append
 *)
Lemma bvInc_append: forall w1 w2 (x: bitvector w1) (y: bitvector w2),
   bvInc (append x y) =
        match bvInc_carry x with
        | (false, x') => append x' y
        | (true, x') => append x' (bvInc y)
        end.
Proof.
   intros.
   revert y.
   revert w2.
   induction x; intros.
   - simpl; auto.
   - simpl.
     rewrite IHx.
     destruct x; simpl; auto.
     destruct (bvInc_carry x0) eqn:Hcarry.
     simpl.
     destruct b; auto.
Qed.

(*
 * increment on take is take on increment
 *)
Lemma bvInc_take: forall w k (x: bitvector w),
   bvInc (take k x) = take k (bvInc x).
Proof.
   intros.
Admitted.

(*
 * increment on dropEnd is dropEnd on increment
 *)
Lemma bvInc_dropEnd: forall w k (x: bitvector w),
   bvInc (dropEnd k x) = dropEnd k (bvInc x).
Proof.
   intros.
Admitted.

(*
 * Increment is injective.
 *)
Lemma bvInc_inj: forall w (x y: bitvector w), bvInc x = bvInc y <-> x = y.
Proof.
   split; intros * H.
   - revert H. revert y.
     induction x; intros.
     + destruct y using caseVec_0; auto.
     + destruct y using caseVec_S.
       simpl in H.
       destruct x; destruct x1; try congruence.
       rewrite IHx with (y := y); auto.
       congruence.
   - subst; auto.
Qed.

(*
 * Decrement
 *)
Fixpoint bvDec {w: nat} (x: bitvector w) :=
   match x with
   | NilVec _ => NilVec bool
   | ConsVec b x' =>
        match b with
        | false => ConsVec true (bvDec x')
        | true => ConsVec false x'
        end
   end.

(*
 * decrement with borrow, which we need to be able to decrement over append.
 *)
Fixpoint bvDec_borrow {w: nat} (x: bitvector w) : bool * bitvector w :=
   match x with
   | NilVec _ => (true, NilVec bool)
   | ConsVec x0 x' =>
        match x0 with
        | false =>
             let (borrow, x'') := bvDec_borrow x' in
             (borrow, ConsVec true x'')
        | true =>
             (false, ConsVec false x')
        end
   end.

(*
 * Equivalence
 *)
Lemma bvDec_borrow_bvDec: forall w (x x': bitvector w) b,
   (b, x') = bvDec_borrow x -> x' = bvDec x.
Proof.
   intros * Heq.
   revert Heq.
   revert b x'.
   induction x; intros.
   - destruct x' using caseVec_0.
     simpl; auto.
   - destruct x' using caseVec_S.
     simpl.
     simpl in Heq.
     destruct (bvDec_borrow x0) eqn:Hborrow.
     specialize (IHx b0 v eq_refl).
     subst v.
     destruct x; congruence.
Qed.

(*
 * Unfold lemma for decrementing nil
 *)
Lemma bvDec_NilVec: bvDec (NilVec bool) = NilVec bool.
Proof.
   simpl; auto.
Qed.

(*
 * Unfold lemma for decrementing cons
 *)
Lemma bvDec_ConsVec: forall w x0 (x: bitvector w),
   bvDec (ConsVec x0 x) =
      match x0 with
      | false => ConsVec true (bvDec x)
      | true => ConsVec false x
      end.
Proof.
   intros; simpl; auto.
Qed.

(*
 * Pull a coercion out of bvDec.
 *)
Lemma bvDec_coerceVec: forall w w' (x: bitvector w) pf,
   bvDec (coerceVec w' pf x) = coerceVec w' pf (bvDec x).
Proof.
   intros.
   destruct pf.
   simpl; auto.
Qed.

(*
 * Decrementing zero gives minusone.
 *)
Lemma bvDec_bvZero: forall w, bvDec (bvZero w) = bvMinusOne w.
Proof.
   intros.
   unfold bvZero.
   unfold bvMinusOne.
   unfold gen.
   induction w; simpl; auto.
   do 2 (rewrite gen_visit_S_l; try lia).
   rewrite IHw.
   auto.
Qed.

(*
 * Decrementing one gives zero.
 *)
Lemma bvDec_bvOne: forall w, bvDec (bvOne w) = bvZero w.
Proof.
   intros.
   unfold bvOne.
   unfold bvZero.
   unfold gen.
   induction w; simpl; auto.
   assert (w - w = 0) as -> by lia.
   do 2 (rewrite gen_visit_S_l; try lia).
   auto.
Qed.

(*
 * Decrementing zero borrows
 *)
Lemma bvDec_borrow_bvZero: forall w,
   bvDec_borrow (bvZero w) = (true, bvMinusOne w).
Proof.
   induction w.
   - rewrite bvZero_0. rewrite bvMinusOne_0.
     simpl; auto.
   - rewrite bvZero_S. rewrite bvMinusOne_S.
     simpl.
     rewrite IHw; auto.
Qed.

(*
 * decrementing anything else does not borrow
 *)
Lemma bvDec_borrow_other: forall w (x: bitvector w),
   x <> bvZero w -> bvDec_borrow x = (false, bvDec x).
Proof.
   intros * Hneq.
   induction w.
   - destruct x using caseVec_0. contradiction.
   - destruct x using caseVec_S.
     rewrite bvZero_S in Hneq.
     simpl.
     destruct x; auto.
     rewrite IHw; auto.
     congruence.
Qed.

(*
 * bvInc applied to bvDec cancels out.
 *)
Lemma bvInc_bvDec: forall w (x: bitvector w), bvInc (bvDec x) = x.
Proof.
   intros.
   induction x; simpl; auto.
   destruct x; simpl; auto.
   rewrite IHx. auto.
Qed.

(*
 * bvDec applied to bvInc also cancels out.
 *)
Lemma bvDec_bvInc: forall w (x: bitvector w), bvDec (bvInc x) = x.
Proof.
   intros.
   induction x; simpl; auto.
   destruct x; simpl; auto.
   rewrite IHx. auto.
Qed.

(*
 * decrement on append
 *)
Lemma bvDec_append: forall w1 w2 (x: bitvector w1) (y: bitvector w2),
   bvDec (append x y) =
        match bvDec_borrow x with
        | (false, x') => append x' y
        | (true, x') => append x' (bvDec y)
        end.
Proof.
   intros.
   revert y.
   revert w2.
   induction x; intros.
   - simpl; auto.
   - simpl.
     rewrite IHx.
     destruct x; simpl; auto.
     destruct (bvDec_borrow x0) eqn:Hborrow.
     simpl.
     destruct b; auto.
Qed.

(*
 * decrement on take is take on decrement
 *)
Lemma bvDec_take: forall w k (x: bitvector w),
   bvDec (take k x) = take k (bvDec x).
Proof.
   intros.
Admitted.

(*
 * decrement on dropEnd is dropEnd on decrement
 *)
Lemma bvDec_dropEnd: forall w k (x: bitvector w),
   bvDec (dropEnd k x) = dropEnd k (bvDec x).
Proof.
   intros.
Admitted.

(*
 * Decrement is injective.
 *)
Lemma bvDec_inj: forall w (x y: bitvector w), bvDec x = bvDec y <-> x = y.
Proof.
   split; intros * H.
   - revert H. revert y.
     induction x; intros.
     + destruct y using caseVec_0; simpl; auto.
     + destruct y using caseVec_S.
       simpl in H.
       destruct x; destruct x1; try congruence.
       rewrite IHx with (y := y); auto.
       congruence.
   - subst; auto.
Qed.

(*
 * flip bvInc across an equality (to make a bvDec)
 *)
Lemma bvInc_antisym: forall w (x y: bitvector w),
   bvInc x = y -> x = bvDec y.
Proof.
   intros.
   subst.
   rewrite bvDec_bvInc; auto.
Qed.

(*
 * flip bvDec across an equality (to make a bvInc)
 *)
Lemma bvDec_antisumm: forall w (x y: bitvector w),
   bvDec x = y -> x = bvInc y.
Proof.
   intros.
   subst.
   rewrite bvInc_bvDec; auto.
Qed.


(*************************************************************)
(* bitwise ops *)

Fixpoint bvNot {w : nat} (x: bitvector w) : bitvector w :=
   match x with
   | NilVec _ => NilVec bool
   | ConsVec b x' => ConsVec (negb b) (bvNot x')
   end.

(*
 * bvNot is its own inverse.
 *)
Lemma bvNot_bvNot: forall w (x: bitvector w), bvNot (bvNot x) = x.
Proof.
   intros.
   induction x; simpl; auto.
   rewrite negb_involutive.
   rewrite IHx.
   auto.
Qed.

(*
 * bvNot on NilVec is still NilVec
 *)
Lemma bvNot_NilVec: bvNot (NilVec bool) = NilVec bool.
Proof.
   simpl; auto.
Qed.

(*
 * bvNot on ConsVec is another ConsVec.
 *)
Lemma bvNot_ConsVec: forall w x0 (x: bitvector w),
   bvNot (ConsVec x0 x) = ConsVec (negb x0) (bvNot x).
Proof.
   intros; simpl; auto.
Qed.

(*
 * Pull a coercion out of a bvNot.
 *)
Lemma bvNot_coerceVec: forall w w' (x: bitvector w) pf,
   bvNot (coerceVec w' pf x) = coerceVec w' pf (bvNot x).
Proof.
   intros.
   destruct pf.
   simpl; auto.
Qed.

(*
 * bvNot applied to a gen makes a different gen.
 *)
Lemma bvNot_gen: forall w f, bvNot (gen w f) = gen w (fun i => negb (f i)).
Proof.
   intros.
   unfold gen.
   revert f.
   induction w; intros; simpl; auto.
   assert (w - w = 0) as -> by lia.
   do 2 (rewrite gen_visit_S_l; try lia).
   rewrite IHw; auto.
Qed.

(*
 * head applied to bvNot
 *)
Lemma bvHead_bvNot: forall w (x: bitvector (S w)),
   head (bvNot x) = negb (head x).
Proof.
Admitted.

(*
 * bvNot commutes with tail
 *)
Lemma bvNot_tail: forall w (x: bitvector (S w)),
   bvNot (tail x) = tail (bvNot x).
Proof.
Admitted.

(*
 * tail commutes with bvNot (other direction)
 *)
Lemma tail_bvNot: forall w (x: bitvector (S w)),
   tail (bvNot x) = bvNot (tail x).
Proof.
   intros.
   rewrite bvNot_tail; auto.
Qed.

(*
 * bvNot distributes over append.
 *)
Lemma bvNot_append: forall w1 w2 (x: bitvector w1) (y: bitvector w2),
   bvNot (append x y) = append (bvNot x) (bvNot y).
Proof.
   intros.
   revert y.
   revert w2.
   induction x; intros; simpl; auto.
   rewrite IHx; auto.
Qed.

(*
 * bvNot commutes with reverse
 *)
Lemma bvNot_reverse: forall w (x: bitvector w),
   bvNot (reverse x) = reverse (bvNot x).
Proof.
Admitted.

(*
 * reverse commutes with bvNot (other direction)
 *)
Lemma reverse_bvNot: forall w (x: bitvector w),
   reverse (bvNot x) = bvNot (reverse x).
Proof.
   intros.
   rewrite bvNot_reverse; auto.
Qed.

(*
 * at on bvNot
 *)
Lemma atOption_bvNot: forall w (x: bitvector w) k,
   atOption (bvNot x) k =
      match atOption x k with
      | None => None
      | Some x0 => Some (negb x0)
      end.
Proof.
   intros.
   revert k.
   induction x; intros; simpl; auto.
   destruct k; auto.
Qed.

(*
 * bvNot commutes with take
 *)
Lemma bvNot_take: forall w k (x: bitvector w),
   bvNot (take k x) = take k (bvNot x).
Proof.
Admitted.

(*
 * take commutes with bvNot (other direction)
 *)
Lemma take_bvNot: forall w k (x: bitvector w),
   take k (bvNot x) = bvNot (take k x).
Proof.
   intros.
   rewrite bvNot_take; auto.
Qed.

(*
 * bvNot commutes with takeEnd
 *)
Lemma bvNot_takeEnd: forall w k (x: bitvector w),
   bvNot (takeEnd k x) = takeEnd k (bvNot x).
Proof.
Admitted.

(*
 * takeEnd commutes with bvNot (other direction)
 *)
Lemma takeEnd_bvNot: forall w k (x: bitvector w),
   takeEnd k (bvNot x) = bvNot (takeEnd k x).
Proof.
   intros.
   rewrite bvNot_takeEnd; auto.
Qed.

(*
 * bvNot commutes with drop
 *)
Lemma bvNot_drop: forall w k (x: bitvector w),
   bvNot (drop k x) = drop k (bvNot x).
Proof.
Admitted.

(*
 * drop commutes with bvNot (other direction)
 *)
Lemma drop_bvNot: forall w k (x: bitvector w),
   drop k (bvNot x) = bvNot (drop k x).
Proof.
   intros.
   rewrite bvNot_drop; auto.
Qed.

(*
 * bvNot commutes with dropEnd
 *)
Lemma bvNot_dropEnd: forall w k (x: bitvector w),
   bvNot (dropEnd k x) = dropEnd k (bvNot x).
Proof.
Admitted.

(*
 * dropEnd commutes with bvNot (other direction)
 *)
Lemma dropEnd_bvNot: forall w k (x: bitvector w),
   dropEnd k (bvNot x) = bvNot (dropEnd k x).
Proof.
   intros.
   rewrite bvNot_dropEnd; auto.
Qed.

(*
 * loop fusion for map/bvNot
 *)
Lemma map_bvNot: forall a w (f: bool -> a) (x: bitvector w),
   map f (bvNot x) = map (fun x0 => f (negb x0)) x.
Proof.
Admitted.

(*
 * loop fusion for bvNot/map
 *)
Lemma bvNot_map: forall a n (f: a -> bool) (xs: Vec a n),
   bvNot (map f xs) = map (fun x => negb (f x)) xs.
Proof.
   intros.
   induction xs; simpl; auto.
   rewrite IHxs. auto.
Qed.

(*
 * bvNot _is_ map negb
 *)
Lemma bvNot_as_map: forall w (x: bitvector w), bvNot x = map negb x.
Proof.
   intros.
   induction x; simpl; auto.
Qed.

(*
 * not 0 = -1
 *)
Lemma bvNot_bvZero: forall w, bvNot (bvZero w) = bvMinusOne w.
Proof.
   intros.
   induction w.
   - unfold bvZero. unfold bvMinusOne. simpl; auto.
   - rewrite bvZero_S. rewrite bvMinusOne_S. simpl. rewrite IHw; auto.
Qed.

(*
 * not -1 = 0
 *)
Lemma bvNot_bvMinusOne: forall w, bvNot (bvMinusOne w) = bvZero w.
Proof.
   intros.
   rewrite <- bvNot_bvZero.
   rewrite bvNot_bvNot; auto.
Qed.

(*
 * not flips the sign
 *)
Lemma bvSign_bvNot: forall w (x: bitvector w),
   0 < w -> bvSign (bvNot x) = negb (bvSign x).
Proof.
   intros.
   unfold bvSign.
   destruct w; try lia.
   rewrite atOption_bvNot.
   destruct (atOption x w) eqn:Heq; auto.
   apply atOption_notNone in Heq; lia.
Qed.

(*
 * It appears that matching on two bitvectors in a binary operator
 * loses track of the fact that the match results are the same size,
 * unless you do a dependent match. FUTURE: it would be better to
 * figure out how to do this with an explicit convoy pattern rather
 * than using proof mode; writing code in proof mode is not wrong,
 * but it's delicate and it's easy to accidentally write the wrong
 * code. Also, what comes out of proof mode is usually verbose and
 * ugly and we'd rather not see it downstream.
 *
 * Note that it's tempting to write a function to do the matching
 * once and then use it in all the operators. Trouble with that is,
 * in addition to making a mess of the index types, it also blows up
 * the termination checker.
 *)

(* nat proof used by essentially all the binary operators *)
Lemma binop_size_proof: forall n n0, S n0 = S n -> n = n0.
Proof. lia. Qed.

(*
 * bitwise and
 *)
Fixpoint bvAnd {w: nat} (x: bitvector w) (y: bitvector w) : bitvector w.
(*
   match x with
   | NilVec _ => NilVec bool
   | ConsVec x0 x' =>
        match y with
        | NilVec _ => NilVec bool (* impossible *)
        | ConsVec y0 y' => ConsVec (x0 && y0) (bvAnd x' y')
        end
   end.
*)
Proof.
   destruct x.
   - exact (NilVec bool).
   - (* call the result x0 :: x' *)
     rename x0 into x'. rename x into x0.
     (* This allows it to not lose track of the sizes being the same. *)
     remember (S n) as m.
     destruct y.
     + (*
        * This case is impossible, so we can produce whatever; returning
        * nil produces less mess in the output than engaging False_rect.
        *)
       exact (NilVec bool).
     + (* call the result y0 :: y' *)
       rename y into y'. rename x into y0.
       (* now the actual code *)
       exact (coerceVec (S n0) Heqm (ConsVec (x0 && y0)
              (bvAnd n x' (coerceVec n (binop_size_proof n n0 Heqm) y')))).
Defined.

(*
 * pull coercions out of and
 *)

Lemma bvAnd_coerceVec_l: forall w w' (x: bitvector w) (y: bitvector w') pf,
   bvAnd (coerceVec w' pf x) y =
      coerceVec w' pf (bvAnd x (coerceVec w (eq_sym pf) y)).
Proof.
   intros.
   subst. simpl. auto.
Qed.

Lemma bvAnd_coerceVec_r: forall w w' (x: bitvector w') (y: bitvector w) pf,
   bvAnd x (coerceVec w' pf y) =
      coerceVec w' pf (bvAnd (coerceVec w (eq_sym pf) x) y).
Proof.
   intros.
   subst. simpl. auto.
Qed.

Lemma bvAnd_coerceVec: forall w w' (x: bitvector w) (y: bitvector w) pf1 pf2,
   bvAnd (coerceVec w' pf1 x) (coerceVec w' pf2 y) =
      coerceVec w' pf1 (bvAnd x y).
Proof.
  intros.
  subst; simpl.
  rewrite coerceVec_vacuous.
  auto.
Qed.

Lemma bvAnd_coerceVec_heterogeneous:
   forall w w' w'' (x: bitvector w) (y: bitvector w') pf1 pf2 pf3,
   bvAnd (coerceVec w'' pf1 x) (coerceVec w'' pf2 y) =
          coerceVec w'' pf1 (bvAnd x (coerceVec w pf3 y)).
Proof.
  intros.
  subst; simpl.
  rewrite coerceVec_vacuous.
  auto.
Qed.

(*
 * and on two gens
 *)
Lemma bvAnd_gen_gen: forall w (f g: nat -> bool),
   bvAnd (gen w f) (gen w g) = gen w (fun i => andb (f i) (g i)).
Proof.
Admitted.

(*
 * and distributes over append if the sizes on each side match
 *)
Lemma bvAnd_append: forall w1 w2 (x y: bitvector w1) (x' y': bitvector w2),
   bvAnd (append x x') (append y y') = append (bvAnd x y) (bvAnd x' y').
Proof.
Admitted.

(*
 * append can also distribute over and (left side)
 *)
Lemma append_bvAnd_l: forall w1 w2 (x y: bitvector w1) (z: bitvector w2),
   append (bvAnd x y) z = bvAnd (append x (bvMinusOne w2)) (append y z).
Proof.
Admitted.

(*
 * append can also distribute over and (right side)
 *)
Lemma append_bvAnd_r: forall w1 w2 (x: bitvector w1) (y z: bitvector w2),
   append x (bvAnd y z) = bvAnd (append (bvMinusOne w1) y) (append x z).
Proof.
Admitted.

(*
 * reverse distributes over and
 *)
Lemma reverse_bvAnd: forall w (x y: bitvector w),
   reverse (bvAnd x y) = bvAnd (reverse x) (reverse y).
Proof.
Admitted.

(*
 * at distributes over and
 *)
Lemma atOption_bvAnd: forall w (x y: bitvector w) k x0 y0,
   atOption x k = Some x0 -> atOption y k = Some y0 ->
   atOption (bvAnd x y) k = Some (andb x0 y0).
Proof.
Admitted.

(*
 * take distributes over and
 *)
Lemma take_bvAnd: forall w k (x y: bitvector w),
   take k (bvAnd x y) = bvAnd (take k x) (take k y).
Proof.
Admitted.

(*
 * takeEnd distributes over and
 *)
Lemma takeEnd_bvAnd: forall w k (x y: bitvector w),
   takeEnd k (bvAnd x y) = bvAnd (takeEnd k x) (takeEnd k y).
Proof.
Admitted.

(*
 * drop distributes over and
 *)
Lemma drop_bvAnd: forall w k (x y: bitvector w),
   drop k (bvAnd x y) = bvAnd (drop k x) (drop k y).
Proof.
Admitted.

(*
 * dropEnd distributes over and
 *)
Lemma dropEnd_bvAnd: forall w k (x y: bitvector w),
   dropEnd k (bvAnd x y) = bvAnd (dropEnd k x) (dropEnd k y).
Proof.
Admitted.

(*
 * and is zipWith andb
 *)
Lemma bvAnd_as_zipWith: forall w (x y: bitvector w),
   bvAnd x y = coerceVec w (eq_sym (Nat.min_id w)) (zipWith andb x y).
Proof.
   intros.
   revert y.
   induction x; intros; simpl.
   - rewrite NilVec_unique. auto.
   - destruct y using caseVec_S.
     rewrite bvAnd_coerceVec_r.
Admitted.

(*
 * left zero
 *)
Lemma bvAnd_bvZero_l: forall w (x: bitvector w), bvAnd (bvZero w) x = bvZero w.
Proof.
   intros.
   induction x.
   - simpl. rewrite bvZero_0. auto.
   - (*
      * Despite trying to mark bvZero so simpl won't unfold it, and
      * despite simpl ordinarily not unfolding plain Definitions
      * anyway, it does unfold it here and that makes a mess, so use
      * bvZero_S first.
      *)
     rewrite bvZero_S.
     simpl.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * right zero
 *)
Lemma bvAnd_bvZero_r: forall w (x: bitvector w), bvAnd x (bvZero w) = bvZero w.
Proof.
   intros.
   induction x.
   - simpl. rewrite bvZero_0. auto.
   - rewrite bvZero_S.
     simpl.
     rewrite andb_false_r.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * left identity
 *)
Lemma bvAnd_minusone_l: forall w (x: bitvector w), bvAnd (bvMinusOne w) x = x.
Proof.
   intros.
   induction x.
   - simpl. auto.
   - rewrite bvMinusOne_S.
     simpl.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * right identity
 *)
Lemma bvAnd_minusone_r: forall w (x: bitvector w), bvAnd x (bvMinusOne w) = x.
Proof.
   intros.
   induction x.
   - simpl. auto.
   - rewrite bvMinusOne_S.
     simpl.
     rewrite andb_true_r.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * and with self is identity
 *)
Lemma bvAnd_self: forall w (x: bitvector w), bvAnd x x = x.
Proof.
Admitted.

(*
 * sign distributes over and
 *)
Lemma bvSign_bvAnd: forall w (x y: bitvector w),
   bvSign (bvAnd x y) = andb (bvSign x) (bvSign y).
Proof.
Admitted.

(*
 * and is associative (left)
 *)
Lemma bvAnd_bvAnd_l: forall w (x y z: bitvector w),
   bvAnd (bvAnd x y) z = bvAnd x (bvAnd y z).
Proof.
Admitted.

(*
 * and is associative (right)
 *)
Lemma bvAnd_bvAnd_r: forall w (x y z: bitvector w),
   bvAnd x (bvAnd y z) = bvAnd (bvAnd x y) z.
Proof.
   intros.
   rewrite bvAnd_bvAnd_l.
   auto.
Qed.

(*
 * and is commutative
 *)
Lemma bvAnd_comm: forall w (x y: bitvector w), bvAnd x y = bvAnd y x.
Proof.
Admitted.

(*
 * bitwise or
 *)
Fixpoint bvOr {w : nat} (x: bitvector w) (y: bitvector w) : bitvector w.
(*
   match x with
   | NilVec _ => NilVec bool
   | ConsVec x0 x' =>
        match y with
        | NilVec _ => NilVec bool (* impossible *)
        | ConsVec y0 y' => ConsVec (x0 && y0) (bvAnd x' y')
        end
   end.
*)
Proof.
   destruct x.
   - exact (NilVec bool).
   - (* call the result x0 :: x' *)
     rename x0 into x'. rename x into x0.
     (* This allows it to not lose track of the sizes being the same. *)
     remember (S n) as m.
     destruct y.
     + (*
        * This case is impossible, so we can produce whatever; returning
        * nil produces less mess in the output than engaging False_rect.
        *)
       exact (NilVec bool).
     + (* call the result y0 :: y' *)
       rename y into y'. rename x into y0.
       (* now the actual code *)
       exact (coerceVec (S n0) Heqm (ConsVec (x0 || y0)
              (bvOr n x' (coerceVec n (binop_size_proof n n0 Heqm) y')))).
Defined.

(*
 * pull coercions out of or
 *)

Lemma bvOr_coerceVec_l: forall w w' (x: bitvector w) (y: bitvector w') pf,
   bvOr (coerceVec w' pf x) y =
      coerceVec w' pf (bvOr x (coerceVec w (eq_sym pf) y)).
Proof.
   intros.
   subst. simpl. auto.
Qed.

Lemma bvOr_coerceVec_r: forall w w' (x: bitvector w') (y: bitvector w) pf,
   bvOr x (coerceVec w' pf y) =
      coerceVec w' pf (bvOr (coerceVec w (eq_sym pf) x) y).
Proof.
   intros.
   subst. simpl. auto.
Qed.

Lemma bvOr_coerceVec: forall w w' (x: bitvector w) (y: bitvector w) pf1 pf2,
   bvOr (coerceVec w' pf1 x) (coerceVec w' pf2 y) = coerceVec w' pf1 (bvOr x y).
Proof.
  intros.
  subst; simpl.
  rewrite coerceVec_vacuous.
  auto.
Qed.

Lemma bvOr_coerceVec_heterogeneous:
   forall w w' w'' (x: bitvector w) (y: bitvector w') pf1 pf2 pf3,
   bvOr (coerceVec w'' pf1 x) (coerceVec w'' pf2 y) =
         coerceVec w'' pf1 (bvOr x (coerceVec w pf3 y)).
Proof.
  intros.
  subst; simpl.
  rewrite coerceVec_vacuous.
  auto.
Qed.

(*
 * or on two gens
 *)
Lemma bvOr_gen_gen: forall w (f g: nat -> bool),
   bvOr (gen w f) (gen w g) = gen w (fun i => orb (f i) (g i)).
Proof.
Admitted.

(*
 * or distributes over append if the sizes on each side match
 *)
Lemma bvOr_append: forall w1 w2 (x y: bitvector w1) (x' y': bitvector w2),
   bvOr (append x x') (append y y') = append (bvOr x y) (bvOr x' y').
Proof.
Admitted.

(*
 * append can also distribute over or (left side)
 *)
Lemma append_bvOr_l: forall w1 w2 (x y: bitvector w1) (z: bitvector w2),
   append (bvOr x y) z = bvOr (append x (bvMinusOne w2)) (append y z).
Proof.
Admitted.

(*
 * append can also distribute over or (right side)
 *)
Lemma append_bvOr_r: forall w1 w2 (x: bitvector w1) (y z: bitvector w2),
   append x (bvOr y z) = bvOr (append (bvMinusOne w1) y) (append x z).
Proof.
Admitted.

(*
 * reverse distributes over or
 *)
Lemma reverse_bvOr: forall w (x y: bitvector w),
   reverse (bvOr x y) = bvOr (reverse x) (reverse y).
Proof.
Admitted.

(*
 * at distributes over or
 *)
Lemma atOption_bvOr: forall w (x y: bitvector w) k x0 y0,
   atOption x k = Some x0 -> atOption y k = Some y0 ->
   atOption (bvOr x y) k = Some (orb x0 y0).
Proof.
Admitted.

(*
 * take distributes over or
 *)
Lemma take_bvOr: forall w k (x y: bitvector w),
   take k (bvOr x y) = bvOr (take k x) (take k y).
Proof.
Admitted.

(*
 * takeEnd distributes over or
 *)
Lemma takeEnd_bvOr: forall w k (x y: bitvector w),
   takeEnd k (bvOr x y) = bvOr (takeEnd k x) (takeEnd k y).
Proof.
Admitted.

(*
 * drop distributes over or
 *)
Lemma drop_bvOr: forall w k (x y: bitvector w),
   drop k (bvOr x y) = bvOr (drop k x) (drop k y).
Proof.
Admitted.

(*
 * dropEnd distributes over or
 *)
Lemma dropEnd_bvOr: forall w k (x y: bitvector w),
   dropEnd k (bvOr x y) = bvOr (dropEnd k x) (dropEnd k y).
Proof.
Admitted.

(*
 * or is zipWith orb
 *)
Lemma bvOr_as_zipWith: forall w (x y: bitvector w),
   bvOr x y = coerceVec w (eq_sym (Nat.min_id w)) (zipWith orb x y).
Proof.
Admitted.

(*
 * left identity
 *)
Lemma bvOr_bvZero_l: forall w (x: bitvector w), bvOr (bvZero w) x = x.
Proof.
   intros.
   induction x.
   - simpl. auto.
   - rewrite bvZero_S.
     simpl.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * right identity
 *)
Lemma bvOr_bvZero_r: forall w (x: bitvector w), bvOr x (bvZero w) = x.
Proof.
   intros.
   induction x.
   - simpl. auto.
   - rewrite bvZero_S.
     simpl.
     rewrite orb_false_r.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * left annihilator
 *)
Lemma bvOr_minusone_l: forall w (x: bitvector w),
   bvOr (bvMinusOne w) x = bvMinusOne w.
Proof.
   intros.
   induction x.
   - simpl. rewrite bvMinusOne_0. auto.
   - rewrite bvMinusOne_S.
     simpl.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * right annihilator
 *)
Lemma bvOr_minusone_r: forall w (x: bitvector w),
   bvOr x (bvMinusOne w) = bvMinusOne w.
Proof.
   intros.
   induction x.
   - simpl. rewrite bvMinusOne_0. auto.
   - rewrite bvMinusOne_S.
     simpl.
     rewrite orb_true_r.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * or with self is identity
 *)
Lemma bvOr_self: forall w (x: bitvector w), bvOr x x = x.
Proof.
Admitted.

(*
 * sign distributes over or
 *)
Lemma bvSign_bvOr: forall w (x y: bitvector w),
   bvSign (bvOr x y) = orb (bvSign x) (bvSign y).
Proof.
Admitted.

(*
 * or is associative (left)
 *)
Lemma bvOr_bvOr_l: forall w (x y z: bitvector w),
   bvOr (bvOr x y) z = bvOr x (bvOr y z).
Proof.
Admitted.

(*
 * or is associative (right)
 *)
Lemma bvOr_bvOr_r: forall w (x y z: bitvector w),
   bvOr x (bvOr y z) = bvOr (bvOr x y) z.
Proof.
   intros.
   rewrite bvOr_bvOr_l.
   auto.
Qed.

(*
 * or is commutative
 *)
Lemma bvOr_comm: forall w (x y: bitvector w), bvOr x y = bvOr y x.
Proof.
Admitted.

(*
 * bitwise exclusive-or
 *)
Fixpoint bvXor {w : nat} (x: bitvector w) (y: bitvector w) : bitvector w.
(*
   match x with
   | NilVec _ => NilVec bool
   | ConsVec x0 x' =>
        match y with
        | NilVec _ => NilVec bool (* impossible *)
        | ConsVec y0 y' => ConsVec (x0 && y0) (bvXor x' y')
        end
   end.
*)
Proof.
   destruct x.
   - exact (NilVec bool).
   - (* call the result x0 :: x' *)
     rename x0 into x'. rename x into x0.
     (* This allows it to not lose track of the sizes being the same. *)
     remember (S n) as m.
     destruct y.
     + (*
        * This case is impossible, so we can produce whatever; returning
        * nil produces less mess in the output than engaging False_rect.
        *)
       exact (NilVec bool).
     + (* call the result y0 :: y' *)
       rename y into y'. rename x into y0.
       (* now the actual code *)
       exact (coerceVec (S n0) Heqm (ConsVec (xorb x0 y0)
              (bvXor n x' (coerceVec n (binop_size_proof n n0 Heqm) y')))).
Defined.

(*
 * pull coercions out of xor
 *)

Lemma bvXor_coerceVec_l: forall w w' (x: bitvector w) (y: bitvector w') pf,
   bvXor (coerceVec w' pf x) y =
      coerceVec w' pf (bvXor x (coerceVec w (eq_sym pf) y)).
Proof.
   intros.
   subst. simpl. auto.
Qed.

Lemma bvXor_coerceVec_r: forall w w' (x: bitvector w') (y: bitvector w) pf,
   bvXor x (coerceVec w' pf y) =
      coerceVec w' pf (bvXor (coerceVec w (eq_sym pf) x) y).
Proof.
   intros.
   subst. simpl. auto.
Qed.

Lemma bvXor_coerceVec: forall w w' (x: bitvector w) (y: bitvector w) pf1 pf2,
   bvXor (coerceVec w' pf1 x) (coerceVec w' pf2 y) =
      coerceVec w' pf1 (bvXor x y).
Proof.
  intros.
  subst; simpl.
  rewrite coerceVec_vacuous.
  auto.
Qed.

Lemma bvXor_coerceVec_heterogeneous:
   forall w w' w'' (x: bitvector w) (y: bitvector w') pf1 pf2 pf3,
   bvXor (coerceVec w'' pf1 x) (coerceVec w'' pf2 y) =
          coerceVec w'' pf1 (bvXor x (coerceVec w pf3 y)).
Proof.
  intros.
  subst; simpl.
  rewrite coerceVec_vacuous.
  auto.
Qed.

(*
 * xor on two gens
 *)
Lemma bvXor_gen_gen: forall w (f g: nat -> bool),
   bvXor (gen w f) (gen w g) = gen w (fun i => xorb (f i) (g i)).
Proof.
Admitted.

(*
 * xor distributes over append if the sizes on each side match
 *)
Lemma bvXor_append: forall w1 w2 (x y: bitvector w1) (x' y': bitvector w2),
   bvXor (append x x') (append y y') = append (bvXor x y) (bvXor x' y').
Proof.
Admitted.

(*
 * append can also distribute over xor (left side)
 *)
Lemma append_bvXor_l: forall w1 w2 (x y: bitvector w1) (z: bitvector w2),
   append (bvXor x y) z = bvXor (append x (bvMinusOne w2)) (append y z).
Proof.
Admitted.

(*
 * append can also distribute over xor (right side)
 *)
Lemma append_bvXor_r: forall w1 w2 (x: bitvector w1) (y z: bitvector w2),
   append x (bvXor y z) = bvXor (append (bvMinusOne w1) y) (append x z).
Proof.
Admitted.

(*
 * reverse distributes over xor
 *)
Lemma reverse_bvXor: forall w (x y: bitvector w),
   reverse (bvXor x y) = bvXor (reverse x) (reverse y).
Proof.
Admitted.

(*
 * at distributes over xor
 *)
Lemma atOption_bvXor: forall w (x y: bitvector w) k x0 y0,
   atOption x k = Some x0 -> atOption y k = Some y0 ->
   atOption (bvXor x y) k = Some (xorb x0 y0).
Proof.
Admitted.

(*
 * take distributes over xor
 *)
Lemma take_bvXor: forall w k (x y: bitvector w),
   take k (bvXor x y) = bvXor (take k x) (take k y).
Proof.
Admitted.

(*
 * takeEnd distributes over xor
 *)
Lemma takeEnd_bvXor: forall w k (x y: bitvector w),
   takeEnd k (bvXor x y) = bvXor (takeEnd k x) (takeEnd k y).
Proof.
Admitted.

(*
 * drop distributes over xor
 *)
Lemma drop_bvXor: forall w k (x y: bitvector w),
   drop k (bvXor x y) = bvXor (drop k x) (drop k y).
Proof.
Admitted.

(*
 * dropEnd distributes over xor
 *)
Lemma dropEnd_bvXor: forall w k (x y: bitvector w),
   dropEnd k (bvXor x y) = bvXor (dropEnd k x) (dropEnd k y).
Proof.
Admitted.

(*
 * xor is zipWith xorb
 *)
Lemma bvXor_as_zipWith: forall w (x y: bitvector w),
   bvXor x y = coerceVec w (eq_sym (Nat.min_id w)) (zipWith xorb x y).
Proof.
Admitted.

(*
 * left identity
 *)
Lemma bvXor_bvZero_l: forall w (x: bitvector w), bvXor (bvZero w) x = x.
Proof.
   intros.
   induction x.
   - simpl. auto.
   - rewrite bvZero_S.
     simpl.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * right identity
 *)
Lemma bvXor_bvZero_r: forall w (x: bitvector w), bvXor x (bvZero w) = x.
Proof.
   intros.
   induction x.
   - simpl. auto.
   - rewrite bvZero_S.
     simpl.
     rewrite xorb_false_r.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * left flip
 *)
Lemma bvXor_minusone_l: forall w (x: bitvector w),
   bvXor (bvMinusOne w) x = bvNot x.
Proof.
   intros.
   induction x.
   - simpl. auto.
   - rewrite bvMinusOne_S.
     simpl.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * right flip
 *)
Lemma bvXor_minusone_r: forall w (x: bitvector w),
   bvXor x (bvMinusOne w) = bvNot x.
Proof.
   intros.
   induction x.
   - simpl. auto.
   - rewrite bvMinusOne_S.
     simpl.
     rewrite xorb_true_r.
     rewrite coerceVec_vacuous.
     rewrite IHx.
     auto.
Qed.

(*
 * annihilator
 *)
Lemma bvXor_self: forall w (x: bitvector w), bvXor x x = bvZero w.
Proof.
Admitted.

(*
 * sign distributes over xor
 *)
Lemma bvSign_bvXor: forall w (x y: bitvector w),
   bvSign (bvXor x y) = xorb (bvSign x) (bvSign y).
Proof.
Admitted.

(*
 * xor is associative (left)
 *)
Lemma bvXor_bvXor_l: forall w (x y z: bitvector w),
   bvXor (bvXor x y) z = bvXor x (bvXor y z).
Proof.
Admitted.

(*
 * xor is associative (right)
 *)
Lemma bvXor_bvXor_r: forall w (x y z: bitvector w),
   bvXor x (bvXor y z) = bvXor (bvXor x y) z.
Proof.
   intros.
   rewrite bvXor_bvXor_l.
   auto.
Qed.

(*
 * xor is commutative
 *)
Lemma bvXor_comm: forall w (x y: bitvector w), bvXor x y = bvXor y x.
Proof.
Admitted.


(*************************************************************)
(* truncate/extend *)

(*
 * Because truncate is only valid for smaller sizes, and extend for larger,
 * and that's a headache, we'll have one bvResize that is both truncate and
 * zero-extend.
 *)

Lemma bvResize_shrink_proof: forall w w',
   Nat.ltb w' w = true -> w' = min w w'.
Proof. intros * H. rewrite Nat.ltb_lt in H. lia. Qed.

Lemma bvResize_extend_proof: forall w w',
   Nat.ltb w' w = false -> w' = w + (w' - w).
Proof. intros * H. rewrite Nat.ltb_ge in H. lia. Qed.

Definition bvResize {w: nat} (w': nat) (x: bitvector w) : bitvector w'.
(*
   match Nat.ltb w' w with
   | true =>
        coerceVec w' (bvTrunc_shrink_proof w w' _) (dropEnd (w - w') x)
   | false =>
        coerceVec w' (bvTrunc_extend_proof w w' _) (append x (bvZero (w' - w))
   end.
*)
Proof.
   destruct (Nat.ltb w' w) eqn:Hcmp.
   - exact (
        coerceVec w' (bvResize_shrink_proof w w' Hcmp)
           (take w' x)
     ).
   - exact (
        coerceVec w' (bvResize_extend_proof w w' Hcmp)
           (append x (bvZero (w' - w)))
     ).
Defined.

Definition bvTrunc {w: nat} (w': nat) (x: bitvector w) := bvResize w' x.
Definition bvZExt {w: nat} (w': nat) (x: bitvector w) := bvResize w' x.

Definition bvSExt {w: nat} (w': nat) (x: bitvector w) : bitvector w'.
(*
   match bvSign x with
   | false => bvZExt w' x
   | true =>
        match Nat.ltb w' w with
        | true =>
             coerceVec w' (bvTrunc_shrink_proof w w' _)
                       (dropEnd (w - w') x)
        | false =>
             coerceVec w' (bvTrunc_extend_proof w w' _)
                       (append x (bvMinusOne (w' - w))
        end
   end.
*)
Proof.
   refine (
      match bvSign x with
      | false => bvZExt w' x
      | true => _
      end).
   destruct (Nat.ltb w' w) eqn:Hcmp.
   - exact (
        coerceVec w' (bvResize_shrink_proof w w' Hcmp)
           (take w' x)
     ).
   - exact (
        coerceVec w' (bvResize_extend_proof w w' Hcmp)
           (append x (bvMinusOne (w' - w)))
     ).
Defined.

(*
 * Resizing to the same size is an identity operation.
 *)
Lemma bvResize_same: forall w (x: bitvector w), bvResize w x = x.
Proof.
   intros.
   unfold bvResize.
Admitted.

(*
 * Truncating to the same size is an identity operation.
 *)
Lemma bvTrunc_same: forall w (x: bitvector w), bvTrunc w x = x.
Proof.
   intros.
   unfold bvTrunc.
   apply bvResize_same.
Qed.

(*
 * Zero-extending to the same size is an identity operation.
 *)
Lemma bvZExt_same: forall w (x: bitvector w), bvZExt w x = x.
Proof.
   intros.
   unfold bvTrunc.
   apply bvResize_same.
Qed.

(*
 * Sign-extending to the same size is an identity operation.
 *)
Lemma bvSExt_same: forall w (x: bitvector w), bvSExt w x = x.
Proof.
   intros.
   unfold bvSExt.
   destruct (bvSign x); try apply bvZExt_same.
   admit.
Admitted.

(*
 * Truncating a gen gives a smaller gen.
 *)
Lemma bvTrunc_gen: forall w w' (f: nat -> bool),
   w' < w -> bvResize w' (gen w f) = gen w' f.
Proof.
Admitted.

(*
 * Zero-extending a gen gives a gen that uses zero in any new space.
 *)
Lemma bvZExt_gen: forall w w' (f: nat -> bool),
   w < w' ->
   bvZExt w' (gen w f) = gen w' (fun i =>
        if Nat.ltb i w then f i else false
   ).
Proof.
Admitted.

(*
 * Sign-extending a gen gives a gen that uses the sign bit in any new space.
 *)
Lemma bvSExt_gen: forall w w' (f: nat -> bool),
   0 < w < w' ->
   bvSExt w' (gen w f) = gen w' (fun i =>
        if Nat.ltb i w then f i else f (Nat.pred w)
   ).
Proof.
Admitted.

(*
 * at on truncate gives none in the truncated area
 *)
Lemma atOption_bvTrunc: forall w k (x: bitvector w) i,
   k <= w ->
   atOption (bvTrunc k x) i =
      match Nat.ltb i k with
      | false => None
      | true => atOption x i
      end.
Proof.
Admitted.

(*
 * at on zext gives false in the new area
 *)
Lemma atOption_bvZExt: forall w k (x: bitvector w) i,
   w <= k ->
   atOption (bvZExt k x) i =
      match Nat.ltb i w with
      | false => Some false
      | true => atOption x i
      end.
Proof.
Admitted.

(*
 * at on sext gives the sign bit in the new area
 *)
Lemma atOption_bvSExt: forall w k (x: bitvector w) i,
   0 < w ->
   w <= k ->
   atOption (bvZExt k x) i =
      match Nat.ltb i w with
      | false => atOption x (Nat.pred k)
      | true => atOption x i
      end.
Proof.
Admitted.

(*
 * Resizing zero gives another zero.
 *)
Lemma bvResize_bvZero: forall w w', bvResize w' (bvZero w) = bvZero w'.
Proof.
   intros.
   unfold bvResize.
Admitted.

(*
 * Truncating zero gives zero.
 *)
Lemma bvTrunc_bvZero: forall w w', w' <= w -> bvTrunc w' (bvZero w) = bvZero w'.
Proof.
   intros.
   unfold bvTrunc.
   apply bvResize_bvZero.
Qed.

(*
 * Zero-extending zero gives zero.
 *)
Lemma bvZExt_bvZero: forall w w', w <= w' -> bvZExt w' (bvZero w) = bvZero w'.
Proof.
   intros.
   unfold bvZExt.
   apply bvResize_bvZero.
Qed.

(*
 * Sign-extending zero gives zero.
 *)
Lemma bvSExt_bvZero: forall w w', w <= w' -> bvSExt w' (bvZero w) = bvZero w'.
Proof.
   intros.
   unfold bvSExt.
   rewrite bvSign_bvZero.
   apply bvZExt_bvZero; auto.
Qed.

(*
 * Resizing one gives one, provided you have and don't drop the ones bit.
 *)
Lemma bvResize_bvOne: forall w w', 0 < w -> 0 < w' ->
   bvResize w' (bvOne w) = bvOne w'.
Proof.
   intros.
   destruct w; try lia.
   destruct w'; try lia.
   do 2 rewrite bvOne_S.
   unfold bvResize.
Admitted.

(*
 * Truncating one gives one, provided you don't drop the ones bit.
 *)
Lemma bvTrunc_bvOne: forall w w', 0 < w' -> w' < w ->
   bvTrunc w' (bvOne w) = bvOne w'.
Proof.
   intros.
   unfold bvTrunc.
   apply bvResize_bvOne; auto; lia.
Qed.

(*
 * Zero-extending one gives one, provided you start with a ones bit.
 *)
Lemma bvZExt_bvOne: forall w w',
   0 < w -> w < w' -> bvZExt w' (bvOne w) = bvOne w'.
Proof.
   intros.
   unfold bvZExt.
   apply bvResize_bvOne; lia.
Qed.

(*
 * Sign-extending one gives one, provided you start with at least one zero bit.
 *)
Lemma bvSExt_bvOne: forall w w',
   1 < w -> w < w' -> bvSExt w' (bvOne w) = bvOne w'.
Proof.
   intros.
   unfold bvSExt.
   rewrite bvSign_bvOne; auto.
   apply bvZExt_bvOne; auto; lia.
Qed.

(*
 * resizing minusone gives minusone, provided you don't visit NilVec.
 *)
Lemma bvResize_bvMinusOne: forall w w',
   0 < w -> 0 < w' -> bvResize w' (bvMinusOne w) = bvMinusOne w'.
Proof.
   intros.
   unfold bvResize.
Admitted.

(*
 * truncating minusone gives minusone, provided you don't reach NilVec.
 *)
Lemma bvTrunc_bvMinusOne: forall w w',
   0 < w' -> w' < w -> bvTrunc w' (bvMinusOne w) = bvMinusOne w'.
Proof.
   intros.
   unfold bvTrunc.
   apply bvResize_bvMinusOne; lia.
Qed.

(*
 * zero-extending minusone doesn't give anything in particular
 *)

(*
 * sign-extending minusone gives minusone, provided you don't start from NilVec.
 *)
Lemma bvSExt_bvMinusOne: forall w w',
   0 < w -> w < w' -> bvSExt w' (bvMinusOne w) = bvMinusOne w'.
Proof.
   intros.
   unfold bvSExt.
   rewrite bvSign_bvMinusOne; try lia.
Admitted.

(*
 * Truncating an extension by less gives a shorter extension.
 *)

Lemma bvTrunc_bvZExt_less: forall w1 w2 w3 (x: bitvector w1),
   w1 < w3 < w2 -> bvTrunc w3 (bvZExt w2 x) = bvZExt w3 x.
Proof.
Admitted.

Lemma bvTrunc_bvSExt_less: forall w1 w2 w3 (x: bitvector w1),
   w1 < w3 < w2 -> bvTrunc w3 (bvSExt w2 x) = bvSExt w3 x.
Proof.
Admitted.

(*
 * Truncating an extension to the original length is a nop.
 *
 * These are written with an explicit equality (even though it
 * introduces a coercion that needs to be taken out again later)
 * to make it easier to rewrite with them in a dependently typed
 * context.
 *)

Lemma bvTrunc_bvZExt_same: forall w1 w2 w3 (x: bitvector w1),
   w1 < w2 -> forall (pf: w3 = w1),
   bvTrunc w3 (bvZExt w2 x) = coerceVec w3 pf x.
Proof.
Admitted.

Lemma bvTrunc_bvSExt_same: forall w1 w2 w3 (x: bitvector w1),
   w1 < w2 -> forall (pf: w3 = w1),
   bvTrunc w3 (bvSExt w2 x) = coerceVec w3 pf x.
Proof.
Admitted.

(*
 * Truncating an extension by more is just truncate.
 *)

Lemma bvTrunc_bvZExt_more: forall w1 w2 w3 (x: bitvector w1),
   w3 < w1 -> bvTrunc w3 (bvZExt w2 x) = bvTrunc w3 x.
Proof.
Admitted.

Lemma bvTrunc_bvSExt_more: forall w1 w2 w3 (x: bitvector w1),
   w3 < w1 -> bvTrunc w3 (bvSExt w2 x) = bvTrunc w3 x.
Proof.
Admitted.




(*************************************************************)
(* shifts *)

(*
 * unsigned shift right
 *
 * Recall that the cons end ("left") of the vector is the least
 * significant ("right") part of the bitvector value. So we're
 * dropping bits from the cons end of the vector.
 *
 * XXX: this is very confusing. Implementing bitvectors with the
 * most significant bit on the top would be a pain, but maybe we
 * should use snoc-vectors so the ordering is consistent.
 *)
Definition bvUShr {w : nat} (x: bitvector w) (amt: nat) : bitvector w :=
   bvZExt w (drop amt x).

(*
 * signed shift right
 *)
Definition bvSShr {w : nat} (x: bitvector w) (amt: nat) : bitvector w :=
   bvSExt w (drop amt x).

(*
 * shift left
 *)
Definition bvShl {w : nat} (x: bitvector w) (amt: nat) : bitvector w :=
   bvTrunc w (append (bvZero amt) x).

(*
 * shifting by zero is a nop
 *)

Lemma bvUShr_0_r: forall w (x: bitvector w), bvUShr x 0 = x.
Proof.
Admitted.

Lemma bvSShr_0_r: forall w (x: bitvector w), bvSShr x 0 = x.
Proof.
Admitted.

Lemma bvShl_0_r: forall w (x: bitvector w), bvShl x 0 = x.
Proof.
Admitted.

(*
 * shifting by the vector width or more is degenerate
 *)

Lemma bvUShr_degenerate: forall w (x: bitvector w) amt,
   w <= amt -> bvUShr x amt = bvZero w.
Proof.
Admitted.

Lemma bvSShr_degenerate: forall w (x: bitvector w) amt,
   w <= amt -> bvSShr x amt = if bvSign x then bvMinusOne w else bvZero w.
Proof.
Admitted.

Lemma bvShl_degenerate: forall w (x: bitvector w) amt,
   w <= amt -> bvShl x amt = bvZero w.
Proof.
Admitted.

(*
 * pull out a coercion
 *)

Lemma bvUShr_coerceVec: forall w w' (x: bitvector w) amt pf,
   bvUShr (coerceVec w' pf x) amt = coerceVec w' pf (bvUShr x amt).
Proof.
Admitted.

Lemma bvSShr_coerceVec: forall w w' (x: bitvector w) amt pf,
   bvSShr (coerceVec w' pf x) amt = coerceVec w' pf (bvSShr x amt).
Proof.
Admitted.

Lemma bvShl_coerceVec: forall w w' (x: bitvector w) amt pf,
   bvShl (coerceVec w' pf x) amt = coerceVec w' pf (bvShl x amt).
Proof.
Admitted.

(*
 * shift a gen right (unsigned)
 *)
Lemma bvUShr_gen: forall w (f: nat -> bool) amt,
   amt < w ->
   bvUShr (gen w f) amt = gen w (fun i =>
      match Nat.ltb i (w - amt) with
      | false => false
      | true => f (i + amt)
      end
   ).
Proof.
Admitted.

(*
 * shift a gen right (signed)
 *)
Lemma bvSShr_gen: forall w (f: nat -> bool) amt,
   amt < w ->
   bvSShr (gen w f) amt = gen w (fun i =>
      match Nat.ltb i (w - amt) with
      | false => f (Nat.pred w)
      | true => f (i + amt)
      end
   ).
Proof.
Admitted.

(*
 * shift a gen left
 *)
Lemma bvShl_gen: forall w (f: nat -> bool) amt,
   amt < w ->
   bvShl (gen w f) amt = gen w (fun i =>
      match Nat.ltb i amt with
      | false => f (i - amt)
      | true => false
      end
   ).
Proof.
Admitted.

(*
 * Shift an append right.
 *
 * There are three cases:
 *    - the shift amount is more than w1 + w2; use bv[US]Shr_degenerate.
 *    - the shift amount is more than w1; use bv[US]Shr_append_large.
 *    - the shift amount is less than w1; use bv[US]Shr_append_small.
 *
 * Recall that the left side of the vector (and thus the left side
 * of the append) is the less-significant ("right") part of the
 * bitvector value.
 *)

(*
 * unsigned large case
 *)
Lemma bvUShr_append_large: forall w1 w2 (x: bitvector w1) (y: bitvector w2) amt,
   w1 <= amt ->
   bvUShr (append x y) amt = bvZExt (w1 + w2) (bvUShr y (amt - w1)).
Proof.
Admitted.

(*
 * unsigned small case
 *)
Lemma bvUShr_append_small: forall w1 w2 (x: bitvector w1) (y: bitvector w2) amt,
   amt < w1 ->
   bvUShr (append x y) amt = bvZExt (w1 + w2) (append (bvTrunc (w1 - amt) x) y).
Proof.
Admitted.

(*
 * signed large case
 *)
Lemma bvSShr_append_large: forall w1 w2 (x: bitvector w1) (y: bitvector w2) amt,
   w1 <= amt ->
   bvSShr (append x y) amt = bvSExt (w1 + w2) (bvSShr y (amt - w1)).
Proof.
Admitted.

(*
 * signed small case
 *)
Lemma bvSShr_append_small: forall w1 w2 (x: bitvector w1) (y: bitvector w2) amt,
   amt < w1 ->
   bvSShr (append x y) amt = bvSExt (w1 + w2) (append (bvTrunc (w1 - amt) x) y).
Proof.
Admitted.

(*
 * Shift an append left.
 *
 * There are three cases:
 *    - the shift amount is more than w1 + w2; use bvShl_degenerate.
 *    - the shift amount is more than w2; use bvShl_append_large.
 *    - the shift amount is less than w2; use bvShl_append_small.
 *
 * Recall that the left side of the vector (and thus the left side
 * of the append) is the less-significant ("right") part of the
 * bitvector value.
 *)

Lemma bvShl_append_large:
   forall w1 w2 (x: bitvector w1) (y: bitvector w2) amt pf,
   w2 <= amt ->
   bvShl (append x y) amt = coerceVec (w1 + w2) pf (
      append (bvZero amt) (bvShl x (amt - w2))
   ).
Proof.
Admitted.

Lemma bvShl_append_small:
   forall w1 w2 (x: bitvector w1) (y: bitvector w2) amt pf,
   amt < w2 ->
   bvShl (append x y) amt = coerceVec (w1 + w2) pf (
      append (bvZero amt) (append x (bvTrunc (w2 - amt) (bvShl y amt)))
   ).
Proof.
Admitted.

(*
 * reverse on shift
 *)
 
Lemma reverse_bvUShr: forall w (x: bitvector w) amt,
   reverse (bvUShr x amt) = bvShl (reverse x) amt.
Proof.
Admitted.

Lemma reverse_bvShl: forall w (x: bitvector w) amt,
   reverse (bvShl x amt) = bvUShr (reverse x) amt.
Proof.
Admitted.

(*
 * at on shift
 *)

Lemma atOption_bvUShr: forall w (x: bitvector w) amt i,
   amt < w ->
   atOption (bvUShr x amt) i =
      match Nat.ltb i (w - amt) with
      | false => Some false
      | true => atOption x (i + amt)
      end.
Proof.
Admitted.

Lemma atOption_bvSShr: forall w (x: bitvector w) amt i,
   amt < w ->
   atOption (bvSShr x amt) i =
      match Nat.ltb i (w - amt) with
      | false => atOption x (Nat.pred w)
      | true => atOption x (i + amt)
      end.
Proof.
Admitted.

Lemma atOption_bvShl: forall w (x: bitvector w) amt i,
   amt < w ->
   atOption (bvShl x amt) i =
      match Nat.ltb i amt with
      | false => atOption x (i - amt)
      | true => Some false
      end.
Proof.
Admitted.

(*
 * shifting zero is zero
 *)
 
Lemma bvUShr_bvZero: forall w amt, bvUShr (bvZero w) amt = bvZero w.
Proof.
Admitted.

Lemma bvSShr_bvZero: forall w amt, bvSShr (bvZero w) amt = bvZero w.
Proof.
Admitted.

Lemma bvShl_bvZero: forall w amt, bvShl (bvZero w) amt = bvZero w.
Proof.
Admitted.

(*
 * shifting one right by more than one gives zero.
 *)

Lemma bvUShr_bvOne: forall w amt,
   amt < 0 -> bvUShr (bvOne w) amt = bvZero w.
Proof.
Admitted.

Lemma bvSShr_bvOne: forall w amt,
   1 < w -> amt < 0 -> bvSShr (bvOne w) amt = bvZero w.
Proof.
Admitted.

(*
 * signed shift right of minusone is minusone
 *)
Lemma bvSShr_bvMinusOne: forall w amt, bvSShr (bvMinusOne w) amt = bvMinusOne w.
Proof.
Admitted.

(*
 * signed shift right is sign-preserving
 *)
Lemma bvSign_sbvSShr: forall w (x: bitvector w) amt,
   bvSign (bvSShr x amt) = bvSign x.
Proof.
Admitted.

(*
 * shifts distribute over and
 *)

Lemma bvUShr_bvAnd: forall w (x y: bitvector w) amt,
   bvUShr (bvAnd x y) amt = bvAnd (bvUShr x amt) (bvUShr y amt).
Proof.
Admitted.

Lemma bvSShr_bvAnd: forall w (x y: bitvector w) amt,
   bvUShr (bvAnd x y) amt = bvAnd (bvSShr x amt) (bvSShr y amt).
Proof.
Admitted.

Lemma bvShl_bvAnd: forall w (x y: bitvector w) amt,
   bvShl (bvAnd x y) amt = bvAnd (bvShl x amt) (bvShl y amt).
Proof.
Admitted.

(*
 * shifts distribute over or
 *)

Lemma bvUShr_bvOr: forall w (x y: bitvector w) amt,
   bvUShr (bvOr x y) amt = bvOr (bvUShr x amt) (bvUShr y amt).
Proof.
Admitted.

Lemma bvSShr_bvOr: forall w (x y: bitvector w) amt,
   bvUShr (bvOr x y) amt = bvOr (bvSShr x amt) (bvSShr y amt).
Proof.
Admitted.

Lemma bvShl_bvOr: forall w (x y: bitvector w) amt,
   bvShl (bvOr x y) amt = bvOr (bvShl x amt) (bvShl y amt).
Proof.
Admitted.

(*
 * shifts distribute over xor
 *)

Lemma bvUShr_bvXor: forall w (x y: bitvector w) amt,
   bvUShr (bvXor x y) amt = bvXor (bvUShr x amt) (bvUShr y amt).
Proof.
Admitted.

Lemma bvSShr_bvXor: forall w (x y: bitvector w) amt,
   bvUShr (bvXor x y) amt = bvXor (bvSShr x amt) (bvSShr y amt).
Proof.
Admitted.

Lemma bvShl_bvXor: forall w (x y: bitvector w) amt,
   bvShl (bvXor x y) amt = bvXor (bvShl x amt) (bvShl y amt).
Proof.
Admitted.

(*
 * shifts sort of cancel each other
 *)

Lemma bvUShr_bvShl: forall w (x: bitvector w) amt,
   amt < w ->
   bvUShr (bvShl x amt) amt = bvZExt w (bvTrunc (w - amt) x).
Proof.
Admitted.

Lemma bvSShr_bvShl: forall w (x: bitvector w) amt,
   amt < w ->
   bvSShr (bvShl x amt) amt = bvSExt w (bvTrunc (w - amt) x).
Proof.
Admitted.

Lemma bvShl_bvUShr: forall w (x: bitvector w) amt pf,
   amt < w ->
   bvShl (bvUShr x amt) amt =
      coerceVec w pf (append (bvZero amt) (bvTrunc (w - amt) x)).
Proof.
Admitted.

Lemma bvShl_bvSShr: forall w (x: bitvector w) amt pf,
   amt < w ->
   bvShl (bvSShr x amt) amt =
      coerceVec w pf (append (bvZero amt) (bvTrunc (w - amt) x)).
Proof.
Admitted.


(*************************************************************)
(* rotate *)

(*
 * rotate left
 *)
Definition bvRotl {w : nat} (x: bitvector w) (amt: nat) : bitvector w :=
   bvOr (bvUShr x amt) (bvShl x amt).

(*
 * rotate right
 *)
Definition bvRotr {w : nat} (x: bitvector w) (amt: nat) : bitvector w :=
   bvOr (bvShl x amt) (bvUShr x amt).

(*
 * Degenerate rotations of greater than the width produce zero.
 *
 * (This is a consequence of how rotations are defined, not
 * necessarily a reasonable result; if you want to reduce mod w, do
 * that explicitly first. Otherwise everyone who touches rotate has to
 * reason about the modulus and that's a large pain.)
 *)

Lemma bvRotl_degenerate: forall w (x: bitvector w) amt,
   w <= amt -> bvRotl x amt = bvZero w.
Proof.
Admitted.

Lemma bvRotr_degenerate: forall w (x: bitvector w) amt,
   w <= amt -> bvRotr x amt = bvZero w.
Proof.
Admitted.

(*
 * rotate on gen
 *)

Lemma bvRotl_gen: forall w (f: nat -> bool) amt,
   amt < w ->
   bvRotl (gen w f) amt = gen w (fun i =>
      match Nat.ltb i amt with
      | false => f (i - amt)
      | true => f (i + w - amt)
      end
   ).
Proof.
Admitted.

Lemma bvRotr_gen: forall w (f: nat -> bool) amt,
   amt < w ->
   bvRotr (gen w f) amt = gen w (fun i =>
      match Nat.ltb i (w - amt) with
      | false => f (i - (w - amt))
      | true => f (i - amt)
      end
   ).
Proof.
Admitted.

(*
 * Special cases of rotate on append when the lengths match just so.
 *
 * We could write the general case but it'd be extremely tedious.
 * (FUTURE)
 *)

Lemma bvRotl_append_exact: forall w1 w2 (x: bitvector w1) (y: bitvector w2),
   bvRotl (append x y) w1 =
      coerceVec (w1 + w2) (Nat.add_comm w1 w2) (append y x).
Proof.
Admitted.

Lemma bvRotr_append_exact: forall w1 w2 (x: bitvector w1) (y: bitvector w2),
   bvRotr (append x y) w2 =
      coerceVec (w1 + w2) (Nat.add_comm w1 w2) (append y x).
Proof.
Admitted.

(*
 * Rotating zero is zero.
 *)

Lemma bvRotl_bvZero: forall w amt, bvRotl (bvZero w) amt = bvZero w.
Proof.
Admitted.

Lemma bvRotr_bvZero: forall w amt, bvRotr (bvZero w) amt = bvZero w.
Proof.
Admitted.

(*
 * Rotating minusone is minusone.
 *)

Lemma bvRotl_bvMinusOne: forall w amt, bvRotl (bvMinusOne w) amt = bvMinusOne w.
Proof.
Admitted.

Lemma bvRotr_bvMinusOne: forall w amt, bvRotr (bvMinusOne w) amt = bvMinusOne w.
Proof.
Admitted.

(*
 * rotates commute with not
 *)

Lemma bvRotl_bvNot: forall w (x: bitvector w) amt,
   bvRotl (bvNot x) amt = bvNot (bvRotl x amt).
Proof.
Admitted.

Lemma bvRotr_bvNot: forall w (x: bitvector w) amt,
   bvRotr (bvNot x) amt = bvNot (bvRotr x amt).
Proof.
Admitted.

(*
 * rotates distribute over and, or, xor
 *)

Lemma bvRotl_bvAnd: forall w (x y: bitvector w) amt,
   bvRotl (bvAnd x y) amt = bvAnd (bvRotl x amt) (bvRotl y amt).
Proof.
Admitted.

Lemma bvRotr_bvAnd: forall w (x y: bitvector w) amt,
   bvRotr (bvAnd x y) amt = bvAnd (bvRotr x amt) (bvRotr y amt).
Proof.
Admitted.

Lemma bvRotl_bvOr: forall w (x y: bitvector w) amt,
   bvRotl (bvOr x y) amt = bvOr (bvRotl x amt) (bvRotl y amt).
Proof.
Admitted.

Lemma bvRotr_bvOr: forall w (x y: bitvector w) amt,
   bvRotr (bvOr x y) amt = bvOr (bvRotr x amt) (bvRotr y amt).
Proof.
Admitted.

Lemma bvRotl_bvXor: forall w (x y: bitvector w) amt,
   bvRotl (bvXor x y) amt = bvXor (bvRotl x amt) (bvRotl y amt).
Proof.
Admitted.

Lemma bvRotr_bvXor: forall w (x y: bitvector w) amt,
   bvRotr (bvXor x y) amt = bvXor (bvRotr x amt) (bvRotr y amt).
Proof.
Admitted.

(*
 * rotates back and forth cancel
 *)

Lemma bvRotl_bvRotr: forall w (x: bitvector w) amt,
   bvRotl (bvRotr x amt) amt = x.
Proof.
Admitted.

Lemma bvRotr_bvRotl: forall w (x: bitvector w) amt,
   bvRotr (bvRotl x amt) amt = x.
Proof.
Admitted.


(*************************************************************)
(* computational equality *)

Fixpoint bvEqb {w: nat} (x y: bitvector w) : bool.
Proof.
(*
   match x with
   | NilVec _ => true
   | ConsVec x0 x' =>
        match y with
        | NilVec _ => false (* impossible *)
        | ConsVec y0 y' =>
             match bool_eq x0 y0 with
             | false => false
             | true => bvEqb x' y'
        end
   end.
*)
Proof.
   destruct x.
   - exact true.
   - (* call the result x0 :: x' *)
     rename x0 into x'. rename x into x0.
     (* This allows it to not lose track of the sizes being the same. *)
     remember (S n) as m.
     destruct y.
     + (*
        * This case is impossible, so we can produce whatever; returning
        * false produces less mess in the output than engaging False_rect.
        *)
       exact false.
     + (* call the result y0 :: y' *)
       rename y into y'. rename x into y0.
       (* now the actual code *)
       exact (
          bool_eq x0 y0 &&
          bvEqb n x' (coerceVec n (binop_size_proof n n0 Heqm) y')
       ).
Defined.

(*
 * Unfold lemma for bvEqb in case simpl unrolls too far.
 *)
Lemma bvEqb_ConsVec: forall w x0 y0 (x: bitvector w) (y: bitvector w),
   bvEqb (ConsVec x0 x) (ConsVec y0 y) = bool_eq x0 y0 && bvEqb x y.
Proof.
   intros.
   simpl.
   rewrite coerceVec_vacuous.
   auto.
Qed.

Lemma bvEqb_refl: forall w (x: bitvector w), bvEqb x x = true.
Proof.
   intros.
   induction x; simpl; auto.
   rewrite coerceVec_vacuous.
   rewrite andb_true_iff.
   rewrite IHx.
   split; auto.
   (* apparently there's no bool_eq_refl... *)
   destruct x; simpl; auto.
Qed.

Lemma bvEqb_eq: forall w (x y: bitvector w), bvEqb x y = true <-> x = y.
Proof.
   split; intros; try (subst; apply bvEqb_refl).
   revert H.
   revert y.
   induction x; intros; simpl in H.
   - destruct y using caseVec_0; auto.
   - destruct y using caseVec_S.
     rewrite andb_true_iff in H.
     destruct H as [H H0].
     apply bool_eq_ok in H.
     rewrite coerceVec_vacuous in H0.
     apply IHx in H0.
     subst; auto.
Qed.

Lemma bvEqb_neq: forall w (x y: bitvector w), bvEqb x y = false <-> x <> y.
Proof.
   split; intros * H.
   - intro Hf. subst. rewrite bvEqb_refl in H. discriminate.
   - destruct (bvEqb x y) eqn:H0; auto. rewrite bvEqb_eq in H0. contradiction.
Qed.


(*************************************************************)
(* minval/maxval *)

(*
 * Unsigned minimum is 0.
 *
 * I'm not going to provide lemmas about this; just unfold it
 * if it appears.
 *)
Definition bvUMinVal (w: nat) := bvZero w.

(*
 * Unsigned maximum is -1
 *
 * I'm not going to provide lemmas about this; just unfold it
 * if it appears.
 *)
Definition bvUMaxVal (w: nat) := bvMinusOne w.

(*
 * Signed minimum is 2^w-1, zero with a 1 at the top
 *)
Definition bvSMinVal (w: nat) :=
   gen w (fun i => Nat.eqb (S i) w).

(*
 * Signed maximum is 2^(w-1) - 1, minusone with a 0 at the top.
 *)
Definition bvSMaxVal (w: nat) := bvNot (bvSMinVal w).

(*
 * width zero of these is zero
 *)

Lemma bvSMinVal_0: bvSMinVal 0 = NilVec bool.
Proof.
   unfold bvSMinVal.
   apply gen_0_l.
Qed.

Lemma bvSMaxVal_0: bvSMaxVal 0 = NilVec bool.
Proof.
   unfold bvSMaxVal.
   unfold bvSMinVal.
   simpl; auto.
Qed.

(*
 * width 1 of these is a special case.
 *
 * (Signed bitvectors of length 1 have two values, 0 and -1.)
 *)

Lemma bvSMinVal_1: bvSMinVal 1 = bvOne 1.
Proof.
   unfold bvSMinVal.
   simpl; auto.
Qed.

Lemma bvSMaxVal_1: bvSMaxVal 1 = bvZero 1.
Proof.
   unfold bvSMaxVal.
   rewrite bvSMinVal_1.
   simpl; auto.
Qed.

(*
 * unfold lemmas for other S w
 *)

Lemma bvSMinVal_S: forall w, 0 < w ->
   bvSMinVal (S w) = ConsVec false (bvSMinVal w).
Proof.
   intros * H.
   unfold bvSMinVal.
   rewrite gen_S_l.
   destruct (Nat.eqb 1 (S w)) eqn:Heq.
   - rewrite Nat.eqb_eq in Heq. lia.
   - f_equal.
Qed.

Lemma bvSMaxVal_S: forall w, 0 < w ->
   bvSMaxVal (S w) = ConsVec true (bvSMaxVal w).
Proof.
   intros * H.
   unfold bvSMaxVal.
   rewrite bvSMinVal_S; auto.
Qed.

(*
 * Signed minimum is negative
 *)
Lemma bvSign_bvSMinVal: forall w, 0 < w -> bvSign (bvSMinVal w) = true.
Proof.
   intros.
   unfold bvSMinVal.
   destruct w; try lia.
   rewrite bvSign_gen.
   rewrite Nat.eqb_eq; auto.
Qed.

(*
 * Signed maximum is positive
 *)
Lemma bvSign_bvSMaxVal: forall w, bvSign (bvSMaxVal w) = false.
Proof.
   intros.
   unfold bvSMaxVal.
   destruct w; [ | induction w ].
   - rewrite bvSMinVal_0.
     rewrite bvNot_NilVec.
     apply bvSign_NilVec.
   - rewrite bvSMinVal_1.
     simpl; auto.
   - rewrite bvSMinVal_S; try lia.
     rewrite bvNot_ConsVec.
     rewrite bvSign_ConsVec; auto.
Qed.

(*
 * Incrementing signed maxval gives signed minval.
 *)
Lemma bvInc_bvSMaxVal: forall w, bvInc (bvSMaxVal w) = bvSMinVal w.
Proof.
   intros.
   unfold bvSMaxVal.
   induction w.
   - simpl. apply bvSMinVal_0.
   - destruct w.
     + compute. auto.
     + rewrite bvSMinVal_S; try lia.
       rewrite bvNot_ConsVec.
       rewrite bvInc_ConsVec.
       rewrite IHw.
       simpl; auto.
Qed.

(*
 * Decrementing signed minval gives signed maxval.
 *)
Lemma bvDec_bvSMinVal: forall w, bvDec (bvSMinVal w) = bvSMaxVal w.
Proof.
   intros.
   rewrite <- bvInc_bvSMaxVal.
   rewrite bvDec_bvInc.
   auto.
Qed.


(*************************************************************)
(* add *)

(*
 * Add one bit.
 *)
Definition adder (x y carry: bool) : bool * bool :=
   match carry with
   | false =>
        match (x, y) with
        | (false, false) => (false, false)
        | (false, true) => (false, true)
        | (true, false) => (false, true)
        | (true, true) => (true, false)
        end
   | true =>
        match (x, y) with
        | (false, false) => (false, true)
        | (false, true) => (true, false)
        | (true, false) => (true, false)
        | (true, true) => (true, true)
        end
   end.

Lemma adder_comm: forall x y c, adder x y c = adder y x c.
Proof.
   intros.
   unfold adder.
   destruct c; destruct x; destruct y; auto.
Qed.

(*
 * Add bitvectors with an explicit carry.
 *
 * Note: unlike bvInc_carry, this takes a carry input.
 * Also unlike bvInc_carry, it discards the carry output.
 * (In both cases, the shape implemented is what downstream logic needs.)
 *)
Fixpoint bvAdd_carry {w : nat}
     (x: bitvector w) (y: bitvector w) (carry: bool) : bitvector w.
(*
   match x with
   | NilVec _ => NilVec bool
   | ConsVec x0 x' =>
        match y with
        | NilVec _ => NilVec bool (* not actually possible *)
        | ConsVec y0 y' =>
             let (carry', xy0) := adder x0 y0 carry in
             ConsVec xy0 (bvAdd_carry x' y' carry')
        end
   end.
*)
Proof.
   destruct x.
   - exact (NilVec bool).
   - (* call the result x0 :: x' *)
     rename x0 into x'. rename x into x0.
     (* This allows it to not lose track of the sizes being the same. *)
     remember (S n) as m.
     destruct y.
     + (*
        * This case is impossible, so we can produce whatever; returning
        * nil produces less mess in the output than engaging False_rect.
        *)
       exact (NilVec bool).
     + (* call the result y0 :: y' *)
       rename y into y'. rename x into y0.
       (* now the actual code *)
       exact (let (carry', xy0) := adder x0 y0 carry in
              coerceVec (S n0) Heqm (ConsVec xy0
                 (bvAdd_carry n x' (coerceVec n (binop_size_proof n n0 Heqm) y')
                                    carry'))).
Defined.

(*
 * Unfold lemma for bvAdd_carry, in case simpl unfolds too much.
 * Also, this automatically eliminates the vacuous coerceVec that
 * we can't seem to avoid in the definition.
 *)
Lemma bvAdd_carry_ConsVec: forall w x0 y0 (x y: bitvector w) carry,
   bvAdd_carry (ConsVec x0 x) (ConsVec y0 y) carry =
      let (carry', xy0) := adder x0 y0 carry in
      ConsVec xy0 (bvAdd_carry x y carry').
Proof.
   intros.
   simpl.
   destruct (adder x0 y0 carry).
   rewrite coerceVec_vacuous.
   auto.
Qed.

(*
 * Add with carry is commutative.
 *)
Lemma bvAdd_carry_comm: forall w (x y: bitvector w) carry,
   bvAdd_carry x y carry = bvAdd_carry y x carry.
Proof.
   intros.
   revert carry y.
   induction x; intros.
   - destruct y using caseVec_0.
     simpl; auto.
   - destruct y using caseVec_S.
     simpl.
     rewrite adder_comm.
     do 2 rewrite coerceVec_vacuous.
     destruct (adder x1 x carry).
     rewrite IHx; auto.
Qed.

(*
 * Carry is the same as incrementing afterward.
 *)
Lemma bvAdd_carry_true: forall w (x y: bitvector w),
   bvAdd_carry x y true = bvInc (bvAdd_carry x y false).
Proof.
   intros.
   induction x.
   - simpl; auto.
   - destruct y using caseVec_S.
     do 2 rewrite bvAdd_carry_ConsVec.
     destruct x; destruct x1; simpl; auto; rewrite IHx; auto.
Qed.

(*
 * Carry is the same as incrementing the left argment.
 *)
Lemma bvAdd_carry_true_l: forall w (x y: bitvector w),
   bvAdd_carry x y true = bvAdd_carry (bvInc x) y false.
Proof.
   intros.
   induction x.
   - simpl; auto.
   - destruct y using caseVec_S.
     rewrite bvAdd_carry_ConsVec.
     destruct (adder x x1 true) eqn:H.
     rewrite bvInc_ConsVec.
     destruct x; simpl in H.
     + assert (b = true) as -> by
            (destruct x1; injection H; intros; subst; auto).
       rewrite IHx.
       rewrite bvAdd_carry_ConsVec.
       destruct (adder false x1 false) eqn:H0.
       simpl in H0.
       assert (b = false) as -> by
            (destruct x1; injection H0; intros; subst; auto).
       assert (b0 = b1) as -> by
            (destruct x1; injection H; injection H0; intros; subst; auto).
       auto.
     + rewrite bvAdd_carry_ConsVec.
       destruct (adder true x1 false) eqn:H0.
       simpl in H0.
       destruct x1; injection H; injection H0; intros; subst; auto.
Qed.

(*
 * Carry is the same as incrementing the right argment.
 *)
Lemma bvAdd_carry_true_r: forall w (x y: bitvector w),
   bvAdd_carry x y true = bvAdd_carry x (bvInc y) false.
Proof.
   intros.
   rewrite bvAdd_carry_comm.
   rewrite bvAdd_carry_comm with (y := bvInc y).
   apply bvAdd_carry_true_l.
Qed.

(*
 * add with carry is associative (left argument)
 *)
Lemma bvAdd_carry_bvAdd_carry_l: forall w c1 c2 (x y z: bitvector w),
   bvAdd_carry (bvAdd_carry x y c2) z c1 =
      bvAdd_carry x (bvAdd_carry y z c2) c1.
Proof.
   intros.
   revert z y c2 c1.
   induction x as [ | w x0 x]; intros.
   - destruct y using caseVec_0.
     destruct z using caseVec_0.
     simpl; auto.
   - destruct y as [y0 y] using caseVec_S.
     destruct z as [z0 z] using caseVec_S.
     rewrite bvAdd_carry_ConsVec.
     destruct (adder x0 y0 c2) as [cxyL xy0L] eqn:HL1.
     rewrite bvAdd_carry_ConsVec.
     destruct (adder xy0L z0 c1) as [cxyzL xyzL] eqn:HL2.
     rewrite bvAdd_carry_ConsVec.
     destruct (adder y0 z0 c2) as [cyzR yz0R] eqn:HR1.
     rewrite bvAdd_carry_ConsVec.
     destruct (adder x0 yz0R c1) as [cxyzR xyzR] eqn:HR2.
     rewrite IHx.
     destruct x0; destruct y0; destruct z0; destruct c1; destruct c2.
     all: simpl in *.
     all: injection HL1; injection HR1; intros; subst.
     all: injection HL2; injection HR2; intros; subst.
     all: auto.
     all: rewrite bvAdd_carry_true with (x := y).
     all: rewrite bvAdd_carry_true_r.
     all: auto.
Qed.

(*
 * add with carry is associative (right argument)
 *)
Lemma bvAdd_carry_bvAdd_carry_r: forall w c1 c2 (x y z: bitvector w),
   bvAdd_carry x (bvAdd_carry y z c2) c1 =
      bvAdd_carry (bvAdd_carry x y c2) z c1.
Proof.
   intros.
   rewrite bvAdd_carry_bvAdd_carry_l; auto.
Qed.

(*
 * Addition without an explicit carry input.
 *)
Definition bvAdd {w : nat} (x y: bitvector w) : bitvector w :=
   bvAdd_carry x y false.

(*
 * Unfold lemma for bvAdd that will (often) avoid having to
 * think about bvAdd_carry at all.
 *)
Lemma bvAdd_ConsVec: forall w x0 y0 (x y: bitvector w),
   bvAdd (ConsVec x0 x) (ConsVec y0 y) =
      match adder x0 y0 false with
      | (false, xy0) => ConsVec xy0 (bvAdd x y)
      | (true, xy0) => ConsVec xy0 (bvInc (bvAdd x y))
      end.
Proof.
   intros.
   unfold bvAdd.
   rewrite <- bvAdd_carry_true.
   rewrite bvAdd_carry_ConsVec.
   destruct (adder x0 y0 false).
   destruct b; auto.
Qed.

(*
 * Addition is commutative.
 *)
Lemma bvAdd_comm: forall w (x y: bitvector w),
   bvAdd x y = bvAdd y x.
Proof.
   intros.
   unfold bvAdd.
   apply bvAdd_carry_comm.
Qed.

(*
 * Adding zero on the left has no effect.
 *)
Lemma bvAdd_bvZero_l: forall w (x: bitvector w), bvAdd (bvZero w) x = x.
Proof.
   intros.
   induction x; auto.
   - rewrite bvZero_S.
     rewrite bvAdd_ConsVec.
     rewrite IHx.
     destruct x; simpl; auto.
Qed.

(*
 * Adding zero on the right has no effect.
 *)
Lemma bvAdd_bvZero_r: forall w (x: bitvector w), bvAdd x (bvZero w) = x.
Proof.
   intros.
   induction x; auto.
   - rewrite bvZero_S.
     rewrite bvAdd_ConsVec.
     rewrite IHx.
     destruct x; simpl; auto.
Qed.

(*
 * Adding one on the left is the same as increment.
 *)
Lemma bvAdd_one_l: forall w (x: bitvector w), bvAdd (bvOne w) x = bvInc x.
Proof.
   intros.
   destruct x; auto.
   rewrite bvOne_S.
   rewrite bvAdd_ConsVec.
   rewrite bvAdd_bvZero_l.
   unfold adder.
   destruct x; simpl; auto.
Qed.

(*
 * Adding one on the right is also the same as increment.
 *)
Lemma bvAdd_one_r: forall w (x: bitvector w), bvAdd x (bvOne w) = bvInc x.
Proof.
   intros.
   rewrite bvAdd_comm.
   apply bvAdd_one_l.
Qed.

(*
 * Adding minusone on the left is decrement.
 *)
Lemma bvAdd_minusone_l: forall w (x: bitvector w),
   bvAdd (bvMinusOne w) x = bvDec x.
Proof.
   intros.
   induction x; auto.
   - rewrite bvMinusOne_S.
     rewrite bvAdd_ConsVec.
     rewrite IHx.
     destruct x; simpl; auto.
     rewrite bvInc_bvDec; auto.
Qed.

(*
 * Adding minusone on the right is also decrement.
 *)
Lemma bvAdd_minusone_r: forall w (x: bitvector w),
   bvAdd x (bvMinusOne w) = bvDec x.
Proof.
   intros.
   rewrite bvAdd_comm.
   apply bvAdd_minusone_l.
Qed.

(*
 * An increment on the left side of add can be moved out.
 *) 
Lemma bvAdd_bvInc_l: forall w (x y: bitvector w),
   bvAdd (bvInc x) y = bvInc (bvAdd x y).
Proof.
   intros.
   revert y.
   induction x; intros.
   - destruct y using caseVec_0; simpl; auto.
   - destruct y using caseVec_S; simpl.
     destruct x; destruct x1; do 2 rewrite bvAdd_ConsVec; unfold adder;
          simpl; auto; rewrite IHx; auto.
Qed.

(*
 * An increment on the right side of add can be moved out.
 *)
Lemma bvAdd_bvInc_r: forall w (x y: bitvector w),
   bvAdd x (bvInc y) = bvInc (bvAdd x y).
Proof.
   intros.
   rewrite bvAdd_comm.
   rewrite bvAdd_bvInc_l.
   f_equal.
   apply bvAdd_comm.
Qed.

(*
 * A decrement on the left side of an add can be moved out.
 *)
Lemma bvAdd_bvDec_l: forall w (x y: bitvector w),
   bvAdd (bvDec x) y = bvDec (bvAdd x y).
Proof.
   intros.
   revert y.
   induction x; intros.
   - destruct y using caseVec_0; simpl; auto.
   - destruct y using caseVec_S; simpl.
     destruct x; destruct x1; do 2 rewrite bvAdd_ConsVec; unfold adder;
          simpl; try rewrite IHx;
          try rewrite bvDec_bvInc; try rewrite bvInc_bvDec; auto.
Qed.

(*
 * A decrement on the right side of an add can be moved out.
 *)
Lemma bvAdd_bvDec_r: forall w (x y: bitvector w),
   bvAdd x (bvDec y) = bvDec (bvAdd x y).
Proof.
   intros.
   rewrite bvAdd_comm.
   rewrite bvAdd_bvDec_l.
   f_equal.
   apply bvAdd_comm.
Qed.

(*
 * add is associative (left argument)
 *)
Lemma bvAdd_bvAdd_l: forall w (x y z: bitvector w),
   bvAdd (bvAdd x y) z = bvAdd x (bvAdd y z).
Proof.
   intros.
   unfold bvAdd.
   rewrite bvAdd_carry_bvAdd_carry_l; auto.
Qed.

(*
 * add is associative (right argument)
 *)
Lemma bvAdd_bvAdd_r: forall w (x y z: bitvector w),
   bvAdd x (bvAdd y z) = bvAdd (bvAdd x y) z.
Proof.
   intros.
   rewrite <- bvAdd_bvAdd_l.
   auto.
Qed.

(*
 * add is injective (left argument)
 *)
Lemma bvAdd_inj_l: forall w (x y z: bitvector w),
   bvAdd x y = bvAdd x z <-> y = z.
Proof.
   split; intros * H.
   - revert H. revert y z.
     induction x; intros.
     + rewrite <- bvZero_0 in H.
       do 2 rewrite bvAdd_bvZero_l in H.
       auto.
     + destruct y using caseVec_S.
       destruct z using caseVec_S.
       do 2 rewrite bvAdd_ConsVec in H.
       do 2 rewrite <- bvAdd_bvInc_r in H.
       enough (x1 = x2 /\ y = z) as H0 by (destruct H0; subst; auto).
       destruct x; destruct x1; destruct x2; simpl in H.
       all: try congruence.
       all: split; auto.
       all: try (apply IHx; congruence).
       assert (bvAdd x0 (bvInc y) = bvAdd x0 (bvInc z)) as H0 by congruence.
       apply IHx in H0.
       rewrite bvInc_inj in H0; auto.
   - subst. auto.
Qed.

(*
 * add is injective (right argument)
 *)
Lemma bvAdd_inj_r: forall w (x y z: bitvector w),
   bvAdd y x = bvAdd z x <-> y = z.
Proof.
   split; intros * H.
   - revert H. revert y z.
     induction x; intros.
     + rewrite <- bvZero_0 in H.
       do 2 rewrite bvAdd_bvZero_r in H.
       auto.
     + destruct y using caseVec_S.
       destruct z using caseVec_S.
       do 2 rewrite bvAdd_ConsVec in H.
       do 2 rewrite <- bvAdd_bvInc_l in H.
       enough (x1 = x2 /\ y = z) as H0 by (destruct H0; subst; auto).
       destruct x; destruct x1; destruct x2; simpl in H.
       all: try congruence.
       all: split; auto.
       all: try (apply IHx; congruence).
       assert (bvAdd (bvInc y) x0 = bvAdd (bvInc z) x0) as H0 by congruence.
       apply IHx in H0.
       rewrite bvInc_inj in H0; auto.
   - subst. auto.
Qed.


(*************************************************************)
(* neg/sub *)

(*
 * We'll define negate as increment of bitwise not.
 *)
Definition bvNeg {w : nat} (x: bitvector w) : bitvector w :=
   bvInc (bvNot x).

(*
 * Negating nil gives nil.
 *)
Lemma bvNeg_NilVec: bvNeg (NilVec bool) = NilVec bool.
Proof.
   unfold bvNeg; simpl; auto.
Qed.

(*
 * Unfold lemma for negating a cons. This is set up so it
 * moves the ConsVec all the way to the outside, because that's
 * what we want for most downstream uses.
 *)
Lemma bvNeg_ConsVec: forall w x0 (x: bitvector w),
   bvNeg (ConsVec x0 x) = 
         (match x0 with
          | false => ConsVec x0 (bvNeg x)
          | true => ConsVec x0 (bvDec (bvNeg x))
          end).
Proof.
   intros.
   unfold bvNeg.
   destruct x0; simpl; auto.
   rewrite bvDec_bvInc; auto.
Qed.

(*
 * Negation is its own inverse.
 *)
Lemma bvNeg_bvNeg: forall w (x: bitvector w), bvNeg (bvNeg x) = x.
Proof.
   intros.
   unfold bvNeg.
   induction x; simpl; auto.
   destruct x; simpl.
   - rewrite bvNot_bvNot; auto.
   - rewrite IHx; auto.
Qed.

(*
 * neg 0 = 0
 *)
Lemma bvNeg_bvZero: forall w, bvNeg (bvZero w) = bvZero w.
Proof.
   intros.
   unfold bvNeg.
   rewrite bvNot_bvZero.
   apply bvInc_bvMinusOne.
Qed.

(*
 * neg 1 = -1
 *)
Lemma bvNeg_bvOne: forall w, bvNeg (bvOne w) = bvMinusOne w.
Proof.
   intros.
   destruct w.
   - rewrite bvOne_0. rewrite bvMinusOne_0.
     apply bvNeg_NilVec.
   - rewrite bvOne_S. rewrite bvMinusOne_S.
     rewrite bvNeg_ConsVec.
     rewrite bvNeg_bvZero.
     rewrite bvDec_bvZero.
     auto.
Qed.

(*
 * neg -1 = 1
 *)
Lemma bvNeg_bvMinusOne: forall w, bvNeg (bvMinusOne w) = bvOne w.
Proof.
   intros.
   rewrite <- bvNeg_bvOne.
   rewrite bvNeg_bvNeg.
   auto.
Qed.

(*
 * negating the signed minimum value is a nop
 *)
Lemma bvNeg_bvSMinVal: forall w, bvNeg (bvSMinVal w) = bvSMinVal w.
Proof.
   intros.
   unfold bvNeg.
   fold bvSMaxVal.
   apply bvInc_bvSMaxVal.
Qed.

(*
 * Incrementing a negation is negating a decrement.
 *)
Lemma bvInc_bvNeg: forall w (x: bitvector w), bvInc (bvNeg x) = bvNeg (bvDec x).
Proof.
   intros.
   induction x; simpl.
   - rewrite bvNeg_NilVec. auto.
   - rewrite bvNeg_ConsVec.
     destruct x; simpl.
     + rewrite bvInc_bvDec.
       rewrite bvNeg_ConsVec; auto.
     + rewrite bvNeg_ConsVec.
       rewrite <- IHx.
       rewrite bvDec_bvInc; auto.
Qed.

(*
 * Decrementing a negation is negating an increment.
 *)
Lemma bvDec_bvNeg: forall w (x: bitvector w), bvDec (bvNeg x) = bvNeg (bvInc x).
Proof.
   intros.
   induction x; simpl.
   - rewrite bvNeg_NilVec. auto.
   - rewrite bvNeg_ConsVec.
     destruct x; simpl.
     + rewrite bvNeg_ConsVec.
       rewrite IHx; auto.
     + rewrite bvNeg_ConsVec; auto.
Qed.

(*
 * Negating an increment is decrementing a negation.
 * (inverse of the above)
 *)
Lemma bvNeg_bvInc: forall w (x: bitvector w), bvNeg (bvInc x) = bvDec (bvNeg x).
Proof.
   intros.
   rewrite <- bvDec_bvNeg; auto.
Qed.

(*
 * Negating a decrement is incrementing a negation.
 * (inverse of the above)
 *)
Lemma bvNeg_bvDec: forall w (x: bitvector w), bvNeg (bvDec x) = bvInc (bvNeg x).
Proof.
   intros.
   rewrite <- bvInc_bvNeg; auto.
Qed.

(*
 * negation distributes over add.
 *)
Lemma bvNeg_bvAdd: forall w (x y: bitvector w),
   bvNeg (bvAdd x y) = bvAdd (bvNeg x) (bvNeg y).
Proof.
   intros.
   revert y.
   induction x; intros.
   - destruct y using caseVec_0.
     rewrite <- bvZero_0.
     do 2 rewrite bvNeg_bvZero.
     rewrite bvAdd_bvZero_l; auto.
   - destruct y using caseVec_S.
     do 2 rewrite bvNeg_ConsVec.
     rewrite bvAdd_ConsVec.
     destruct x; destruct x1; rewrite bvAdd_ConsVec; simpl;
          rewrite bvNeg_ConsVec.
     + rewrite bvNeg_bvInc.
       rewrite IHx.
       rewrite bvAdd_bvDec_l.
       rewrite bvAdd_bvDec_r.
       rewrite bvInc_bvDec; auto.
     + rewrite bvAdd_bvDec_l.
       rewrite IHx; auto.
     + rewrite bvAdd_bvDec_r.
       rewrite IHx; auto.
     + rewrite IHx; auto.
Qed.

(*
 * Inverses of the previous for one side at a time
 *)

Lemma bvAdd_bvNeg_l: forall w (x y: bitvector w),
   bvAdd (bvNeg x) y = bvNeg (bvAdd x (bvNeg y)).
Proof.
   intros.
   rewrite bvNeg_bvAdd.
   rewrite bvNeg_bvNeg; auto.
Qed.

Lemma bvAdd_bvNeg_r: forall w (x y: bitvector w),
   bvAdd x (bvNeg y) = bvNeg (bvAdd (bvNeg x) y).
Proof.
   intros.
   rewrite bvNeg_bvAdd.
   rewrite bvNeg_bvNeg; auto.
Qed.

(*
 * x + (-x) is 0
 *)
Lemma bvAdd_bvNeg_diag_r: forall w (x: bitvector w),
   bvAdd x (bvNeg x) = bvZero w.
Proof.
   induction x; simpl.
   - unfold bvAdd. simpl. rewrite bvZero_0. auto.
   - rewrite bvNeg_ConsVec.
     rewrite bvZero_S.
     destruct x; rewrite bvAdd_ConsVec; unfold adder;
          try rewrite bvAdd_bvDec_r; try rewrite bvInc_bvDec;
          rewrite IHx; auto.
Qed.

(*
 * -x + x is 0
 *)
Lemma bvAdd_bvNeg_diag_l: forall w (x: bitvector w),
   bvAdd (bvNeg x) x = bvZero w.
Proof.
   intros.
   rewrite bvAdd_comm.
   apply bvAdd_bvNeg_diag_r.
Qed.

(*
 * Negation is injective.
 *)
Lemma bvNeg_inj: forall w (x y: bitvector w),
   bvNeg x = bvNeg y <-> x = y.
Proof.
   split; intros * H.
   - revert H.
     revert y.
     induction x; intros.
     + destruct y using caseVec_0. auto.
     + destruct y using caseVec_S.
       do 2 rewrite bvNeg_ConsVec in H.
       assert (x1 = x) as -> by (destruct x; destruct x1; congruence).
       f_equal. apply IHx.
       destruct x; try congruence.
       assert (bvDec (bvNeg x0) = bvDec (bvNeg y)) as H0 by congruence.
       rewrite bvDec_inj in H0; auto.
   - subst; auto.
Qed.

(*
 * flip bvNeg to the other side of an equality
 *)
Lemma bvNeg_antisym: forall w (x y: bitvector w),
   bvNeg x = y <-> x = bvNeg y.
Proof.
   split; intros H.
   - rewrite <- H. rewrite bvNeg_bvNeg. auto.
   - rewrite H. rewrite bvNeg_bvNeg. auto.
Qed.

(*
 * Subtraction. Define it in terms of negation and addition.
 *)
Definition bvSub {w: nat} (x: bitvector w) (y: bitvector w) : bitvector w :=
   bvAdd x (bvNeg y).

(*
 * Subtracting a value from itself gives zero.
 *)
Lemma bvSub_diag: forall w (x: bitvector w), bvSub x x = bvZero w.
Proof.
   intros.
   unfold bvSub.
   apply bvAdd_bvNeg_diag_r.
Qed.

(*
 * a - b = - (b - a).
 *)
Lemma bvSub_anticomm: forall w (x y: bitvector w),
   bvSub x y = bvNeg (bvSub y x).
Proof.
   intros.
   unfold bvSub.
   rewrite bvNeg_bvAdd.
   rewrite bvNeg_bvNeg.
   rewrite bvAdd_comm; auto.
Qed.

(*
 * inverse of previous
 *)
Lemma bvNeg_bvSub: forall w (x y: bitvector w),
   bvNeg (bvSub x y) = bvSub y x.
Proof.
   intros.
   rewrite <- bvSub_anticomm; auto.
Qed.

(*
 * Subtracting from zero is negate
 *)
Lemma bvSub_bvZero_l: forall w (y: bitvector w), bvSub (bvZero w) y = bvNeg y.
Proof.
Admitted.

(*
 * Subtracting zero is a nop
 *)
Lemma bvSub_bvZero_r: forall w (x: bitvector w), bvSub x (bvZero w) = x.
Proof.
Admitted.

(*
 * Subtracting one is decrement
 *)
Lemma bvSub_bvOne_r: forall w (x: bitvector w), bvSub x (bvOne w) = bvDec x.
Proof.
Admitted.

(*
 * An increment on the left can be shifted out
 *)
Lemma bvSub_bvInc_l: forall w (x y: bitvector w),
   bvSub (bvInc x) y = bvInc (bvSub x y).
Proof.
Admitted.

(*
 * An increment on the right can be shifted out
 * (becomes a decrement)
 *)
Lemma bvSub_bvInc_r: forall w (x y: bitvector w),
   bvSub x (bvInc y) = bvDec (bvSub x y).
Proof.
Admitted.

(*
 * A decrement on the left can be shifted out
 *)
Lemma bvSub_bvDec_l: forall w (x y: bitvector w),
   bvSub (bvDec x) y = bvDec (bvSub x y).
Proof.
Admitted.

(*
 * A decrement on the right can be shifted out
 * (becomes an increment)
 *)
Lemma bvSub_bvDec_r: forall w (x y: bitvector w),
   bvSub x (bvDec y) = bvInc (bvSub x y).
Proof.
Admitted.

(*
 * Adding and subtracting is a nop
 *)
Lemma bvAdd_bvSub_l: forall w (x y: bitvector w),
   bvAdd (bvSub x y) y = x.
Proof.
   intros.
   unfold bvSub.
   rewrite bvAdd_bvAdd_l.
   rewrite bvAdd_comm with (y := y).
   fold (bvSub y y).
   rewrite bvSub_diag.
   apply bvAdd_bvZero_r.
Qed.

(*
 * Adding and subtracting is a nop
 *)
Lemma bvAdd_bvSub_r: forall w (x y: bitvector w),
   bvAdd x (bvSub y x) = y.
Proof.
   intros.
   rewrite bvAdd_comm.
   apply bvAdd_bvSub_l.
Qed.


(*************************************************************)
(* comparisons *)

(*
 * Unsigned comparison.
 *
 * Caution: currently SAWCoreScaffolding shadows "Eq" (makes it
 * a synonym of "eq") so we need to refer to it as Datatypes.Eq.
 *)
Fixpoint bvucmp {w: nat} (x y: bitvector w) : comparison.
(*
   match x with
   | NilVec _ => Eq
   | ConsVec x0 x' =>
        match y with
        | NilVec _ => Eq (* impossible *)
        | ConsVec y0 y' =>
             match bvucmp x' y' with
             | Lt => Lt
             | Gt => Gt
             | Eq =>
                  match (x0, y0) with
                  | (false, false) => Eq
                  | (true, false) => Gt
                  | (false, true) => Lt
                  | (true, true) => Eq
                  end
             end
        end
   end.
*)
Proof.
   destruct x.
   - exact Datatypes.Eq.
   - rename x0 into x'. rename x into x0.
     remember (S n) as m.
     destruct y.
     + exact Datatypes.Eq. (* impossible *)
     + rename y into y'. rename x into y0.
       refine (
          match bvucmp n x' (coerceVec n (binop_size_proof n n0 Heqm) y') with
          | Lt => Lt
          | Gt => Gt
          | Datatypes.Eq =>
               match (x0, y0) with
               | (false, false) => Datatypes.Eq
               | (true, false) => Gt
               | (false, true) => Lt
               | (true, true) => Datatypes.Eq
               end
          end
       ).
Defined.

Lemma bvucmp_refl: forall w (x: bitvector w), bvucmp x x = Datatypes.Eq.
Proof.
   intros.
   induction x; simpl; auto.
   rewrite coerceVec_vacuous.
   rewrite IHx.
   destruct x; auto.
Qed.

Lemma bvucmp_antisym: forall w (x y: bitvector w),
   bvucmp x y = CompOpp (bvucmp y x).
Proof.
   intros.
   revert y.
   induction x; intros.
   - destruct y using caseVec_0; simpl; auto.
   - destruct y using caseVec_S; simpl.
     do 2 rewrite coerceVec_vacuous.
     rewrite IHx.
     destruct (bvucmp y x0); simpl; auto.
     destruct x; destruct x1; simpl; auto.
Qed.

Lemma bvucmp_eq_eq: forall w (x y: bitvector w),
   bvucmp x y = Datatypes.Eq <-> x = y.
Proof.
   split; intros * H.
   - revert H. revert y.
     induction x; intros.
     + destruct y using caseVec_0; simpl in *; auto.
     + destruct y using caseVec_S; simpl in *.
       rewrite coerceVec_vacuous in H.
       destruct (bvucmp x0 y) eqn:Hxy; try discriminate.
       rewrite IHx with (y := y) in *; auto.
       destruct x; destruct x1; try discriminate; auto.
   - subst. apply bvucmp_refl.
Qed.

Lemma bvucmp_neq_neq: forall w (x y: bitvector w),
   bvucmp x y <> Datatypes.Eq <-> x <> y.
Proof.
   split; intros * H; contradict H.
   - subst. apply bvucmp_refl.
   - rewrite bvucmp_eq_eq in H; auto.
Qed.

Lemma bvucmp_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w ->
   bvucmp (bvZero w) y = Lt.
Proof.
   intros * Hnz.
   revert Hnz.
   revert y.
   induction w; intros.
   - destruct y using caseVec_0. contradiction.
   - destruct y using caseVec_S.
     rewrite bvZero_S in *.
     destruct (bv_eq_dec y (bvZero w)).
     + subst.
       destruct x; try contradiction.
       simpl.
       rewrite coerceVec_vacuous.
       rewrite bvucmp_refl. auto.
     + simpl.
       rewrite coerceVec_vacuous.
       rewrite IHw; auto.
Qed.

Lemma bvucmp_bvZero_r: forall w (x: bitvector w),
   x <> bvZero w ->
   bvucmp x (bvZero w) = Gt.
Proof.
   intros * Hnz.
   rewrite bvucmp_antisym.
   rewrite bvucmp_bvZero_l; simpl; auto.
Qed.

Lemma bvucmp_trans: forall w (x y z: bitvector w) cmp,
   bvucmp x y = cmp -> bvucmp y z = cmp -> bvucmp x z = cmp.
Proof.
   intros * Hxy Hyz.
   revert Hxy Hyz.
   revert y z.
   induction x; intros; simpl in *; auto.
   destruct y using caseVec_S.
   destruct z using caseVec_S.
   simpl in *.
   rewrite coerceVec_vacuous in *.
   specialize (IHx y z).
   destruct (bvucmp x0 y) eqn:Hxy'.
   - rewrite bvucmp_eq_eq in Hxy'. subst.
     destruct (bvucmp y z); destruct x; destruct x1; destruct x2;
          try discriminate; auto.
   - subst.
     destruct (bvucmp y z) eqn:Hyz'; try discriminate.
     + rewrite bvucmp_eq_eq in Hyz'. subst.
       destruct x1; destruct x2; try discriminate.
       rewrite Hxy'. auto.
     + rewrite IHx; auto.
   - subst.
     destruct (bvucmp y z) eqn:Hyz'; try discriminate.
     + rewrite bvucmp_eq_eq in Hyz'. subst.
       destruct x1; destruct x2; try discriminate.
       rewrite Hxy'. auto.
     + rewrite IHx; auto.
Qed.

Definition bvscmp {w: nat} (x y: bitvector w) : comparison :=
   bvucmp (bvAdd (bvSMinVal w) x) (bvAdd (bvSMinVal w) y).

Lemma bvscmp_refl: forall w (x: bitvector w), bvscmp x x = Datatypes.Eq.
Proof.
   intros.
   unfold bvscmp.
   apply bvucmp_refl.
Qed.

Lemma bvscmp_antisym: forall w (x y: bitvector w),
   bvscmp x y = CompOpp (bvscmp y x).
Proof.
   intros.
   unfold bvscmp.
   apply bvucmp_antisym.
Qed.

Lemma bvscmp_eq_eq: forall w (x y: bitvector w),
   bvscmp x y = Datatypes.Eq <-> x = y.
Proof.
   intros.
   unfold bvscmp.
   rewrite bvucmp_eq_eq.
   split; intro H.
   - rewrite bvAdd_inj_l in H; auto.
   - subst; auto.
Qed.

Lemma bvscmp_neq_neq: forall w (x y: bitvector w),
   bvscmp x y <> Datatypes.Eq <-> x <> y.
Proof.
   split; intros * H; contradict H.
   - subst. apply bvscmp_refl.
   - rewrite bvscmp_eq_eq in H; auto.
Qed.

Lemma bvscmp_trans: forall w (x y z: bitvector w) cmp,
   bvscmp x y = cmp -> bvscmp y z = cmp -> bvscmp x z = cmp.
Proof.
   intros.
   unfold bvscmp in *.
   apply bvucmp_trans with (y := bvAdd (bvSMinVal w) y); auto.
Qed.

Definition bvult {w : nat} (x y: bitvector w) : bool :=
   match bvucmp x y with
   | Lt => true
   | Gt => false
   | Datatypes.Eq => false
   end.

Definition bvugt {w : nat} (x y: bitvector w) : bool :=
   match bvucmp x y with
   | Lt => false
   | Gt => true
   | Datatypes.Eq => false
   end.

Definition bvule {w : nat} (x y: bitvector w) : bool :=
   match bvucmp x y with
   | Lt => true
   | Gt => false
   | Datatypes.Eq => true
   end.

Definition bvuge {w : nat} (x y: bitvector w) : bool :=
   match bvucmp x y with
   | Lt => false
   | Gt => true
   | Datatypes.Eq => true
   end.

Definition bvslt {w : nat} (x y: bitvector w) : bool :=
   match bvscmp x y with
   | Lt => true
   | Gt => false
   | Datatypes.Eq => false
   end.

Definition bvsgt {w : nat} (x y: bitvector w) : bool :=
   match bvscmp x y with
   | Lt => false
   | Gt => true
   | Datatypes.Eq => false
   end.

Definition bvsle {w : nat} (x y: bitvector w) : bool :=
   match bvscmp x y with
   | Lt => true
   | Gt => false
   | Datatypes.Eq => true
   end.

Definition bvsge {w : nat} (x y: bitvector w) : bool :=
   match bvscmp x y with
   | Lt => false
   | Gt => true
   | Datatypes.Eq => true
   end.

Lemma bvugt_bvult: forall w (x y: bitvector w), bvugt x y = bvult y x.
Proof.
   intros.
   unfold bvugt.
   unfold bvult.
   rewrite bvucmp_antisym.
   destruct (bvucmp y x); simpl; auto.
Qed.

Lemma bvuge_bvule: forall w (x y: bitvector w), bvuge x y = bvule y x.
Proof.
   intros.
   unfold bvuge.
   unfold bvule.
   rewrite bvucmp_antisym.
   destruct (bvucmp y x); simpl; auto.
Qed.

Lemma bvuge_bvult: forall w (x y: bitvector w), bvuge x y = negb (bvult x y).
Proof.
   intros.
   unfold bvuge.
   unfold bvult.
   destruct (bvucmp x y); simpl; auto.
Qed.

Lemma bvule_bvugt: forall w (x y: bitvector w), bvule x y = negb (bvugt x y).
Proof.
   intros.
   unfold bvule.
   unfold bvugt.
   destruct (bvucmp x y); simpl; auto.
Qed.

Lemma bvsgt_bvslt: forall w (x y: bitvector w), bvsgt x y = bvslt y x.
Proof.
   intros.
   unfold bvsgt.
   unfold bvslt.
   rewrite bvscmp_antisym.
   destruct (bvscmp y x); simpl; auto.
Qed.

Lemma bvsge_bvsle: forall w (x y: bitvector w), bvsge x y = bvsle y x.
Proof.
   intros.
   unfold bvsge.
   unfold bvsle.
   rewrite bvscmp_antisym.
   destruct (bvscmp y x); simpl; auto.
Qed.

Lemma bvsge_bvslt: forall w (x y: bitvector w), bvsge x y = negb (bvslt x y).
Proof.
   intros.
   unfold bvsge.
   unfold bvslt.
   destruct (bvscmp x y); simpl; auto.
Qed.

Lemma bvsle_bvsgt: forall w (x y: bitvector w), bvsle x y = negb (bvsgt x y).
Proof.
   intros.
   unfold bvsle.
   unfold bvsgt.
   destruct (bvscmp x y); simpl; auto.
Qed.

Lemma bvult_irrefl: forall w (x: bitvector w), bvult x x = false.
Proof.
   intros.
   unfold bvult.
   rewrite bvucmp_refl; auto.
Qed.

Lemma bvule_refl: forall w (x: bitvector w), bvule x x = true.
Proof.
   intros.
   unfold bvule.
   rewrite bvucmp_refl; auto.
Qed.

Lemma bvugt_irrefl: forall w (x: bitvector w), bvugt x x = false.
Proof.
   intros.
   unfold bvugt.
   rewrite bvucmp_refl; auto.
Qed.

Lemma bvuge_refl: forall w (x: bitvector w), bvuge x x = true.
Proof.
   intros.
   unfold bvuge.
   rewrite bvucmp_refl; auto.
Qed.

Lemma bvslt_irrefl: forall w (x: bitvector w), bvslt x x = false.
Proof.
   intros.
   unfold bvslt.
   rewrite bvscmp_refl; auto.
Qed.

Lemma bvsle_refl: forall w (x: bitvector w), bvsle x x = true.
Proof.
   intros.
   unfold bvsle.
   rewrite bvscmp_refl; auto.
Qed.

Lemma bvsgt_irrefl: forall w (x: bitvector w), bvsgt x x = false.
Proof.
   intros.
   unfold bvsgt.
   rewrite bvscmp_refl; auto.
Qed.

Lemma bvsge_refl: forall w (x: bitvector w), bvsge x x = true.
Proof.
   intros.
   unfold bvsge.
   rewrite bvscmp_refl; auto.
Qed.

Lemma bvult_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvult (bvZero w) y = true.
Proof.
   intros * Hneq.
   unfold bvult.
   rewrite bvucmp_bvZero_l; auto.
Qed.

Lemma bvule_bvZero_l: forall w (y: bitvector w),
   bvule (bvZero w) y = true.
Proof.
   intros.
   unfold bvule.
   destruct (bv_eq_dec (bvZero w) y).
   - subst. rewrite bvucmp_refl. auto.
   - rewrite bvucmp_bvZero_l; auto.
Qed.

Lemma bvult_bvZero_r: forall w (x: bitvector w),
   bvult x (bvZero w) = false.
Proof.
   intros.
   unfold bvult.
   destruct (bv_eq_dec x (bvZero w)).
   - subst. rewrite bvucmp_refl. auto.
   - rewrite bvucmp_bvZero_r; auto.
Qed.

Lemma bvule_bvZero_r: forall w (x: bitvector w),
   x <> bvZero w -> bvule x (bvZero w) = false.
Proof.
   intros * Hneq.
   unfold bvule.
   rewrite bvucmp_bvZero_r; auto.
Qed.

Lemma bvugt_bvZero_l: forall w (y: bitvector w),
   bvugt (bvZero w) y = false.
Proof.
   intros.
   unfold bvugt.
   destruct (bv_eq_dec (bvZero w) y).
   - subst. rewrite bvucmp_refl. auto.
   - rewrite bvucmp_bvZero_l; auto.
Qed.

Lemma bvuge_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvuge (bvZero w) y = false.
Proof.
   intros * Hneq.
   unfold bvuge.
   rewrite bvucmp_bvZero_l; auto.
Qed.

Lemma bvugt_bvZero_r: forall w (x: bitvector w),
   x <> bvZero w -> bvugt x (bvZero w) = true.
Proof.
   intros * Hneq.
   unfold bvugt.
   rewrite bvucmp_bvZero_r; auto.
Qed.

Lemma bvuge_bvZero_r: forall w (x: bitvector w),
   bvuge x (bvZero w) = true.
Proof.
   intros *.
   unfold bvuge.
   destruct (bv_eq_dec x (bvZero w)).
   - subst. rewrite bvucmp_refl. auto.
   - rewrite bvucmp_bvZero_r; auto.
Qed.

Lemma bvult_trans: forall w (x y z: bitvector w),
   bvult x y = true -> bvult y z = true -> bvult x z = true.
Proof.
   intros * Hxy Hyz.
   unfold bvult in *.
   destruct (bvucmp x y) eqn:Hxy'; try discriminate.
   destruct (bvucmp y z) eqn:Hyz'; try discriminate.
   rewrite bvucmp_trans with (y := y) (cmp := Lt); auto.
Qed.

Lemma bvule_trans: forall w (x y z: bitvector w),
   bvule x y = true -> bvule y z = true -> bvule x z = true.
Proof.
   intros * Hxy Hyz.
   unfold bvule in *.
   destruct (bvucmp x y) eqn:Hxy'; try discriminate.
   - rewrite bvucmp_eq_eq in Hxy'; subst. auto.
   - destruct (bvucmp y z) eqn:Hyz'; try discriminate.
     + rewrite bvucmp_eq_eq in Hyz'; subst. rewrite Hxy'. auto.
     + rewrite bvucmp_trans with (y := y) (cmp := Lt); auto.
Qed.

Lemma bvugt_trans: forall w (x y z: bitvector w),
   bvugt x y = true -> bvugt y z = true -> bvugt x z = true.
Proof.
   intros * Hxy Hyz.
   unfold bvugt in *.
   destruct (bvucmp x y) eqn:Hxy'; try discriminate.
   destruct (bvucmp y z) eqn:Hyz'; try discriminate.
   rewrite bvucmp_trans with (y := y) (cmp := Gt); auto.
Qed.

Lemma bvuge_trans: forall w (x y z: bitvector w),
   bvuge x y = true -> bvuge y z = true -> bvuge x z = true.
Proof.
   intros * Hxy Hyz.
   unfold bvuge in *.
   destruct (bvucmp x y) eqn:Hxy'; try discriminate.
   - rewrite bvucmp_eq_eq in Hxy'; subst. auto.
   - destruct (bvucmp y z) eqn:Hyz'; try discriminate.
     + rewrite bvucmp_eq_eq in Hyz'; subst. rewrite Hxy'. auto.
     + rewrite bvucmp_trans with (y := y) (cmp := Gt); auto.
Qed.

Lemma bvslt_trans: forall w (x y z: bitvector w),
   bvslt x y = true -> bvslt y z = true -> bvslt x z = true.
Proof.
   intros * Hxy Hyz.
   unfold bvslt in *.
   destruct (bvscmp x y) eqn:Hxy'; try discriminate.
   destruct (bvscmp y z) eqn:Hyz'; try discriminate.
   rewrite bvscmp_trans with (y := y) (cmp := Lt); auto.
Qed.

Lemma bvsle_trans: forall w (x y z: bitvector w),
   bvsle x y = true -> bvsle y z = true -> bvsle x z = true.
Proof.
   intros * Hxy Hyz.
   unfold bvsle in *.
   destruct (bvscmp x y) eqn:Hxy'; try discriminate.
   - rewrite bvscmp_eq_eq in Hxy'; subst. auto.
   - destruct (bvscmp y z) eqn:Hyz'; try discriminate.
     + rewrite bvscmp_eq_eq in Hyz'; subst. rewrite Hxy'. auto.
     + rewrite bvscmp_trans with (y := y) (cmp := Lt); auto.
Qed.

Lemma bvsgt_trans: forall w (x y z: bitvector w),
   bvsgt x y = true -> bvsgt y z = true -> bvsgt x z = true.
Proof.
   intros * Hxy Hyz.
   unfold bvsgt in *.
   destruct (bvscmp x y) eqn:Hxy'; try discriminate.
   destruct (bvscmp y z) eqn:Hyz'; try discriminate.
   rewrite bvscmp_trans with (y := y) (cmp := Gt); auto.
Qed.

Lemma bvsge_trans: forall w (x y z: bitvector w),
   bvsge x y = true -> bvsge y z = true -> bvsge x z = true.
Proof.
   intros * Hxy Hyz.
   unfold bvsge in *.
   destruct (bvscmp x y) eqn:Hxy'; try discriminate.
   - rewrite bvscmp_eq_eq in Hxy'; subst. auto.
   - destruct (bvscmp y z) eqn:Hyz'; try discriminate.
     + rewrite bvscmp_eq_eq in Hyz'; subst. rewrite Hxy'. auto.
     + rewrite bvscmp_trans with (y := y) (cmp := Gt); auto.
Qed.


(*************************************************************)
(* max/min *)

(*
 * unsigned max
 *)
Definition bvUMax {w: nat} (x y: bitvector w) : bitvector w :=
   match bvult x y with
   | false => y
   | true => x
   end.

(*
 * unsigned min
 *)
Definition bvUMin {w: nat} (x y: bitvector w) : bitvector w :=
   match bvult x y with
   | false => x
   | true => y
   end.

(*
 * signed max
 *)
Definition bvSMax {w: nat} (x y: bitvector w) : bitvector w :=
   match bvslt x y with
   | false => y
   | true => x
   end.

(*
 * signed min
 *)
Definition bvSMin {w: nat} (x y: bitvector w) : bitvector w :=
   match bvslt x y with
   | false => x
   | true => y
   end.

(*
 * max and min are symmetric
 *)

Lemma bvUMax_sym: forall w (x y: bitvector w), bvUMax x y = bvUMax y x.
Proof.
Admitted.

Lemma bvUMin_sym: forall w (x y: bitvector w), bvUMin x y = bvUMin y x.
Proof.
Admitted.

Lemma bvSMax_sym: forall w (x y: bitvector w), bvSMax x y = bvSMax y x.
Proof.
Admitted.

Lemma bvSMin_sym: forall w (x y: bitvector w), bvSMin x y = bvSMin y x.
Proof.
Admitted.

(*
 * the unsigned max of minusone and anything is minusone
 *)

Lemma bvUMax_bvMinusOne_l: forall w (y: bitvector w),
   bvUMax (bvMinusOne w) y = bvMinusOne w.
Proof.
Admitted.

Lemma bvUMax_bvMinusOne_r: forall w (x: bitvector w),
   bvUMax x (bvMinusOne w) = bvMinusOne w.
Proof.
   intros.
   rewrite bvUMax_sym.
   apply bvUMax_bvMinusOne_l.
Qed.

(*
 * the unsigned min of zero and anything is zero
 *)

Lemma bvUMin_bvZero_l: forall w (y: bitvector w),
   bvUMin (bvZero w) y = bvZero w.
Proof.
Admitted.

Lemma bvUMin_bvZero_r: forall w (x: bitvector w),
   bvUMin x (bvZero w) = bvZero w.
Proof.
   intros.
   rewrite bvUMin_sym.
   apply bvUMin_bvZero_l.
Qed.

(*
 * the signed max of bvSMaxVal and anything is bvSMaxVal
 *)

Lemma bvSMax_bvSMaxVal_l: forall w (y: bitvector w),
   bvSMax (bvSMaxVal w) y = bvSMaxVal w.
Proof.
Admitted.

Lemma bvSMax_bvSMaxVal_r: forall w (x: bitvector w),
   bvSMax x (bvSMaxVal w) = bvSMaxVal w.
Proof.
   intros.
   rewrite bvSMax_sym.
   apply bvSMax_bvSMaxVal_l.
Qed.

(*
 * the signed min of bvSMinVal and anything is bvSMinVal
 *)

Lemma bvSMin_bvSMinVal_l: forall w (y: bitvector w),
   bvSMin (bvSMinVal w) y = bvSMinVal w.
Proof.
Admitted.

Lemma bvSMin_bvSMinVal_r: forall w (x: bitvector w),
   bvSMin x (bvSMinVal w) = bvSMinVal w.
Proof.
   intros.
   rewrite bvSMin_sym.
   apply bvSMin_bvSMinVal_l.
Qed.


(*************************************************************)
(* abs *)

(*
 * absolute value
 *)
Definition bvAbs {w: nat} (x: bitvector w) : bitvector w :=
   match bvSign x with
   | false => x
   | true => bvNeg x
   end.

(*
 * abs 0 = 0
 *)
Lemma bvAbs_bvZero: forall w, bvAbs (bvZero w) = bvZero w.
Proof.
   intros.
   unfold bvAbs.
   rewrite bvSign_bvZero; auto.
Qed.

(*
 * abs 1 = 1
 *)
Lemma bvAbs_bvOne: forall w, bvAbs (bvOne w) = bvOne w.
Proof.
   intros *.
   unfold bvAbs.
   destruct w.
   - simpl; auto.
   - destruct w.
     + rewrite bvNeg_bvOne.
       rewrite bvOne_S.
       rewrite bvMinusOne_S.
       simpl; auto.
     + rewrite bvSign_bvOne; auto. lia.
Qed.

(*
 * abs -1 = 1
 *)
Lemma bvAbs_bvMinusOne: forall w, bvAbs (bvMinusOne w) = bvOne w.
Proof.
   intros.
   unfold bvAbs.
   destruct w.
   - simpl; auto.
   - rewrite bvSign_bvMinusOne; try lia.
     rewrite bvNeg_bvMinusOne; auto.
Qed.

(*
 * abs bvSMaxVal = bvSMaxVal
 *)
Lemma bvAbs_bvSMaxVal: forall w, bvAbs (bvSMaxVal w) = bvSMaxVal w.
Proof.
   intros.
   unfold bvAbs.
   rewrite bvSign_bvSMaxVal; auto.
Qed.

(*
 * abs bvSMinVal = bvSMinVal
 * note! It is still negative. However, it does have the correct
 * value if treated as unsigned.
 *)
Lemma bvAbs_bvSMinVal: forall w, bvAbs (bvSMinVal w) = bvSMinVal w.
Proof.
   intros.
   unfold bvAbs.
   destruct w.
   - simpl; auto.
   - rewrite bvSign_bvSMinVal; try lia.
     rewrite bvNeg_bvSMinVal; auto.
Qed.

(*
 * abs (neg x) = abs x
 *)
Lemma bvAbs_bvNeg: forall w (x: bitvector w), bvAbs (bvNeg x) = bvAbs x.
Proof.
   (* XXX wants a bvSign_bvNeg lemma *)
Admitted.


(*************************************************************)
(* mul *)

(*
 * Full width unsigned multiply.
 *
 * This accepts mismatched widths so it can recurse effectively; that is,
 * you can multiply two vectors of any width.
 *
 * The signed version would use bvSExt insted of bvZExt and otherwise be
 * identical.
 *
 * I'm not providing the signed version because all we actually need
 * externally (so far anyway) is n * n -> n multiply, which throws away
 * the top half of the result and is the same signed and unsigned.
 *)
Fixpoint bvUFullMul {w1 w2: nat}
     (x: bitvector w1) (y: bitvector w2) : bitvector (w1 + w2).
(*
   match x with
   | NilVec _ => bvZero w2
   | ConsVec x0 x' =>
        match x0 with
        | false => ConsVec false (bvFullMul x' y)
        | true => bvAdd (bvZExt (w1 + w2) y) (ConsVec false (bvFullMul x' y))
        end
   end.
*)
Proof.
   destruct x.
   - exact (bvZero w2).
   - rename x0 into x'. rename x into x0.
     exact (
        match x0 with
        | false => ConsVec false (bvUFullMul n w2 x' y)
        | true => bvAdd (bvZExt (S (n + w2)) y)
                        (ConsVec false (bvUFullMul n w2 x' y))
        end
     ).
Defined.

(*
 * unfold lemma
 *)
Lemma bvUFullMul_ConsVec_l: forall w1 w2 x0 (x: bitvector w1) (y: bitvector w2),
   bvUFullMul (ConsVec x0 x) y =
        match x0 with
        | false =>
             ConsVec false (bvUFullMul x y)
        | true =>
             bvAdd (bvZExt (S (w1 + w2)) y) (ConsVec false (bvUFullMul x y))
        end.
Proof.
   intros.
   simpl.
   destruct x0; auto.
Qed.

(*
 * left zero
 *)
Lemma bvUFullMul_bvZero_l: forall w1 w2 (y: bitvector w2),
   bvUFullMul (bvZero w1) y = bvZero (w1 + w2).
Proof.
   intros.
   revert y.
   revert w2.
   induction w1; intros.
   - simpl; auto.
   - rewrite bvZero_S. simpl.
     rewrite bvZero_S.
     rewrite IHw1; auto.
Qed.

(*
 * right zero
 *)
Lemma bvUFullMul_bvZero_r: forall w1 w2 (x: bitvector w1),
   bvUFullMul x (bvZero w2) = bvZero (w1 + w2).
Proof.
   intros.
   revert w2.
   induction x; intros.
   - simpl; auto.
   - simpl.
     rewrite IHx.
     rewrite bvZExt_bvZero; try lia.
     rewrite bvAdd_bvZero_l.
     rewrite bvZero_S.
     destruct x; auto.
Qed.

(*
 * Multiplying by nil on the left produces zero.
 *)
Lemma bvUFullMul_NilVec_l: forall w (y: bitvector w),
   bvUFullMul (NilVec bool) y = bvZero w.
Proof.
Admitted.

(*
 * Multiplying by nil on the right produces zero.
 *)
Lemma bvUFullMul_NilVec_r: forall w (x: bitvector w),
   bvUFullMul x (NilVec bool) = coerceVec (w + 0) (Nat.add_0_r w) (bvZero w).
Proof.
   intros.
   assert (NilVec bool = bvZero 0) as -> by (rewrite bvZero_0; auto).
   rewrite bvUFullMul_bvZero_r.
   rewrite bvZero_unique.
   auto.
Qed.

(*
 * left identity
 *)
Lemma bvUFullMul_bvOne_l: forall w1 w2 (y: bitvector w2),
   0 < w1 -> bvUFullMul (bvOne w1) y = bvZExt (w1 + w2) y.
Proof.
   intros * Hlt.
   revert Hlt.
   revert y.
   revert w2.
   induction w1; intros; try lia.
   rewrite bvOne_S.
   rewrite bvUFullMul_ConsVec_l.
   rewrite bvUFullMul_bvZero_l.
   rewrite ConsVec_false_bvZero.
   rewrite bvAdd_bvZero_r.
   simpl; auto.
Qed.

(*
 * right identity
 *)
Lemma bvUFullMul_bvOne_r: forall w1 w2 (x: bitvector w1),
   0 < w2 -> bvUFullMul x (bvOne w2) = bvZExt (w1 + w2) x.
Proof.
   intros * Hlt.
   revert Hlt.
   revert w2.
   induction x; intros.
   - simpl.
     assert (NilVec bool = bvZero 0) as -> by (rewrite bvZero_0; auto).
     rewrite bvZExt_bvZero; auto; lia.
   - simpl.
     rewrite IHx; auto.
     destruct x.
     + simpl.
       rewrite bvZExt_bvOne; try lia.
       rewrite bvAdd_one_l.
       simpl.
       (* XXX and this isn't true, something's wrong *)
       admit.
     + (* XXX same *)
       admit.
Admitted.

(*
 * bvUFullMul is commutative
 *)
Lemma bvUFullMul_comm: forall w1 w2 (x: bitvector w1) (y: bitvector w2) pf,
   bvUFullMul x y = coerceVec (w1 + w2) pf (bvUFullMul y x).
Proof.
   intros.
   revert pf.
   revert y.
   revert w2.
   induction x; intros.
   - simpl.
     assert (NilVec bool = bvZero 0) as -> by (rewrite bvZero_0; auto).
     rewrite bvUFullMul_bvZero_r.
     induction y.
     + simpl. rewrite bvZero_0. rewrite NilVec_unique. auto.
     + simpl. rewrite bvZero_unique. auto.
   - simpl.
     erewrite IHx.
     (* XXX this proof doesn't work *)
Admitted.

(*
 * same-size word multiplication (signedness-independent)
 *)
Definition bvMul {w : nat} (x y: bitvector w) : bitvector w :=
   bvTrunc w (bvUFullMul x y).

(*
 * multiplication is commutative
 *)
Lemma bvMul_comm: forall w (x y: bitvector w), bvMul x y = bvMul y x.
Proof.
   intros.
   unfold bvMul.
   rewrite bvUFullMul_comm with (pf := eq_refl).
   rewrite coerceVec_vacuous.
   auto.
Qed.

(*
 * left zero
 *)
Lemma bvMul_bvZero_l: forall w (y: bitvector w), bvMul (bvZero w) y = bvZero w.
Proof.
   intros.
   unfold bvMul.
   rewrite bvUFullMul_bvZero_l.
   rewrite bvTrunc_bvZero; auto; lia.
Qed.

(*
 * right zero
 *)
Lemma bvMul_bvZero_r: forall w (x: bitvector w), bvMul x (bvZero w) = bvZero w.
Proof.
   intros.
   rewrite bvMul_comm.
   apply bvMul_bvZero_l.
Qed.

(*
 * left identity
 *)
Lemma bvMul_bvOne_l: forall w (y: bitvector w), 0 < w -> bvMul (bvOne w) y = y.
Proof.
   intros * Hgt.
   unfold bvMul.
   rewrite bvUFullMul_bvOne_l; auto.
   (* XXX need a lemma for this *)
Admitted.

(*
 * right identity
 *)
Lemma bvMul_bvOne_r: forall w (x: bitvector w), 0 < w -> bvMul x (bvOne w) = x.
Proof.
   intros * Hgt.
   rewrite bvMul_comm.
   apply bvMul_bvOne_l; auto.
Qed.

(*
 * left negation
 *)
Lemma bvMul_bvMinusOne_l: forall w (y: bitvector w),
   bvMul (bvMinusOne w) y = bvNeg y.
Proof.
   intros.
Admitted.

(*
 * right negation
 *)
Lemma bvMul_bvMinusOne_r: forall w (x: bitvector w),
   bvMul x (bvMinusOne w) = bvNeg x.
Proof.
   intros.
   rewrite bvMul_comm.
   apply bvMul_bvMinusOne_l.
Qed.

(*
 * increment on the left
 *)
Lemma bvMul_bvInc_l: forall w (x y: bitvector w),
   bvMul (bvInc x) y = bvAdd y (bvMul x y).
Proof.
Admitted.

(*
 * increment on the right
 *)
Lemma bvMul_bvInc_r: forall w (x y: bitvector w),
   bvMul x (bvInc y) = bvAdd x (bvMul x y).
Proof.
   intros.
   rewrite bvMul_comm.
   rewrite bvMul_bvInc_l.
   rewrite bvMul_comm; auto.
Qed.

(*
 * decrement on the left
 *)
Lemma bvMul_bvDec_l: forall w (x y: bitvector w),
   bvMul (bvDec x) y = bvSub (bvMul x y) y.
Proof.
Admitted.

(*
 * decrement on the right
 *)
Lemma bvMul_bvDec_r: forall w (x y: bitvector w),
   bvMul x (bvDec y) = bvSub (bvMul x y) x.
Proof.
   intros.
   rewrite bvMul_comm.
   rewrite bvMul_bvDec_l.
   rewrite bvMul_comm; auto.
Qed.

(*
 * negate on the left
 *)
Lemma bvMul_bvNeg_l: forall w (x y: bitvector w),
   bvMul (bvNeg x) y = bvNeg (bvMul x y).
Proof.
Admitted.

(*
 * negate on the right
 *)
Lemma bvMul_bvNeg_r: forall w (x y: bitvector w),
   bvMul x (bvNeg y) = bvNeg (bvMul x y).
Proof.
   intros.
   rewrite bvMul_comm.
   rewrite bvMul_bvNeg_l.
   rewrite bvMul_comm; auto.
Qed.

(*
 * multiplication distributes over addition (right)
 *)
Lemma bvMul_bvAdd_r: forall w (x y z: bitvector w),
   bvMul x (bvAdd y z) = bvAdd (bvMul x y) (bvMul x z).
Proof.
Admitted.

(*
 * multiplication distributes over addition (left)
 *)
Lemma bvMul_bvAdd_l: forall w (x y z: bitvector w),
   bvMul (bvAdd x y) z = bvAdd (bvMul x z) (bvMul y z).
Proof.
   intros.
   rewrite bvMul_comm.
   rewrite bvMul_bvAdd_r.
   f_equal; rewrite bvMul_comm; auto.
Qed.


(*************************************************************)
(* div/mod *)

(*
 * Divide and return both the quotient and remainder.
 *
 * Core version that does unsigned division where the widths
 * aren't necessarily the same. (y should be longer than x)
 *)
Fixpoint coreDivRem {w1 w2: nat}
     (x: bitvector w1) (y: bitvector w2) : bitvector w1 * bitvector w1 :=
   match bvult (bvZExt w2 x) y with
   | true => (bvZero w1, x)
   | false =>
        match x as x_ in Vec _ w1_ return bitvector w1_ * bitvector w1_ with
        | NilVec _ => (NilVec bool, NilVec bool) (* division by zero *)
        | ConsVec x0 x' =>
             let (q, r) := coreDivRem x' y in
             let r' := ConsVec x0 r in
             match bvule y (bvZExt w2 r') with
             | true =>
                 (ConsVec true q,
                  bvTrunc (size r') (bvSub (bvZExt w2 r') y))
             | false =>
                 (ConsVec false q, r')
             end
        end
   end.

(*
 * Correctness statement for core division.
 *
 * Note that for bitvectors this is only true left to right, because there
 * are zero divisors and division doesn't return them.
 * For example, in 4 bits, 8 * 2 is 0, but 0 / 2 is 0, not 8.
 *)
Lemma coreDivRem_correct: forall w1 w2
     (x: bitvector w1) (y: bitvector w2) (q r: bitvector w1),
   coreDivRem x y = (q, r) ->
      bvAdd (bvMul (bvZExt w2 q) y) (bvZExt w2 r) = bvZExt w2 x.
Proof.
Admitted.

(*
 * Unsigned divide and remainder.
 *)
Definition bvUDivRem {w: nat} (x y: bitvector w) : bitvector w * bitvector w :=
   coreDivRem x y.

(*
 * Correctness statement for unsigned division.
 *)
Lemma bvUDivRem_correct: forall w (x y q r: bitvector w),
   bvUDivRem x y = (q, r) -> bvAdd (bvMul q y) r = x.
Proof.
   intros.
   unfold bvUDivRem.
   apply coreDivRem_correct in H.
   do 3 rewrite bvZExt_same in H.
   auto.
Qed.

(*
 * Divide and return the quotient. (unsigned)
 *)
Definition bvUDiv {w : nat} (x y: bitvector w) : bitvector w :=
   match bvUDivRem x y with
   | (q, _r) => q
   end.

(*
 * Divide and return the remainder. (unsigned)
 *)
Definition bvURem {w : nat} (x y: bitvector w) : bitvector w :=
   match bvUDivRem x y with
   | (_q, r) => r
   end.

(*
 * Signed division/remainder.
 *
 * This is the correct way (what CPUs do).
 *)
Definition bvSDivRem {w: nat} (x y: bitvector w) : bitvector w * bitvector w :=
   match (bvSign x, bvSign y) with
   | (false, false) =>
        bvUDivRem x y
   | (true, false) =>
        let (q, r) := bvUDivRem (bvNeg x) y in
        (bvNeg q, bvNeg r)
   | (false, true) =>
        let (q, r) := bvUDivRem x (bvNeg y) in
        (bvNeg q, r)
   | (true, true) =>
        let (q, r) := bvUDivRem (bvNeg x) (bvNeg y) in
        (q, bvNeg r)
   end.

(*
 * Alternate signed division/remainder.
 *
 * This matches some other environments.
 *)
Definition bvSDivRem' {w: nat} (x y: bitvector w) : bitvector w * bitvector w :=
   match (bvSign x, bvSign y) with
   | (false, false) =>
        bvUDivRem x y
   | (true, false) =>
        let (q, r) := bvUDivRem (bvNeg x) y in
        match bvEqb r (bvZero w) with
        | false => (bvNeg (bvInc q), bvSub y r)
        | true => (bvNeg q, r)
        end
   | (false, true) =>
        let (q, r) := bvUDivRem x (bvNeg y) in
        match bvEqb r (bvZero w) with
        | false => (bvNeg (bvInc q), bvNeg (bvSub (bvNeg y) r))
        | true => (bvNeg q, r)
        end
   | (true, true) =>
        let (q, r) := bvUDivRem (bvNeg x) (bvNeg y) in
        (q, bvNeg r)
   end.

(*
 * Correctness for signed division/remainder.
 *)
Lemma bvSDivRem_correct: forall w (x y q r: bitvector w),
   bvSDivRem x y = (q, r) -> bvAdd (bvMul q y) r = x.
Proof.
   intros * H.
   unfold bvSDivRem in H.
   destruct (bvSign x) eqn:Hnegx; destruct (bvSign y) eqn:Hnegy.
   - 
     destruct (bvUDivRem (bvNeg x) (bvNeg y)) as [uq ur] eqn:Huqr.
     assert (bvAdd (bvMul uq (bvNeg y)) ur = bvNeg x) as Hu by
          (apply bvUDivRem_correct in Huqr; auto).
     injection H; intros; subst.
     rewrite bvMul_bvNeg_r in Hu.
     rewrite bvAdd_bvNeg_l in Hu.
     rewrite bvNeg_inj in Hu; auto.
   - 
     destruct (bvUDivRem (bvNeg x) y) as [uq ur] eqn:Huqr.
     assert (bvAdd (bvMul uq y) ur = (bvNeg x)) as Hu by
          (apply bvUDivRem_correct in Huqr; auto).
     injection H; intros; subst.
     rewrite bvMul_bvNeg_l.
     rewrite <- bvNeg_bvAdd.
     rewrite Hu.
     apply bvNeg_bvNeg.
   - 
     destruct (bvUDivRem x (bvNeg y)) as [uq ur] eqn:Huqr.
     assert (bvAdd (bvMul uq (bvNeg y)) ur = x) as Hu by
          (apply bvUDivRem_correct in Huqr; auto).
     injection H; intros; subst.
     rewrite bvMul_bvNeg_l. rewrite bvMul_bvNeg_r.
     auto.
   - 
     destruct (bvUDivRem x y) as [uq ur] eqn:Huqr.
     assert (bvAdd (bvMul uq y) ur = x) as Hu by
          (apply bvUDivRem_correct in Huqr; auto).
     injection H; intros; subst.
     auto.
Qed.

(*
 * Correctness for alternate signed division/remainder.
 *)
Lemma bvSDivRem'_correct: forall w (x y q r: bitvector w),
   bvSDivRem' x y = (q, r) -> bvAdd (bvMul q y) r = x.
Proof.
   intros * H.
   unfold bvSDivRem' in H.
   destruct (bvSign x) eqn:Hnegx; destruct (bvSign y) eqn:Hnegy.
   - 
     destruct (bvUDivRem (bvNeg x) (bvNeg y)) as [uq ur] eqn:Huqr.
     assert (bvAdd (bvMul uq (bvNeg y)) ur = bvNeg x) as Hu by
          (apply bvUDivRem_correct in Huqr; auto).
     injection H; intros; subst.
     rewrite bvMul_bvNeg_r in Hu.
     rewrite bvAdd_bvNeg_l in Hu.
     rewrite bvNeg_inj in Hu; auto.
   - 
     destruct (bvUDivRem (bvNeg x) y) as [uq ur] eqn:Huqr.
     assert (bvAdd (bvMul uq y) ur = (bvNeg x)) as Hu by
          (apply bvUDivRem_correct in Huqr; auto).
     destruct (bv_eq_dec ur (bvZero w)).
     + subst. rewrite bvEqb_refl in H.
       injection H; intros; subst.
       rewrite bvAdd_bvZero_r in *.
       rewrite bvMul_bvNeg_l.
       rewrite Hu.
       rewrite bvNeg_bvNeg; auto.
     + rewrite <- bvEqb_neq in n.
       rewrite n in H.
       injection H; intros; subst.
       rewrite bvMul_bvNeg_l.
       rewrite bvAdd_bvNeg_l.
       rewrite bvMul_bvInc_l.
       rewrite bvNeg_bvSub.
       rewrite bvNeg_antisym.
       rewrite bvAdd_comm with (x := y).
       rewrite bvAdd_bvAdd_l.
       rewrite bvAdd_bvSub_r; auto.
   -
     destruct (bvUDivRem x (bvNeg y)) as [uq ur] eqn:Huqr.
     assert (bvAdd (bvMul uq (bvNeg y)) ur = x) as Hu by
          (apply bvUDivRem_correct in Huqr; auto).
     destruct (bv_eq_dec ur (bvZero w)).
     + subst. rewrite bvEqb_refl in H.
       injection H; intros; subst.
       rewrite bvMul_bvNeg_l.
       rewrite bvMul_bvNeg_r.
       auto.
     + rewrite <- bvEqb_neq in n.
       rewrite n in H.
       injection H; intros; subst.
       rewrite bvMul_bvNeg_l.
       rewrite bvMul_bvInc_l.
       rewrite bvAdd_comm with (x := y).
       rewrite <- bvNeg_bvAdd.
       rewrite bvMul_bvNeg_r.
       rewrite bvAdd_bvNeg_l.
       rewrite bvAdd_bvAdd_l.
       unfold bvSub.
       rewrite bvAdd_bvAdd_r with (x := y).
       rewrite bvAdd_bvNeg_diag_r.
       rewrite bvAdd_bvZero_l.
       auto.
   - 
     destruct (bvUDivRem x y) as [uq ur] eqn:Huqr.
     assert (bvAdd (bvMul uq y) ur = x) as Hu by
          (apply bvUDivRem_correct in Huqr; auto).
     injection H; intros; subst.
     auto.
Qed.

(*
 * Signed division.
 *)
Definition bvSDiv {w : nat} (x y: bitvector w) : bitvector w :=
   match bvSDivRem x y with
   | (q, _r) => q
   end.

(*
 * Signed remainder.
 *)
Definition bvSRem {w : nat} (x y: bitvector w) : bitvector w :=
   match bvSDivRem x y with
   | (_q, r) => r
   end.

(*
 * Alternate signed division.
 *)
Definition bvSDiv' {w : nat} (x y: bitvector w) : bitvector w :=
   match bvSDivRem' x y with
   | (q, _r) => q
   end.

(*
 * Alternate signed remainder.
 *)
Definition bvSRem' {w : nat} (x y: bitvector w) : bitvector w :=
   match bvSDivRem' x y with
   | (_q, r) => r
   end.

(*
 * 0 / y is 0, and 0 % y is 0.
 *)

Lemma coreDivRem_bvZero_l: forall w1 w2 (y: bitvector w2), w1 <= w2 ->
   y <> bvZero w2 ->
   coreDivRem (bvZero w1) y = (bvZero w1, bvZero w1).
Proof.
   intros * Hlt Hne.
   revert Hlt Hne.
   revert y.
   revert w2.
   destruct w1; intros.
   - simpl.
     destruct (bvult (bvZExt w2 (NilVec bool))); auto.
   - rewrite bvZero_S.
     simpl.
     assert (bvZExt w2 (ConsVec false (bvZero w1)) = bvZero w2) as H.
     { rewrite <- bvZero_S. rewrite bvZExt_bvZero; auto. }
     rewrite H.
     rewrite bvZero_S.
     rewrite bvult_bvZero_l; auto.
Qed.

Lemma bvUDivRem_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvUDivRem (bvZero w) y = (bvZero w, bvZero w).
Proof.
   intros.
   unfold bvUDivRem.
   apply coreDivRem_bvZero_l; auto.
Qed.

Lemma bvUDiv_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvUDiv (bvZero w) y = bvZero w.
Proof.
   intros.
   unfold bvUDiv.
   rewrite bvUDivRem_bvZero_l; auto.
Qed.

Lemma bvURem_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvURem (bvZero w) y = bvZero w.
Proof.
   intros.
   unfold bvURem.
   rewrite bvUDivRem_bvZero_l; auto.
Qed.

Lemma bvSDivRem_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvSDivRem (bvZero w) y = (bvZero w, bvZero w).
Proof.
   intros * Hlt.
   unfold bvSDivRem.
   rewrite bvSign_bvZero.
   assert (bvNeg y <> bvZero w).
   {
      contradict Hlt.
      rewrite bvNeg_antisym in Hlt.
      subst.
      rewrite bvNeg_bvZero; auto.
   }
   do 2 (rewrite bvUDivRem_bvZero_l; auto).
   rewrite bvNeg_bvZero.
   destruct (bvSign y); auto.
Qed.

Lemma bvSDiv_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvSDiv (bvZero w) y = bvZero w.
Proof.
   intros.
   unfold bvSDiv.
   rewrite bvSDivRem_bvZero_l; auto.
Qed.

Lemma bvSRem_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvSRem (bvZero w) y = bvZero w.
Proof.
   intros.
   unfold bvSRem.
   rewrite bvSDivRem_bvZero_l; auto.
Qed.

Lemma bvSDivRem'_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvSDivRem' (bvZero w) y = (bvZero w, bvZero w).
Proof.
   intros * Hlt.
   unfold bvSDivRem'.
   rewrite bvSign_bvZero.
   assert (bvNeg y <> bvZero w).
   {
      contradict Hlt.
      rewrite bvNeg_antisym in Hlt.
      subst.
      rewrite bvNeg_bvZero; auto.
   }
   do 2 (rewrite bvUDivRem_bvZero_l; auto).
   destruct (bvSign y); auto.
   rewrite bvEqb_refl.
   rewrite bvNeg_bvZero; auto.
Qed.

Lemma bvSDiv'_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvSDiv' (bvZero w) y = bvZero w.
Proof.
   intros.
   unfold bvSDiv'.
   rewrite bvSDivRem'_bvZero_l; auto.
Qed.

Lemma bvSRem'_bvZero_l: forall w (y: bitvector w),
   y <> bvZero w -> bvSRem' (bvZero w) y = bvZero w.
Proof.
   intros.
   unfold bvSRem'.
   rewrite bvSDivRem'_bvZero_l; auto.
Qed.

(*
 * In this implementation, x / 0 is minusone and x % 0 is x.
 * Except, signed divide of negative by 0 does odd things.
 * We could fix that up but it doesn't seem worthwhile.
 *
 * Don't divide by zero.
 *)

Lemma coreDivRem_bvZero_r: forall w1 w2 (x: bitvector w1),
   w1 <= w2 ->
   (*x <> bvZero w1 ->*)
   coreDivRem x (bvZero w2) = (bvMinusOne w1, x).
Proof.
   intros * Hlt.
   revert Hlt.
   revert w2.
   induction x; intros.
   - simpl. rewrite bvZero_0.
     destruct (bvult (bvZExt w2 (NilVec bool)) (bvZero w2)); auto.
   - simpl.
     rewrite bvult_bvZero_r.
     rewrite bvMinusOne_S in *.
     rewrite IHx; try lia.
     rewrite bvule_bvZero_l.
     rewrite bvSub_bvZero_r.
     f_equal.
     destruct (Nat.eq_dec (S n) w2).
     + subst.
       rewrite bvTrunc_same.
       rewrite bvZExt_same.
       auto.
     + assert (size (ConsVec x x0) = S n) as HN1 by (unfold size; auto).
       rewrite bvTrunc_bvZExt_same with (pf := HN1); try lia.
       rewrite coerceVec_vacuous; auto.
Qed.

Lemma bvUDivRem_bvZero_r: forall w (x: bitvector w),
   bvUDivRem x (bvZero w) = (bvMinusOne w, x).
Proof.
   intros.
   unfold bvUDivRem.
   apply coreDivRem_bvZero_r; lia.
Qed.

Lemma bvUDiv_bvZero_r: forall w (x: bitvector w),
   bvUDiv x (bvZero w) = bvMinusOne w.
Proof.
   intros.
   unfold bvUDiv.
   rewrite bvUDivRem_bvZero_r; auto.
Qed.

Lemma bvURem_bvZero_r: forall w (x: bitvector w),
   bvURem x (bvZero w) = x.
Proof.
   intros.
   unfold bvURem.
   rewrite bvUDivRem_bvZero_r; auto.
Qed.

Lemma bvSDivRem_bvZero_r: forall w (x: bitvector w),
   bvSDivRem x (bvZero w) = (if bvSign x then bvOne w else bvMinusOne w, x).
Proof.
   intros.
   unfold bvSDivRem.
   rewrite bvSign_bvZero.
   do 2 rewrite bvUDivRem_bvZero_r.
   rewrite bvNeg_bvMinusOne.
   rewrite bvNeg_bvNeg.
   destruct (bvSign x); auto.
Qed.

Lemma bvSDiv_bvZero_r: forall w (x: bitvector w),
   bvSDiv x (bvZero w) = if bvSign x then bvOne w else bvMinusOne w.
Proof.
   intros.
   unfold bvSDiv.
   rewrite bvSDivRem_bvZero_r; auto.
Qed.

Lemma bvSRem_bvZero_r: forall w (x: bitvector w),
   bvSRem x (bvZero w) = x.
Proof.
   intros.
   unfold bvSRem.
   rewrite bvSDivRem_bvZero_r; auto.
Qed.

Lemma bvSDivRem'_bvZero_r: forall w (x: bitvector w),
   bvSDivRem' x (bvZero w) = (if bvSign x then bvZero w else bvMinusOne w, x).
Proof.
   intros.
   unfold bvSDivRem'.
   rewrite bvSign_bvZero.
   do 2 rewrite bvUDivRem_bvZero_r.
   rewrite bvNeg_bvMinusOne.
   rewrite bvInc_bvMinusOne.
   rewrite bvNeg_bvZero.
   rewrite bvSub_bvZero_l.
   rewrite bvNeg_bvNeg.
   destruct (bvSign x) eqn:Hneg; auto.
   assert (bvEqb (bvNeg x) (bvZero w) = false) as ->; auto.
   rewrite bvEqb_neq. intro Hf.
   rewrite bvNeg_antisym in Hf.
   rewrite bvNeg_bvZero in Hf.
   subst.
   rewrite bvSign_bvZero in Hneg.
   discriminate.
Qed.

Lemma bvSDiv'_bvZero_r: forall w (x: bitvector w),
   bvSDiv' x (bvZero w) = if bvSign x then bvZero w else bvMinusOne w.
Proof.
   intros.
   unfold bvSDiv'.
   rewrite bvSDivRem'_bvZero_r; auto.
Qed.

Lemma bvSRem'_bvZero_r: forall w (x: bitvector w),
   bvSRem' x (bvZero w) = x.
Proof.
   intros.
   unfold bvSRem'.
   rewrite bvSDivRem'_bvZero_r; auto.
Qed.

(*
 * x / 1 is x; x % 1 is 0.
 *)

Lemma coreDivRem_1_r: forall w1 w2 (x: bitvector w1),
   coreDivRem x (bvOne w2) = (x, bvZero w1).
Proof.
Admitted.

Lemma bvUDivRem_1_r: forall w (x: bitvector w),
   bvUDivRem x (bvOne w) = (x, bvZero w).
Proof.
   intros.
   unfold bvUDivRem.
   apply coreDivRem_1_r.
Qed.

Lemma bvUDiv_1_r: forall w (x: bitvector w),
   bvUDiv x (bvOne w) = x.
Proof.
   intros.
   unfold bvUDiv.
   rewrite bvUDivRem_1_r; auto.
Qed.

Lemma bvURem_1_r: forall w (x: bitvector w),
   bvURem x (bvOne w) = bvZero w.
Proof.
   intros.
   unfold bvURem.
   rewrite bvUDivRem_1_r; auto.
Qed.

Lemma bvSDivRem_1_r: forall w (x: bitvector w),
   1 < w -> bvSDivRem x (bvOne w) = (x, bvZero w).
Proof.
   intros * Hlt.
   unfold bvSDivRem.
   rewrite bvSign_bvOne; auto.
   do 2 rewrite bvUDivRem_1_r.
   rewrite bvNeg_bvNeg.
   rewrite bvNeg_bvZero.
   destruct (bvSign x); auto.
Qed.

Lemma bvSDiv_1_r: forall w (x: bitvector w),
   1 < w -> bvSDiv x (bvOne w) = x.
Proof.
   intros * Hlt.
   unfold bvSDiv.
   rewrite bvSDivRem_1_r; auto.
Qed.

Lemma bvSRem_1_r: forall w (x: bitvector w),
   1 < w -> bvSRem x (bvOne w) = bvZero w.
Proof.
   intros * Hlt.
   unfold bvSRem.
   rewrite bvSDivRem_1_r; auto.
Qed.

Lemma bvSDivRem'_1_r: forall w (x: bitvector w),
   1 < w -> bvSDivRem' x (bvOne w) = (x, bvZero w).
Proof.
   intros * Hlt.
   unfold bvSDivRem'.
   rewrite bvSign_bvOne; auto.
   do 2 rewrite bvUDivRem_1_r.
   rewrite bvNeg_bvNeg.
   rewrite bvEqb_refl.
   destruct (bvSign x); auto.
Qed.

Lemma bvSDiv'_1_r: forall w (x: bitvector w),
   1 < w -> bvSDiv' x (bvOne w) = x.
Proof.
   intros * Hlt.
   unfold bvSDiv'.
   rewrite bvSDivRem'_1_r; auto.
Qed.

Lemma bvSRem'_1_r: forall w (x: bitvector w),
   1 < w -> bvSRem' x (bvOne w) = bvZero w.
Proof.
   intros * Hlt.
   unfold bvSRem'.
   rewrite bvSDivRem'_1_r; auto.
Qed.

(*
 * x / x is 1.
 *)

Lemma coreDivRem_same: forall w1 (x: bitvector w1),
   coreDivRem x x = (bvOne w1, bvZero w1).
Proof.
   intros.
Admitted.

Lemma bvUDivRem_same: forall w (x: bitvector w),
   bvUDivRem x x = (bvOne w, bvZero w).
Proof.
   intros.
   unfold bvUDivRem.
   apply coreDivRem_same.
Qed.

Lemma bvUDiv_same: forall w (x: bitvector w),
   bvUDiv x x = bvOne w.
Proof.
   intros.
   unfold bvUDiv.
   rewrite bvUDivRem_same; auto.
Qed.

Lemma bvURem_same: forall w (x: bitvector w),
   bvURem x x = bvZero w.
Proof.
   intros.
   unfold bvURem.
   rewrite bvUDivRem_same; auto.
Qed.

Lemma bvSDivRem_same: forall w (x: bitvector w),
   bvSDivRem x x = (bvOne w, bvZero w).
Proof.
   intros.
   unfold bvSDivRem.
   do 2 rewrite bvUDivRem_same.
   destruct (bvSign x); auto.
   rewrite bvNeg_bvZero; auto.
Qed.

Lemma bvSDiv_same: forall w (x: bitvector w),
   bvSDiv x x = bvOne w.
Proof.
   intros.
   unfold bvSDiv.
   rewrite bvSDivRem_same; auto.
Qed.

Lemma bvSRem_same: forall w (x: bitvector w),
   bvSRem x x = bvZero w.
Proof.
   intros.
   unfold bvSRem.
   rewrite bvSDivRem_same; auto.
Qed.

Lemma bvSDivRem'_same: forall w (x: bitvector w),
   bvSDivRem' x x = (bvOne w, bvZero w).
Proof.
   intros.
   unfold bvSDivRem'.
   do 2 rewrite bvUDivRem_same.
   rewrite bvNeg_bvZero.
   destruct (bvSign x); auto.
Qed.

Lemma bvSDiv'_same: forall w (x: bitvector w),
   bvSDiv' x x = bvOne w.
Proof.
   intros.
   unfold bvSDiv'.
   rewrite bvSDivRem'_same; auto.
Qed.

Lemma bvSRem'_same: forall w (x: bitvector w),
   bvSRem' x x = bvZero w.
Proof.
   intros.
   unfold bvSRem'.
   rewrite bvSDivRem'_same; auto.
Qed.

(*
 * x / y with x < y is 0 with remainder x.
 *
 * ...except for the alternate signed divides when y is negative...
 *)

Lemma coreDivRem_small: forall w1 w2 (x: bitvector w1) (y: bitvector w2),
   w1 <= w2 -> bvult (bvZExt w2 x) y = true ->
   coreDivRem x y = (bvZero w1, x).
Proof.
   intros * Hwlt Hxlt.
Admitted.

Lemma bvUDivRem_small: forall w (x: bitvector w) (y: bitvector w),
   bvult x y = true ->
   bvUDivRem x y = (bvZero w, x).
Proof.
   intros * Hlt.
   unfold bvUDivRem.
   apply coreDivRem_small; auto.
   rewrite bvZExt_same; auto.
Qed.

Lemma bvUDiv_small: forall w (x: bitvector w) (y: bitvector w),
   bvult x y = true ->
   bvUDiv x y = bvZero w.
Proof.
   intros * Hlt.
   unfold bvUDiv.
   rewrite bvUDivRem_small; auto.
Qed.

Lemma bvURem_small: forall w (x: bitvector w) (y: bitvector w),
   bvult x y = true ->
   bvURem x y = x.
Proof.
   intros * Hlt.
   unfold bvURem.
   rewrite bvUDivRem_small; auto.
Qed.

Lemma bvSDivRem_small: forall w (x: bitvector w) (y: bitvector w),
   bvult (bvAbs x) (bvAbs y) = true ->
   bvSDivRem x y = (bvZero w, x).
Proof.
   intros * Hlt.
   unfold bvSDivRem.
   unfold bvAbs in Hlt.
   destruct (bvSign x) eqn:Hx; destruct (bvSign y) eqn:Hy.
   - rewrite bvUDivRem_small; auto.
     rewrite bvNeg_bvNeg; auto.
   - rewrite bvUDivRem_small; auto.
     rewrite bvNeg_bvZero. rewrite bvNeg_bvNeg. auto.
   - rewrite bvUDivRem_small; auto.
     rewrite bvNeg_bvZero. auto.
   - rewrite bvUDivRem_small; auto.
Qed.

Lemma bvSDiv_small: forall w (x: bitvector w) (y: bitvector w),
   bvult (bvAbs x) (bvAbs y) = true ->
   bvSDiv x y = bvZero w.
Proof.
   intros * Hlt.
   unfold bvSDiv.
   rewrite bvSDivRem_small; auto.
Qed.

Lemma bvSRem_small: forall w (x: bitvector w) (y: bitvector w),
   bvult (bvAbs x) (bvAbs y) = true ->
   bvSRem x y = x.
Proof.
   intros * Hlt.
   unfold bvSRem.
   rewrite bvSDivRem_small; auto.
Qed.

Lemma bvSDivRem'_small: forall w (x: bitvector w) (y: bitvector w),
   bvult (bvAbs x) (bvAbs y) = true ->
   bvSDivRem' x y =
      if bool_eq (bvSign x) (bvSign y) || bvEqb x (bvZero w) then (bvZero w, x)
      else (bvMinusOne w, bvAdd y x).
Proof.
   intros * Hlt.
   unfold bvSDivRem'.
   unfold bvAbs in Hlt.
   destruct (bvSign x) eqn:Hx; destruct (bvSign y) eqn:Hy.
   - rewrite bvUDivRem_small; auto.
     rewrite bvNeg_bvNeg; auto.
   - rewrite bvUDivRem_small; auto.
     rewrite bvNeg_bvZero.
     rewrite bvInc_bvZero.
     rewrite bvNeg_bvOne.
     unfold bvSub.
     rewrite bvNeg_bvNeg.
     simpl.
     (*
      * XXX would be tidier to have a lemma bvEqb (bvNeg x) y = bvEqb
      * x (bvNeg y)
      *)
     destruct (bvEqb x (bvZero w)) eqn:Hz.
     + apply bvEqb_eq in Hz. subst.
       rewrite bvNeg_bvZero.
       rewrite bvEqb_refl; auto.
     + apply bvEqb_neq in Hz.
       assert (bvNeg x <> bvZero w) as Hz'.
       {
          contradict Hz.
          rewrite bvNeg_antisym in Hz.
          subst.
          apply bvNeg_bvZero.
       }
       rewrite <- bvEqb_neq in Hz'.
       rewrite Hz'; auto.
   - rewrite bvUDivRem_small; auto.
     rewrite bvNeg_bvZero.
     rewrite bvInc_bvZero.
     rewrite bvNeg_bvOne.
     unfold bvSub.
     rewrite bvNeg_bvAdd.
     do 2 rewrite bvNeg_bvNeg.
     simpl; auto.
   - rewrite bvUDivRem_small; auto.
Qed.

Lemma bvSDiv'_small: forall w (x: bitvector w) (y: bitvector w),
   bvult (bvAbs x) (bvAbs y) = true ->
   bvSDiv' x y =
      if bool_eq (bvSign x) (bvSign y) || bvEqb x (bvZero w) then bvZero w
      else bvMinusOne w.
Proof.
   intros * Hlt.
   unfold bvSDiv'.
   rewrite bvSDivRem'_small; auto.
   destruct (bool_eq (bvSign x) (bvSign y) || bvEqb x (bvZero w)); auto.
Qed.

Lemma bvSRem'_small: forall w (x: bitvector w) (y: bitvector w),
   bvult (bvAbs x) (bvAbs y) = true ->
   bvSRem' x y =
      if bool_eq (bvSign x) (bvSign y) || bvEqb x (bvZero w) then x
      else bvAdd y x.
Proof.
   intros * Hlt.
   unfold bvSRem'.
   rewrite bvSDivRem'_small; auto.
   destruct (bool_eq (bvSign x) (bvSign y) || bvEqb x (bvZero w)); auto.
Qed.


(*************************************************************)
(* integer conversions *)

(*
 * Convert a bitvector to nat.
 *)
Fixpoint bvToNat {w} (x: bitvector w) : nat :=
   match x with
   | NilVec _ => 0
   | ConsVec b x' =>
        let x'' := 2 * bvToNat x' in
        match b with
        | false => x''
        | true => S x''
        end
   end.

(*
 * Convert a nat to a bitvector.
 *)
Fixpoint bvNat (w: nat) (n: nat) : bitvector w :=
   match n with
   | 0 => bvZero w
   | S n' => bvInc (bvNat w n')
   end.

Arguments bvNat /.

(*
 * Convert a positive to a bitvector.
 *)
Fixpoint bvPositive (w: nat) (n: positive) : bitvector w :=
   match n with
   | xH => bvOne w
   | xO n' => bvShl (bvPositive w n') 1
   | xI n' => bvInc (bvShl (bvPositive w n') 1)
   end.

(*
 * Convert an N to a bitvector.
 *)
Definition bvN (w: nat) (n: N) : bitvector w :=
   match n with
   | N0 => bvZero w
   | Npos p => bvPositive w p
   end.

(*
 * Convert a bitvector to an N.
 *)
Fixpoint bvToN {w: nat} (x: bitvector w) : N :=
   match x with
   | NilVec _ => 0%N
   | ConsVec x0 x' =>
        match x0 with
        | false => 2 * bvToN x'
        | true => 1 + 2 * bvToN x'
        end
   end.

(*
 * Convert a Z to a bitvector. (formerly "intToBv")
 *)
Definition bvZ (w: nat) (n: Z) : bitvector w :=
   match n with
   | Z0 => bvZero w
   | Zpos p => bvPositive w p
   | Zneg p => bvNeg (bvPositive w p)
   end.

Arguments bvZ : simpl never.

(*
 * Convert a bitvector (treated as unsigned) to a Z.
 * (formerly bvToInt)
 *)
Fixpoint bvUtoZ {w: nat} (x: bitvector w) : Z :=
   match x with
   | NilVec _ => 0%Z
   | ConsVec x0 x' =>
        match x0 with
        | false => 2 * bvUtoZ x'
        | true => 1 + 2 * bvUtoZ x'
        end
   end.

(*
 * Convert a bitvector (treated as signed) to a Z.
 * (formerly sbvToInt)
 *
 * note: "Z.opp" is negate.
 *)
Definition bvStoZ {w: nat} (x: bitvector w) : Z :=
   match bvSign x with
   | false => bvUtoZ x
   | true => Z.opp (bvUtoZ (bvNeg x))
   end.


(*************************************************************)
(* base 2 log *)

(*
 * Take the log base 2. Returns None if given 0.
 *)
Fixpoint bvLg2Option {w: nat} (x: bitvector w) : option (bitvector w).
(*
   match x with
   | NilVec _ => None
   | ConsVec x0 x' =>
        match bvLg2Option x' with
        | None =>
             match x0 with
             | false => None
             | true => Some (bvZero w)
             end
        | Some k => Some (coerceVec w _ (bvInc (append k (bvZero 1))))
        end
   end.
*)
Proof.
   destruct x as [ | w x0 x'].
   - exact None.
   - refine (
        match bvLg2Option w x' with
        | None =>
             match x0 with
             | false => None
             | true => Some _
             end
        | Some k => Some _
        end
     ).
     + exact (bvZero (S w)).
     + refine (coerceVec (S w) _ (bvInc (append x' (bvZero 1)))).
       exact (eq_sym (Nat.add_1_r w)).
Defined.

(*
 * Take the log base 2.
 *
 * This version returns zero for zero.
 *)
Definition bvLg2 {w : nat} (x: bitvector w) : bitvector w :=
   match bvLg2Option x with
   | None => bvZero w
   | Some k => k
   end.

(*
 * It only returns none on zero.
 *)
Lemma bvLg2Option_nonzero: forall w (x: bitvector w),
   x <> bvZero w -> bvLg2Option x <> None.
Proof.
   intros * Hnz.
   revert Hnz.
   induction x; intros; simpl; try contradiction.
   rewrite bvZero_S in *.
   destruct x.
   - destruct (bvLg2Option x0); discriminate.
   - destruct (bvLg2Option x0); try discriminate.
     assert (x0 <> bvZero n) as H by congruence.
     apply IHx in H.
     contradiction.
Qed.

(*
 * Lower bound on x.
 *)
Lemma bvLg2Option_lb: forall w (x: bitvector w) k,
   bvLg2Option x = Some k -> bvule (bvShl (bvOne w) (bvToNat k)) x = true.
Proof.
Admitted.

(*
 * Upper bound on x.
 *)
Lemma bvLg2Option_ub: forall w (x: bitvector w) k,
   bvLg2Option x = Some k -> bvult x (bvShl (bvOne w) (S (bvToNat k))) = true.
Proof.
Admitted.

(*
 * FUTURE: we don't have the machinery to say that if
 * x is a power of 2, 2 ^ lg2 x = x.
 *)


(*************************************************************)
(* other pieces *)

(*
 * The old bitvector library contained this. Does anything downstream
 * rely on it? It would probably be better to get rid of it as it can
 * cause confusion.
 *)

(* Useful notation for bools *)
Definition boolToInt (b : bool) : Z := if b then 1%Z else 0%Z.
Number Notation bool Z.odd boolToInt : bool_scope.
Close Scope bool_scope. (* no, don't interpret all numbers as booleans... *)

(*
 * Return whether adding x and y incurs a signed overflow.
 *
 * If x and y have the same sign, and the sum has a different
 * sign, that's an overflow.
 *)
Definition bvAddOverflow {w : nat} (x y: bitvector w) : bool :=
   match bool_eq (bvSign x) (bvSign y) with
   | false => false
   | true =>
        match bool_eq (bvSign x) (bvSign (bvAdd x y)) with
        | false => true
        | true => false
        end
   end.

(*
 * Return whether subtracting y from x incurs a signed
 * overflow.
 *)
Definition bvSubOverflow {w : nat} (x y: bitvector w) : bool :=
   bvAddOverflow x (bvNeg y).

