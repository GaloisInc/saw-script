(*
 * Vectors.
 *
 * This implementation uses an inductive indexed by length.
 *
 * The type is "Vec a n" where "a" is the type (in Type) and "n" is
 * the length (in nat).
 *
 * This does result in some dependent typing headaches. Mostly, we
 * need explicit coercions in annoying cases like when we need a Vec
 * of length n and we have one of length n + 0.
 *
 * Using nat as the index type gives us free proof irrelevance; that
 * means that we should be able to avoid incurring any axioms.
 * However, the basic mechanisms for handling things incur the axiom
 * anyway. Right now most things do incur the axiom, but the direct
 * use has been contained in one or two places. FUTURE: clean that up.
 *
 * On the plus side we do not need to carry proofs around inside our
 * vectors, which saves on numerous other headaches.
 *
 * The lemma collection is fairly complete. The goal is that users of
 * this library should not have to open the internals of the vectors;
 * with some luck that may actually be true. If you find something
 * missing, please open a ticket.
 *
 * Lemmas about combinations of functions (which is most of them) are
 * named with the outer function first, then the inner one and, if
 * necessary, the position. Thus for example "append_nil_r" gives us a
 * statement about append with nil in its right argument position.
 *
 * A few other names exist, mostly standard conventions like _trans
 * for transitivity, _comm for commutativity, etc.
 *
 * If you find inconsistent or confusing naming, please also open a
 * ticket.
 *
 * Note that the prior version of this library used "Vec n a" rather
 * that "Vec a n". Unfortunately, the arguments to Vec need to be in
 * this order (the type first) for the inductive to work properly.
 * (That is: the type needs to be a parameter and the length needs to
 * be an index, and parameters come before indexes.) If you find old
 * logic using the old library (SAWCoreVectorsAsRocqVectors) you'll
 * need to swap all the arguments to Vec. :-|
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Eqdep.
From Stdlib Require Import Eqdep_dec.
(*From Stdlib Require Import JMeq.*)
(*From Stdlib Require Import FunctionalExtensionality.*)

(*
 * Current state:
 *   - whole thing could use (another) top-to-bottom pass in emacs to
 *     fix formatting, fix names, add comments, add statements of
 *     missing lemmas, etc.
 *   - there should be a documentation file
 *   - should maybe have a compat file for uses of the old library, though
 *     it's likely doomed
 *   - should have a migration guide for any existing uses
 *   - needs integration
 *)

(*
 * XXX in general we need to decide whether we should use names
 * (and in some cases styles/etc) matching SAWCore or matching the
 * usual Rocq idioms. Could go either way; the one is easier to follow
 * if you're looking specifically at SAWCore things, the other if you're
 * used to Rocq.
 *
 * Tentative conclusion is: the goal here is being able to do manual
 * proofs. Therefore, we should do all possible automated steps to
 * make that as easy as possible, and that includes rewriting away
 * SAWCore idiosyncrasies in favor of conventional Rocq idioms.
 *)


(*************************************************************)
(* Vec *)

(*
 * Build up vectors as a list indexed by size
 *
 * The argument order has to be this way but it's opposite the
 * previous version of this library.
 *)
Inductive Vec (a: Type): nat -> Type :=
| NilVec: Vec a 0
| ConsVec: forall n (x: a) (xs: Vec a n), Vec a (S n)
.

(*
 * The type needs to be explicit for NilVec, but not ConsVec.
 * The length can be implicit too.
 *)
Arguments ConsVec {a} {n}.

(*
 * Induction rule for proving things about vectors of length 0 given a
 * corresponding proof about NilVec. This allows unpacking the vector
 * without getting into trouble with other things of the same type.
 *)
Definition caseVec_0 {a: Type} (P: Vec a 0 -> Type)
      (H: P (NilVec a))
      (xs: Vec a 0) : P xs :=
   match xs with
   | NilVec _ => H
   | _ => False_rect
   end.

(*
 * Induction rule for proving things about vectors of length > 0 given
 * a corresponding proof about ConsVec. This allows unpacking the
 * vector without getting into trouble with other things of the same
 * type.
 *)
Definition caseVec_S {a: Type} {n: nat} (P: Vec a (S n) -> Type)
     (H: forall x xs, P (ConsVec x xs))
     (xs: Vec a (S n)) : P xs :=
  match xs as xs' in Vec _ (S n') return
    forall (P: Vec a (S n') -> Type) (H: forall x xs, P (ConsVec x xs)), P xs'
  with
  | NilVec _ => idProp
  | ConsVec h t => fun P H => H h t
  end P H.


(*
 * Vectors of length 0 are always nil.
 *)
Lemma Vec_0:
   forall a (xs: Vec a 0), xs = NilVec a.
Proof.
   intros.
   induction xs using caseVec_0.
   auto.
Qed.

(*
 * Vectors of nonzero length can be decomposed.
 *)
Lemma Vec_S:
   forall a n (xs: Vec a (S n)), exists x xs', xs = ConsVec x xs'.
Proof.
   intros.
   induction xs using caseVec_S.
   exists x, xs.
   auto.
Qed.


(*************************************************************)
(* decidable equality *)

Lemma Vec_eq_dec: forall {a n} (xs ys: Vec a n),
   (forall (x y: a), { x = y } + { x <> y }) ->
   { xs = ys } + { xs <> ys }.
Proof.
   intros * a_eq_dec.
   revert ys.
   induction xs as [ | n x xs]; intros.
   - destruct ys using caseVec_0. left; auto.
   - destruct ys as [y ys] using caseVec_S.
     destruct (a_eq_dec x y).
     + destruct (IHxs ys); subst.
       * left; auto.
       * right; congruence.
     + right; congruence.
Qed.


(*************************************************************)
(* size *)

(*
 * The size of a vector.
 *)
Definition size {a: Type} {n: nat} (_: Vec a n) : nat := n.

(*
 * This is here mostly so if you type the name it's available.
 * Under ordinary circumstances all you ever need to do with
 * size is unfold it.
 *)
Lemma size_NilVec: forall a, size (NilVec a) = 0.
Proof.
   intros; simpl; auto.
Qed.

(*
 * Unfold lemma for cases where the full size expression might
 * be more complicated and you don't want to incur that.
 *)
Lemma size_ConsVec:
   forall a n x (xs: Vec a n), size (ConsVec x xs) = S (size xs).
Proof.
   intros; simpl; auto.
Qed.


(*************************************************************)
(* coerce *)

(*
 * Because Rocq is very conservative about convertibility of dependent
 * types, in general we need coercions anywhere we have sizes that are
 * the same but not syntactically identical. This extends even to
 * cases like "n" vs "n + 0".
 *
 * The form of a coercion in this library is:
 *    coerceVec <new-size> <proof> <vector-of-old-size>
 *
 * where <proof> is a proof of the identity <new-size> = <old-size>.
 *
 * When writing code (definitions and fixpoints meant to be
 * executable) you will need coercions, and it's important to avoid
 * using large proof terms. You'll see them appear again in your proof
 * context when trying to prove things about the code, and often
 * you'll get combinations of two or three of them, so if they're more
 * than trivial the resulting proof context becomes unreadable and
 * unmanageable.
 *
 * This is still true, though to a lesser extent, when stating lemmas;
 * you will often need coercions and if you put explicit proof terms in
 * them, they'll tend to show up in other proofs downstream.
 *
 * When _applying_ lemmas this doesn't matter, because the results
 * appear only in the proof term inside the lemma and (as usual) those
 * are invisible in normal usage.
 *
 * For these reasons the code below uses the following procedures.
 *
 * 0. Since most of the proofs are equalities intended for rewriting
 * and the default direction is left to right, coercions go on the
 * right hand side. This introduces coercions when rewriting, which is
 * undesirable, but better than the alternative which is to require a
 * matching coercion to already exist in the goal. This order
 * preference gets in the way of rewriting in reverse; therefore we
 * often provide both the forward and backward versions of the same
 * equality statement, in both cases with the coercion on the RHS.
 *
 * 1. In code, the proof terms are always explicit and have been
 * arranged so they're always size 1, that is, a single application of
 * some lemma with arguments only as needed from context. Because the
 * coercions we need tend to be simple arithmetic, often these are
 * lemmas straight from the stdlib, like Nat.add_0_r. When the lemma
 * needed isn't in the stdlib, it's stated separately along with the
 * code, with a name of the form <function>_<case>_proof, where <case>
 * says something about which branch of the function it's used in.
 * These lemmas are generally proved with lia; lia generates large
 * messy proof terms, but we don't need to look at the proof terms
 * inside the lemmas so that's ok. We specifically don't use lia to
 * generate proof terms that appear in code.
 *
 * 2. In lemma statements, the proof terms are explicit size 1
 * applications in cases where a suitable lemma already exists in the
 * stdlib. (Or at least, that's the intent. Might have missed some.)
 * In other cases, the lemmas are generalized over all proof terms of
 * the right type and the lemma user needs to supply the proof. This
 * avoids incurring that cost for simple cases and avoids generating
 * messes in the others.
 *
 * 3. In lemma applications, where a proof is needed it's generated
 * with lia. The scheme for this seen below typically looks like this:
 *    assert (m + n - m = n) as HN1 by lia.
 *    assert (min (min n m) n = n) as HN2 by lia.
 *      :
 *    rewrite lemma1 with (pf := HN1).
 *    rewrite lemma2 in H with (pf := HN2).
 *      :
 *
 * It does not work to do "rewrite lemma with (pf := ltac:(lia))",
 * though you'd think it should; not sure why.
 *
 * When writing these proofs the basic method is:
 *    - At first when you need a proof, use erewrite and let Rocq
 *      generate an evar for it.
 *    - When the proof is otherwise done, it'll tell you all the
 *      proofs you need.
 *    - You can fill them in at that point, but it's ultimately
 *      simpler and more robust to paste them as assertions and change
 *      erewrite to rewrite with explicit proofs as shown above.
 *
 * Essentially all the coercion proofs needed can be retired with lia.
 *
 * The following tools are available to get rid of coercions:
 *    - NilVec_unique: coercions of NilVec are redundant.
 *    - coerceVec_vacuous: coercions from n to n are redundant.
 *    - coerceVec_coerceVec: chains of coercions can be reduced to
 *      one.
 *    - coerceVec_irr: coercions on both sides of an equality can be
 *      dropped, provided the sizes of the underlying terms match.
 *    - coerceVec_sym: a coercion can be moved to the other side of
 *      an equality.
 *    - coerceVec_rewrite: you can drop a coercion when rewriting
 *      using a vector equality.
 *    - ConsVec_coerceVec, head_coerceVec, tail_coerceVec,
 *      append_coerceVec_[lr], etc.: coercions inside functions can
 *      either be dropped or moved to the outside.
 *
 * Unfortunately, the same restrictions that cause coercions to be
 * needed in the first place mean that they can't just be dropped
 * arbitrarily. This is a fundamental restriction of trying to have
 * statically checked lengths in Rocq.
 *
 * Beware that the typechecker will sometimes simplify when checking
 * convertibility. This means (because add is implemented so it
 * matches on the left first) that while you need an explicit coercion
 * from n + 0 to n, 0 + n and n are convertible, and so are S (n + m)
 * and S n + m. Sometimes this means that the vector size will reduce
 * but the size value in the implicit argument of the thing taking the
 * vector won't, and then one rewrite works but further rewrites and
 * simplifications refuse to go for no obvious reason. This can
 * usually be worked around by including the surrounding call in the
 * rewrite. See for example the proof of revAppend_append_r. And don't
 * forget to turn on display of implicit arguments when things start
 * behaving weirdly.
 *)
 
(*
 * Cast a vector to a different but equivalent length. Takes the new
 * size and an explicit proof of size equality.
 *
 * Note that the proof is m = n: output length on the left, input
 * length on the right.
 *
 * You can use eq_sym to flip your proof if necessary.
 *)
Definition coerceVec {a: Type} {n: nat}
     (m: nat) (pf: m = n) (xs: Vec a n) : Vec a m :=
   match
      pf in eq _ m'
      return Vec a m' -> Vec a m
   with
   | eq_refl => fun x => x
   end xs.

(*
 * All NilVecs are the same
 *)
Lemma NilVec_unique: forall a pf, coerceVec 0 pf (NilVec a) = NilVec a.
Proof.
   intros.
   rewrite (UIP_dec Nat.eq_dec pf eq_refl).
   simpl; auto.
Qed.

(*
 * ConsVec commutes with coerceVec.
 *)
Lemma ConsVec_coerceVec: forall a n n' pf x (xs: Vec a n),
   ConsVec x (coerceVec n' pf xs) =
      coerceVec (S n') (eq_S n' n pf) (ConsVec x xs).
Proof.
   intros.
   unfold coerceVec.
   destruct pf.
   simpl; auto.
Qed.

(*
 * Reverse direction
 *)
Lemma coerceVec_ConsVec: forall a n n' pf x (xs: Vec a n),
   coerceVec (S n') pf (ConsVec x xs) =
      ConsVec x (coerceVec n' (eq_add_S n' n pf) xs).
Proof.
   intros.
   unfold coerceVec.
   destruct (eq_add_S n' n pf).
   rewrite (UIP_dec Nat.eq_dec pf eq_refl).
   auto.
Qed.

(*
 * Vacuous coerceVec can be removed.
 *)
Lemma coerceVec_vacuous: forall a n pf (xs: Vec a n),
   coerceVec n pf xs = xs.
Proof.
   intros.
   rewrite (UIP_dec Nat.eq_dec pf eq_refl).
   simpl; auto.
Qed.

(*
 * Two coerceVecs in a row can be condensed
 *)
Lemma coerceVec_coerceVec: forall a n m l pf1 pf2 (xs: Vec a n),
   coerceVec l pf2 (coerceVec m pf1 xs) = coerceVec l (eq_trans pf2 pf1) xs.
Proof.
   intros.
   destruct pf1.
   destruct pf2.
   simpl; auto.
Qed.

(*
 * Because nat has proof irrelevance without needing the axiom (all
 * proofs of nat equality are already eq_refl), coerceVec calls with
 * different proofs are equal.
 *)
Lemma coerceVec_irr: forall a m n pf1 pf2 (xs: Vec a m),
   coerceVec n pf1 xs = coerceVec n pf2 xs.
Proof.
   intros.
   (* only the second of these needs to be dependent *)
   destruct pf1.
   rewrite (UIP_dec Nat.eq_dec pf2 eq_refl).
   auto.
Qed.

(*
 * coerceVec is symmetric (in a sense)
 * (maybe there's a better name for this)
 *
 * Note that most of the equivalences below are written to be used
 * left-to-right, so the coercion is on the output side. You can use
 * this to shift the coercion if you need to use them backwards.
 *)
Lemma coerceVec_sym: forall a n n' (xs: Vec a n) (ys: Vec a n') pf pf',
   xs = coerceVec n pf ys <-> coerceVec n' pf' xs = ys.
Proof.
   intros.
   destruct pf.
   rewrite (UIP_dec Nat.eq_dec pf' eq_refl).
   simpl.
   tauto.
Qed.

(*
 * Given an xs that's equal to ys but with a coercion, rewrite xs to
 * ys and flush the coercion.
 *)
Lemma coerceVec_rewrite: forall (P: forall {a n}, Vec a n -> Prop)
     a n m (xs: Vec a n) (ys: Vec a m) (pf: n = m),
   xs = coerceVec n pf ys -> P xs <-> P ys.
Proof.
   intros.
   destruct pf.
   simpl in H.
   subst.
   tauto.
Qed.


(*************************************************************)
(* gen *)

(*
 * Internal component of gen; call the initialization function
 * with the right indexes.
 *)
Fixpoint gen_visit {a: Type} (n: nat) (f: nat -> a) (i: nat) : Vec a i :=
   match i with
   | 0 => NilVec a
   | S i' => ConsVec (f (n - S i')) (gen_visit n f i')
   end.

(*
 * Unfold lemma for gen_visit on the left argument (n).
 *)
Lemma gen_visit_S_l: forall a n (f: nat -> a) i,
   i <= n ->
   gen_visit (S n) f i = gen_visit n (fun j => f (S j)) i.
Proof.
   intros * Hlt.
   revert Hlt.
   revert n f.
   induction i; intros; simpl; auto.
   assert (S (n - S i) = n - i) as -> by lia.
   f_equal.
   apply IHi.
   lia.
Qed.

(*
 * Unfold lemma for gen_visit on the right argument (i).
 *)
Lemma gen_visit_S_r: forall a n (f: nat -> a) i,
   gen_visit n f (S i) = ConsVec (f (n - S i)) (gen_visit n f i).
Proof.
   intros; simpl; auto.
Qed.

(*
 * gen_visit produces the same vectors when given equivalent functions.
 *)
Lemma gen_visit_extensionality: forall a n (f g: nat -> a) i,
   (forall j, j < n -> f j = g j) ->
   i <= n ->
   gen_visit n f i = gen_visit n g i.
Proof.
   intros * Heq Hle.
   induction i; simpl; auto.
   rewrite IHi; try lia.
   rewrite Heq; try lia.
   auto.
Qed.

(*
 * Create a vector by calling a function on each index.
 *)
Definition gen {a: Type} (n: nat) (f: nat -> a) : Vec a n :=
   gen_visit n f n.

(*
 * gen of zero length produces nil.
 *)
Lemma gen_0_l: forall a (f: nat -> a), gen 0 f = NilVec a.
Proof.
   intros.
   unfold gen.
   simpl; auto.
Qed.

(*
 * gen on S unfolds to gen with a wrapper function.
 * (alternatively you can unfold, simpl, and work with gen_visit directly)
 *)
Lemma gen_S_l: forall a n (f: nat -> a),
   gen (S n) f = ConsVec (f 0) (gen n (fun j => f (S j))).
Proof.
   intros.
   unfold gen.
   simpl.
   rewrite gen_visit_S_l; try lia.
   f_equal; f_equal; lia.
Qed.

(*
 * gen with matching init functions produces the same vector.
 *)
Lemma gen_extensionality n a: forall (f g: nat -> a),
   (forall i, i < n -> f i = g i) ->
   gen n f = gen n g.
Proof.
   intros * Heq.
   unfold gen.
   apply gen_visit_extensionality; try lia.
   intro.
   apply Heq.
Qed.


(*************************************************************)
(* Inhabited (depends on gen) *)

(* XXX: if we have this here we need to import SAWCoreScaffolding and
   I kind of want that to be the other way around. So it should go
   somewhere else.
 *)
(*
 * Vectors are inhabited if the element type is.
 *)
(*
Instance Inhabited_Vec (a: Type) (n: nat) {Ha: Inhabited a}
       : Inhabited (Vec a n) :=
   MkInhabited (Vec a n) (gen n (fun _ => inhabitant)).
*)


(*************************************************************)
(* head/tail *)

(*
 * Get the first element of a nonempty vector.
 *)
Definition head {a: Type} {n: nat} (v: Vec a (S n)) : a :=
   match v with
   | NilVec _ => False_rect
   | ConsVec x _xs => x
   end.

(*
 * Get the non-first elements of a nonempty vector.
 *)
Definition tail {a: Type} {n: nat} (v: Vec a (S n)) : Vec a n :=
   match v with
   | NilVec _ => False_rect
   | ConsVec _x xs => xs
   end.

(*
 * head or tail on nil isn't possible.
 *)

(*
 * head on cons does the obvious thing
 * (usually all you need for this is simpl; but sometimes that unfolds too much)
 *)
Lemma head_ConsVec: forall a n x (xs: Vec a n), head (ConsVec x xs) = x.
Proof.
   intros; simpl; auto.
Qed.

(*
 * tail on cons does the obvious thing
 * (usually all you need for this is simpl; but sometimes that unfolds too much)
 *)
Lemma tail_ConsVec: forall a n x (xs: Vec a n), tail (ConsVec x xs) = xs.
Proof.
   intros; simpl; auto.
Qed.

(*
 * consing head and tail returns the original vector
 *)
Lemma head_tail_ConsVec: forall a n x (xs: Vec a n),
   ConsVec (head (ConsVec x xs)) (tail (ConsVec x xs)) = ConsVec x xs.
Proof.
   intros. simpl. auto.
Qed.

(*
 * Coercions in head are immaterial.
 *)
Lemma head_coerceVec: forall a n n' (xs: Vec a (S n)) pf,
   head (coerceVec (S n') pf xs) = head xs.
Proof.
   intros.
   injection pf; intros; subst.
   rewrite (UIP_dec Nat.eq_dec pf eq_refl).
   simpl; auto.
Qed.

(*
 * Pull a coercion out of tail.
 *)
Lemma tail_coerceVec: forall a n n' (xs: Vec a (S n)) pf pf',
   tail (coerceVec (S n') pf xs) = coerceVec n' pf' (tail xs).
Proof.
   intros.
   subst.
   rewrite (UIP_dec Nat.eq_dec pf eq_refl).
   simpl; auto.
Qed.

(*
 * head on (nonempty) gen returns the first element.
 *)
Lemma head_gen: forall a n (f: nat -> a), head (gen (S n) f) = f 0.
Proof.
   intros.
   simpl.
   f_equal.
   lia.
Qed.

(*
 * tail on (nonempty) gen returns a smaller gen.
 *
 * Because we pop index 0, we have to add one to the indexes in the smaller gen.
 *)
Lemma tail_gen: forall a n (f: nat -> a),
   tail (gen (S n) f) = gen n (fun i => f (S i)).
Proof.
   intros.
   unfold gen.
   simpl.
   induction n; simpl; auto.
   rewrite gen_visit_S_l; try lia.
   f_equal.
   f_equal.
   destruct n; lia.
Qed.


(*************************************************************)
(* append *)

(*
 * Append two vectors.
 *)
Fixpoint append {a: Type} {n m: nat}
     (xs: Vec a n) (ys: Vec a m) : Vec a (n + m) :=
   match xs with
   | NilVec _ => ys
   | ConsVec x xs' => ConsVec x (append xs' ys)
   end.

(*
 * Appending nil on the left is a nop.
 *)
Lemma append_NilVec_l: forall a m (ys: Vec a m), append (NilVec a) ys = ys.
Proof.
   intros; simpl; auto.
Qed.

(*
 * Appending nil on the right is a nop.
 *)
Lemma append_NilVec_r: forall a n (xs: Vec a n),
   append xs (NilVec a) = coerceVec (n + 0) (Nat.add_0_r n) xs.
Proof.
   intros.
   induction xs; simpl; auto.
   - rewrite NilVec_unique. auto.
   - rewrite IHxs.
     rewrite ConsVec_coerceVec.
     apply coerceVec_irr.
Qed.

(*
 * cons can be shifted into an append
 *)
Lemma ConsVec_append: forall a n m x (xs: Vec a n) (ys: Vec a m),
   ConsVec x (append xs ys) = append (ConsVec x xs) ys.
Proof.
   intros; simpl; auto.
Qed.

(*
 * cons can also be shifted out of an append
 *)
Lemma append_ConsVec: forall a n m x (xs: Vec a n) (ys: Vec a m),
   append (ConsVec x xs) ys = ConsVec x (append xs ys).
Proof.
   intros.
   rewrite <- ConsVec_append.
   auto.
Qed.

(*
 * Using append to prepend just a cons is the same as just consing.
 *)
Lemma append_ConsVec_only: forall a m x (ys: Vec a m),
   append (ConsVec x (NilVec a)) ys = ConsVec x ys.
Proof.
   intros; simpl; auto.
Qed.

(*
 * We can shift a coercion out of the LHS of an append.
 *)
Lemma append_coerceVec_l: forall a n n' m (xs: Vec a n) (ys: Vec a m) pf pf',
   append (coerceVec n' pf xs) ys = coerceVec (n' + m) pf' (append xs ys).
Proof.
   intros.
   destruct pf.
   rewrite (UIP_dec Nat.eq_dec pf' eq_refl).
   simpl; auto.
Qed.

(*
 * We can shift a coercion out of the RHS of an append.
 *)
Lemma append_coerceVec_r: forall a n m m' (xs: Vec a n) (ys: Vec a m) pf pf',
   append xs (coerceVec m' pf ys) = coerceVec (n + m') pf' (append xs ys).
Proof.
   intros.
   destruct pf.
   rewrite (UIP_dec Nat.eq_dec pf' eq_refl).
   simpl; auto.
Qed.

(*
 * Calling gen on a sum is equivalent to appending two gens.
 *)
Lemma gen_add: forall a n m (f: nat -> a),
   gen (n + m) f = append (gen n f) (gen m (fun i => f (n + i))).
Proof.
   intros.
   unfold gen.
   revert m f.
   induction n; intros; simpl.
   - f_equal.
   - assert (n + m - (n + m) = 0) as -> by lia.
     assert (n - n = 0) as -> by lia.
     f_equal.
     rewrite gen_visit_S_l; try lia.
     rewrite gen_visit_S_l; try lia.
     rewrite IHn.
     auto.
Qed.

(*
 * head on a nondegenerate append reduces.
 *
 * (for head on a degenerate append, use append_nil_l to make the
 * append go away)
 *)
Lemma head_append_ConsVec: forall a n m x (xs: Vec a n) (ys: Vec a m),
   head (append (ConsVec x xs) ys) = x.
Proof.
   intros.
   rewrite append_ConsVec.
   rewrite head_ConsVec.
   auto.
Qed.

(*
 * tail on a nondegenerate append reduces.
 *
 * (for tail on a degenerate append, use append_nil_l to make the
 * append go away)
 *)
Lemma tail_append_ConsVec: forall a n m x (xs: Vec a n) (ys: Vec a m),
   tail (append (ConsVec x xs) ys) = append xs ys.
Proof.
   intros.
   rewrite append_ConsVec.
   rewrite tail_ConsVec.
   auto.
Qed.

(*
 * append is associative.
 *
 * While the Rocq name for this is append_assoc, there's always
 * confusion about which way that lemma should go. So we'll stick to
 * our naming conventions and provide both directions.
 *)
Lemma append_append_l: forall a n m l
     (xs: Vec a n) (ys: Vec a m) (zs: Vec a l) pf,
   append (append xs ys) zs =
      coerceVec (n + m + l) pf (append xs (append ys zs)).
Proof.
   intros.
   revert pf.
   revert zs ys.
   revert m l.
   induction xs; intros; simpl.
   - rewrite coerceVec_vacuous. auto.
   - assert (n + m + l = n + (m + l)) as HN1 by lia.
     rewrite IHxs with (pf := HN1).
     rewrite ConsVec_coerceVec.
     apply coerceVec_irr.
Qed.

(*
 * append is associative (other direction)
 *)
Lemma append_append_r: forall a n m l
     (xs: Vec a n) (ys: Vec a m) (zs: Vec a l) pf,
   append xs (append ys zs) =
      coerceVec (n + (m + l)) pf (append (append xs ys) zs).
Proof.
   intros.
   assert (n + m + l = n + (m + l)) as HN1 by lia.
   rewrite append_append_l with (pf := HN1).
   rewrite coerceVec_coerceVec.
   rewrite coerceVec_vacuous.
   auto.
Qed.

(*
 * append is injective (simple case where the lengths match)
 *)
Lemma append_inj: forall a n m (xs ys: Vec a n) (xs' ys': Vec a m),
   append xs xs' = append ys ys' -> xs = ys /\ xs' = ys'.
Proof.
   intros * Heq.
   revert Heq.
   revert xs' ys' ys.
   revert m.
   induction xs; intros.
   - destruct ys using caseVec_0.
     do 2 rewrite append_NilVec_l in Heq.
     split; auto.
   - destruct ys using caseVec_S.
     simpl in Heq.
     injection Heq; intros; subst.
     apply inj_pair2 in H.
     apply IHxs in H. destruct H.
     split; auto.
     congruence.
Qed.

(*
 * A nonempty vector can have the last element split off the
 * end. (This requires append to state.)
 *)
Lemma unsnoc: forall a n (xs: Vec a (S n)) (pf: S n = n + 1),
   exists xs' y,
   xs = coerceVec (S n) pf (append xs' (ConsVec y (NilVec a))).
Proof.
   intros.
   remember (S n) as m.
   revert Heqm.
   revert pf.
   revert n.
   induction xs; intros; try discriminate.
   destruct n.
   - destruct xs using caseVec_0.
     assert (n0 = 0) as -> by lia.
     exists (NilVec a), x.
     simpl. rewrite coerceVec_vacuous.
     auto.
   - specialize (IHxs n).
     assert (S n = n + 1) as HN1 by lia.
     specialize (IHxs HN1 eq_refl).
     destruct IHxs as [xs' [y IHxs]].
     assert (n0 = S n) as -> by lia.
     exists (ConsVec x xs'), y.
     rewrite IHxs.
     rewrite ConsVec_coerceVec.
     apply coerceVec_irr.
Qed.

(*
 * Simplify gen at both ends. This requires append to state.
 *)
Lemma gen_bothends: forall a n (f: nat -> a),
   gen (S (n + 1)) f =
      append (ConsVec (f 0) (gen n (fun j => f (S j))))
             (ConsVec (f (S n)) (NilVec a)).
Proof.
   intros.
   unfold gen.
   simpl.
   assert (n + 1 - (n + 1) = 0) as -> by lia.
   f_equal.
   revert f.
   induction n; intros; simpl; auto.
   assert (n - n = 0) as -> by lia.
   rewrite gen_visit_S_l; try lia.
   rewrite IHn.
   rewrite gen_visit_S_l; try lia.
   f_equal.
   f_equal.
   assert (n + 1 = S n) as -> by lia.
   lia.
Qed.

(*
 * Induction on nat by twos. There's a Nat.pair_induction in the
 * stdlib, but it doesn't work and I can't figure out why; this has
 * almost the same form (slightly simpler) and _does_ work...
 *
 * This is a building block for Vec_ind_bothends.
 *)
Fixpoint my_nat_pair_ind (P: nat -> Prop)
            (H0: P 0)
            (H1: P 1)
            (Hn: forall n: nat, P n -> P (S n) -> P (S (S n)))
            (n: nat) { struct n } : P n :=
   match n as n0 return (n0 = n -> P n0) with
   | 0 =>
        fun (_: 0 = n) => H0
   | S m =>
        (*
         * Recurse on m now. We need to use m here for termination,
         * and use the next match to launder its type.
         *)
        let HSS := my_nat_pair_ind P H0 H1 Hn m in
        match m as m0 return (P m0 -> S m0 = n -> P (S m0)) with
        | 0 => fun _ (_: 1 = n) => H1
        | S l =>
            fun (HSS': P (S l)) (_: S (S l) = n) =>
               let HS := my_nat_pair_ind P H0 H1 Hn l in
               Hn l HS HSS'
        end HSS
 end eq_refl.

(*
 * Induction principle for visiting a vector from both ends at once.
 *
 * This is used for dealing with revAppend on gen, which is shockingly
 * messy.
 *)
Lemma Vec_ind_bothends
   (P: forall {a n}, Vec a n -> Prop)
   (H0: forall {a} (xs: Vec a 0), P xs)
   (H1: forall {a} (xs: Vec a 1), P xs)
   (Hn: forall {a} (n: nat) x (xs: Vec a n) y, P xs ->
       (*
        * If we don't give the size explicitly, it silently reduces to
        * (S n + 1), and then nothing works.
        *)
       @P a (S (n + 1)) (append (ConsVec x xs) (ConsVec y (NilVec a)))
   )
   {a: Type} : forall {n: nat} (xs: Vec a n), P xs.
Proof.
   intros.
   induction n using my_nat_pair_ind; try apply H0; try apply H1.
   destruct xs using caseVec_S.
   assert (S n = n + 1) as HN1 by lia.
   pose proof (unsnoc a n xs HN1) as Hex.
   destruct Hex as [xs' [y Hex]].
   rewrite Hex.
   rewrite ConsVec_coerceVec.
   assert (S (S n) = S (n + 1)) as HN2 by lia.
   rewrite coerceVec_rewrite with
        (P := P) (n := S (S n)) (m := S (n + 1)) (pf := HN2)
        (ys := (append (ConsVec x xs') (ConsVec y (NilVec a)))).
   - apply Hn. apply IHn.
   - apply coerceVec_irr.
Qed.


(*************************************************************)
(* reverse *)

(*
 * revAppend is mostly useful only as a building block for reverse.
 *
 * It's exposed here because in Rocq hiding subfunctions inside their
 * parents makes them difficult to reason about.
 *)
Fixpoint revAppend {a: Type} {n m: nat}
     (xs: Vec a n) (ys: Vec a m) : Vec a (n + m).
   (* FUTURE: avoid using proof mode *)
(* 
   match xs as xs' return (xs = xs' -> Vec (n + m)) with
   | NilVec _ => coerceVec (n + m) _ ys
   | ConsVec x xs' => coerceVec (n + m) _ (revAppend xs' (ConsVec x ys))
   end.
*)
Proof.
   destruct xs.
   - exact (coerceVec (0 + m) eq_refl ys).
   - refine (
        coerceVec (S n + m) (Nat.add_succ_comm n m)
                            (revAppend a n (S m) xs (ConsVec x ys))
     ).
Defined.

(*
 * unfolding lemma for revAppend on nil
 *)
Lemma revAppend_NilVec: forall a m (ys: Vec a m),
   revAppend (NilVec a) ys = ys.
Proof.
   intros; simpl; auto.
Qed.

(*
 * unfolding lemma for revAppend on cons
 *)
Lemma revAppend_ConsVec: forall a n m x (xs: Vec a n) (ys: Vec a m),
   revAppend (ConsVec x xs) ys =
      coerceVec (S n + m) (Nat.add_succ_comm n m) (revAppend xs (ConsVec x ys)).
Proof.
   intros; simpl; auto.
Qed.

(*
 * We can pull a coercion out of revAppend on the left.
 *)
Lemma revAppend_coerceVec_l: forall a n n' m (xs: Vec a n) (ys: Vec a m) pf pf',
   revAppend (coerceVec n' pf xs) ys = coerceVec (n' + m) pf' (revAppend xs ys).
Proof.
   intros.
   destruct pf.
   simpl.
   rewrite (UIP_dec Nat.eq_dec pf' eq_refl).
   simpl.
   auto.
Qed.

(*
 * We can also pull a coercion out of revAppend on the right.
 *)
Lemma revAppend_coerceVec_r: forall a n m m' (xs: Vec a n) (ys: Vec a m) pf pf',
   revAppend xs (coerceVec m' pf ys) = coerceVec (n + m') pf' (revAppend xs ys).
Proof.
   intros.
   destruct pf.
   simpl.
   rewrite (UIP_dec Nat.eq_dec pf' eq_refl).
   simpl.
   auto.
Qed.

(*
 * revAppend on itself is not too meaningful, but this is the
 * generalized form of reverse (reverse xs) and is needed to prove
 * that.
 *)
Lemma revAppend_revAppend: forall a n m l pf
     (xs: Vec a n) (ys: Vec a m) (zs: Vec a l),
   revAppend (revAppend xs ys) zs =
        coerceVec (n + m + l) pf (revAppend ys (append xs zs)).
Proof.
   intros.
   revert ys zs.
   revert pf.
   revert m l.
   induction xs; intros; simpl.
   - rewrite coerceVec_vacuous. auto.
   - assert (S (n + m) + l = n + S m + l) as H by lia.
     rewrite (revAppend_coerceVec_l) with (pf' := H).
     assert (n + S m + l = S m + (n + l)) as H' by lia.
     rewrite IHxs with (pf := H').
     simpl.
     do 2 rewrite coerceVec_coerceVec.
     apply coerceVec_irr.
Qed.

(*
 * revAppend on append (left hand side, used for reverse on append)
 *)
Lemma revAppend_append_l: forall a n m l
     (xs: Vec a n) (ys: Vec a m) (zs: Vec a l) pf,
   revAppend (append xs ys) zs =
      coerceVec (n + m + l) pf (revAppend ys (revAppend xs zs)).
Proof.
   intros.
   revert pf.
   revert ys zs.
   revert m l.
   induction xs; intros; simpl.
   - rewrite coerceVec_vacuous. auto.
   - assert (n + m + S l = m + (n + S l)) as H1 by lia.
     assert (m + S (n + l) = m + (n + S l)) as H2 by lia.
     rewrite IHxs with (pf := H1).
     rewrite coerceVec_coerceVec.
     rewrite revAppend_coerceVec_r with (pf' := H2).
     rewrite coerceVec_coerceVec.
     apply coerceVec_irr.
Qed.

(*
 * revAppend on append (right hand side)
 *)
Lemma revAppend_append_r: forall a n m l
     (xs: Vec a n) (ys: Vec a m) (zs: Vec a l) pf,
   revAppend xs (append ys zs) =
      coerceVec (n + (m + l)) pf (append (revAppend xs ys) zs).
Proof.
   intros.
   revert pf.
   revert ys zs.
   revert m l.
   induction xs; intros; simpl.
   - rewrite coerceVec_vacuous. auto.
   - (*
      * This is necessary, instead of just rewriting directly with
      * ConsVec_append, to update the implicit argument of revAppend
      * that takes the size of the right argument. Otherwise, the size
      * changes from S (m + l) to (S m + l) in the argument but not in
      * the implicit argument. These are convertible enough for the
      * rewrite to succeed, but not enough to then rewrite with IHxs
      * (which needs to match its m with our (S m)). Even an explicit
      * m := S m doesn't make it go, and because it's in a type you
      * can't change it directly.
      *
      * Feh. And never forget to check implicit arguments when things
      * don't make sense.
      *)
     assert (revAppend xs (ConsVec x (append ys zs)) =
             revAppend xs (append (ConsVec x ys) zs)) as ->.
     { rewrite ConsVec_append. f_equal. }
     assert (n + (S m + l) = n + S m + l) as NH1 by lia.
     assert (S (n + m) + l = n + S m + l) as NH2 by lia.
     rewrite IHxs with (pf := NH1).
     erewrite append_coerceVec_l with (pf' := NH2).
     do 2 rewrite coerceVec_coerceVec.
     apply coerceVec_irr.
Qed.

(*
 * append on revAppend, left hand side (inverse of previous)
 *)
Lemma append_revAppend_l: forall a n m l
     (xs: Vec a n) (ys: Vec a m) (zs: Vec a l) pf,
   append (revAppend xs ys) zs =
      coerceVec (n + m + l) pf (revAppend xs (append ys zs)).
Proof.
   intros.
   revert pf.
   revert ys zs.
   revert m l.
   induction xs; intros; simpl.
   - rewrite coerceVec_vacuous. auto.
   - rewrite coerceVec_coerceVec.
     assert (S (n + m) + l = n + S m + l) as NH1 by lia.
     assert (n + S m + l = n + (S m + l)) as NH2 by lia.
     rewrite append_coerceVec_l with (pf' := NH1).
     rewrite IHxs with (pf := NH2).
     rewrite coerceVec_coerceVec.
     rewrite ConsVec_append.
     apply coerceVec_irr.
Qed.

(*
 * revAppend on gen, which is necessary for reverse on gen.
 *)
Lemma revAppend_gen: forall a n m (f: nat -> a) (ys: Vec a m),
   revAppend (gen n f) ys = append (gen n (fun i => f (n - i - 1))) ys.
Proof.
   intros.
   remember (gen n f) as xs.
   revert Heqxs.
   revert ys.
   revert f m.
   induction xs using Vec_ind_bothends; intros; rewrite Heqxs.
   - do 2 rewrite gen_0_l. simpl; auto.
   - simpl. rewrite coerceVec_vacuous. auto.
   - assert (gen (S (n + 1)) (fun i => f (S (n + 1) - i - 1)) =
             gen (S (n + 1)) (fun i => f (S n - i))) as ->.
     { apply gen_extensionality. intros. f_equal. lia. }
     do 2 rewrite gen_bothends.
     assert (S n - 0 = S n) as -> by lia.
     assert (S n - S n = 0) as -> by lia.
     rewrite gen_bothends in Heqxs.
     do 2 rewrite append_ConsVec in Heqxs.
     injection Heqxs; intros; subst.
     apply inj_pair2 in H.
     clear Heqxs.
     apply append_inj in H; destruct H as [H H0].
     injection H0; intros. clear H0.
     rewrite <- H1.
     rewrite <- H.
     assert (gen n (fun j => f (S n - S j)) =
             gen n (fun j => f (n - j))) as ->.
     { apply gen_extensionality. intros. f_equal. }
     rewrite append_ConsVec.
     simpl.
     assert (n + 1 + m = n + (1 + m)) as HN1 by lia.
     assert (n + 1 + S m = 1 + (n + S m)) as HN2 by lia.
     rewrite append_append_l with (pf := HN1).
     rewrite ConsVec_coerceVec.
     rewrite revAppend_append_l with (pf := HN2).
     rewrite coerceVec_coerceVec.
     rewrite (IHxs _ _ _ H).
     simpl.
     rewrite coerceVec_coerceVec.
     assert (gen n (fun i => f (S (n - i - 1))) =
             gen n (fun i => f (n - i))) as ->.
     { apply gen_extensionality. intros. f_equal. lia. }
     apply coerceVec_irr.
Qed.

(*
 * Reverse is not a super useful operation on vectors per se, but we
 * also use these vectors for things used like lists; and also, even
 * for vectors sometimes it's a useful building block.
 *)
Definition reverse {a: Type} {n: nat} (xs: Vec a n) : Vec a n :=
   coerceVec n (plus_n_O n) (revAppend xs (NilVec a)).

Lemma reverse_NilVec: forall a, reverse (NilVec a) = NilVec a.
Proof.
   intros.
   unfold reverse.
   simpl.
   rewrite NilVec_unique.
   auto.
Qed.

(*
 * Pull a coercion out of a reverse.
 *)
Lemma reverse_coerceVec: forall a n n' (xs: Vec a n) pf,
   reverse (coerceVec n' pf xs) = coerceVec n' pf (reverse xs).
Proof.
   intros.
   unfold reverse.
   assert (n' + 0 = n + 0) as NH1 by lia.
   rewrite revAppend_coerceVec_l with (pf' := NH1).
   do 2 rewrite coerceVec_coerceVec.
   apply coerceVec_irr.
Qed.

(*
 * reverse is its own inverse
 *)
Lemma reverse_reverse: forall a n (xs: Vec a n), reverse (reverse xs) = xs.
Proof.
   intros.
   unfold reverse.
   assert (n + 0 = n + 0 + 0) as NH1 by lia.
   assert (n + 0 + 0 = 0 + (n + 0)) as NH2 by lia.
   rewrite revAppend_coerceVec_l with (pf' := NH1).
   rewrite revAppend_revAppend with (pf := NH2).
   simpl.
   rewrite append_NilVec_r.
   do 3 rewrite coerceVec_coerceVec.
   rewrite coerceVec_vacuous.
   auto.
Qed.

(*
 * reversing a gen gives you a different gen
 *)
Lemma reverse_gen: forall a n (f: nat -> a),
   reverse (gen n f) = gen n (fun i => f (n - i - 1)).
Proof.
   intros.
   unfold reverse.
   rewrite revAppend_gen.
   rewrite append_NilVec_r.
   rewrite coerceVec_coerceVec.
   rewrite coerceVec_vacuous.
   auto.
Qed.

(*
 * reverse of append is append of reverses
 *)
Lemma reverse_append: forall a n m (xs: Vec a n) (ys: Vec a m) pf,
   reverse (append xs ys) =
      coerceVec (n + m) pf (append (reverse ys) (reverse xs)).
Proof.
   intros.
   unfold reverse.
   assert (n + m + 0 = m + (n + 0)) as NH1 by lia.
   assert (m + n = m + 0 + n) as NH2 by lia.
   assert (m + 0 + n = m + 0 + (n + 0)) as NH3 by lia.
   assert (m + 0 + (n + 0) = m + (0 + (n + 0))) as NH4 by lia.
   rewrite revAppend_append_l with (pf := NH1).
   rewrite coerceVec_coerceVec.
   rewrite append_coerceVec_l with (pf' := NH2).
   rewrite append_coerceVec_r with (pf' := NH3).
   do 2 rewrite coerceVec_coerceVec.
   rewrite append_revAppend_l with (pf := NH4).
   rewrite coerceVec_coerceVec.
   rewrite append_NilVec_l.
   apply coerceVec_irr.
Qed.

(*
 * reverse of ConsVec appends it to the reverse
 *)
Lemma reverse_ConsVec: forall a n x (xs: Vec a n),
   reverse (ConsVec x xs) =
      coerceVec (S n) (Nat.add_comm 1 n)
                (append (reverse xs) (ConsVec x (NilVec a))).
Proof.
   intros.

   (*
    * This doesn't work because it doesn't change the implicit length
    * argument in the reverse, and then we can't apply
    * reverse_append. Need to include the context instead.
    *)
(*
   assert (ConsVec x xs = append (ConsVec x (NilVec a)) xs) as ->
        by (simpl; auto).
*)
   assert (reverse (ConsVec x xs) =
           reverse (append (ConsVec x (NilVec a)) xs)) as ->
       by (f_equal; simpl; auto).

   rewrite reverse_append with (pf := Nat.add_comm 1 n).
   enough (reverse (ConsVec x (NilVec a)) = ConsVec x (NilVec a)) as H.
   { rewrite H. apply coerceVec_irr. }
   unfold reverse. simpl.
   rewrite coerceVec_coerceVec.
   rewrite coerceVec_vacuous.
   auto.
Qed.


(*************************************************************)
(* at 1: atOption *)

(*
 * Currently SAWCore's native form of at is atWithDefault, which takes
 * a default value to return when out of bounds. This has the drawback
 * that the default value might also be in your vector, so you can't
 * know for sure if the index was out of bounds. This is ok for simple
 * uses, but not good if you want to reason about failure cases.
 *
 * That should get fixed eventually. See #3353.
 *
 * The base form here will be atOption, which returns an option
 * instead.
 *
 * Note that SAWCore also has a plain "at", which crashes when out of
 * bounds. We don't support that here because Rocq doesn't allow partial
 * functions.
 *)

(*
 * Get the element at index i. If there is no such index, return None.
 *)
Fixpoint atOption {a: Type} {n: nat} (v: Vec a n) (index: nat) : option a :=
   match v with
   | NilVec _ => None
   | ConsVec x xs' =>
        match index with
        | 0 => Some x
        | S index' => atOption  xs' index'
        end
   end.

(*
 * unfold lemma for atOption on nil
 *)
Lemma atOption_NilVec: forall a i, atOption (NilVec a) i = None.
Proof.
   intros; simpl; auto.
Qed.

(*
 * unfold lemma for atOption on cons, with 0 index
 *)
Lemma atOption_ConsVec_0: forall a n x (xs: Vec a n),
   atOption (ConsVec x xs) 0 = Some x.
Proof.
   intros; simpl; auto.
Qed.

(*
 * unfold lemma for atOption on cons, with nonzero index
 *)
Lemma atOption_ConsVec_S: forall a n x (xs: Vec a n) i,
   atOption (ConsVec x xs) (S i) = atOption xs i.
Proof.
   intros; simpl; auto.
Qed.

(*
 * atOption returns None if the index is out of bounds.
 *)
Lemma atOption_None: forall a n (v: Vec a n) i,
   n <= i <-> atOption v i = None.
Proof.
   intros.
   revert i.
   induction v; intros; simpl.
   - split; auto; lia.
   - destruct i.
     + split; try discriminate; lia.
     + rewrite <- IHv. lia.
Qed.

(*
 * atOption returns non-None if and only if the index is in bounds.
 *)
Lemma atOption_notNone: forall a n (v: Vec a n) i,
   i < n <-> atOption v i <> None.
Proof.
   intros.
   revert i.
   induction v; intros; simpl.
   - split; intro; try contradiction; lia.
   - destruct i.
     + split; intro; try discriminate; lia.
     + split; intro.
       * apply IHv; lia.
       * rewrite <- IHv in H. lia.
Qed.

(*
 * Separate forward and reverse cases of the previous.
 *)
Lemma atOption_notNone_fwd: forall a n (v: Vec a n) i,
   i < n -> atOption v i <> None.
Proof.
   intros * Hlt.
   rewrite atOption_notNone with (v := v) in Hlt; auto.
Qed.
Lemma atOption_notNone_rev: forall a n (v: Vec a n) i,
   atOption v i <> None -> i < n.
Proof.
   intros * Hsome.
   rewrite atOption_notNone with (v := v); auto.
Qed.

(*
 * Explicit Some forms of the previous. These cannot be
 * written with <-> because the quantifier flips.
 *)
Lemma atOption_Some_fwd: forall a n (v: Vec a n) i,
   i < n -> exists x, atOption v i = Some x.
Proof.
   intros * Hlt.
   apply atOption_notNone_fwd with (v := v) in Hlt.
   destruct (atOption v i) eqn:Heq; try contradiction.
   exists a0. auto.
Qed.
Lemma atOption_Some_rev: forall a n (v: Vec a n) i x,
   atOption v i = Some x -> i < n.
Proof.
   intros * Hsome.
   apply atOption_notNone_rev with (v := v).
   destruct (atOption v i); auto; discriminate.
Qed.

(*
 * coercions in at are immaterial
 *)
Lemma atOption_coerceVec: forall a n n' (xs: Vec a n) i pf,
   atOption (coerceVec n' pf xs) i = atOption xs i.
Proof.
   intros.
   revert pf.
   revert n'.
   revert i.
   destruct xs; intros; simpl.
   - subst. rewrite NilVec_unique. simpl. auto.
   - subst. simpl. auto.
Qed.

(*
 * at on gen is a direct call to the gen function (if in bounds)
 *)
Lemma atOption_gen: forall a n k (f: nat -> a),
   k < n -> atOption (gen n f) k = Some (f k).
Proof.
   intros.
   unfold gen.
   revert H.
   revert f k.
   induction n; intros; try lia; simpl.
   assert (n - n = 0) as -> by lia.
   rewrite gen_visit_S_l; try lia.
   destruct k; auto.
   rewrite IHn; try lia; auto.
Qed.

(*
 * at on tail
 *)
Lemma atOption_tail: forall a n (xs: Vec a (S n)) i,
   atOption (tail xs) i = atOption xs (S i).
Proof.
   intros.
   unfold tail.
   destruct xs using caseVec_S.
   simpl. auto.
Qed.

(*
 * at on reverse
 *)
Lemma atOption_reverse: forall a n (xs: Vec a n) i,
   i < n -> atOption xs i = atOption (reverse xs) (n - i - 1).
Proof.
Admitted.

(*
 * at distributes over append. Left argument case.
 *)
Lemma atOption_append_l: forall a n m (v: Vec a n) (w: Vec a m) i,
   i < n ->
   atOption (append v w) i = atOption v i.
Proof.
   intros * Hlt.
   revert Hlt.
   revert w.
   revert m i.
   induction v; intros; simpl; try lia.
   destruct i; auto.
   apply IHv.
   lia.
Qed.

(*
 * at distributes over append. Right argument case.
 *)
Lemma atOption_append_r: forall a n m (v: Vec a n) (w: Vec a m) i,
   n <= i ->
   atOption (append v w) i = atOption w (i - n).
Proof.
   intros * Hge.
   revert Hge.
   revert w.
   revert m i.
   induction v; intros; simpl.
   - f_equal. lia.
   - destruct i; try lia.
     rewrite IHv; try lia.
     auto.
Qed.

(*
 * Vectors that are the same at all points are equal.
 *)
Lemma atOption_extensionality: forall a n (xs ys: Vec a n),
   (forall i, atOption xs i = atOption ys i) <-> xs = ys.
Proof.
   intros.
   split; intro H.
   - revert H.
     revert ys.
     induction xs; intros.
     + destruct ys using caseVec_0. auto.
     + destruct ys using caseVec_S.
       assert (x0 = x) as ->.
       { specialize (H 0). simpl in H. injection H; intros; subst. auto. }
       f_equal.
       apply IHxs.
       intro i.
       specialize (H (S i)).
       simpl in H; auto.
   - intro i. subst; auto.
Qed.


(*************************************************************)
(* at 2: atWithDefault *)

(*
 * atWithDefault is the current SAWCore way of doing things. This
 * should get migrated to atOption. See #3353.
 *
 * (There's also a plain at, but it's partial and crashes on out of
 * bounds and we can't handle it in Rocq.)
 *)

(*
 * Get the element at index i. If there is no such index, return the
 * passeed-in default value.
 *)
Definition atWithDefault {a: Type} {n: nat}
     (default: a) (v: Vec a n) (i: nat) : a :=
   match atOption v i with
   | None => default
   | Some x => x
   end.

(*
 * atWithDefault returns the default if the index is out of bounds.
 * Note: the reverse is not true because the default value could be
 * in the vector.
 *)
Lemma atWithDefault_outofbounds: forall a n default (v: Vec a n) i,
   n <= i -> atWithDefault default v i = default.
Proof.
   intros * Hgt.
   unfold atWithDefault.
   rewrite atOption_None with (v := v) in Hgt.
   rewrite Hgt; auto.
Qed.

(*
 * We can't say anything useful about what atWithDefault does if the
 * index is in bounds, because it might return the default value
 * anyway.
 *)

(*
 * atOption failing implies atWithDefault produces the default.
 *
 * Note that the reverse isn't true because the default value might be
 * in the vector.
 *)
Lemma atOption_None_atWithDefault: forall a n default (v: Vec a n) i,
   atOption v i = None -> atWithDefault default v i = default.
Proof.
   intros * H.
   unfold atWithDefault.
   rewrite H; auto.
Qed.

(*
 * atOption succeeding implies atWithDefault produces the same value.
 *)
Lemma atOption_Some_atWithDefault: forall a n default (v: Vec a n) i x,
   atOption v i = Some x -> atWithDefault default v i = x.
Proof.
   intros * H.
   unfold atWithDefault.
   rewrite H; auto.
Qed.

(*
 * atWithDefault producing a non-default value implies atOption succeeds.
 *)
Lemma atWithDefault_atOption: forall a n default (v: Vec a n) i x,
   x <> default -> atWithDefault default v i = x -> atOption v i = Some x.
Proof.
   intros * Hne Heq.
   unfold atWithDefault in Heq.
   destruct (atOption v i); subst; auto.
   contradiction.
Qed.

(*
 * at distributes over append. Left argument case.
 *)
Lemma atWithDefault_append_l: forall a n m default (v: Vec a n) (w: Vec a m) i,
   i < n ->
   atWithDefault default (append v w) i = atWithDefault default v i.
Proof.
   intros * Hlt.
   unfold atWithDefault.
   rewrite atOption_append_l; auto.
Qed.

(*
 * at distributes over append. Right argument case.
 *)
Lemma atWithDefault_append_r: forall a n m default (v: Vec a n) (w: Vec a m) i,
   n <= i ->
   atWithDefault default (append v w) i = atWithDefault default w (i - n).
Proof.
   intros * Hge.
   unfold atWithDefault.
   rewrite atOption_append_r; auto.
Qed.

(*
 * Vectors that are the same at all points are equal.
 *)
Lemma atWithDefault_extensionality: forall a n def (xs ys: Vec a n),
   (forall i, atWithDefault def xs i = atWithDefault def ys i) <-> xs = ys.
Proof.
   intros.
   unfold atWithDefault.
   split; intro H.
   - apply atOption_extensionality.
     intro i.
     specialize (H i).
     destruct (lt_dec i n).
     + assert (atOption xs i <> None) by (apply atOption_notNone; auto).
       assert (atOption ys i <> None) by (apply atOption_notNone; auto).
       destruct (atOption xs i); try contradiction.
       destruct (atOption ys i); try contradiction.
       subst; auto.
     + assert (atOption xs i = None) as -> by (apply atOption_None; lia).
       assert (atOption ys i = None) as -> by (apply atOption_None; lia).
       auto.
   - subst. intro i. destruct (atOption ys i); auto.
Qed.


(*************************************************************)
(* at 3: atWithProof *)

(*
 * In SAWCore, there's also an atWithProof that takes a proof that the
 * index is in bounds. It just returns a value, and so it's
 * superficially preferable.
 *
 * However, it's rather a nuisance to deal with in Rocq because of the
 * dependent typing, so some of the bits below are a bit ugly, and
 * downstream users will likely find that working with it is a
 * headache too. Recommendation: unwrap to atOption as soon as
 * possible (using atWithProof_atOption) and reason about that
 * instead.
 *)

(*
 * Get the element at index i. Accept a proof that the index is in
 * bounds, and thereby eliminate the failure case.
 *)
Definition atWithProof {a: Type} {n: nat}
     (v: Vec a n) (i: nat) (pf: i < n) : a :=
   match atOption v i as opt return (atOption v i = opt -> a) with
   | None => fun H => False_rect a (atOption_notNone_fwd a n v i pf H)
   | Some x => fun _ => x
   end eq_refl.

(*
 * Support lemma containing a generalized version of atWithProof's
 * body. This version supports reducing the dependent match.
 *)
Lemma atWithProof_support: forall a n (v: Vec a n) i pf
        optx (Heqoptx: atOption v i = optx) x,
   (
      match optx as optx' return (atOption v i = optx' -> a) with
      | None => fun H => False_rect a (atOption_notNone_fwd a n v i pf H)
      | Some x => fun _ => x
      end Heqoptx = x
   ) <-> atOption v i = Some x.
Proof.
  intros.
  dependent destruction optx. 
  - split; intro.
    + subst; auto.
    + congruence.
  - pose proof Heqoptx as H.
    rewrite <- atOption_None in H.
    lia.
Qed.

(*
 * atWithProof is equivalent to atOption returning Some.
 *)
Lemma atWithProof_atOption: forall a n (v: Vec a n) (i: nat) (x: a) (pf: i < n),
    atWithProof v i pf = x <-> atOption v i = Some x.
Proof.
   intros.
   unfold atWithProof.
   rewrite atWithProof_support.
   tauto.
Qed.

(*
 * at distributes over append. Left argument case.
 *)
Lemma atWithProof_append_l: forall a n m (v: Vec a n) (w: Vec a m) i pf1 pf2,
   i < n ->
   atWithProof (append v w) i pf1 = atWithProof v i pf2.
Proof.
   intros * Hlt.
   rewrite atWithProof_atOption.
   remember (atWithProof v i pf2) as x. symmetry in Heqx.
   rewrite atWithProof_atOption in Heqx.
   rewrite atOption_append_l; auto.
Qed.

(*
 * at distributes over append. Right argument case.
 *)
Lemma atWithProof_append_r: forall a n m (v: Vec a n) (w: Vec a m) i pf1 pf2,
   n <= i ->
   atWithProof (append v w) i pf1 = atWithProof w (i - n) pf2.
Proof.
   intros * Hge.
   rewrite atWithProof_atOption.
   remember (atWithProof w (i - n) pf2) as x. symmetry in Heqx.
   rewrite atWithProof_atOption in Heqx.
   rewrite atOption_append_r; auto.
Qed.

(*
 * Shortcut for when two atWithProofs are the same.
 *)
Lemma atWithProof_double_atOption: forall a n (xs ys: Vec a n) (i j: nat)
      (pf1: i < n) (pf2: j < n),
    atWithProof xs i pf1 = atWithProof ys j pf2 <->
       atOption xs i = atOption ys j.
Proof.
   intros.
   split; intro H.
   - unfold atWithProof in H.
     rewrite atWithProof_support in H.
     remember (match _ as _ return _ with | Some _ => _ | None => _ end _) as Q.
     symmetry in HeqQ.
     rewrite atWithProof_support in HeqQ.
     rewrite HeqQ. rewrite H.
     auto.
   - unfold atWithProof.
     rewrite atWithProof_support.
     remember (match _ as _ return _ with | Some _ => _ | None => _ end _) as Q.
     symmetry in HeqQ.
     rewrite atWithProof_support in HeqQ.
     rewrite <- HeqQ.
     auto.
Qed.

(*
 * Vectors that are the same at all points are equal.
 *)
Lemma atWithProof_extensionality: forall a n (xs ys: Vec a n),
   (forall i (pf1 pf2: i < n),
    atWithProof xs i pf1 = atWithProof ys i pf2) <->
   xs = ys.
Proof.
   intros.
   split; intros * H.
   - rewrite <- atOption_extensionality.
     intro i.
     specialize (H i).
     destruct (lt_dec i n).
     + specialize (H l l).
       rewrite atWithProof_double_atOption in H; auto.
     + assert (atOption xs i = None) as -> by (apply atOption_None; lia).
       assert (atOption ys i = None) as -> by (apply atOption_None; lia).
       auto.
   - intros. subst.
     rewrite atWithProof_double_atOption.
     auto.
Qed.


(*************************************************************)
(* take/drop *)

(*
 * take the first k elements
 *)
Fixpoint take {a: Type} {n: nat} (k: nat) (xs: Vec a n) : Vec a (min n k).
   (* FUTURE avoid using proof mode *)
(*
   match k with
   | 0 => coerceVec _ _ (NilVec a)
   | S k' =>
        match xs with
        | NilVec _ => coerceVec _ _ (NilVec a)
        | ConsVec x xs' => take k' xs'
        end
   end.
*)
Proof.
   destruct k.
   - refine (coerceVec (min n 0) _ (NilVec a)). apply Nat.min_0_r.
   - destruct xs.
     + refine (coerceVec (min 0 (S k)) _ (NilVec a)). apply Nat.min_0_l.
     + refine (ConsVec x (take a _ k xs)).
Defined.

(*
 * Take the last k elements
 *)
Definition takeEnd {a: Type} {n: nat}
     (k: nat) (xs: Vec a n) : Vec a (min n k) :=
   reverse (take k (reverse xs)).

(*
 * drop the first k elements
 *)
Fixpoint drop {a: Type} {n: nat} (k: nat) (xs: Vec a n) : Vec a (n - k).
   (* FUTURE avoid using proof mode *)
(*
   match k with
   | 0 => coerceVec (n - k) _ xs
   | S k' =>
        match xs with
        | NilVec _ => coerceVec (n - k) _ (NilVec a)
        | ConsVec x xs' => coerceVec (n - k) _ (drop k' xs')
        end
   end
*)
Proof.
   destruct k.
   - refine (coerceVec (n - 0) _ xs). apply Nat.sub_0_r.
   - destruct xs.
     + refine (coerceVec (0 - S k) _ (NilVec a)). apply Nat.sub_0_l.
     + refine (coerceVec (S n - S k) _ (drop a n k xs)). apply Nat.sub_succ.
Defined.

(*
 * drop the last k elements
 *)
Definition dropEnd {a: Type} {n: nat} (k: nat) (xs: Vec a n) : Vec a (n - k) :=
   reverse (drop k (reverse xs)).

(*
 * take 0 is nil
 *)
Lemma take_0_l: forall a n (xs: Vec a n),
   take 0 xs = coerceVec (min n 0) (Nat.min_0_r n) (NilVec a).
Proof.
   intros; simpl; auto.
Qed.

(*
 * takeEnd 0 is nil
 *)
Lemma takeEnd_0_l: forall a n (xs: Vec a n),
   takeEnd 0 xs = coerceVec (min n 0) (Nat.min_0_r n) (NilVec a).
Proof.
   intros.
   unfold takeEnd.
   rewrite take_0_l.
   rewrite reverse_coerceVec.
   rewrite reverse_NilVec.
   auto.
Qed.

(*
 * drop 0 is identity
 *)
Lemma drop_0_l: forall a n (xs: Vec a n),
   drop 0 xs = coerceVec (n - 0) (Nat.sub_0_r n) xs.
Proof.
   intros.
   induction xs; simpl; auto.
Qed.

(*
 * dropEnd 0 is identity
 *)
Lemma dropEnd_0_l: forall a n (xs: Vec a n),
   dropEnd 0 xs = coerceVec (n - 0) (Nat.sub_0_r n) xs.
Proof.
   intros.
   unfold dropEnd.
   rewrite drop_0_l.
   rewrite reverse_coerceVec.
   rewrite reverse_reverse.
   apply coerceVec_irr.
Qed.

(*
 * drop 1 is the same as tail
 *)
Lemma drop_1_l: forall a n (xs: Vec a (S n)) pf,
   drop 1 xs = coerceVec (S n - 1) pf (tail xs).
Proof.
   intros.
   simpl.
   destruct xs using caseVec_S.
   rewrite coerceVec_coerceVec.
   apply coerceVec_irr.
Qed.

(*
 * taking from nil is nil
 *)
Lemma take_NilVec_r: forall a k, take k (NilVec a) = NilVec a.
Proof.
   intros.
   induction k; simpl; rewrite NilVec_unique; auto.
Qed.

(*
 * taking from the end of nil is also nil
 *)
Lemma takeEnd_NilVec_r: forall a k, takeEnd k (NilVec a) = NilVec a.
Proof.
   intros.
   unfold takeEnd.
   rewrite reverse_NilVec.
   rewrite take_NilVec_r.
   apply reverse_NilVec.
Qed.

(*
 * dropping from nil is nil
 *)
Lemma drop_NilVec_r: forall a k, drop k (NilVec a) = NilVec a.
Proof.
   intros.
   induction k; simpl; rewrite NilVec_unique; auto.
Qed.

(*
 * dropping from the end of nil is also nil
 *)
Lemma dropEnd_NilVec_r: forall a k, dropEnd k (NilVec a) = NilVec a.
Proof.
   intros.
   unfold dropEnd.
   rewrite reverse_NilVec.
   rewrite drop_NilVec_r.
   apply reverse_NilVec.
Qed.

(*
 * taking from cons gives a cons (unless you take zero)
 *)
Lemma take_ConsVec_r: forall a n k x (xs: Vec a n),
   take (S k) (ConsVec x xs) = ConsVec x (take k xs).
Proof.
   intros; simpl; auto.
Qed.

(*
 * dropping from cons drops a cons (unless you drop zero)
 *)
Lemma drop_ConsVec_r: forall a n k x (xs: Vec a n),
   drop (S k) (ConsVec x xs) = drop k xs.
Proof.
   intros; simpl.
   rewrite coerceVec_vacuous; auto.
Qed.

(*
 * Unfortunately takeEnd and dropEnd from cons don't do anything
 * interesting, so we can't say anything about those cases.
 *)

(*
 * pull a coercion out of take
 *)
Lemma take_coerceVec_r: forall a n n' k (xs: Vec a n) pf pf',
   take k (coerceVec n' pf xs) = coerceVec (min n' k) pf' (take k xs).
Proof.
   intros.
   revert pf pf'.
   revert n' k.
   induction xs; intros; simpl.
   - subst. rewrite NilVec_unique. rewrite coerceVec_vacuous. auto.
   - destruct n'; try discriminate.
     rewrite coerceVec_ConsVec.
     destruct k; simpl.
     + rewrite coerceVec_coerceVec. apply coerceVec_irr.
     + assert (min n' k = min n k) as HN1 by lia.
       rewrite IHxs with (pf' := HN1).
       rewrite ConsVec_coerceVec.
       apply coerceVec_irr.
Qed.

(*
 * pull a coercion out of takeEnd
 *)
Lemma takeEnd_coerceVec_r: forall a n n' k (xs: Vec a n) pf pf',
   takeEnd k (coerceVec n' pf xs) = coerceVec (min n' k) pf' (takeEnd k xs).
Proof.
   intros.
   unfold takeEnd.
   rewrite reverse_coerceVec.
   assert (min n' k = min n k) as HN1 by lia.
   rewrite take_coerceVec_r with (pf' := HN1).
   rewrite reverse_coerceVec.
   apply coerceVec_irr.
Qed.

(*
 * pull a coercion out of drop
 *)
Lemma drop_coerceVec_r: forall a n n' k (xs: Vec a n) pf pf',
   drop k (coerceVec n' pf xs) = coerceVec (n' - k) pf' (drop k xs).
Proof.
   intros.
   revert pf pf'.
   revert n' k.
   induction xs; intros.
   - subst. rewrite NilVec_unique. rewrite coerceVec_vacuous. auto.
   - destruct n'; try discriminate.
     rewrite coerceVec_ConsVec.
     destruct k; simpl.
     + rewrite ConsVec_coerceVec.
       do 2 rewrite coerceVec_coerceVec.
       apply coerceVec_irr.
     + assert (n' - k = n - k) as NH1 by lia.
       rewrite IHxs with (pf' := NH1).
       do 2 rewrite coerceVec_coerceVec.
       apply coerceVec_irr.
Qed.

(*
 * pull a coercion out of dropEnd
 *)
Lemma dropEnd_coerceVec: forall a n n' k (xs: Vec a n) pf pf',
   dropEnd k (coerceVec n' pf xs) = coerceVec (n' - k) pf' (dropEnd k xs).
Proof.
   intros.
   unfold dropEnd.
   rewrite reverse_coerceVec.
   assert (n' - k = n - k) as HN1 by lia.
   rewrite drop_coerceVec_r with (pf' := HN1).
   rewrite reverse_coerceVec.
   apply coerceVec_irr.
Qed.

(*
 * take from gen is a smaller gen
 *)
Lemma take_gen: forall a k n (f: nat -> a),
   take k (gen n f) = gen (min n k) f.
Proof.
   intros.
   revert k f.
   induction n; intros; simpl.
   - rewrite gen_0_l. rewrite take_NilVec_r. auto.
   - rewrite gen_S_l.
     destruct k; simpl.
     + rewrite gen_0_l. rewrite NilVec_unique. auto.
     + rewrite IHn. rewrite gen_S_l. auto.
Qed.

(*
 * takeEnd from gen is a smaller (and more complicated) gen
 *)
Lemma takeEnd_gen: forall a k n (f: nat -> a),
   takeEnd k (gen n f) = gen (min n k) (fun i => f ((n - k) + i)).
Proof.
   intros.
   unfold takeEnd.
   rewrite reverse_gen.
   rewrite take_gen.
   rewrite reverse_gen.
   apply gen_extensionality.
   intros.
   f_equal.
   lia.
Qed.

(*
 * drop from gen is a smaller (more complicated) gen
 *)
Lemma drop_gen: forall a k n (f: nat -> a),
   drop k (gen n f) = gen (n - k) (fun i => f (k + i)).
Proof.
Admitted.

(*
 * dropEnd from gen is a smaller gen
 *)
Lemma dropEnd_gen: forall a k n (f: nat -> a),
   dropEnd k (gen n f) = gen (n - k) f.
Proof.
Admitted.

(*
 * If you take the whole vector (or more than it) you get it back.
 *)
Lemma take_all: forall a n (xs: Vec a n) k,
   forall (Hge: n <= k), take k xs = coerceVec (min n k) (Nat.min_l n k Hge) xs.
Proof.
   intros.
   revert Hge.
   revert k.
   induction xs; intros; simpl.
   - rewrite take_NilVec_r. rewrite NilVec_unique. auto.
   - destruct k; simpl.
     + lia.
     + assert (n <= k) as Hge' by lia.
       rewrite IHxs with (Hge := Hge'). 
       rewrite ConsVec_coerceVec.
       apply coerceVec_irr.
Qed.

(*
 * If you take the whole vector (or more than it) from the end,
 * you get it back.
 *)
Lemma takeEnd_all: forall a n (xs: Vec a n) k pf,
   forall (Hge: n <= k), takeEnd k xs = coerceVec (min n k) pf xs.
Proof.
   intros.
   unfold takeEnd.
   rewrite take_all with (Hge := Hge).
   rewrite reverse_coerceVec.
   rewrite reverse_reverse.
   apply coerceVec_irr.
Qed.

(*
 * take from reverse is reverse of takeEnd
 *)
Lemma take_reverse: forall a n k (xs: Vec a n),
   take k (reverse xs) = reverse (takeEnd k xs).
Proof.
   intros.
   unfold takeEnd.
   rewrite reverse_reverse.
   auto.
Qed.

(*
 * takeEnd from reverse is reverse of take
 *)
Lemma takeEnd_reverse: forall a n k (xs: Vec a n),
   takeEnd k (reverse xs) = reverse (take k xs).
Proof.
   intros.
   unfold takeEnd.
   rewrite reverse_reverse.
   auto.
Qed.

(*
 * take from append is take from the LHS, if it doesn't go into the RHS.
 *)
Lemma take_append_l: forall a n m k (xs: Vec a n) (ys: Vec a m) pf,
   k <= n ->
   take k (append xs ys) = coerceVec (min (n + m) k) pf (take k xs).
Proof.
Admitted.

(*
 * take from append is still an append if it goes into the RHS.
 *)
Lemma take_append_r: forall a n m k (xs: Vec a n) (ys: Vec a m) pf,
   n < k ->
   take k (append xs ys) =
      coerceVec (min (n + m) k) pf (append xs (take (k - n) ys)).
Proof.
Admitted.

(*
 * takeEnd from append is take from the RHS, if it doesn't go into the LHS.
 *)
Lemma takeEnd_append_l: forall a n m k (xs: Vec a n) (ys: Vec a m) pf,
   k <= m ->
   takeEnd k (append xs ys) = coerceVec (min (n + m) k) pf (takeEnd k ys).
Proof.
Admitted.

(*
 * take from append is still an append if it goes into the RHS.
 *)
Lemma takeEnd_append_r: forall a n m k (xs: Vec a n) (ys: Vec a m) pf,
   m < k ->
   takeEnd k (append xs ys) =
      coerceVec (min (n + m) k) pf (append (take (k - m) xs) ys).
Proof.
Admitted.

(*
 * at on take is just at, if in bounds.
 *
 * (if out of bounds, atOption_None should be sufficient)
 *)
Lemma atOption_take: forall a n k (xs: Vec a n) i,
   i < k -> atOption (take k xs) i = atOption xs i.
Proof.
Admitted.

(*
 * at on takeEnd is a more complicated at, if in bounds.
 *)
Lemma atOption_takeEnd: forall a n k (xs: Vec a n) i,
   i < k -> atOption (takeEnd k xs) i = atOption xs ((n - k) + i).
Proof.
Admitted.

(*
 * take on another take can be contracted
 *)
Lemma take_take: forall a n k1 k2 (xs: Vec a n) pf,
   take k1 (take k2 xs) =
      coerceVec (min (min n k2) k1) pf (take (min k1 k2) xs).
Proof.
Admitted.

(*
 * relationship between take and dropEnd
 *)
Lemma take_is_dropEnd: forall a n k (xs: Vec a n) pf,
   take k xs = coerceVec (min n k) pf (dropEnd (n - k) xs).
Proof.
Admitted.

(*
 * relationship between takeEnd and drop
 *)
Lemma takeEnd_is_drop: forall a n k (xs: Vec a n) pf,
   takeEnd k xs = coerceVec (min n k) pf (drop (n - k) xs).
Proof.
Admitted.

(*
 * If you take the whole vector from both ends, then paste back
 * together, you get the same vector back.
 *
 * k1 + k2 must be exactly equal to n; if it's less you obviously drop
 * some elements, and if it's more you repeat some.
 *)
Lemma take_takeEnd_all: forall a n k1 k2 (xs: Vec a n) pf,
   n = k1 + k2 ->
   append (take k1 xs) (takeEnd k2 xs) = coerceVec (min n k1 + min n k2) pf xs.
Proof.
   intros * Heq.
   revert Heq.
   revert pf.
   revert k2 n xs.
   induction k1; intros.
   - simpl.
     erewrite append_coerceVec_l.
     rewrite append_NilVec_l.
     erewrite takeEnd_all; try lia.
     rewrite coerceVec_coerceVec.
     apply coerceVec_irr.
   - simpl.
     destruct xs.
     + rewrite NilVec_unique.
       rewrite append_NilVec_l.
       rewrite takeEnd_NilVec_r.
       rewrite coerceVec_vacuous.
       auto.
     + (*
        * this doesn't work because it's simplified S (min n k1) to
        * min (S n) (S k1)
        *)
       Fail (rewrite append_ConsVec).
       (* XXX notyet *)
       admit.
Admitted.


(*************************************************************)
(* map *) 

(*
 * map on vectors
 *
 * Note that the nested fix is important for making downstream proofs
 * work (it makes f invariant).
 *)
Definition map {a b: Type} (f: a -> b) : forall {n}, Vec a n -> Vec b n :=
   fix visit {n: nat} (xs: Vec a n) :=
      match xs with
      | NilVec _ => NilVec b
      | ConsVec x xs' => ConsVec (f x) (visit xs')
      end.
(*
 * pull a coercion out of map
 *)
Lemma map_coerceVec: forall a b n n' (f: a -> b) (xs: Vec a n) pf,
   map f (coerceVec n' pf xs) = coerceVec n' pf (map f xs).
Proof.
Admitted.

(*
 * map on gen composes with the gen function
 *)
Lemma map_gen: forall a b n (f: nat -> a) (g: a -> b),
   map g (gen n f) = gen n (fun i => g (f i)).
Proof.
Admitted.

(*
 * head of map f is f head
 *)
Lemma head_map: forall a b n (f: a -> b) (xs: Vec a (S n)),
   head (map f xs) = f (head xs).
Proof.
Admitted.

(*
 * map of tail is tail of map
 *)
Lemma map_tail: forall a b n (f: a -> b) (xs: Vec a (S n)),
   map f (tail xs) = tail (map f xs).
Proof.
Admitted.

(*
 * tail of map is map of tail
 *)
Lemma tail_map: forall a b n (f: a -> b) (xs: Vec a (S n)),
   tail (map f xs) = map f (tail xs).
Proof.
   intros.
   symmetry.
   apply map_tail.
Qed.

(*
 * map of append is append of map
 *)
Lemma map_append: forall a b n m (f: a -> b) (xs: Vec a n) (ys: Vec a m),
   map f (append xs ys) = append (map f xs) (map f ys).
Proof.
   intros.
   intros.
   revert ys.
   induction xs; intros; simpl; auto.
   rewrite IHxs.
   auto.
Qed.

(*
 * at of map f is f at
 *)
Lemma atOption_map: forall a b n (f: a -> b) (xs: Vec a n) i,
   atOption (map f xs) i =
      match atOption xs i with
      | None => None
      | Some x => Some (f x)
      end.
Proof.
   intros.
Admitted.

(*
 * map of take is take of map
 *)
Lemma map_take: forall a b n (f: a -> b) k (xs: Vec a n),
   map f (take k xs) = take k (map f xs).
Proof.
Admitted.

(*
 * map of takeEnd is takeEnd of map
 *)
Lemma map_takeEnd: forall a b n (f: a -> b) k (xs: Vec a n),
   map f (takeEnd k xs) = takeEnd k (map f xs).
Proof.
Admitted.

(*
 * map of drop is drop of map
 *)
Lemma map_drop: forall a b n (f: a -> b) k (xs: Vec a n),
   map f (drop k xs) = drop k (map f xs).
Proof.
Admitted.

(*
 * map of dropEnd is dropEnd of map
 *)
Lemma map_dropEnd: forall a b n (f: a -> b) k (xs: Vec a n),
   map f (dropEnd k xs) = dropEnd k (map f xs).
Proof.
Admitted.

(*
 * loop fusion
 *)
Lemma map_compose: forall a b c n (f: a -> b) (g: b -> c) (v: Vec a n),
   map g (map f v) = map (fun x => g (f x)) v.
Proof.
   intros.
   induction v; simpl; auto.
   rewrite IHv; auto.
Qed.


(*************************************************************)
(* fold *)

(*
 * fold left.
 *
 * This argument order allows the loop to be nested, which is important
 * for making downstream proofs work (it makes f invariant)
 *)
Definition foldl {a b: Type}
     (f: b -> a -> b) : b -> forall {n}, Vec a n -> b :=
   fix visit (base: b) {n: nat} (xs: Vec a n) :=
      match xs with
      | NilVec _ => base
      | ConsVec x xs' => visit (f base x) xs'
      end.

(*
 * fold right.
 *
 * This argument order allows the loop to be nested, which is important
 * for making downstream proofs work (it makes f invariant)
 *)
Definition foldr {a b: Type}
     (f: a -> b -> b) (base: b) : forall {n}, Vec a n -> b :=
   fix visit {n: nat} (xs: Vec a n) :=
      match xs with
      | NilVec _ => base
      | ConsVec x xs' => f x (visit xs')
      end.

(*
 * fold on nil does nothing
 *)

Lemma foldl_NilVec: forall a b (f: b -> a -> b) base,
   foldl f base (NilVec a) = base.
Proof.
   intros; simpl; auto.
Qed.

Lemma foldr_NilVec: forall a b (f: a -> b -> b) base,
   foldr f base (NilVec a) = base.
Proof.
   intros; simpl; auto.
Qed.

(*
 * unroll fold on cons once
 *)

Lemma foldl_ConsVec: forall a b n (f: b -> a -> b) base x (xs: Vec a n),
   foldl f base (ConsVec x xs) = foldl f (f base x) xs.
Proof. 
   intros; simpl; auto.
Qed.

Lemma foldr_ConsVec: forall a b n (f: a -> b -> b) base x (xs: Vec a n),
   foldr f base (ConsVec x xs) = f x (foldr f base xs).
Proof.
   intros; simpl; auto.
Qed.

(*
 * coercions in fold are immaterial
 *)

Lemma foldl_coerceVec: forall a b n n' (f: b -> a -> b) base (xs: Vec a n) pf,
   foldl f base (coerceVec n' pf xs) = foldl f base xs.
Proof.
Admitted.

Lemma foldr_coerceVec: forall a b n n' (f: a -> b -> b) base (xs: Vec a n) pf,
   foldr f base (coerceVec n' pf xs) = foldr f base xs.
Proof.
Admitted.

(*
 * foldl on reverse is foldr, foldr on reverse is foldl
 *)

Lemma foldl_reverse: forall a b n (f: b -> a -> b) base (xs: Vec a n),
   foldl f base (reverse xs) = foldr (fun s x => f x s) base xs.
Proof.
Admitted.

Lemma foldr_reverse: forall a b n (f: a -> b -> b) base (xs: Vec a n),
   foldr f base (reverse xs) = foldl (fun x s => f s x) base xs.
Proof.
Admitted.

(*
 * fold on append is two folds
 *)

Lemma foldl_append: forall a b n m
     (f: b -> a -> b) base (xs: Vec a n) (ys: Vec a m),
   foldl f base (append xs ys) = foldl f (foldl f base xs) ys.
Proof.
Admitted.

Lemma foldr_append: forall a b n m
     (f: a -> b -> b) base (xs: Vec a n) (ys: Vec a m),
   foldr f base (append xs ys) = foldr f (foldr f base ys) xs.
Proof.
Admitted.

(*
 * fold/map fusion
 *)

Lemma foldl_map: forall a b c n m
     (f: a -> b) (g: c -> b -> c) base (xs: Vec a n) (ys: Vec a m),
   foldl g base (map f xs) = foldl (fun s x => g s (f x)) base xs.
Proof.
Admitted.

Lemma foldr_map: forall a b c n m
     (f: a -> b) (g: b -> c -> c) base (xs: Vec a n) (ys: Vec a m),
   foldr g base (map f xs) = foldr (fun x s => g (f x) s) base xs.
Proof.
Admitted.


(*************************************************************)
(* zip *)

(*
 * Splice together two vectors using a combining function.
 *
 * Excess elements on either side are dropped.
 *)
Fixpoint zipWith {a b c: Type} {n m: nat}
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m) : Vec c (min n m) :=
   match xs with
   | NilVec _ => NilVec c
   | ConsVec x xs' =>
        match ys with
        | NilVec _ => NilVec c
        | ConsVec y ys' =>
             ConsVec (f x y) (zipWith f xs' ys')
        end
   end.

(*
 * zipWith with nil on the left produces nil
 *)
Lemma zipWith_NilVec_l: forall a b c m (f: a -> b -> c) (ys: Vec b m),
   zipWith f (NilVec a) ys = NilVec c.
Proof.
Admitted.

(*
 * zipWith with nil on the right produces nil
 *)
Lemma zipWith_NilVec_r: forall a b c n (f: a -> b -> c) (xs: Vec a n),
   zipWith f xs (NilVec b) = coerceVec (min n 0) (Nat.min_0_r n) (NilVec c).
Proof.
Admitted.

(*
 * unfold lemma for cons on both sides
 *)
Lemma zipWith_ConsVec: forall a b c n m
     (f: a -> b -> c) x y (xs: Vec a n) (ys: Vec b m),
   zipWith f (ConsVec x xs) (ConsVec y ys) = ConsVec (f x y) (zipWith f xs ys).
Proof.
Admitted.

(*
 * coercions on the left of zipWith can be pulled out
 *)
Lemma zipWith_coerceVec_l: forall a b c n n' m
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m) pf pf',
   zipWith f (coerceVec n' pf xs) ys =
      coerceVec (min n' m) pf' (zipWith f xs ys).
Proof.
Admitted.

(*
 * coercions on the right of zipWith can be pulled out
 *)
Lemma zipWith_coerceVec_r: forall a b c n m m'
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m) pf pf',
   zipWith f xs (coerceVec m' pf ys) =
      coerceVec (min n m') pf' (zipWith f xs ys).
Proof.
Admitted.

(*
 * zipping two gens with f is equivalent to a gen with the combined function
 *)
Lemma zipWith_gen_gen: forall a b c n m
     (fa: nat -> a) (fb: nat -> b) (fc: a -> b -> c),
   zipWith fc (gen n fa) (gen m fb) = gen (min n m) (fun i => fc (fa i) (fb i)).
Proof.
   intros.
   unfold gen.
   revert m fa fb fc.
   induction n; intros; simpl; auto.
   destruct m; simpl; auto.
   do 3 assert (forall k, k - k = 0) as -> by lia.
   do 3 (rewrite gen_visit_S_l; try lia).
   rewrite IHn.
   auto.
Qed.

(*
 * head distributes over zipWith (in a manner of speaking)
 *)
Lemma head_zipWith: forall a b c n m
     (f: a -> b -> c) (xs: Vec a (S n)) (ys: Vec b (S m)),
   head (zipWith f xs ys) = f (head xs) (head ys).
Proof.
Admitted.

(*
 * tail distributes over zipWith
 *)
Lemma tail_zipWith: forall a b c n m
     (f: a -> b -> c) (xs: Vec a (S n)) (ys: Vec b (S m)),
   tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys).
Proof.
Admitted.

(*
 * reverse distributes over zipWith
 *)
Lemma reverse_zipWith: forall a b c n m
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m),
   reverse (zipWith f xs ys) = zipWith f (reverse xs) (reverse ys).
Proof.
Admitted.

(*
 * zipWith drops append on the left if the right is short enough
 *)
Lemma zipWith_append_l_short: forall a b c n m l
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec a m) (zs: Vec b l) pf,
   l <= n ->
   zipWith f (append xs ys) zs = coerceVec (min (n + m) l) pf (zipWith f xs zs).
Proof.
Admitted.

(*
 * zipWith drops append on the right if the left is short enough
 *)
Lemma zipWith_append_r_short: forall a b c n m l
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m) (zs: Vec b l) pf,
   n <= m ->
   zipWith f xs (append ys zs) = coerceVec (min n (m + l)) pf (zipWith f xs ys).
Proof.
Admitted.

(*
 * zipWith distributes over append if the left-hand lengths match
 *)
Lemma zipWith_append: forall a b c n m l
     (f: a -> b -> c) (xs: Vec a n) (xs': Vec a m) (ys: Vec b m) (ys': Vec b l)
     pf,
   zipWith f (append xs xs') (append ys ys') =
      coerceVec (min (n + m) (m + l)) pf
                (append (zipWith f xs ys) (zipWith f xs' ys')).
Proof.
Admitted.

(*
 * at distributes over zipWith
 *)
Lemma atOption_zipWith: forall a b c n m
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m) i,
   atOption (zipWith f xs ys) i =
      match atOption xs i with
      | None => None
      | Some x =>
           match atOption ys i with
           | None => None
           | Some y => Some (f x y)
           end
      end.
Proof.
Admitted.

(*
 * take distributes over zipWith
 *)
Lemma take_zipWith: forall a b c n m k
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m) pf,
   take k (zipWith f xs ys) =
      coerceVec (min (min n m) k) pf (zipWith f (take k xs) (take k ys)).
Proof.
Admitted.

(*
 * takeEnd distributes over zipWith
 *)
Lemma takeEnd_zipWith: forall a b c n m k
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m) pf,
   takeEnd k (zipWith f xs ys) =
      coerceVec (min (min n m) k) pf (zipWith f (takeEnd k xs) (takeEnd k ys)).
Proof.
Admitted.

(*
 * drop distributes over zipWith
 *)
Lemma drop_zipWith: forall a b c n m k
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m) pf,
   drop k (zipWith f xs ys) =
      coerceVec (min n m - k) pf (zipWith f (drop k xs) (drop k ys)).
Proof.
Admitted.

(*
 * dropEnd distributes over zipWith
 *)
Lemma dropEnd_zipWith: forall a b c n m k
     (f: a -> b -> c) (xs: Vec a n) (ys: Vec b m) pf,
   dropEnd k (zipWith f xs ys) =
      coerceVec (min n m - k) pf (zipWith f (dropEnd k xs) (dropEnd k ys)).
Proof.
Admitted.

(*
 * loop fusion for map on zipWith
 *)
Lemma map_zipWith: forall a b c d n m
     (f: a -> b -> c) (g: c -> d) (xs: Vec a n) (ys: Vec b m),
   map g (zipWith f xs ys) = zipWith (fun x y => g (f x y)) xs ys.
Proof.
Admitted.

(*
 * loop fusion for zipWith on map (left side)
 *)
Lemma zipWith_map_l: forall a b c d n m
     (f: a -> b) (g: b -> c -> d) (xs: Vec a n) (ys: Vec c m),
   zipWith g (map f xs) ys = zipWith (fun x y => g (f x) y) xs ys.
Proof.
Admitted.

(*
 * loop fusion for zipWith on map (right side)
 *)
Lemma zipWith_map_r: forall a b c d n m
     (f: b -> c) (g: a -> c -> d) (xs: Vec a n) (ys: Vec b m),
   zipWith g xs (map f ys) = zipWith (fun x y => g x (f y)) xs ys.
Proof.
Admitted.

(*
 * Splice together two vectors to make a vector of pairs.
 *)
Definition zip {a b: Type} {n m: nat}
     (xs: Vec a n) (ys: Vec b m) : Vec (a * b) (min n m) :=
   zipWith pair xs ys.

(*
 * zip with nil on the left produces nil
 *)
Lemma zip_NilVec_l: forall a b m (ys: Vec b m),
   zip (NilVec a) ys = NilVec (a * b).
Proof.
Admitted.

(*
 * zip with nil on the right produces nil
 *)
Lemma zip_NilVec_r: forall a b n (xs: Vec a n),
   zip xs (NilVec b) = coerceVec (min n 0) (Nat.min_0_r n) (NilVec (a * b)).
Proof.
Admitted.

(*
 * unfold lemma for cons on both sides
 *)
Lemma zip_ConsVec: forall a b n m x y (xs: Vec a n) (ys: Vec b m),
   zip (ConsVec x xs) (ConsVec y ys) = ConsVec (x, y) (zip xs ys).
Proof.
Admitted.

(*
 * coercions on the left of zip can be pulled out
 *)
Lemma zip_coerceVec_l: forall a b n n' m (xs: Vec a n) (ys: Vec b m) pf pf',
   zip (coerceVec n' pf xs) ys = coerceVec (min n' m) pf' (zip xs ys).
Proof.
Admitted.

(*
 * coercions on the right of zip can be pulled out
 *)
Lemma zip_coerceVec_r: forall a b n m m' (xs: Vec a n) (ys: Vec b m) pf pf',
   zip xs (coerceVec m' pf ys) = coerceVec (min n m') pf' (zip xs ys).
Proof.
Admitted.

(*
 * zipping two gens with f is equivalent to a gen that makes pairs
 *)
Lemma zip_gen_gen: forall a b n m (fa: nat -> a) (fb: nat -> b),
   zip (gen n fa) (gen m fb) = gen (min n m) (fun i => (fa i, fb i)).
Proof.
   intros.
   unfold zip.
   apply zipWith_gen_gen.
Qed.

(*
 * head distributes over zip (in a manner of speaking)
 *)
Lemma head_zip: forall a b n m (xs: Vec a (S n)) (ys: Vec b (S m)),
   head (zip xs ys) = (head xs, head ys).
Proof.
Admitted.

(*
 * tail distributes over zip
 *)
Lemma tail_zip: forall a b n m (xs: Vec a (S n)) (ys: Vec b (S m)),
   tail (zip xs ys) = zip (tail xs) (tail ys).
Proof.
Admitted.

(*
 * reverse distributes over zip
 *)
Lemma reverse_zip: forall a b n m (xs: Vec a n) (ys: Vec b m),
   reverse (zip xs ys) = zip (reverse xs) (reverse ys).
Proof.
Admitted.

(*
 * zip drops append on the left if the right is short enough
 *)
Lemma zip_append_l_short: forall a b n m l
     (xs: Vec a n) (ys: Vec a m) (zs: Vec b l) pf,
   l <= n -> zip (append xs ys) zs = coerceVec (min (n + m) l) pf (zip xs zs).
Proof.
Admitted.

(*
 * zip drops append on the right if the left is short enough
 *)
Lemma zip_append_r_short: forall a b n m l
     (xs: Vec a n) (ys: Vec b m) (zs: Vec b l) pf,
   n <= m -> zip xs (append ys zs) = coerceVec (min n (m + l)) pf (zip xs ys).
Proof.
Admitted.

(*
 * zip distributes over append if the left-hand lengths match
 *)
Lemma zip_append: forall a b n m l
     (xs: Vec a n) (xs': Vec a m) (ys: Vec b n) (ys': Vec b l) pf,
   zip (append xs xs') (append ys ys') =
      coerceVec (min (n + m) (n + l)) pf (append (zip xs ys) (zip xs' ys')).
Proof.
Admitted.

(*
 * at distributes over zip
 *)
Lemma atOption_zip: forall a b n m (xs: Vec a n) (ys: Vec b m) i,
   atOption (zip xs ys) i =
      match atOption xs i with
      | None => None
      | Some x =>
           match atOption ys i with
           | None => None
           | Some y => Some (x, y)
           end
      end.
Proof.
Admitted.

(*
 * take distributes over zip
 *)
Lemma take_zip: forall a b n m k (xs: Vec a n) (ys: Vec b m) pf,
   take k (zip xs ys) =
      coerceVec (min (min n m) k) pf (zip (take k xs) (take k ys)).
Proof.
Admitted.

(*
 * takeEnd distributes over zip
 *)
Lemma takeEnd_zip: forall a b n m k (xs: Vec a n) (ys: Vec b m) pf,
   takeEnd k (zip xs ys) =
      coerceVec (min (min n m) k) pf (zip (takeEnd k xs) (takeEnd k ys)).
Proof.
Admitted.

(*
 * drop distributes over zip
 *)
Lemma drop_zip: forall a b n m k (xs: Vec a n) (ys: Vec b m) pf,
   drop k (zip xs ys) =
      coerceVec (min n m - k) pf (zip (drop k xs) (drop k ys)).
Proof.
Admitted.

(*
 * dropEnd distributes over zip
 *)
Lemma dropEnd_zip: forall a b n m k (xs: Vec a n) (ys: Vec b m) pf,
   dropEnd k (zip xs ys) =
      coerceVec (min n m - k) pf (zip (dropEnd k xs) (dropEnd k ys)).
Proof.
Admitted.

(*
 * loop fusion for map on zip
 *)
Lemma map_zip: forall a b c n m (f: (a * b) -> c) (xs: Vec a n) (ys: Vec b m),
   map f (zip xs ys) = zipWith (fun x y => f (x, y)) xs ys.
Proof.
Admitted.

(*
 * loop fusion for zip on map (left side)
 *)
Lemma zip_map_l: forall a b c n m (f: a -> b) (xs: Vec a n) (ys: Vec c m),
   zip (map f xs) ys = zipWith (fun x y => (f x, y)) xs ys.
Proof.
Admitted.

(*
 * loop fusion for zip on map (right side)
 *)
Lemma zip_map_r: forall a b c n m (f: b -> c) (xs: Vec a n) (ys: Vec b m),
   zip xs (map f ys) = zipWith (fun x y => (x, f y)) xs ys.
Proof.
Admitted.
