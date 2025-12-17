From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Stdlib Require Import ZifyBool.
From Stdlib Require Import ZifyClasses.

From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

Import SAWCorePrelude.

(* This file defines the necessary Zify-related instances to be able to use the
   `lia` tactic on many theorems involving `bitvector 64` equalities and
   inequalities. This file includes a small number of proofs to test that `lia`
   is working as intended. The design was heavily inspired by the Zify instances
   for Coq's Uint63, which can be found here:
   https://github.com/coq/coq/blob/756c560ab5d19a1568cf41caac6f0d67a97b08c6/theories/micromega/ZifyUint63.v

   This is far from complete, however. Be aware of the following caveats:

   1. These instances only work over unsigned arithmetic, so theorems involving
      signed arithmetic are not supported. If we wanted to support signed
      arithmetic, we would likely need to take inspiration from how Coq's Zify
      instances for the Sint63 type work:
      https://github.com/coq/coq/blob/756c560ab5d19a1568cf41caac6f0d67a97b08c6/theories/micromega/ZifySint63.v

   2. There are likely many operations that are not covered here. If there is
      an unsupported operation that you would like to see added, please file an
      issue to the saw-script repo.

   3. These instances only support bitvectors where the bit width is 64.
      Ideally, we would make the Zify instances parametric in the bit width, but
      this is surprisingly difficult to accomplish. At a minimum, this would
      require some upstream changes to Coq. See, for instance,
      https://github.com/coq/coq/issues/16404.

      For now, we simply provide the machinery at 64 bits, which is a common
      case. If there is enough demand, we can also provide similar machinery
      for bitvectors at other common bit widths.
*)

(* Unfortunately, https://github.com/coq/coq/issues/16404 prevents us from
   simply defining instances for `bitvector 64`, so we provide a thin wrapper
   around it and define instances for it. We may be able to remove this
   workaround once the upstream Coq issue is fixed and enough time has passed.
*)
Definition bitvector_64 := bitvector 64.

(* Notations *)

(* 2^64 *)
Notation modulus := 0x10000000000000000%Z.

Notation Zadd_mod_64 x y :=
  (Z.modulo (Z.add x y) modulus).

Notation Zsub_mod_64 x y :=
  (Z.modulo (Z.sub x y) modulus).

Notation Zmul_mod_64 x y :=
  (Z.modulo (Z.mul x y) modulus).

Notation bv64_bounded x :=
  (Z.le 0 x /\ Z.lt x modulus).

(* Auxiliary lemmas *)

Lemma bvToInt_inj w a b :
  bvToInt w a = bvToInt w b ->
  a = b.
Proof. holds_for_bits_up_to_3. Qed.

Lemma of_nat_bvToNat_bvToInt w a :
  Z.of_nat (bvToNat w a) = bvToInt w a.
Proof. holds_for_bits_up_to_3. Qed.

Lemma msb_Ztestbit w a :
  msb w a = Z.testbit (bvToInt (S w) a) (Z.of_nat w).
Proof. holds_for_bits_up_to_3. Qed.

Global Instance Proper_bvToInt_le w :
  Proper (isBvule w ==> Z.le) (bvToInt w).
Proof. holds_for_bits_up_to_3. Qed.

Global Instance Proper_bvToInt_lt w :
  Proper (isBvult w ==> Z.lt) (bvToInt w).
Proof. holds_for_bits_up_to_3. Qed.

(* See zify_ubv64.cry for a version of this lemma that can be proven with
   an SMT solver. In particular, run the following:

   > :prove bvAdd_Zadd_mod`{3}
 *)
Lemma bvAdd_Zadd_mod_64 a b :
  bvToInt 64 (bvAdd 64 a b) =
  Zadd_mod_64 (bvToInt 64 a) (bvToInt 64 b).
Admitted.

(* See zify_ubv64.cry for a version of this lemma that can be proven with
   an SMT solver. In particular, run the following:

   > :prove bvSub_Zsub_mod`{3}
 *)
Lemma bvSub_Zsub_mod_64 a b :
  bvToInt 64 (bvSub 64 a b) =
  Zsub_mod_64 (bvToInt 64 a) (bvToInt 64 b).
Admitted.

(* See zify_ubv64.cry for a version of this lemma that can be proven with
   an SMT solver. In particular, run the following:

   > :prove bvMul_Zmul_mod`{3}
 *)
Lemma bvMul_Zmul_mod_64 a b :
  bvToInt 64 (bvMul 64 a b) =
  Zmul_mod_64 (bvToInt 64 a) (bvToInt 64 b).
Admitted.

(* See zify_ubv64.cry for a version of this lemma that can be proven with
   an SMT solver. In particular, run the following:

   > :prove bvToInt_intToBv`{3}
 *)
Lemma bvToInt_intToBv_64 (a : Z) :
  bvToInt 64 (intToBv 64 a) = Z.modulo a modulus.
Admitted.

Lemma bvule_Zleb w a b :
  bvule w a b =
  Z.leb (bvToInt w a) (bvToInt w b).
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvult_Zltb w a b :
  bvult w a b =
  Z.ltb (bvToInt w a) (bvToInt w b).
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvEq_Zeqb w a b :
  bvEq w a b =
  Z.eqb (bvToInt w a) (bvToInt w b).
Proof. holds_for_bits_up_to_3. Qed.

Lemma Zle_bvToInt_to_isBvule w a b :
  Z.le (bvToInt w a) (bvToInt w b) ->
  isBvule w a b.
Proof. holds_for_bits_up_to_3. Qed.

Lemma Zlt_bvToInt_to_isBvult w a b :
  Z.lt (bvToInt w a) (bvToInt w b) ->
  isBvult w a b.
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvToInt_lt_max w a :
  Z.lt (bvToInt w a) (Z.pow 2 (Z.of_nat w)).
Proof. holds_for_bits_up_to_3. Qed.

Lemma bvToInt_64_bounded :
  forall (x : bitvector 64),
  bv64_bounded (bvToInt 64 x).
Proof.
  intros x. split.
  - change 0%Z with (bvToInt 64 (intToBv 64 0)).
    apply Proper_bvToInt_le.
    apply isBvule_zero_n.
  - change modulus with (Z.pow 2 (Z.of_nat 64)).
    apply bvToInt_lt_max.
Qed.

(* Zify-related instances *)

Global Instance Inj_bv64_Z : InjTyp bitvector_64 Z :=
  { inj := bvToInt 64
  ; pred := fun x => bv64_bounded x
  ; cstr := bvToInt_64_bounded
  }.
Add Zify InjTyp Inj_bv64_Z.

Global Instance Op_bvumin : CstOp (bvumin 64 : bitvector_64) :=
  { TCst := 0%Z
  ; TCstInj := eq_refl
  }.
Add Zify CstOp Op_bvumin.

Global Instance Op_bvumax : CstOp (bvumax 64 : bitvector_64) :=
  { TCst := 0xffffffffffffffff%Z
  ; TCstInj := eq_refl
  }.
Add Zify CstOp Op_bvumax.

Global Instance Op_bvsmin : CstOp (bvsmin 64 : bitvector_64) :=
  { TCst := 0x8000000000000000%Z
  ; TCstInj := eq_refl
  }.
Add Zify CstOp Op_bvsmin.

Global Instance Op_bvsmax : CstOp (bvsmax 64 : bitvector_64) :=
  { TCst := 0x7fffffffffffffff%Z
  ; TCstInj := eq_refl
  }.
Add Zify CstOp Op_bvsmax.

Global Program Instance Op_msb : UnOp (msb 63 : bitvector_64 -> bool) :=
  { TUOp := fun x => Z.testbit x 63
  ; TUOpInj := _
  }.
Next Obligation.
  apply msb_Ztestbit.
Qed.
Add Zify UnOp Op_msb.

Global Instance Op_intToBv : UnOp (intToBv 64 : Z -> bitvector_64) :=
  { TUOp := fun x => Z.modulo x modulus
  ; TUOpInj := bvToInt_intToBv_64
  }.
Add Zify UnOp Op_intToBv.

Global Instance Op_bvToNat : UnOp (bvToNat 64 : bitvector_64 -> nat) :=
  { TUOp := fun x => x
  ; TUOpInj := of_nat_bvToNat_bvToInt 64
  }.
Add Zify UnOp Op_bvToNat.

Global Instance Op_bvNat : UnOp (bvNat 64 : nat -> bitvector_64) :=
  { TUOp := fun x => Z.modulo x modulus
  ; TUOpInj := fun n => bvToInt_intToBv_64 (Z.of_nat n)
  }.
Add Zify UnOp Op_bvNat.

Global Instance Op_bvAdd : BinOp (bvAdd 64 : bitvector_64 -> bitvector_64 -> bitvector_64) :=
  { TBOp := fun x y => Zadd_mod_64 x y
  ; TBOpInj := bvAdd_Zadd_mod_64
  }.
Add Zify BinOp Op_bvAdd.

Global Instance Op_bvSub : BinOp (bvSub 64 : bitvector_64 -> bitvector_64 -> bitvector_64) :=
  { TBOp := fun x y => Zsub_mod_64 x y
  ; TBOpInj := bvSub_Zsub_mod_64
  }.
Add Zify BinOp Op_bvSub.

Global Instance Op_bvMul : BinOp (bvMul 64 :bitvector_64 -> bitvector_64 -> bitvector_64) :=
  { TBOp := fun x y => Zmul_mod_64 x y
  ; TBOpInj := bvMul_Zmul_mod_64
  }.
Add Zify BinOp Op_bvMul.

Global Instance Op_bvule : BinOp (bvule 64 : bitvector_64 -> bitvector_64 -> bool) :=
  { TBOp := Z.leb
  ; TBOpInj := bvule_Zleb 64
  }.
Add Zify BinOp Op_bvule.

Global Instance Op_bvult : BinOp (bvult 64 : bitvector_64 -> bitvector_64 -> bool) :=
  { TBOp := Z.ltb
  ; TBOpInj := bvult_Zltb 64
  }.
Add Zify BinOp Op_bvult.

Global Instance Op_bvEq : BinOp (bvEq 64 : bitvector_64 -> bitvector_64 -> bool) :=
  { TBOp := Z.eqb
  ; TBOpInj := bvEq_Zeqb 64
  }.
Add Zify BinOp Op_bvEq.

Global Program Instance Rel_isBvule : BinRel (isBvule 64 : bitvector_64 -> bitvector_64 -> Prop) :=
  { TR := Z.le
  ; TRInj := _
  }.
Next Obligation.
  split.
  - apply Proper_bvToInt_le.
  - apply Zle_bvToInt_to_isBvule.
Qed.
Add Zify BinRel Rel_isBvule.

Global Program Instance Rel_isBvult : BinRel (isBvult 64 : bitvector_64 -> bitvector_64 -> Prop) :=
  { TR := Z.lt
  ; TRInj := _
  }.
Next Obligation.
  split.
  - apply Proper_bvToInt_lt.
  - apply Zlt_bvToInt_to_isBvult.
Qed.
Add Zify BinRel Rel_isBvult.

Global Program Instance Rel_eq : BinRel (@eq bitvector_64) :=
  { TR := @eq Z
  ; TRInj := _
  }.
Next Obligation.
  split; intros H.
  - rewrite -> H. reflexivity.
  - apply (bvToInt_inj _ _ _ H).
Qed.
Add Zify BinRel Rel_eq.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Test cases *)

Lemma bv64_refl (x : bitvector 64) : x = x.
Proof. lia. Qed.

Lemma bvAdd_comm (x y : bitvector 64) : bvAdd 64 x y = bvAdd 64 y x.
Proof. lia. Qed.

Lemma isBvult_bvSub (x y : bitvector 64) : isBvult 64 (bvSub 64 x (intToBv 64 1)) y ->
                                           isBvult 64 (bvSub 64 y x) y.
Proof. lia. Qed.

Lemma isBvule_bvSub (x y : bitvector 64) : isBvule 64 x y ->
                                           isBvule 64 (bvSub 64 y x) y.
Proof. lia. Qed.

Lemma isBvult_is_Bvule (x y z : bitvector 64) :
  isBvult 64 x y -> isBvule 64 y z -> isBvult 64 x z.
Proof. lia. Qed.

Lemma bvNat_bvToNat_inv (x : bitvector 64) : bvNat 64 (bvToNat 64 x) = x.
Proof. lia. Qed.

Lemma isBvule_antisymm a b : isBvule 64 a b -> isBvule 64 b a -> a = b.
Proof. lia. Qed.

Lemma bvEq_neq':
  forall (a b : bitvector 64), bvEq 64 a b = false <-> a <> b.
Proof. lia. Qed.

Lemma bvSub_bvAdd_cancel a b : bvSub 64 (bvAdd 64 a b) b = a.
Proof. lia. Qed.

Lemma bvSub_bvAdd_distrib a b c :
  bvSub 64 a (bvAdd 64 b c) = bvSub 64 (bvSub 64 a b) c.
Proof. lia. Qed.

Lemma bvSub_left_cancel a b :
  bvSub 64 b (bvSub 64 b a) = a.
Proof. lia. Qed.

Lemma bvToNat_bvAdd_succ a :
  isBvult 64 a (bvumax 64) ->
  bvToNat 64 (bvAdd 64 a (intToBv 64 1)) = S (bvToNat 64 a).
Proof. lia. Qed.

Lemma isBvult_bvSub_zero
        (a b : bitvector 64) :
      isBvult 64 a b ->
      isBvult 64 (intToBv 64 0) (bvSub 64 b a).
Proof. lia. Qed.

Lemma isBvult_bvToNat
        (a b : bitvector 64) :
      isBvult 64 a b ->
      bvToNat 64 a < bvToNat 64 b.
Proof. lia. Qed.

Lemma isBvule_bvToNat
        (a b : bitvector 64) :
      isBvule 64 a b ->
      bvToNat 64 a <= bvToNat 64 b.
Proof. lia. Qed.

Lemma bvToNat_bvSub
        (a b : bitvector 64) :
      isBvult 64 a b ->
      bvToNat 64 (bvSub 64 b a) = bvToNat 64 b - bvToNat 64 a.
Proof. lia. Qed.

Lemma bvToNat_intToBv_0 :
  bvToNat 64 (intToBv 64 0) = 0.
Proof. lia. Qed.

Lemma bvAdd_succ n :
  bvAdd 64 (bvNat 64 n) (intToBv 64 1) = bvNat 64 (S n).
Proof. lia. Qed.
