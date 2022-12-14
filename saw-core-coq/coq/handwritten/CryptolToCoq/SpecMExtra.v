(***
 *** Extra Proofs for SpecM that Rely on SAWCorePrelude
 ***)

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From EnTree Require Export
     Basics.HeterogeneousRelations
     Basics.QuantType
     Ref.SpecM.


(***
 *** QuantType Instances
 ***)

(** Simple QuantType Instances **)

Program Instance QuantType_Bool : QuantType Bool :=
  { quantEnc := QEnc_nat;
    quantEnum := fun n => match n with
                          | 0 => false
                          | S _ => true
                          end;
    quantEnumInv := fun b => if b then 1 else 0 }.
Next Obligation.
  destruct a; reflexivity.
Defined.


(** QuantType Vec Instance **)

(* Build the encoding of the N-tuple of a given encoding *)
Fixpoint QEnc_NTuple n (qenc : QuantEnc) : QuantEnc :=
  match n with
  | 0 => QEnc_prop True
  | S n' => QEnc_pair qenc (QEnc_NTuple n' qenc)
  end.

(* The quantEnum function for Vec n a *)
Definition quantEnum_Vec n A `{QuantType A} :
  encodes (QEnc_NTuple n (quantEnc (A:=A))) -> Vec n A :=
  nat_rect
    (fun n => encodes (QEnc_NTuple n (quantEnc (A:=A))) -> Vec n A)
    (fun _ => VectorDef.nil _)
    (fun n enumF x => VectorDef.cons _ (quantEnum (fst x)) _ (enumF (snd x)))
    n.

(* The quantEnumInv function for Vec n a *)
Definition quantEnumInv_Vec n A `{QuantType A} :
  Vec n A -> encodes (QEnc_NTuple n (quantEnc (A:=A))) :=
  nat_rect
    (fun n => Vec n A -> encodes (QEnc_NTuple n (quantEnc (A:=A))))
    (fun _ => I)
    (fun n enumInvF x => (quantEnumInv (VectorDef.hd x), enumInvF (VectorDef.tl x)))
    n.

Program Instance QuantType_Vec n A `{QuantType A} : QuantType (Vec n A) :=
  { quantEnc := QEnc_NTuple n (quantEnc (A:=A));
    quantEnum := quantEnum_Vec n A;
    quantEnumInv := quantEnumInv_Vec n A }.
Next Obligation.
  induction a.
  - reflexivity.
  - simpl. rewrite quantEnumSurjective. rewrite IHa. reflexivity.
Defined.

Program Instance QuantType_bitvector w : QuantType (bitvector w) :=
  QuantType_Vec w _.
