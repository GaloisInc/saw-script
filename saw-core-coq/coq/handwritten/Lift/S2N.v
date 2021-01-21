From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCorePrelude.

From S2N Require Import S2N.

From mathcomp Require Import eqtype.
From mathcomp Require Import ssrnat.
From mathcomp Require Import tuple.

Scheme Minimality for tuple.tuple_of Sort Prop.
Scheme Induction  for tuple.tuple_of Sort Set.
Scheme Induction  for tuple.tuple_of Sort Type.

Scheme Minimality for eqtype.Equality.type Sort Prop.
Scheme Induction  for eqtype.Equality.type Sort Set.
Scheme Induction  for eqtype.Equality.type Sort Type.

Scheme Minimality for eqtype.Equality.mixin_of Sort Prop.
Scheme Induction  for eqtype.Equality.mixin_of Sort Set.
Scheme Induction  for eqtype.Equality.mixin_of Sort Type.

Scheme Induction for eqtype.Sub_spec Sort Prop.
Scheme Induction for eqtype.Sub_spec Sort Set.
Scheme Induction for eqtype.Sub_spec Sort Type.

Scheme Induction for eqtype.insub_spec Sort Prop.
Scheme Induction for eqtype.insub_spec Sort Set.
Scheme Induction for eqtype.insub_spec Sort Type.

Scheme Induction for eqtype.subType Sort Prop.
Scheme Induction for eqtype.subType Sort Set.
Scheme Induction for eqtype.subType Sort Type.

From Ornamental Require Import Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)

Preprocess Module S2N
  as S2N'
       { opaque
           Bits.spec.spec.low
           Coq.Arith.PeanoNat.Nat.even
           Records.CoreRecords.Fields
           Records.CoreRecords.ascii_to_p
           Records.CoreRecords.bool_to_p
           Records.CoreRecords.fields_get
           Records.CoreRecords.fields_insert
           Records.CoreRecords.fields_leaf
           Records.CoreRecords.fields_join
           Records.CoreRecords.fields_singleton
           Records.CoreRecords.get_member
           Records.CoreRecords.record_empty
           Records.CoreRecords.record_get
           Records.CoreRecords.record_here
           Records.CoreRecords.record_left
           Records.CoreRecords.record_right
           Records.CoreRecords.record_singleton
           Records.CoreRecords.Rjoin
           Records.CoreRecords.string_to_p
           Records.Notation.Rget
           CryptolToCoq.SAWCoreScaffolding.error
           SAWCorePrelude.bvToInt
           SAWCorePrelude.intToBv
           mathcomp.ssreflect.eqtype.eq_irrelevance
           mathcomp.ssreflect.ssrnat.half
           mathcomp.ssreflect.tuple.behead_tupleP

           CryptolPrimitives.PArithSeqBool
           CryptolPrimitives.PCmpSeq
           CryptolPrimitives.PCmpSeqBool
           CryptolPrimitives.PLiteralSeqBool
           CryptolPrimitives.PZeroSeq
           CryptolPrimitives.PZeroSeqBool
           CryptolPrimitives.ecAt
           CryptolPrimitives.ecEq
           CryptolPrimitives.ecFromTo
           CryptolPrimitives.ecGt
           CryptolPrimitives.ecLt
           CryptolPrimitives.ecMinus
           CryptolPrimitives.ecNotEq
           CryptolPrimitives.ecNumber
           CryptolPrimitives.ecPlus
           CryptolPrimitives.ecZero
           CryptolPrimitives.seq
           CryptolPrimitives.seqMap
           CryptolPrimitives.seq_cong1
           CryptolPrimitives.tcAdd
           CryptolPrimitives.tcSub
           SAWCoreScaffolding.Bool
           SAWCoreScaffolding.coerce

           S2N.and
           S2N.boolImplies
           S2N.handshakes_fn
           S2N.length

           (* S2N.state_machine_fn *)
       } .

(* Import CryptolPrimitives. *)
(* From CryptolToCoq Require Import SAWCoreScaffolding. *)
(* From CryptolToCoq Require Import SAWCorePrelude. *)

(* Import SAWCoreScaffolding. *)
(* Import SAWCorePrelude. *)
(* From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra. *)

(* Definition MY_CLIENT_HELLO : (seq 8 bool * (seq 8 bool * seq 8 bool)) := *)
(*   mkAct (TLS_HANDSHAKE (seq 8 Bool) (PLiteralSeqBool 8)) *)
(*         (TLS_CLIENT_HELLO (seq 8 Bool) (PLiteralSeqBool 8)) *)
(*         (ecNumber 67 (seq 8 Bool) (PLiteralSeqBool 8)). *)
