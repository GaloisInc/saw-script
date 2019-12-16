From Bits Require Import spec.

From Coq Require Import Vectors.Vector.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From Lift Require Import S2N.

From Ornamental Require Import Ornaments.

From S2N Require Import S2N.

Set DEVOID search prove equivalence.
Set DEVOID lift type.

Import CryptolPrimitives.

Module Handshake.

  (** [cry_handshake] is the [handshake] type as it comes out of the translation
from Cryptol to Coq.  The fields have been inlined into a nested tuple type.

This is what the original [handshake] type looked like:

type handshake = {handshake_type : [32]
                 ,message_number : [32]
                 }
   *)
  Definition handshake : Type := (seq 32 bool * seq 32 bool).

  (** We can define more convenient types for [handshake] and [connection] in Coq.
Ideally, we'd like the translation to generate those, but in its current state,
it goes through an intermediate language that does not support records and
record types.
   *)
  Record Handshake :=
    MkHandshake
      {
        handshakeType : seq 32 bool;
        messageNumber : seq 32 bool;
      }.

  Scheme Induction for Handshake Sort Prop.
  Scheme Induction for Handshake Sort Type.
  Scheme Induction for Handshake Sort Set.

  Definition get_handshake_type (h : handshake) : seq 32 bool :=
    fst h.

  Definition get_message_number (h : handshake) : seq 32 bool :=
    snd h.

End Handshake.

Preprocess Module Handshake
  as HandshakePP
       { opaque
           PArithSeqBool
           PCmpSeq
           PCmpSeqBool
           PLiteralSeqBool
           ecAt
           ecGt
           ecLt
           ecMinus
           ecNotEq
           ecNumber
           ecPlus
           handshakes_fn
           natToNat
           seq
       }.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in HandshakePP.get_handshake_type
  as getHandshake.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in HandshakePP.get_message_number
  as getMessageNumber.

Configure Lift HandshakePP.handshake HandshakePP.Handshake
          { opaque
              PArithSeqBool
              PCmpSeq
              PCmpSeqBool
              PLiteralSeqBool
              ecAt
              ecGt
              ecLt
              ecMinus
              ecNotEq
              ecNumber
              ecPlus
              handshakes_fn
              natToNat
              seq
          }.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N'.valid_handshake
  as validHandshake.
