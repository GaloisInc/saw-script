From Coq Require Import Vectors.Vector.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From Lift Require Import Handshake.

From Ornamental Require Import Ornaments.

From S2N Require Import S2N.

Set DEVOID search prove equivalence.
Set DEVOID lift type.

Import CryptolPrimitives.

Module Connection.

  (**
This is what the original Cryptol [connection] type looked like:

type connection = {handshake : handshake
                  ,mode : [32]
                  ,corked_io : [8]
                  ,corked : [2]
                  ,is_caching_enabled : Bit
                  ,resume_from_cache : Bit
                  ,server_can_send_ocsp : Bit
                  ,key_exchange_eph : Bit
                  ,client_auth_flag : Bit //whether the server will request client cert
                  }

   *)
  Definition connection :=
    ((prod)
       (* client_auth_flag *)
       (@SAWCoreScaffolding.Bool)
       (((prod)
           (* corked *)
           (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@SAWCoreScaffolding.Bool)))
           (((prod)
               (* corked_io *)
               (((@CryptolPrimitives.seq) (((@TCNum) (8))) (@SAWCoreScaffolding.Bool)))
               (((prod)
                   Handshake.handshake
                   (*((prod)
                       (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool)))
                       (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool))))*)
                   (((prod)
                       (* is_caching_enabled *)
                       (@SAWCoreScaffolding.Bool)
                       (((prod)
                           (* key_exchange_eph *)
                           (@SAWCoreScaffolding.Bool)
                           (((prod)
                               (* mode *)
                               (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool)))
                               (((prod)
                                   (* resume_from_cache *)
                                   (@SAWCoreScaffolding.Bool)
                                   (* server_can_send_ocsp *)
                                   (@SAWCoreScaffolding.Bool)))))))))))))))).

  Record Connection :=
    MkConnection
      {
        clientAuthFlag    : bool;
        corked            : seq 2 bool;
        corkedIO          : seq 8 bool;
        handshake         : HandshakePP.Handshake;
        isCachingEnabled  : bool;
        keyExchangeEPH    : bool;
        mode              : seq 32 bool;
        resumeFromCache   : bool;
        serverCanSendOCSP : bool;
      }.

  Scheme Induction for Connection Sort Prop.
  Scheme Induction for Connection Sort Type.
  Scheme Induction for Connection Sort Set.

  Definition get_client_auth_flag (c : connection) : bool :=
    fst c.

  Definition get_corked (c : connection) : seq 2 bool :=
    fst (snd c).

  Definition get_corked_IO (c : connection) : seq 8 bool :=
    fst (snd (snd c)).

  Definition get_handshake (c : connection) : Handshake.handshake :=
    fst (snd (snd (snd c))).

  (* Definition get_is_caching_enabled (c : connection) : bool := *)
  (*   fst (snd (snd (snd (snd c)))). *)

  (* Definition get_key_exchange_EPH (c : connection) : bool := *)
  (*   fst (snd (snd (snd (snd (snd c))))). *)

  (* Definition get_mode (c : connection) : seq 32 bool := *)
  (*   fst (snd (snd (snd (snd (snd (snd c)))))). *)

  (* Definition get_resume_from_cache (c : connection) : bool := *)
  (*   fst (snd (snd (snd (snd (snd (snd (snd c))))))). *)

  (* Definition get_server_can_send_ocsp (c : connection) : bool := *)
  (*   snd (snd (snd (snd (snd (snd (snd (snd c))))))). *)

End Connection.

Preprocess Module Connection
  as ConnectionPP
     { opaque
         seq
     }.

Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.connection               as connectionPP.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.get_client_auth_flag     as getClientAuthFlag0.
Lift connectionPP ConnectionPP.Connection        in getClientAuthFlag0                    as getClientAuthFlag.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.get_corked               as getCorked0.
Lift connectionPP ConnectionPP.Connection        in getCorked0                            as getCorked.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.get_corked_IO            as getCorkedIO0.
Lift connectionPP ConnectionPP.Connection        in getCorkedIO0                          as getCorkedIO.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.get_handshake            as getHandshake0.
Lift connectionPP ConnectionPP.Connection        in getHandshake0                         as getHandshake.
(* Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.get_is_caching_enabled   as getIsCachingEnabled0. *)
(* Lift connectionPP ConnectionPP.Connection        in getIsCachingEnabled0                  as getIsCachingEnabled. *)
(* Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.get_key_exchange_EPH     as getKeyExchangeEPH0. *)
(* Lift connectionPP ConnectionPP.Connection        in getKeyExchangeEPH0                    as getKeyExchangeEPH. *)
(* Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.get_mode                 as getMode0. *)
(* Lift connectionPP ConnectionPP.Connection        in getMode0                              as getMode. *)
(* Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.get_resume_from_cache    as getResumeFromCache0. *)
(* Lift connectionPP ConnectionPP.Connection        in getResumeFromCache0                   as getResumeFromCache. *)
(* Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP.get_server_can_send_ocsp as getServerCanSendOCSP0. *)
(* Lift connectionPP ConnectionPP.Connection        in getServerCanSendOCSP0                 as getServerCanSendOCSP. *)

From Lift Require Import S2N.

Configure Lift
          HandshakePP.handshake
          HandshakePP.Handshake
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
              S2N'.handshakes
          }.

Configure Lift
          connectionPP ConnectionPP.Connection
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
              S2N'.handshakes
          }.

(* Lift HandshakePP.handshake *)
(*      HandshakePP.Handshake *)
(*   in ecAt *)
(*   as ecAt0. *)

(* Lift connectionPP ConnectionPP.Connection *)
(*   in ecAt0 *)
(*   as ecAt. *)

From Lift Require Import Handshake.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N'.ACTIVE_MESSAGE
  as ActiveMessage0.

Lift connectionPP ConnectionPP.Connection
  in ActiveMessage0
  as ActiveMessage.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N'.advance_message
  as advanceMessage0.

(* This one does not terminate. *)
Lift connectionPP ConnectionPP.Connection
  in advanceMessage0
  as advanceMessage.

Definition myHandshake : HandshakePP.Handshake :=
  HandshakePP.MkHandshake
    (bvNat _ 0)
    (bvNat _ 0)
.

Definition myConnection : ConnectionPP.Connection :=
  ConnectionPP.MkConnection
    (false)
    (bvNat _ 0)
    (bvNat _ 0)
    (myHandshake)
    (false)
    (false)
    (bvNat _ 0)
    (false)
    (false)
.
