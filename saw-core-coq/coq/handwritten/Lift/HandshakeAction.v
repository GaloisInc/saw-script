From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From Coq Require Import Vectors.Vector.

(* From mathcomp Require Import seq. *)
(* From mathcomp Require Import tuple. *)

From S2N Require Import S2N.

From Ornamental Require Import Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)

(* Import CryptolPrimitives. *)
(* (* Import ListNotations. *) *)
(* Import SAWCorePrelude. *)
(* (* Import VectorNotations. *) *)

(* Definition seq : Num -> (Type) -> Type := *)
(*   (fun (num : ((@Num))) (a : Type) => *)
(*    ((@Num_rect) *)
(*     ((fun (num : ((@Num))) => Type)) *)
(*     ((fun (n : ((@Nat))) => *)
(*       ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) *)
(*     (((@Stream) (a))) (num))). *)

(* When those two lines are commented out, the lifting of [get_record_type]
works! *)

Import CryptolPrimitives.

Module HandshakeAction.

  Definition cry_handshake_action : Type
    := (seq 8 bool * (seq 8 bool * seq 8 bool)).

  Record HandshakeAction :=
    MkHandshakeAction
    {
    recordType  : seq 8 bool;
    messageType : seq 8 bool;
    writer      : seq 8 bool;
    }.

  Scheme Induction for HandshakeAction Sort Prop.
  Scheme Induction for HandshakeAction Sort Type.
  Scheme Induction for HandshakeAction Sort Set.

  Definition get_record_type (ha : cry_handshake_action) : seq 8 bool :=
    fst ha.

  Definition get_message_type (ha : cry_handshake_action) : seq 8 bool :=
    Prod.fst _ _ (Prod.snd _ _ ha).

  Definition get_writer (ha : cry_handshake_action) : seq 8 bool :=
    Prod.snd _ _ (Prod.snd _ _ ha).

  Definition MY_CLIENT_HELLO : (seq 8 bool * (seq 8 bool * seq 8 bool)) :=
    mkAct (TLS_HANDSHAKE (seq 8 Bool) (PLiteralSeqBool 8))
          (TLS_CLIENT_HELLO (seq 8 Bool) (PLiteralSeqBool 8))
          (ecNumber 67 (seq 8 Bool) (PLiteralSeqBool 8)).

End HandshakeAction.

Preprocess Module HandshakeAction
  as HandshakeAction'
     { opaque
       seq
     }.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in HandshakeAction'.get_record_type
  as getRecordType.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in HandshakeAction'.get_message_type
  as getMessageType.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in HandshakeAction'.get_writer
  as getWriter.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in HandshakeAction'.MY_CLIENT_HELLO
  as clientHello.

Theorem checkMessageType
  : getMessageType clientHello
    = HandshakeAction.get_message_type HandshakeAction.MY_CLIENT_HELLO.
Proof.
  reflexivity.
Qed.

Theorem checkRecordType
  : getRecordType clientHello
    =
    HandshakeAction.get_record_type HandshakeAction.MY_CLIENT_HELLO.
Proof.
  reflexivity.
Qed.

Theorem checkWriter
  : getWriter clientHello
    =
    HandshakeAction.get_writer HandshakeAction.MY_CLIENT_HELLO.
Proof.
  reflexivity.
Qed.

From Lift Require Import S2N.

Check S2N'.state_machine_fn.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.mkAct
  as mkAct'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_HANDSHAKE
  as TLS_HANDSHAKE'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_CLIENT_HELLO
  as TLS_CLIENT_HELLO'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in PLiteralSeqBool
  as PLiteralSeqBool'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in PCmp
  as PCmpP
     { opaque
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
     }.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in PCmpWord
  as PCmpWordP
     { opaque
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
       bvCmp
     }.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in PCmpSeqBool
  as PCmpSeqBool'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in ecNumber
  as ecNumber'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in ecZero
  as ..P.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in ecEq
  as ecEq'
     { opaque
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
     }.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_SERVER_SESSION_LOOKUP
  as TLS_SERVER_SESSION_LOOKUP'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_SERVER_HELLO
  as TLS_SERVER_HELLO'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_SERVER_NEW_SESSION_TICKET
  as TLS_SERVER_NEW_SESSION_TICKET'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_SERVER_CERT
  as TLS_SERVER_CERT'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_SERVER_CERT_STATUS
  as TLS_SERVER_CERT_STATUS'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_SERVER_KEY
  as TLS_SERVER_KEY'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_SERVER_CERT_REQ
  as TLS_SERVER_CERT_REQ'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_SERVER_HELLO_DONE
  as TLS_SERVER_HELLO_DONE'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_CLIENT_CERT
  as TLS_CLIENT_CERT'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_CLIENT_KEY
  as TLS_CLIENT_KEY'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_CLIENT_CERT_VERIFY
  as TLS_CLIENT_CERT_VERIFY'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_CHANGE_CIPHER_SPEC
  as TLS_CHANGE_CIPHER_SPEC'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_CLIENT_FINISHED
  as TLS_CLIENT_FINISHED'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_SERVER_FINISHED
  as TLS_SERVER_FINISHED'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.TLS_APPLICATION_DATA
  as TLS_APPLICATION_DATA'.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.state_machine_fn
  as stateMachineFn.

Compute getRecordType
        (stateMachineFn
         (S2N'.CLIENT_HELLO
          (seq 5 bool)
          ((@CryptolPrimitives.PLiteralSeqBool) (((@TCNum) (5))))
         )
        ) = HandshakeAction'.get_record_type
            (S2N'.state_machine_fn
             (S2N'.CLIENT_HELLO
              (seq 5 bool)
              ((@CryptolPrimitives.PLiteralSeqBool) (((@TCNum) (5))))
             )
            ).

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.state_machine
  as stateMachine.


Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.
  as '.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.
  as '.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.
  as '.

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.
  as '.

Check (S2N'.TLS_HANDSHAKE).

Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction
  in S2N'.state_machine
  as stateMachine
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
       CryptolPrimitives.seq
       CryptolPrimitives.seqMap
       CryptolPrimitives.ecFromTo
       CryptolPrimitives.PLiteralSeqBool
       CryptolPrimitives.tcAdd
       CryptolPrimitives.tcSub
       CryptolPrimitives.seq_cong1
       SAWCoreScaffolding.Bool
       SAWCoreScaffolding.coerce
     } .

Local Open Scope form_scope.





Definition ACTIVE_MESSAGE (conn : ((prod) (@SAWCoreScaffolding.Bool) (((prod)
(((@CryptolPrimitives.seq) (((@TCNum) (2))) (@SAWCoreScaffolding.Bool)))
(((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
(@SAWCoreScaffolding.Bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
(((@TCNum) (32))) (@SAWCoreScaffolding.Bool))) (((@CryptolPrimitives.seq)
(((@TCNum) (32))) (@SAWCoreScaffolding.Bool))))) (((prod)
(@SAWCoreScaffolding.Bool) (((prod) (@SAWCoreScaffolding.Bool) (((prod)
(((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool)))
(((prod) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.Bool)))))))))))))))))
:= ((@CryptolPrimitives.ecAt) (((@TCNum) (32))) (((@CryptolPrimitives.seq)
(((@TCNum) (32))) (@SAWCoreScaffolding.Bool))) (((@TCNum) (32)))
(((@CryptolPrimitives.ecAt) (((@TCNum) (128))) (((@CryptolPrimitives.seq)
(((@TCNum) (32))) (((@CryptolPrimitives.seq) (((@TCNum) (32)))
(@SAWCoreScaffolding.Bool))))) (((@TCNum) (32))) (handshakes) (((fst) (((fst)
(((snd) (((snd) (((snd) (conn))))))))))))) (((snd) (((fst) (((snd) (((snd)
(((snd) (conn)))))))))))).

Definition ACTIVE_STATE (conn : ((prod) (@SAWCoreScaffolding.Bool) (((prod)
(((@CryptolPrimitives.seq) (((@TCNum) (2))) (@SAWCoreScaffolding.Bool)))
(((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
(@SAWCoreScaffolding.Bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
(((@TCNum) (32))) (@SAWCoreScaffolding.Bool))) (((@CryptolPrimitives.seq)
(((@TCNum) (32))) (@SAWCoreScaffolding.Bool))))) (((prod)
(@SAWCoreScaffolding.Bool) (((prod) (@SAWCoreScaffolding.Bool) (((prod)
(((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool)))
(((prod) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.Bool)))))))))))))))))
:= ((@CryptolPrimitives.ecAt) (((@TCNum) (17))) (((prod)
(((@CryptolPrimitives.seq) (((@TCNum) (8))) (@SAWCoreScaffolding.Bool)))
(((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
(@SAWCoreScaffolding.Bool))) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
(@SAWCoreScaffolding.Bool))))))) (((@TCNum) (32))) (state_machine)
(((ACTIVE_MESSAGE) (conn)))).

Fixpoint seq_to_tuple {T} {n : nat} (s : seq n T) : n.-tuple T :=
  match s with
  | nil => [tuple]
  | cons h _ t => cat_tuple [tuple of [:: h]] (seq_to_tuple t)
  end.

Fixpoint tuple_to_seq {T} {n : nat} (t : n.-tuple T) : seq n T.
  move : n t.
  match t with
  |  => Vector.nil
  end.










Lift HandshakeAction'.cry_handshake_action
     HandshakeAction'.HandshakeAction'
  in S2N'.ACTIVE_STATE
  as stateMachineFn
     { opaque
       S2N'.CryptolToCoq_CryptolPrimitivesForSAWCore_CryptolPrimitives_ecAt
       S2N'.ACTIVE_MESSAGE
       CryptolPrimitives.seq
     }.

Print 42.

(*

// A model of the handshake states (array state_machine in C)
state_machine : [17]handshake_action
state_machine = [state_machine_fn m | m <- [0..16]]

// Function that tells a handshake_action for a given state
state_machine_fn : [5] -> handshake_action
state_machine_fn m =
  if      m == CLIENT_HELLO then mkAct TLS_HANDSHAKE TLS_CLIENT_HELLO 'C'
  else if m == SERVER_SESSION_LOOKUP then mkAct TLS_HANDSHAKE TLS_SERVER_SESSION_LOOKUP 'A'
  else if m == SERVER_HELLO then mkAct TLS_HANDSHAKE TLS_SERVER_HELLO 'S'
  else if m == SERVER_NEW_SESSION_TICKET then mkAct TLS_HANDSHAKE TLS_SERVER_NEW_SESSION_TICKET 'S'
  else if m == SERVER_CERT then mkAct TLS_HANDSHAKE TLS_SERVER_CERT 'S'
  else if m == SERVER_CERT_STATUS then mkAct TLS_HANDSHAKE TLS_SERVER_CERT_STATUS 'S'
  else if m == SERVER_KEY then mkAct TLS_HANDSHAKE TLS_SERVER_KEY 'S'
  else if m == SERVER_CERT_REQ then mkAct TLS_HANDSHAKE TLS_SERVER_CERT_REQ 'S'
  else if m == SERVER_HELLO_DONE then mkAct TLS_HANDSHAKE TLS_SERVER_HELLO_DONE 'S'
  else if m == CLIENT_CERT then mkAct TLS_HANDSHAKE TLS_CLIENT_CERT 'C'
  else if m == CLIENT_KEY then mkAct TLS_HANDSHAKE TLS_CLIENT_KEY 'C'
  else if m == CLIENT_CERT_VERIFY then mkAct TLS_HANDSHAKE TLS_CLIENT_CERT_VERIFY 'C'
  else if m == CLIENT_CHANGE_CIPHER_SPEC then mkAct TLS_CHANGE_CIPHER_SPEC 0 'C'
  else if m == CLIENT_FINISHED then mkAct TLS_HANDSHAKE TLS_CLIENT_FINISHED 'C'
  else if m == SERVER_CHANGE_CIPHER_SPEC then mkAct TLS_CHANGE_CIPHER_SPEC 0 'S'
  else if m == SERVER_FINISHED then mkAct TLS_HANDSHAKE TLS_SERVER_FINISHED 'S'
  else if m == APPLICATION_DATA then mkAct TLS_APPLICATION_DATA 0 'B'
  else zero

 *)
