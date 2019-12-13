From Bits Require Import operations.
From Bits Require Import properties.
From Bits Require Import spec.

From Coq Require Import Lists.List.
From Coq Require Import Morphisms.
From Coq Require Import String.
From Coq Require Import Program.Equality.
From Coq Require Import Vector.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import S2N.
From CryptolToCoq Require Import S2N.Embedding.
From CryptolToCoq Require Import S2N.Pointed.
From CryptolToCoq Require Import S2N.Translation.HandshakeAction.

From mathcomp Require Import eqtype.
From mathcomp Require Import fintype.
From mathcomp Require Import seq.
From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrbool.
From mathcomp Require Import ssrnat.
From mathcomp Require Import tuple.

Import CryptolPrimitives.
Import ListNotations.
Import SAWCorePrelude.
Import VectorNotations.

Scheme Induction for tuple_of Sort Prop.
Scheme Induction for tuple_of Sort Set.
Scheme Induction for tuple_of Sort Type.

Scheme Induction for eqtype.Sub_spec Sort Prop.
Scheme Induction for eqtype.Sub_spec Sort Set.
Scheme Induction for eqtype.Sub_spec Sort Type.

Scheme Induction for eqtype.Equality.type Sort Prop.
Scheme Induction for eqtype.Equality.type Sort Set.
Scheme Induction for eqtype.Equality.type Sort Type.

Scheme Induction for eqtype.Equality.mixin_of Sort Prop.
Scheme Induction for eqtype.Equality.mixin_of Sort Set.
Scheme Induction for eqtype.Equality.mixin_of Sort Type.

Scheme Induction for eqtype.subType Sort Prop.
Scheme Induction for eqtype.subType Sort Set.
Scheme Induction for eqtype.subType Sort Type.

Scheme Induction for eqtype.insub_spec Sort Prop.
Scheme Induction for eqtype.insub_spec Sort Set.
Scheme Induction for eqtype.insub_spec Sort Type.

From Ornamental Require Import Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)

(* Preprocess *)
(*   Module *)
(*   SAWCorePrelude *)
(*   as SAWCorePrelude' *)
(*        { opaque *)
(*            SAWCoreScaffolding.error *)
(*            SAWCorePrelude.intToBv *)
(*            SAWCorePrelude.bvToInt *)
(*            mathcomp.ssreflect.ssrnat.half *)
(*            Nat.even *)
(*            Coq.Init.Nat.pred *)
(*        } . *)


(** [cry_handshake] is the [handshake] type as it comes out of the translation
from Cryptol to Coq.  The fields have been inlined into a nested tuple type.

This is what the original [handshake] type looked like:

type handshake = {handshake_type : [32]
                 ,message_number : [32]
                 }
 *)
Definition cry_handshake :=
  ((prod) (((@CryptolPrimitives.seq)
              (((@TCNum) (32)))
              (@SAWCoreScaffolding.Bool)))
          (((@CryptolPrimitives.seq)
              (((@TCNum) (32)))
              (@SAWCoreScaffolding.Bool)))).

(** Same for [cry_connection] and Cryptol's [connection].  Note that we could
inline [cry_handshake] in place of the [handshake] since those type definitions
are completely structural.

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
Definition cry_connection :=
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
                 (* handshake *)
                 (((prod)
                     (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool)))
                     (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool)))))
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

Local Open Scope form_scope.

(** We can define more convenient types for [handshake] and [connection] in Coq.
Ideally, we'd like the translation to generate those, but in its current state,
it goes through an intermediate language that does not support records and
record types.
*)
Record Handshake :=
  MkHandshake
    {
      handshakeType : BITS 32;
      messageNumber : BITS 32;
    }.

Ltac simplHandshake :=
  cbv
    [
      handshakeType
        messageNumber
    ].

Record Connection :=
  MkConnection
    {
      clientAuthFlag    : bool;
      corked            : BITS 2;
      corkedIO          : BITS 8;
      handshake         : Handshake;
      isCachingEnabled  : bool;
      keyExchangeEPH    : bool;
      mode              : BITS 32;
      resumeFromCache   : bool;
      serverCanSendOCSP : bool;
    }.

Ltac simplConnection :=
  cbv
    [
      clientAuthFlag
        corked
        corkedIO
        handshake
        isCachingEnabled
        keyExchangeEPH
        mode
        resumeFromCache
        serverCanSendOCSP
    ].

Notation "a || b" := (operations.orB a b).

(** The function [conn_set_handshake_type] as we obtain it after translation is
quite unreadable. *)
Print conn_set_handshake_type.

(** Reasoning about it would get quite messy.  We can instead "copy" its
original code and adapt it to work with [Connection]. *)
Definition connSetHandshakeType (conn : Connection) : Connection :=
  let fullHandshake :=
      if (isCachingEnabled conn && negb (resumeFromCache conn))%bool
      then # 0
      else toAbstract FULL_HANDSHAKE
  in
  let perfectForwardSecrecy :=
      if keyExchangeEPH conn
      then toAbstract PERFECT_FORWARD_SECRECY
      else # 0
  in
  let ocspStatus :=
      if serverCanSendOCSP conn
      then toAbstract OCSP_STATUS
      else # 0
  in
  let clientAuth :=
      if clientAuthFlag conn
      then toAbstract CLIENT_AUTH
      else # 0
  in
  let handshakeType' :=
      (
        toAbstract NEGOTIATED
        || (fullHandshake
           || if ~~ (fullHandshake == #0)
             then perfectForwardSecrecy || ocspStatus || clientAuth
             else # 0
          )
      ) in
  let handshake' :=
      {|
        handshakeType := handshakeType';
        messageNumber := messageNumber (handshake conn);
      |}
  in
  {|
    handshake         := handshake';
    mode              := mode conn;
    corkedIO          := corkedIO conn;
    corked            := corked conn;
    isCachingEnabled  := isCachingEnabled  conn;
    resumeFromCache   := resumeFromCache   conn;
    serverCanSendOCSP := serverCanSendOCSP conn;
    keyExchangeEPH    := keyExchangeEPH    conn;
    clientAuthFlag    := clientAuthFlag    conn;
  |}.

Definition cry_handshakes := handshakes.

Definition handshakes : 128.-tuple (32.-tuple (32.-tuple bool))
  := toAbstract cry_handshakes.

Definition cry_state_machine := state_machine.

Definition state_machine
  : 17.-tuple HandshakeAction
  := toAbstract cry_state_machine.

Definition s2nCork (c : Connection) : 2.-tuple bool
  := incB (corked c).

Definition s2nUncork (c : Connection) : 2.-tuple bool
  := decB (corked c).

Definition ascii_A : 8.-tuple bool := fromNat 65.
Definition ascii_C : 8.-tuple bool := fromNat 67.
Definition ascii_S : 8.-tuple bool := fromNat 83.

Definition S2N_CLIENT : 32.-tuple bool := fromNat 1.

Definition modeWriter (m : 32.-tuple bool) : 8.-tuple bool :=
  if m == S2N_CLIENT
  then ascii_C
  else ascii_S.

Definition advanceMessage (conn : Connection) : Connection :=

  let handshake' :=
      {|
        handshakeType := handshakeType (handshake conn);
        messageNumber := incB (messageNumber (handshake conn));
      |}
  in

  let activeState' :=
      (nth pointed
         state_machine
         (toNat
            (nth pointed
                 (nth pointed
                      handshakes
                      (toNat (messageNumber handshake'))
                 )
                 (toNat (handshakeType handshake'))
            )
         )
      )
  in

  let previousState' :=
      (nth pointed
         state_machine
         (toNat
            (nth pointed
                 (nth pointed
                      handshakes
                      (toNat (messageNumber handshake') - 1)
                 )
                 (toNat (handshakeType handshake'))
            )
         )
      )
  in

  let corked' :=
      if (
          (writer activeState' != writer previousState')
            &&
            (writer activeState' != ascii_A)
         )
      then
        if writer activeState' == modeWriter (mode conn)
        then s2nCork conn
        else s2nUncork conn
      else corked conn
  in

  {|
    handshake         := handshake';
    mode              := mode conn;
    corkedIO          := corkedIO conn;
    corked            := corked';
    isCachingEnabled  := isCachingEnabled  conn;
    resumeFromCache   := resumeFromCache   conn;
    serverCanSendOCSP := serverCanSendOCSP conn;
    keyExchangeEPH    := keyExchangeEPH    conn;
    clientAuthFlag    := clientAuthFlag    conn;
  |}.

Lemma gen_getBit_shift
  : forall n h (t : n.-tuple bool),
    gen n bool (fun n => getBit [tuple of h :: t] n.+1)
    =
    gen n bool (fun n => getBit t n).
Proof.
  elim.
  {
    move => h t.
    rewrite [t] tuple0.
    simpl.
    reflexivity.
  }
  {
    move => n I h.
    case / tupleP => h' t.
    simpl.
    rewrite (I h').
    reflexivity.
  }
Qed.

Lemma gen_getBit
  : forall n s,
    gen n bool (fun i => getBit (n := n) (seq_to_tuple s) i) = s.
Proof.
  simpl.
  apply Vector.t_ind.
  {
    reflexivity.
  }
  {
    move => h n t IH.
    simpl.
    rewrite gen_getBit_shift.
    rewrite IH.
    unfold getBit.
    simpl.
    reflexivity.
  }
Qed.

Lemma toAbstract_gen_getBit
  : forall n v,
    seq_to_tuple (gen n bool (fun i => getBit (n := n) v i)) = v.
Proof.
  elim.
  {
    move => v.
    rewrite [v] tuple0.
    reflexivity.
  }
  {
    move => n I.
    case / tupleP => h t.
    simpl.
    rewrite gen_getBit_shift.
    rewrite I.
    unfold getBit.
    simpl.
    apply val_inj.
    simpl.
    reflexivity.
  }
Qed.

Theorem genOrdinal_toConcrete A B `{Embedding A B} n (f : 'I_n -> B)
  : genOrdinal n A (fun i => toConcrete (f i))
    =
    Vector.map toConcrete (genOrdinal n B f).
Proof.
  move : n f.
  elim => [|n' IH] f.
  {
    reflexivity.
  }
  {
    simpl.
    f_equal.
    rewrite IH.
    reflexivity.
  }
Qed.

Global Instance Proper_Vector_map {A B n} (f : A -> B) :
  Proper (eq ==> eq) (Vector.map (n := n) f).
Proof.
  move => x y XY.
  subst x.
  reflexivity.
Qed.

Global Instance Proper_toConcrete {A B} `{Embedding A B} :
  Proper (eq ==> eq) toConcrete.
Proof.
  move => x y XY.
  subst x.
  reflexivity.
Qed.

Global Instance Embedding_Handshake
  : Embedding cry_handshake Handshake :=
  {|
    toAbstract :=
      fun '(a, b) =>
        {|
          handshakeType := toAbstract a;
          messageNumber := toAbstract b;
        |}
    ;
    toConcrete :=
      fun c =>
        ( toConcrete (handshakeType c)
        , toConcrete (messageNumber c)
        )
    ;
  |}.

Variant ubn_eq_spec m : nat -> Type := UbnEq n of m == n : ubn_eq_spec m n.
Lemma ubnPeq m : ubn_eq_spec m m.      Proof. by []. Qed.

Lemma gen_getBit'
  : forall n v, gen n bool (fun i => getBit (n := n) (toAbstract v) i) = v.
Proof.
  simpl.
  apply Vector.t_ind.
  {
    simpl.
    reflexivity.
  }
  {
    move => h n t IH.
    simpl.
    setoid_rewrite IH.
    compute.
    reflexivity.
  }
Qed.

Global Instance ProperEmbedding_Handshake
  : ProperEmbedding Embedding_Handshake.
Proof.
  constructor.
  intros [].
  rewrite / toAbstract / toConcrete.
  rewrite / Embedding_Handshake.
  rewrite / handshakeType / messageNumber.
  rewrite roundtrip.
  rewrite roundtrip.
  reflexivity.
Qed.

Global Instance Embedding_Connection
  : Embedding cry_connection Connection :=
  {|
    toAbstract :=
      fun '(a, (b, (c, (d, (e, (f, (g, (h, i)))))))) =>
        {|
          clientAuthFlag    := toAbstract a;
          corked            := toAbstract b;
          corkedIO          := toAbstract c;
          handshake         := toAbstract d;
          isCachingEnabled  := toAbstract e;
          keyExchangeEPH    := toAbstract f;
          mode              := toAbstract g;
          resumeFromCache   := toAbstract h;
          serverCanSendOCSP := toAbstract i;
        |}
    ;
    toConcrete :=
      fun c =>
          ( toConcrete (clientAuthFlag c)
          , ( toConcrete (corked c)
            , ( toConcrete (corkedIO c)
              , ( toConcrete (handshake c)
                , ( toConcrete (isCachingEnabled c)
                  , ( toConcrete (keyExchangeEPH c)
                    , ( toConcrete (mode c)
                      , ( toConcrete (resumeFromCache c)
                        , toConcrete (serverCanSendOCSP c)
                        )
                      )
                    )
                  )
                )
              )
            )
          )
  |}.

Global Instance ProperEmbedding_Connection
  : ProperEmbedding Embedding_Connection.
Proof.
  constructor.
  intros [?[?[?[[][?[?[?[?]]]]]]]].
  cbn - [ genOrdinal ].
  repeat rewrite map_tuple_id.
  repeat rewrite genOrdinal_tnth.
  reflexivity.
Qed.

Class CorrectTranslation
      {CI AI CO AO}
      `{ProperEmbedding CI AI}
      `{ProperEmbedding CO AO}
      (concreteFun : CI -> CO) (abstractFun : AI -> AO)
  :=
    {
      correctTranslation :
        forall ci ai co ao,
          toAbstract ci = ai ->
          concreteFun ci = co ->
          abstractFun ai = ao ->
          toAbstract co = ao;
    }.

Theorem byCorrectTranslation
        {CI AI CO AO}
        (concreteFun : CI -> CO) (abstractFun : AI -> AO)
        `{CT : CorrectTranslation _ _ _ _ concreteFun abstractFun}
  : forall ci, concreteFun ci = toConcrete (abstractFun (toAbstract ci)).
Proof.
  move => ci.
  destruct CT as [CT].
  specialize (CT ci _ _ _ (Logic.eq_refl _) (Logic.eq_refl) (Logic.eq_refl)).
  apply f_equal with (f := toConcrete) in CT.
  rewrite roundtrip in CT.
  apply CT.
Qed.

Theorem ecOr_cons m h1 h2 t1 t2
  : ecOr (Vec m.+1 bool) (PLogicWord m.+1) (h1 :: t1) (h2 :: t2)
    =
    Vector.cons _ (or h1 h2) _ (ecOr (Vec m bool) (PLogicWord m) t1 t2).
Proof.
  move : t1 t2.
  apply (Vector.t_ind _ (fun n v => forall b, _ = _)) with (n := m).
  {
    elim / @Vector.case0.
    compute.
    reflexivity.
  }
  {
    move => h n t IH b.
    move : b t IH.
    elim / @Vector.caseS => h' n' t' t IH.

    rewrite / ecOr.
    simpl.
    unfold Notation.Rget.
    simpl.
    rewrite / bvOr.
    rewrite / bvZipWith.
    rewrite / zipWith.
    simpl.
    f_equal.
  }
Qed.

Theorem seq_to_tuple_ecOr
  : forall {n} a b,
    seq_to_tuple (ecOr (Vec n bool) (PLogicWord n) a b)
    =
    seq_to_tuple a || seq_to_tuple b.
Proof.
  move => n.
  apply (Vector.t_ind _ (fun n v => forall b, _ = _)) with (n0 := n).
  {
    simpl.
    apply case0.
    apply val_inj.
    reflexivity.
  }
  {
    move => h m t IH b.
    move : m b t IH.
    apply (caseS (fun n v => forall t, _ -> _)).
    move => h' m b t IH.
    rewrite ecOr_cons.
    simpl.
    apply val_inj.
    rewrite IH.
    simpl.
    reflexivity.
  }
Qed.

Theorem shiftin_false_zero n
  : shiftin false (bvNat n 0) = bvNat n.+1 0.
Proof.
  reflexivity.
Qed.

Theorem bvNat_S_zero n
  : bvNat n.+1 0 = Vector.append (Vector.cons _ false _ (Vector.nil _)) (bvNat n 0).
Proof.
  simpl.
  induction n.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite IHn.
    unfold joinLSB.
    simpl.
    rewrite shiftin_false_zero.
    simpl.
    now rewrite IHn.
  }
Qed.

Theorem append_assoc :
  forall {T} {sa} (a : Vector.t T sa)
    {sb} (b : Vector.t T sb)
    {sc} (c : Vector.t T sc)
  , existT (fun s => Vector.t T s) _ (Vector.append (Vector.append a b) c)
    =
    existT (fun s => Vector.t T s) _ (Vector.append a (Vector.append b c)).
Proof.
  move => T sa a sb b sc c.
  move : a.
  apply (Vector.t_ind T (fun a sa => _)) with (n := sa).
  {
    simpl.
    reflexivity.
  }
  {
    move => h n t IH.
    simpl.
    dependent rewrite IH.
    reflexivity.
  }
Qed.

Theorem decompose_bvNat_sum
  : forall m n x,
    bvNat (m + n) x
    =
    Vector.append
      (bvNat m (iter n (fun n => n./2) x))
      (bvNat n x).
Proof.
  elim.
  {
    simpl.
    reflexivity.
  }
  {
    move => m' IH n x.
    simpl.
    admit.
  }
Admitted.

Theorem append_bvNat_is_padding' m n x
  : n > Nat.log2 x ->
    Vector.append (bvNat m 0) (bvNat n x) = bvNat (m + n) x.
Proof.
  move : m n x.
  elim.
  {
    reflexivity.
  }
  {
    move => n IH m x L.
    rewrite bvNat_S_zero.
    simpl.
    rewrite (IH _ _ L).
    unfold bvNat.
    (* This is tedious to prove, skipping it since low interest *)
    admit.
  }
Admitted.

Ltac crunchTheNumbersStep :=
  reflexivity

  +

  (* Try breaking boolean variables that block "if"s *)
  match goal with
  | [ |- context [ if ?b then _ else _ ] ] => is_var b; destruct b
  end

  +

  (* Try breaking other boolean variables *)
  match goal with
  | [ b : Bool |- _ ] => destruct b
  end

.

Ltac crunchTheNumbers := repeat crunchTheNumbersStep.

Theorem t_for_n_equal_1 v :
  let n := 1 in
  ecPlus (Vec n bool) (PArithSeqBool n) v (ecNumber 1 (Vec n bool) (PLiteralSeqBool n))
  =
  toConcrete (incB (seq_to_tuple v)).
Proof.
  do 2 dependent destruction v.
  move : h.
  elim => /=.
  {
    cbv -[bvAdd].
    rewrite / bvAdd /=.
    rewrite toNat_addB.
    cbv.
    reflexivity.
  }
  {
    cbv -[bvAdd].
    rewrite / bvAdd /=.
    rewrite toNat_addB.
    cbv.
    reflexivity.
  }
Qed.

Theorem resolve_ecPlus_Vec n a b
  : ecPlus (Vec n bool) (PArithSeqBool n) a b = bvAdd n a b.
Proof.
  reflexivity.
Qed.

Theorem half_toNat s (n : BITS s.+1) : (toNat n)./2 = toNat (droplsb n).
Proof.
Admitted.

Goal
    let n : BITS 3 := decB (ones 3) in
    bvNat _ (toNat n) = toConcrete n.
  unfold toConcrete.
  compute.
  (* 6 *)

Theorem bvNat_toNat size (n : BITS size)
  : bvNat size (toNat n) = toConcrete n.
Proof.
  cbv -[bvNat toNat genOrdinal tnth].
  move : size n.
  elim => [|s IH] n.
  {
    reflexivity.
  }
  {
    rewrite /=.
    rewrite half_toNat.
    rewrite IH.
    rewrite / joinLSB.
    TODO.
    unfol
      rewrite / toNat.
    specialize (IH (toNat n)./2).
    unfold tnth.
    unfold joinLSB.
    unfold shiftin.
    simpl.
  }
  unfold BITS in n.
  unfold toConcrete.
Qed.

Theorem todo a b
  : bvAdd n a b = toConcrete (addB (seq_to_tuple a) (seq_to_tuple b)).
Proof.
  rewrite / bvAdd.

  reflexivity.
Qed.

Theorem t v :
  ecPlus (Vec 32 bool) (PArithSeqBool 32) v (ecNumber 1 (Vec 32 bool) (PLiteralSeqBool 32))
  =
  toConcrete (incB (seq_to_tuple v)).
Proof.
  rewrite resolve_ecPlus_Vec.
  do 33 dependent destruction v.

  simpl.
  crunchTheNumbers.

  rewrite / incB.


  cbv -[ecPlus seq_to_tuple ecNumber PLiteralSeqBool PArithSeqBool].
  cbv [seq_to_tuple cat_tuple].
  cbv -[toConcrete seq_to_tuple].
  rewrite / ecPlus.
  unfold Notation.Rget.
  cbv [
      CoreRecords.record_get
        CoreRecords.get_member
        CoreRecords.Fields
        CoreRecords.fields_insert
        CoreRecords.ascii_to_p
        CoreRecords.bool_to_p
        CoreRecords.string_to_p
        CoreRecords.record_left
        CoreRecords.record_right
    ].
  reflexivity.
Qed.

Global Instance
       CorrectTranslation_connSetHandshakeType
  : CorrectTranslation conn_set_handshake_type connSetHandshakeType.
Proof.
  constructor.
  move => ci.
  repeat (match goal with [ a : _ * _ |- _ ] => destruct a end).
  unfold conn_set_handshake_type.
  cbv [fst snd Datatypes.fst Datatypes.snd].
  move => ai co ao AI CO AO.
  subst ai.
  subst co.
  subst ao.
  unfold connSetHandshakeType.
  simplConnection.
  cbv [
      toAbstract
        Embedding_Connection
        Embedding_Handshake
        Embedding_seq_tuple
        Embedding_Bool
    ].
  repeat setoid_rewrite map_tuple_id.
  f_equal.
  f_equal.
  repeat rewrite seq_to_tuple_ecOr.
  f_equal.
  apply val_inj.
  destruct b1, b3, b, b0, b2; reflexivity.
Qed.

Global Instance
       CorrectTranslation_advanceMessage
  : CorrectTranslation advance_message advanceMessage.
Proof.
  constructor => ca.
  repeat (match goal with [ a : _ * _ |- _ ] => destruct a end).
  move => ai co ao AI CO AO.
  subst ai.
  subst co.
  subst ao.
  rewrite / advance_message.
  cbv [fst snd Datatypes.fst Datatypes.snd].
  cbv [
      toAbstract
        Embedding_Connection
        Embedding_Handshake
        Embedding_seq_tuple
        Embedding_Bool
    ].
  repeat rewrite map_tuple_id.
  rewrite / advanceMessage.
  simplConnection.
  simplHandshake.
  f_equal.
  {
    destruct and eqn:A.
    {
      destruct (_ && _) eqn:B.
      {
        destruct ecEq eqn:C.
        {
          destruct (writer _ == modeWriter _) eqn:D.
          {
            admit.
          }
          {
            (* C and D should agree *)
            exfalso.
            clear A B.
            move : s3 C D.
            unfold seq.
            cbv [Num_rect].


            pose proof (@Vector.caseS Bool) as V.
            apply (V (fun n v => _ = true -> _)). with (n := 31).
            apply (@Vector.caseS _ (fun n v => ecEq _ _ _ _ = true -> _)) with (n := 31).
            dependent destruction s3.
          }
        }
      }

    }
    {
      admit.
    }
    rewrite / S2N.state_machine.
    unfold ecAt.
    simpl.
    rewrite / corked.
    cbv [ecAt Num_rect].
    cbv [bvAt sawAt].
    cbv [corked].
    cbv [s2n_cork ecPlus].
    unfold Notation.Rget.
    simpl.
    rewrite /=.
  }

Qed.

(* The 2-bit vector must always be between 0 and 1.  In other terms, the bit of
order 1 should always remain equal to 0. *)
Definition in_bounds_corked : forall (corked : seq 2 bool), Prop.
  rewrite / seq /= / Vec.
  elim / @Vector.caseS => b1 _ _.
  exact (b1 = false).
Defined.

Definition in_bounds_corked_connection (conn : cry_connection) : Prop :=
  in_bounds_corked (fst (snd conn)).

Ltac destruct_cry_connection :=
  move =>
  [ client_auth_flag
      [ corked
          [ corked_io
              [ handshake
                  [ is_caching_enabled
                      [ key_exchange_eph
                          [ mode
                              [ resume_from_cache
                                  server_can_send_ocsp
                              ]
                          ]
                      ]
                  ]
              ]
          ]
      ]
  ].

Definition inBoundsCorked : forall (corked : BITS 2), Prop.
  case / tupleP => b1 _.
  exact (b1 = false).
Defined.

Definition inBoundsCorkedConnection (conn : Connection) : Prop :=
  inBoundsCorked (corked conn).

Theorem noDoubleCorkUncork_connSetHandshakeType
  : forall conn,
    inBoundsCorkedConnection conn ->
    inBoundsCorkedConnection (connSetHandshakeType conn).
Proof.
  move => conn IB.
  unfold connSetHandshakeType.
  rewrite / inBoundsCorkedConnection.
  simpl.
  apply IB.
Qed.

Theorem noDoubleCorkUncork_advanceMessage
  : forall conn,
    inBoundsCorkedConnection conn ->
    inBoundsCorkedConnection (connSetHandshakeType conn).
Proof.
  move => conn IB.
  unfold connSetHandshakeType.
  rewrite / inBoundsCorkedConnection.
  simpl.
  apply IB.
Qed.

Theorem noDoubleCorkUncork
  : forall conn,
    in_bounds_corked_conn conn ->
    in_bounds_corked_conn (s2nTrans conn).
Proof.
  destruct_cry_connection.
  rewrite / in_bounds_corked_conn.
  rewrite [s2nTrans]lock /= -lock => IB.
  rewrite / s2nTrans.
  destruct orB eqn:D1.
  {
    rewrite byCorrectTranslation.
    rewrite / connSetHandshakeType.
    cbn.
    rewrite [advance_message]lock.
    rewrite [connSetHandshakeType]lock.
    rewrite /=.
    rewrite / conn_set_handshake_type.
    cbv [fst snd Datatypes.fst Datatypes.snd].
  }
Qed.

Definition s2nTrans (conn : ((prod) (@SAWCoreScaffolding.Bool) (((prod)
                                                                   (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@SAWCoreScaffolding.Bool)))
                                                                   (((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
                                                                                                       (@SAWCoreScaffolding.Bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
                                                                                                                                                          (((@TCNum) (32))) (@SAWCoreScaffolding.Bool))) (((@CryptolPrimitives.seq)
                                                                                                                                                                                                             (((@TCNum) (32))) (@SAWCoreScaffolding.Bool))))) (((prod)
                                                                                                                                                                                                                                                                  (@SAWCoreScaffolding.Bool) (((prod) (@SAWCoreScaffolding.Bool) (((prod)
                                                                                                                                                                                                                                                                                                                                     (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool)))
                                                                                                                                                                                                                                                                                                                                     (((prod) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.Bool)))))))))))))))))
  := ((advance_message) (if ((orB) (((@CryptolPrimitives.ecEq)
                                       (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool)))
                                       (((@CryptolPrimitives.PCmpSeqBool) (((@TCNum) (32))))) (((ACTIVE_MESSAGE)
                                                                                                  (conn))) (((CLIENT_HELLO) (((@CryptolPrimitives.seq) (((@TCNum) (32)))
                                                                                                                                                       (@SAWCoreScaffolding.Bool))) (((@CryptolPrimitives.PLiteralSeqBool) (((@TCNum)
                                                                                                                                                                                                                               (32))))))))) (((@CryptolPrimitives.ecEq) (((@CryptolPrimitives.seq) (((@TCNum)
                                                                                                                                                                                                                                                                                                       (32))) (@SAWCoreScaffolding.Bool))) (((@CryptolPrimitives.PCmpSeqBool)
                                                                                                                                                                                                                                                                                                                                               (((@TCNum) (32))))) (((ACTIVE_MESSAGE) (conn))) (((SERVER_HELLO)
                                                                                                                                                                                                                                                                                                                                                                                                   (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@SAWCoreScaffolding.Bool)))
                                                                                                                                                                                                                                                                                                                                                                                                   (((@CryptolPrimitives.PLiteralSeqBool) (((@TCNum) (32)))))))))) then
                           ((conn_set_handshake_type) (conn)) else conn)).
