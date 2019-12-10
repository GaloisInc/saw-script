From Bits Require Import operations.
From Bits Require Import spec.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Program.Equality.
From Coq Require Import Vector.

From CryptolToCoq Require Import Cryptol_proofs.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import S2N.
From CryptolToCoq Require Import S2N.Embedding.
From CryptolToCoq Require Import S2N.Pointed.

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

Record HandshakeAction := MkHandshakeAction
  {
    recordType  : 8.-tuple bool;
    messageType : 8.-tuple bool;
    writer      : 8.-tuple bool;
  }.

Global Instance Embedding_HandshakeAction
  : Embedding (seq 8 bool * (seq 8 bool * seq 8 bool)) HandshakeAction :=
  {|
    toAbstract :=
      fun '(a, (b, c)) =>
        {|
          messageType := toAbstract a; (* Cryptol sorts the fields *)
          recordType  := toAbstract b;
          writer      := toAbstract c;
        |}
    ;
    toConcrete :=
      fun c =>
        ( toConcrete (messageType c)
        , ( toConcrete (recordType c)
          , toConcrete (writer c)
          )
        )
    ;
  |}.

Global Instance Pointed_HandshakeAction : Pointed HandshakeAction :=
  {|
    pointed :=
      {|
        recordType  := pointed;
        messageType := pointed;
        writer      := pointed;
      |};
  |}.
