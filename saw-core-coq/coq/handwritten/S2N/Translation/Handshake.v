From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.

From S2N Require Import Embedding.
From S2N Require Import Pointed.

From mathcomp Require Import tuple.

Import CryptolPrimitives.

Definition cry_handshake : Type
  := (seq 32 bool * seq 32 bool).

Record Handshake := MkHandshake
  {
    handshakeType : 32.-tuple bool;
    messageNumber : 32.-tuple bool;
  }.

Global Instance Embedding_Handshake
    : Embedding cry_handshake Handshake :=
    {|
      toAbstract :=
        fun '(a, b) =>
          {|
            handshakeType := toAbstract a; (* Cryptol sorts the fields *)
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

Global Instance Pointed_Handshake : Pointed Handshake :=
  {|
    pointed :=
      {|
        handshakeType := pointed;
        messageNumber := pointed;
      |};
  |}.
