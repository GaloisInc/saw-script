From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.

From S2N Require Import Embedding.
From S2N Require Import Pointed.
From S2N Require Import Translation.Handshake.

From mathcomp Require Import tuple.

Import CryptolPrimitives.

Definition cry_connection : Type
  := (bool (* client_auth_flag *)
      * (seq 2 bool (* corked *)
         * (seq 8 bool (* corked_io *)
            * (cry_handshake
               * (bool (* is_caching_enabled *)
                  * (bool (* key_exchange_eph *)
                     * (seq 32 bool (* mode *)
                        * (bool (* resume_from_cache *)
                           * bool (* server_can_send_ocsp *)
                        )
                     )
                  )
               )
            )
         )
      )
  )
.

Record Connection         := MkConnection
{
  handshake             : Handshake;
  mode                  : 32.-tuple bool;
  corkedIO              : 8.-tuple bool;
  corked                : 2.-tuple bool;
  isCachingEnabled      : bool;
  resumeFromCache       : bool;
  serverCanSendOCSP     : bool;
  keyExchangeEPH        : bool;
  clientAuthFlag        : bool;
}.

Global Instance Embedding_Connection
  : Embedding cry_connection Connection :=
  {|
    toAbstract :=
      fun '(a, (b, (c, (d, (e, (f, (g, (h, i)))))))) =>
        {| (* Cryptol sorts the fields *)
          clientAuthFlag        := toAbstract a;
          corked                := toAbstract b;
          corkedIO              := toAbstract c;
          handshake             := toAbstract d;
          isCachingEnabled      := toAbstract e;
          keyExchangeEPH        := toAbstract f;
          mode                  := toAbstract g;
          resumeFromCache       := toAbstract h;
          serverCanSendOCSP     := toAbstract i;
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
                                      , toConcrete (serverCanSendOCSP c
                                      )
                                  )
                              )
                          )
                      )
                  )
              )
          )
        )
    ;
  |}.

Global Instance Pointed_Connection : Pointed Connection :=
  {|
    pointed :=
      {|
        handshake             := pointed;
        mode                  := pointed;
        corkedIO              := pointed;
        corked                := pointed;
        isCachingEnabled      := pointed;
        resumeFromCache       := pointed;
        serverCanSendOCSP     := pointed;
        keyExchangeEPH        := pointed;
        clientAuthFlag        := pointed;
      |};
  |}.
