
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Bool.Bool.
From Coq          Require Import Equalities.
From Coq          Require Import Classes.EquivDec.
From Coq          Require Import Program.Equality.
From Coq          Require Import PArith.BinPos.
From Coq          Require Import FSets.FMapPositive.
From CryptolToCoq Require Import CtxInterface.
From CryptolToCoq Require Import CtxPositive.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import CompM.

From CryptolToCoq Require Import CompRefl.Utils.

Import ListNotations.

Lemma refinesM_bind_f_equal {A B} (m1 m2 : CompM A) (f1 f2 : A -> CompM B) :
  m1 |= m2 -> (forall a, f1 a |= f2 a) ->
  m1 >>= f1 |= m2 >>= f2.
Proof.
  unfold refinesM, bindM, MonadBindOp_OptionT, bindM, MonadBindOp_SetM.
  intros ref_m ref_f b H.
  destruct H as [a ?H ?H]; exists a; eauto.
  destruct a; eauto.
Qed.


(** * Types, names, and contexts *)

Inductive type : Type :=
| TypeT : nat -> type
| unitT : type
| EitherT : type -> type -> type
| prodT : type -> type -> type
| listT : type -> type
.
Inductive fmtype : Type :=
| FunMT : type -> fmtype -> fmtype
| CompMT : type -> fmtype
.

Definition type_decEq (x y : type) : {x = y} + {x <> y}.
Proof. repeat (decide equality). Defined.

Module UsualDecidableType_type <: UsualDecidableType.
  Definition t := type.
  Definition eq := @eq type.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_equiv := @eq_equivalence type.
  Definition eq_dec := type_decEq.
End UsualDecidableType_type.

Module Ctx.
  Module PositiveCtxDefs := PositiveMapCtx UsualDecidableType_type.
  Include PositiveCtxDefs.
  Include CtxExtras UsualDecidableType_type PositiveCtxDefs.
End Ctx.
Export Ctx(name, ctx).
Opaque Ctx.ext.


Section env.

(** * Denotations of types *)

Variable typeEnv : list Set.
Definition nthTypeEnv (i : nat) := nth i typeEnv Empty_set.

Fixpoint typeD (t : type) : Set :=
  match t with
  | TypeT i => nthTypeEnv i
  | unitT => unit
  | EitherT tl tr => SAWCorePrelude.Either (typeD tl) (typeD tr)
  | prodT tl tr => prod (typeD tl) (typeD tr)
  | listT t => list (typeD t)
  end.

(* Fixpoint fmtypeD (fmt : fmtype) : Type := *)
(*   match fmt with *)
(*   | FunMT t fmt => typeD t -> fmtypeD fmt *)
(*   | CompMT t => CompM (typeD t) *)
(*   end. *)

Fixpoint fmtypeD (fmt : fmtype) : LetRecType :=
  match fmt with
  | FunMT t fmt => LRT_Fun (typeD t) (fun _ => fmtypeD fmt)
  | CompMT t => LRT_Ret (typeD t)
  end.


(** * Expressions and their denotations *)

Variable propEnv : list Prop.
Definition nthPropEnv (i : nat) := nth i propEnv False.

Inductive expr : type -> Type :=
| varE {t} : name t -> expr t
| termE {t} : typeD t -> expr t
(* | funE {t} : nat -> list { ti & expr ti } -> expr t *)
| ttE : expr unitT
| LeftE tl tr : expr tl -> expr (EitherT tl tr)
| RightE tl tr : expr tr -> expr (EitherT tl tr)
| fstE {tl tr} : expr (prodT tl tr) -> expr tl
| sndE {tl tr} : expr (prodT tl tr) -> expr tr
| pairE {tl tr} : expr tl -> expr tr -> expr (prodT tl tr)
| nilE {t} : expr (listT t)
| consE {t} : expr t -> expr (listT t) -> expr (listT t)
| unfoldListE t : expr (listT t) ->
                  expr (EitherT unitT (prodT t (prodT (listT t) unitT)))
| foldListE t : expr (EitherT unitT (prodT t (prodT (listT t) unitT))) ->
                expr (listT t)
.
Inductive prop : Type :=
| PropP : nat -> prop
| eqP {t} : expr t -> expr t -> prop
| AndP : prop -> prop -> prop
.
Inductive mexpr (t : type) : Type :=
(* | funME : nat -> list { ti & expr ti } -> mexpr t *)
| returnE : expr t -> mexpr t
| bindE {t'} : mexpr t' -> (name t' -> mexpr t) -> mexpr t
| errorE : string -> mexpr t
| eitherE {tl tr} : (name tl -> mexpr t) ->
                    (name tr -> mexpr t) ->
                    expr (EitherT tl tr) -> mexpr t
.
Fixpoint fmexpr (fmt : fmtype) : Type :=
  match fmt with
  | FunMT t fmt => name t -> fmexpr fmt
  | CompMT t => mexpr t
  end
.

Arguments returnE {t}.
Arguments bindE {t t'}.
Arguments errorE {t}.
Arguments eitherE {t tl tr}.

(* Definition Fun (F : type -> Type) args ret := *)
(*   fold_right (fun t T => prod (typeD t) T) unit args -> F ret. *)

(* Definition findFun {F} (env : list { args & { ret & Fun F args ret } }) *)
(*                        (i : nat) (args : list type) (ret : type) : *)
(*   option (Fun F args ret) := *)
(*   match nth_error env i with *)
(*   | Some (existT args' (existT ret' f)) => *)
(*     match list_eq_dec type_decEq args args', type_decEq ret ret' with *)
(*     | left eq_args, left eq_ret => *)
(*       Some (eq_rect_r (fun z => Fun _ z _) *)
(*                       (eq_rect_r (fun z => Fun _ _ z) *)
(*                                  f eq_ret) eq_args) *)
(*     | _,_ => None *)
(*     end *)
(*   | None => None *)
(*   end. *)

(* Definition ExprFun := Fun (fun ret => typeD ret). *)
(* Variable exprFunEnv  : list { args & { ret & ExprFun args ret } }. *)
(* Definition findExprFun := findFun exprFunEnv. *)

(* Definition exprFunD (exprD : forall t, expr t -> string + typeD t) *)
(*            {t} (i : nat) (es : list { t & expr t }) : string + typeD t. *)
(* Proof. *)
(*   destruct (findExprFun i (List.map (fun ai => projT1 ai) es) t). *)
(*   - induction es. *)
(*     + exact (inr (f tt)). *)
(*     + destruct (exprD _ (projT2 a)); eauto. *)
(*       apply IHes; intro; apply f; split; eauto. *)
(*   - exact (inl "[proof automation] function of type not found in context"%string). *)
(* Defined. *)

Fixpoint exprD (c : ctx typeD) {t} (e : expr t) : string + typeD t :=
  match e with
  | varE _ n => match Ctx.find n c with
                | inr x => inr x
                | inl _ => inl "[proof automation] name of type not found in context"%string
                end
  | termE _ x => inr x
  (* | funE _ i es => exprFunD (fun _ e => exprD c e) i es *)
  | ttE => inr tt
  | LeftE  _ tr e => fmapSumR (SAWCorePrelude.Left  _ (typeD tr)) (exprD c e)
  | RightE tl _ e => fmapSumR (SAWCorePrelude.Right (typeD tl) _) (exprD c e)
  | fstE _ _ e => fmapSumR fst (exprD c e)
  | sndE _ _ e => fmapSumR snd (exprD c e)
  | pairE _ _ e1 e2 => apSumR (fmapSumR pair (exprD c e1)) (exprD c e2)
  | nilE _ => inr nil
  | consE _ e1 e2 => apSumR (fmapSumR cons (exprD c e1)) (exprD c e2)
  | unfoldListE t e => fmapSumR (SAWCorePrelude.unfoldList (typeD t)) (exprD c e)
  | foldListE t e => fmapSumR (SAWCorePrelude.foldList (typeD t)) (exprD c e)
  end.

Inductive ErrorP : string -> Prop :=.

Notation propEmbExprD c e f := (fromSum ErrorP f (exprD c e)) (only parsing).

Fixpoint propD (c : ctx typeD) (p : prop) : Prop :=
  match p with
  | PropP i => nthPropEnv i
  | eqP _ e1 e2 => propEmbExprD c e1 (fun x1 => propEmbExprD c e2 (fun x2 => x1 = x2))
  | AndP p1 p2 => propD c p1 /\ propD c p2
  end.

Notation mexprEmbExprD c e f := (fromSum errorM f (exprD c e)) (only parsing).

(* Definition MExprFun := Fun (fun ret => CompM (typeD ret)). *)
(* Variable mexprFunEnv : list { args & { ret & MExprFun args ret } }. *)
(* Definition findMExprFun := findFun mexprFunEnv. *)

(* Definition mexprFunD (c : ctx typeD) *)
(*            {t} (i : nat) (es : list { t & expr t }) : CompM (typeD t). *)
(* Proof. *)
(*   destruct (findMExprFun i (List.map (fun ai => projT1 ai) es) t). *)
(*   - induction es. *)
(*     + exact (f tt). *)
(*     + refine (mexprEmbExprD c (projT2 a) _); intro. *)
(*       apply IHes; intro; apply f; split; eauto. *)
(*   - exact (errorM "[proof automation] function of type not found in context"%string). *)
(* Defined. *)

Fixpoint mexprD (c : ctx typeD) {t} (me : mexpr t) : CompM (typeD t) :=
  match me with
  (* | funME i es => mexprFunD c i es *)
  | returnE e => mexprEmbExprD c e returnM
  | bindE t' e f => bindM (mexprD c e) (Ctx.inExt c (fun n c' => mexprD c' (f n)))
  | errorE s => errorM s
  | eitherE tl tr f g e => mexprEmbExprD c e (fun x =>
      SAWCorePrelude.either _ _ _ (Ctx.inExt c (fun nl cl => mexprD cl (f nl)))
                                  (Ctx.inExt c (fun nr cr => mexprD cr (g nr))) x)
  end.

Fixpoint fmexprD (c : ctx typeD) {fmt} : fmexpr fmt -> lrtToType (fmtypeD fmt) :=
  match fmt return fmexpr fmt -> lrtToType (fmtypeD fmt) with
  | FunMT t fmt => fun f => Ctx.inExt c (fun n c' => fmexprD c' (f n))
  | CompMT _ => mexprD c
  end.

(** ** Substitution for expressions *)
(** Important: Any name you use for substitution cannot be used again! **)

Definition substVar {t t'} (n : name t) (x : expr t) (n' : name t') : string + expr t' :=
  if Pos.eqb n n' then match type_decEq t' t with
                       | left e => inr (eq_rect_r _ x e)
                       | right _ => inl "[proof automation] ill-typed substitution"%string
                       end
                  else inr (varE n').

Fixpoint substExpr {t t'} (n : name t) (x : expr t) (e : expr t') : string + expr t' :=
  match e with
  | varE t' n' => substVar n x n'
  | termE _ x => inr (termE x)
  (* | funE _ i es => apSumR (funE i) (mapSumList (fun '(existT ti ei) => apSumR (existT _ ti) (substExpr n x ei)) es) *)
  | ttE => inr ttE
  | LeftE  _ tr e => fmapSumR (@LeftE  _ tr) (substExpr n x e)
  | RightE tl _ e => fmapSumR (@RightE tl _) (substExpr n x e)
  | fstE _ tr e => fmapSumR (@fstE _ tr) (substExpr n x e)
  | sndE tl _ e => fmapSumR (@sndE tl _) (substExpr n x e)
  | pairE _ _ e1 e2 => apSumR (fmapSumR pairE (substExpr n x e1)) (substExpr n x e2)
  | nilE _ => inr nilE
  | consE _ e1 e2 => apSumR (fmapSumR consE (substExpr n x e1)) (substExpr n x e2)
  | unfoldListE t e => fmapSumR (unfoldListE t) (substExpr n x e)
  | foldListE t e => fmapSumR (foldListE t) (substExpr n x e)
  end.

Fixpoint substMExpr {t t'} (n : name t) (x : expr t) (me : mexpr t') : mexpr t' :=
  match me with
  | returnE e => fromSum errorE returnE (substExpr n x e)
  | bindE _ e f => bindE (substMExpr n x e) (fun n' => substMExpr n x (f n'))
  | errorE s => errorE s
  | eitherE _ _ f g e =>
    fromSum errorE (eitherE (fun nl => substMExpr n x (f nl))
                            (fun nr => substMExpr n x (g nr)))
                            (substExpr n x e)
  end.

Fixpoint substFMExpr {t fmt} (n : name t) (x : expr t) : fmexpr fmt -> fmexpr fmt :=
  match fmt return fmexpr fmt -> fmexpr fmt with
  | FunMT t' fmt => fun f n' => substFMExpr n x (f n')
  | CompMT _ => substMExpr n x
  end.

(** ** Size of monadic expressions *)

Fixpoint sizeME {F} (c : ctx F) {t} (x : mexpr t) : nat :=
  match x with
  | returnE _ => 1
  | bindE _ e f => S (sizeME c e + Ctx.withFreshName c (fun n c' => sizeME c' (f n)))
  | errorE _ => 1
  | eitherE _ _ f g e => S (Ctx.withFreshName c (fun nl cl => sizeME cl (f nl)) +
                            Ctx.withFreshName c (fun nr cr => sizeME cr (g nr)))
  end.

Fixpoint sizeFME {F} (c : ctx F) {fmt} : fmexpr fmt -> nat :=
  match fmt with
  | FunMT _ _ => fun f => Ctx.withFreshName c (fun n c' => sizeFME c' (f n))
  | CompMT _ => sizeME c
  end.


(** * Checking closed-ness of expressions in a context *)

Fixpoint closedExpr {F} (c : ctx F) {t} (e : expr t) : bool :=
  match e with
  | varE _ n => Ctx.mem n c
  | termE _ _ => true
  | ttE => true
  | LeftE  _ _ e => closedExpr c e
  | RightE _ _ e => closedExpr c e
  | fstE _ _ e => closedExpr c e
  | sndE _ _ e => closedExpr c e
  | pairE _ _ e1 e2 => closedExpr c e1 && closedExpr c e2
  | nilE _ => true
  | consE _ e1 e2 => closedExpr c e1 && closedExpr c e2
  | unfoldListE t e => closedExpr c e
  | foldListE t e => closedExpr c e
  end.

Fixpoint closedProp {F} (c : ctx F) (p : prop) : bool :=
  match p with
  | PropP _ => true
  | eqP _ e1 e2 => closedExpr c e1 && closedExpr c e2
  | AndP p1 p2 => closedProp c p1 && closedProp c p2
  end.

Definition forallFreshNamesIn {F} (c : ctx F) {t} (g : name t -> ctx F -> Prop) : Prop :=
  forall n (pf : Ctx.isFresh n c = true) x, g n (Ctx.addWith c n pf x).

Fixpoint closedMExpr {F} (c : ctx F) {t} (me : mexpr t) : Prop :=
  match me with
  | returnE e => closedExpr c e = true
  | bindE _ e f => closedMExpr c e /\ forallFreshNamesIn c (fun n c' => closedMExpr c' (f n))
  | errorE _ => True
  | eitherE _ _ f g e => closedExpr c e = true /\
                         forallFreshNamesIn c (fun nl cl => closedMExpr cl (f nl)) /\
                         forallFreshNamesIn c (fun nr cr => closedMExpr cr (g nr))
  end.

Fixpoint closedFMExpr {F} (c : ctx F) {fmt} : fmexpr fmt -> Prop :=
  match fmt with
  | FunMT t fmt => fun f => forallFreshNamesIn c (fun n c' => closedFMExpr c' (f n))
  | CompMT _ => closedMExpr c
  end.

Lemma closedExpr_exprD_eq (c : ctx typeD) {t} (e : expr t) :
  closedExpr c e = true -> exists x, exprD c e = inr x.
Proof.
  induction e; simpl in *; intros;
    try (destruct (IHe H); rewrite H0; simpl); eauto.
  2-3: apply andb_true_iff in H; destruct H.
  2-3: destruct (IHe1 H), (IHe2 H0); rewrite H1, H2; simpl; eauto.
  apply Ctx.mem_2 in H; destruct H.
  rewrite (Ctx.find_1 H); eauto.
Qed.

Lemma wkn1_closedExpr (c : ctx typeD) {t'} (x : typeD t') {t} (e : expr t) :
  closedExpr c e = true -> closedExpr (snd (Ctx.add c x)) e = true.
Proof.
  induction e; simpl; intros; eauto.
  2-3: apply andb_true_iff in H; destruct H; apply andb_true_iff; eauto.
  apply Ctx.mem_2 in H; destruct H.
  apply Ctx.mem_1; exists x0; apply Ctx.ext_2; eauto.
Qed.

Lemma wkn1_closedProp (c : ctx typeD) {t'} (x : typeD t') (p : prop) :
  closedProp c p = true -> closedProp (snd (Ctx.add c x)) p = true.
Proof.
  induction p; simpl; intros; eauto.
  - rewrite andb_true_iff in H; destruct H.
    eapply wkn1_closedExpr in H; eapply wkn1_closedExpr in H0.
    rewrite andb_true_iff; split; simpl in *; eauto.
  - rewrite andb_true_iff in H; destruct H.
    apply IHp1 in H; apply IHp2 in H0.
    rewrite andb_true_iff; split; eauto.
Qed.

Lemma wkn1_closedMExpr (c : ctx typeD) {t'} (x : typeD t') {t} (me : mexpr t) :
  closedMExpr c me -> closedMExpr (snd (Ctx.add c x)) me.
Proof.
  revert c; induction me; simpl in *; intros; eauto.
  - rewrite wkn1_closedExpr; eauto.
  - destruct H0; apply IHme in H0; split; eauto.
Admitted.

Lemma wkn1_closedFMExpr (c : ctx typeD) {t'} (x : typeD t') {fmt} (fme : fmexpr fmt) :
  closedFMExpr c fme -> closedFMExpr (snd (Ctx.add c x)) fme.
Proof.
  revert c fme; induction fmt; simpl; intros; eauto.
  - do 3 intro.
Admitted.

Lemma wkn_exprD (c : ctx typeD) s xs pfs {t} (e : expr t) :
  closedExpr (Ctx.append c xs (Ctx.HasFreshNames_drop_l pfs)) e = true ->
  exprD (Ctx.append c (s :: xs) pfs) e = exprD (Ctx.append c xs (Ctx.HasFreshNames_drop_l pfs)) e.
Proof.
  destruct s as [?t [?n ?pf]].
  induction e; intros; cbn [ closedExpr exprD ] in *;
    try solve [ eauto | destruct (IHe H); eauto ].
  2-3: apply andb_true_iff in H; destruct H.
  2-3: destruct (IHe1 H), (IHe2 H0); eauto.
  apply Ctx.mem_2 in H; destruct H.
  rewrite (Ctx.find_1 H).
  rewrite (Ctx.find_1 (Ctx.append_cons_1 H)); eauto.
Qed.

Lemma wkn1_exprD (c : ctx typeD) {t'} (x : typeD t') {t} (e : expr t) :
  closedExpr c e = true ->
  exprD (snd (Ctx.add c x)) e = exprD c e.
Proof.
  unfold Ctx.add; rewrite Ctx.ext_8.
  apply (@wkn_exprD c (existT _ t' (fst (Ctx.ext c t' (Some x)), x)) [] (exist _ Ctx.ext_5 I) t).
Qed.

Lemma wkn_propD (c : ctx typeD) s xs pfs (p : prop) :
  closedProp (Ctx.append c xs (Ctx.HasFreshNames_drop_l pfs)) p = true ->
  propD (Ctx.append c (s :: xs) pfs) p <-> propD (Ctx.append c xs (Ctx.HasFreshNames_drop_l pfs)) p.
Proof.
  destruct s as [?t [?n ?pf]].
  induction p; intros; cbn [ closedProp propD propEmbExprD ] in *; try easy.
  - rewrite andb_true_iff in H; destruct H.
    rewrite (wkn_exprD _ _ _ _ e); eauto.
    rewrite (wkn_exprD _ _ _ _ e0); easy.
  - rewrite andb_true_iff in H; destruct H.
    rewrite IHp1, IHp2; easy.
Qed.

Lemma wkn1_propD (c : ctx typeD) {t'} (x : typeD t') (p : prop) :
  closedProp c p = true ->
  propD (snd (Ctx.add c x)) p <-> propD c p.
Proof.
  unfold Ctx.add; rewrite Ctx.ext_8.
  apply (wkn_propD c (existT _ t' (fst (Ctx.ext c t' (Some x)), x)) [] (exist _ Ctx.ext_5 I)).
Qed.

Lemma wkn_mexprD (c : ctx typeD) s xs pfs {t} (me : mexpr t) :
  closedMExpr (Ctx.append c xs (Ctx.HasFreshNames_drop_l pfs)) me ->
  mexprD (Ctx.append c (s :: xs) pfs) me ~= mexprD (Ctx.append c xs (Ctx.HasFreshNames_drop_l pfs)) me.
Proof.
  revert xs pfs; induction me; intros; cbn [ closedExpr mexprD mexprEmbExprD ] in *.
  - apply wkn_exprD in H; destruct H; reflexivity.
  - split.
    + destruct H0; apply refinesM_bind_f_equal; intros; eauto.
      unfold Ctx.inExt.
Admitted.

Lemma wkn1_mexprD (c : ctx typeD) {t'} (x : typeD t') {t} (me : mexpr t) :
  closedMExpr c me ->
  mexprD (snd (Ctx.add c x)) me ~= mexprD c me.
Proof.
  unfold Ctx.add; rewrite Ctx.ext_8.
  apply (@wkn_mexprD c (existT _ t' (fst (Ctx.ext c t' (Some x)), x)) [] (exist _ Ctx.ext_5 I) t).
Qed.

(* (* Lemma closed_exprD (c : ctx typeD) {t} (e : expr t) : *) *)
(* (*   closedExpr c e = true -> exists x, exprD c e = inr x. *) *)
(* (* Proof. *) *)
(* (*   induction e; simpl; intros; eauto; *) *)
(* (*     try solve [ destruct (IHe H); rewrite H0; simpl; eauto ]. *) *)
(* (*   apply Ctx.mem_2 in H; destruct H. *) *)
(* (*   apply Ctx.find_1 in H. *) *)
(* (*   rewrite H; eauto. *) *)
(* (* Qed. *) *)

(* Lemma closedExpr_ext {F} (c : ctx F) {t} (e : expr t) {t'} (x : F t') : *)
(*   closedExpr c e = true -> closedExpr (snd (Ctx.add c x)) e = true. *)
(* Proof. *)
(*   intro; induction e; simpl in *; intros; eauto. *)
(*   apply Ctx.mem_1; apply Ctx.mem_2 in H. *)
(*   destruct H; exists x0. *)
(*   apply Ctx.ext_2; eauto. *)
(* Qed. *)

(* Lemma closedExpr_append {F} (c : ctx F) {t} (e : expr t) xs : *)
(*   closedExpr c e = true -> closedExpr (ctxAppend c xs) e = true. *)
(* Proof. *)
(*   revert c; induction xs; [|destruct a]; simpl; intros; eauto. *)
(*   apply IHxs, closedExpr_ext; eauto. *)
(* Qed. *)

(* Lemma closed_exprD_ext (c : ctx typeD) {t} (e : expr t) {t'} (x : typeD t') : *)
(*   closedExpr c e = true -> *)
(*   exprD c e = exprD (snd (Ctx.add c x)) e. *)
(* Proof. *)
(*   induction e; simpl; intros; eauto; *)
(*     try solve [ destruct (IHe H); eauto ]. *)
(*   apply Ctx.mem_2 in H; destruct H. *)
(*   assert (Ctx.MapsTo n (Some x0) (snd (Ctx.add c x))) *)
(*     by (apply Ctx.ext_2; eauto). *)
(*   apply Ctx.find_1 in H; apply Ctx.find_1 in H0. *)
(*   rewrite H, H0; eauto. *)
(* Qed. *)

(*   (* assert (Ctx.MapsTo n (Some x0) (ctxAppend (snd (Ctx.add c x)) xs)). *) *)
(*   (* { revert c t n t' x x0 H; induction xs; [|destruct a]; simpl; intros. *) *)
(*   (*   - apply Ctx.ext_2; eauto. *) *)
(*   (*   - apply IHxs. } *) *)

(* Lemma closedExpr_exprD_append (c : ctx typeD) {t} (e : expr t) {t'} (x : typeD t') xs : *)
(*   closedExpr c e = true -> exprD c e = exprD (ctxAppend c xs) e. *)
(* Proof. *)
(*   revert c; induction xs; [|destruct a as [?t ?x]]; simpl; intros; eauto. *)
(*   pose proof (closed_exprD_ext _ _ x0 H); rewrite H0. *)
(*   apply IHxs, closedExpr_ext; eauto. *)
(* Qed. *)

(* Lemma ctxAppend_r {F} (c : ctx F) xs {t'} (x : F t') : *)
(*   ctxAppend c (xs ++ [existT _ _ x]) = snd (Ctx.add (ctxAppend c xs) x). *)
(* Proof. *)
(*   revert c; induction xs; [|destruct a]; simpl; eauto. *)
(* Qed. *)

(* (* Lemma ctxApppend_1 {F} (c : ctx F) {t} (n : name t) (o : option (F t)) xs : *) *)
(* (*   Ctx.MapsTo n o (ctxAppend c xs) -> *) *)
(* (*   Ctx.MapsTo n o c \/ Ctx.MapsTo n o (ctxAppend  xs). *) *)

(* (* Lemma Ctx_MapsTo_append {F} {c : ctx F} {t} {n : name t} {o} {t'} {x : F t'} xs : *) *)
(* (*   Ctx.MapsTo n o (ctxAppend c xs) -> *) *)
(* (*   Ctx.MapsTo n o (ctxAppend (snd (Ctx.add c x)) xs). *) *)
(* (* Proof. *) *)
(* (*   (* revert c t' x; induction xs; [|destruct a]; simpl; intros. *) *) *)
(* (*   (* - apply Ctx.ext_2; eauto. *) *) *)
(* (*   (* - eapply IHxs in H. *) *) *)
(* (*   rewrite <- (rev_involutive xs). *) *)
(* (*   revert c t' x; induction (rev xs); [|destruct a as [?t ?x]]; simpl; intros. *) *)
(* (*   - apply Ctx.ext_2; eauto. *) *)
(* (*   - rewrite ctxAppend_r in H; rewrite ctxAppend_r. *) *)
(* (*     unfold Ctx.add in *. *) *)
(* (*     destruct (Ctx.ext_3 H). *) *)
(* (*     + destruct (Ctx.nameEq_type_eq H0). *) *)
(* (*       apply Ctx.nameEq_name_eq in H0; destruct H0. *) *)
(* (*       pose proof (Ctx.MapsTo_1 H Ctx.ext_1); rewrite H0. *) *)
(* (*       apply Ctx.ext_1. *) *)
(* (*       unfold Ctx.add in *. *) *)
(* (*       unfold Ctx.add. apply Ctx.ext_1. *) *)
(* (*     Check Ctx.ext_3. *) *)
(* (*     apply (fun H H' => Ctx.ext_3 H' H) in H. *) *)
(* (*     pose proof (Ctx.ext_3 _ H). *) *)
(* (*     apply Ctx.ext_3 in H; apply Ctx.ext_2. *) *)
(* (*     specialize (IHxs _ _ x0 H). *) *)

(* Lemma closed_exprD_append_ext (c : ctx typeD) {t} (e : expr t) {t'} (x : typeD t') xs : *)
(*   closedExpr (ctxAppend c xs) e = true -> *)
(*   exprD (ctxAppend c xs) e = exprD (ctxAppend (snd (Ctx.add c x)) xs) e. *)
(* Proof. *)
(*   induction e; simpl; intros; eauto. *)
(*   - apply Ctx.mem_2 in H; destruct H. *)

(* Lemma wfMExpr_ext (c : ctx typeD) {t} (me : mexpr t) {t'} (x : typeD t') xs : *)
(*   wfMExpr (ctxAppend c xs) me -> *)
(*   mexprD (ctxAppend c xs) me |= mexprD (ctxAppend (snd (Ctx.add c x)) xs) me. *)
(* Proof. *)
(*   revert t' x xs; induction me; simpl; intros; try reflexivity. *)
(*   - assert (exprD (ctxAppend c xs) e = exprD (ctxAppend (snd (Ctx.add c x)) xs) e). *)
(*     +  *)
(*     admit. *)
(*     (* induction xs. Focus 2. [|destruct a]; simpl. *) *)
(*     (* + eapply wfExpr_ext in H. rewrite <- H; reflexivity. *) *)
(*   - destruct H0. *)
(*     apply refinesM_bind_f_equal; eauto; intros. *)
(*     unfold Ctx.inExt. *)
(*     pose (xs' := existT _ _ a :: xs). *)
(*     replace (snd (Ctx.add (ctxAppend c xs) a)) with (ctxAppend c xs'). *)
(*     remember (fst (Ctx.add (ctxAppend c xs) a)) as n1. *)
(*     replace (snd (Ctx.add (ctxAppend (snd (Ctx.add c x)) xs) a)) with (ctxAppend (snd (Ctx.add c x)) xs'). *)
(*     remember (fst (Ctx.add (ctxAppend (snd (Ctx.add c x)) xs) a)) as n2. *)
(*     unfold forallFreshInCtx in H1. *)
(*     apply H. *)
(*     apply IHme. *)
(*     rewrite (prod_let (Ctx.add (ctxAppend c xs) a) (fun n c' => )). *)
(*     remember (Ctx.add (ctxAppend c xs) a) as c1; destruct c1 as [n1 c1]. *)
(*     remember (Ctx.add (ctxAppend (snd (Ctx.add c x)) xs) a) as c2; destruct c2 as [n2 c2]. *)

(*     remember (fst (Ctx.add (ctxAppend c xs) a)) as n1. *)

(* (* Lemma wfExpr_extCtx (c : ctx typeD) {t} (e : expr t): *) *)
(* (*   wfExpr c e = true -> *) *)
(* (*   forall {t'} (x : typeD t'), exprD c e = exprD (snd (extCtx c x)) e. *) *)
(* (* Proof. *) *)
(* (*   induction e; intro wfe; intros; eauto; simpl in *; *) *)
(* (*     try solve [ rewrite (IHe wfe _ x); reflexivity ]. *) *)
(* (*   apply findInCtx_extCtx_2. *) *)
(* (* Qed. *) *)

(* (* Lemma wfMExpr_extCtx (c : ctx typeD) {t} (me : mexpr t): *) *)
(* (*   wfMExpr c me = true -> *) *)
(* (*   forall {t'} (x : typeD t'), mexprD c me = mexprD (snd (extCtx c x)) me. *) *)
(* (* Proof. *) *)
(* (*   induction me; intro wfme; intros; eauto; simpl in *. *) *)
(* (*   (* try solve [ rewrite (IHme H _ x); reflexivity ]. *) *) *)
(* (*   - unfold mexprEmbExprD; rewrite <- wfExpr_extCtx; eauto; reflexivity. *) *)
(* (*   - apply andb_true_iff in wfme; destruct wfme as [wfme wfm]. *) *)
(* (*     rewrite (IHme wfme _ x). *) *)
(* (*     unfold Ctx.inExt in *. *) *)
(* (* (*   apply findInCtx_extCtx_2. *) *) *)
(* (* (* Qed. *) *) *)


(** * Hypotheses *)

Definition hyps : Type := list prop.

Definition hypsD (c : ctx typeD) (h : hyps) : Prop :=
  Forall (propD c) h.

Lemma hypsD_app {c h1 h2} :
  hypsD c (h1 ++ h2) <-> hypsD c h1 /\ hypsD c h2.
Proof. apply Forall_app. Qed.

Definition closedHyps (c : ctx typeD) (h : hyps) : bool :=
  forallb (closedProp c) h.

Lemma closedHyps_app {c h1 h2} :
  closedHyps c (h1 ++ h2) = closedHyps c h1 && closedHyps c h2.
Proof. apply forallb_app. Qed.

Lemma wkn1_closedHyps (c : ctx typeD) {t'} (x : typeD t') (h : hyps) :
  closedHyps c h = true -> closedHyps (snd (Ctx.add c x)) h = true.
Proof.
  induction h; simpl; intros; eauto.
  rewrite andb_true_iff in H; destruct H.
  eapply wkn1_closedProp in H; apply IHh in H0.
  rewrite andb_true_iff; eauto.
Qed.

Lemma wkn1_hypsD (c : ctx typeD) {t'} (x : typeD t') (h : hyps) :
  closedHyps c h = true ->
  hypsD (snd (Ctx.add c x)) h <-> hypsD c h.
Proof.
  unfold hypsD; induction h; simpl; intros; eauto.
  - split; constructor; eauto.
  - rewrite andb_true_iff in H; destruct H.
    specialize (IHh H0); destruct IHh.
    split; inversion_clear 1; constructor;
      try eapply wkn1_propD; eauto.
Qed.


(** * Goals *)

Inductive goal :=
| propG : prop -> goal
| refinesMG {t} : mexpr t -> mexpr t -> goal
.

Fixpoint goalD (c : ctx typeD) (g : goal) : Prop :=
  match g with
  | propG p => propD c p
  | refinesMG _ x y => mexprD c x |= mexprD c y
  end.


(** * Checking refinement *)

Definition introArg (c : ctx typeD) {t} (g : name t -> ctx typeD -> Prop) : Prop :=
  forall x, Ctx.inExt c g x.

Fixpoint introHyp (c : ctx typeD) (h : list prop) (p : prop)
                  (g : ctx typeD -> list prop -> Prop) : Prop :=
  match p with
  | AndP p1 p2 => introHyp c h p1 (fun c' h' => introHyp c' h' p2 g)
  | _ => propD c p -> g c (h ++ [p])
  end.

Definition introArgAndHyp (c : ctx typeD) (h : list prop) {t} (p : name t -> prop)
                          (g : name t -> ctx typeD -> list prop -> Prop) : Prop :=
  introArg c (fun n c' => introHyp c' h (p n) (g n)).

Fixpoint check_refinesM_fuel (m : nat) {t} (c : ctx typeD) (h : list prop) (x y : mexpr t) : Prop :=
  match m with
  | S m =>
    match x, y with
    | returnE e1, returnE e2 => goalD c (propG (eqP e1 e2))
    | eitherE _ _ f g x, _ =>
      introArgAndHyp c h (fun nl => eqP x (LeftE _ _ (varE nl)))
                     (fun nl cl hl => check_refinesM_fuel m cl hl (f nl) y) /\
      introArgAndHyp c h (fun nr => eqP x (RightE _ _ (varE nr)))
                     (fun nr cr hr => check_refinesM_fuel m cr hr (g nr) y)
    | _, eitherE _ _ f g y =>
      introArgAndHyp c h (fun nl => eqP y (LeftE _ _ (varE nl)))
                     (fun nl cl hl => check_refinesM_fuel m cl hl x (f nl)) /\
      introArgAndHyp c h (fun nr => eqP y (RightE _ _ (varE nr)))
                     (fun nr cr hr => check_refinesM_fuel m cr hr x (g nr))
    | _,_ => goalD c (refinesMG x y)
    end
  | O => goalD c (refinesMG x y)
  end.

Definition check_refinesM {t} c h x y :=
  @check_refinesM_fuel (sizeME c x + sizeME c y) t c h x y.

Fixpoint check_refinesFun_fuel (m : nat) {fmt} (c : ctx typeD) (h : list prop) :
  fmexpr fmt -> fmexpr fmt -> Prop :=
  match fmt with
  | FunMT _ _ => fun f g => introArg c (fun n c' => check_refinesFun_fuel m c' h (f n) (g n))
  | CompMT _ => check_refinesM_fuel m c h
  end.

Definition check_refinesFun {fmt} c h f g :=
  @check_refinesFun_fuel (sizeFME c f + sizeFME c g) fmt c h f g.


(** * Proving soundness *)

Arguments introArgAndHyp /.
Arguments introArg /.

Lemma introHyp_sound c h p g :
  closedHyps c h = true -> closedProp c p = true ->
  hypsD c h -> propD c p ->
  introHyp c h p g ->
   exists ps, ((closedHyps c (h ++ ps) = true) *
                hypsD c (h ++ ps) *
                g c (h ++ ps))%type.
  (* exists xs pfs ps, ((closedHyps c (h ++ ps) = true) * *)
  (*                    hypsD c (h ++ ps) * *)
  (*                    g (Ctx.append c xs pfs) (h ++ ps))%type. *)
Proof.
  revert h g; induction p; intros.
  - exists [PropP n]; split; [split|]; cbn [introHyp] in *; eauto.
    + rewrite closedHyps_app, andb_true_iff; split; eauto.
    + rewrite hypsD_app; split; [|constructor]; eauto.
  - exists [eqP e e0]; split; [split|]; simpl in H0; eauto.
    + rewrite closedHyps_app, andb_true_iff; split; simpl; eauto.
      rewrite andb_true_iff in H0; destruct H0.
      rewrite H0, H4; reflexivity.
    + rewrite hypsD_app; split; [|constructor]; eauto.
  - simpl in H0, H2; rewrite andb_true_iff in H0; destruct H0, H2; simpl in H3.
    specialize (IHp1 _ _ H H0 H1 H2 H3); destruct IHp1 as [?ps [[?H ?H] ?H]].
    specialize (IHp2 _ _ H6 H4 H7 H5 H8); destruct IHp2 as [?ps [[?H ?H] ?H]].
    rewrite <- app_assoc in H9, H10, H11.
    exists (ps ++ ps0); split; [split|]; eauto.
Qed.

Arguments introHyp : simpl never.

Definition check_refinesM_fuel_soundness m {t} c h (x y : mexpr t) :=
  closedHyps c h = true -> closedMExpr c x -> closedMExpr c y ->
  hypsD c h ->
  check_refinesM_fuel m c h x y ->
  mexprD c x |= mexprD c y.

Definition check_refinesM_fuel_soundness_IH m :=
  (forall t c h x y, @check_refinesM_fuel_soundness m t c h x y).

Arguments check_refinesM_fuel_soundness /.
Arguments check_refinesM_fuel_soundness_IH /.

Lemma check_refinesM_return_lr_sound m {t} c h (e1 e2 : expr t) :
  check_refinesM_fuel_soundness (S m) c h (returnE e1) (returnE e2).
Proof.
  intros clh clx cly hD cf; simpl in *.
  generalize dependent (exprD c e1); intros se1 cf.
  generalize dependent (exprD c e2); intros se2 cf.
  destruct se1, se2; simpl in *; try contradiction.
  rewrite cf; reflexivity.
Qed.

Lemma check_refinesM_either_l_sound m {tl tr t} c h f g x y :
  check_refinesM_fuel_soundness_IH m ->
  check_refinesM_fuel_soundness (S m) c h (@eitherE t tl tr f g x) y.
Proof.
  intros IHm clh [clx [clf clg]] cly hD [cfl cfr]; simpl in *.
  destruct (closedExpr_exprD_eq _ _ clx) as [?x ?H]; rewrite H.
  destruct x0 as [?x|?x]; simpl; unfold Ctx.inExt.
  - specialize (cfl x0); clear cfr.
    rewrite <- (wkn1_exprD _ x0) in H; eauto.
    apply introHyp_sound in cfl.
    + destruct cfl as [?ps [[clh' h'D] cf']].
      rewrite <- (wkn1_mexprD c x0 y); eauto.
      apply (IHm _ _ (h ++ ps)); eauto.
      * unfold Ctx.add; rewrite Ctx.ext_8; apply clf.
      * apply wkn1_closedMExpr; eauto.
    + eapply wkn1_closedHyps; eauto.
    + simpl; rewrite andb_true_iff; split.
      * apply wkn1_closedExpr; eauto.
      * apply Ctx.mem_1; eexists; apply Ctx.ext_1.
    + apply wkn1_hypsD; eauto.
    + simpl; unfold snd in H.
      rewrite H; simpl.
      unfold Ctx.add; rewrite (Ctx.find_1 Ctx.ext_1); simpl; eauto.
  - specialize (cfr x0); clear cfl.
    rewrite <- (wkn1_exprD _ x0) in H; eauto.
    apply introHyp_sound in cfr.
    + destruct cfr as [?ps [[clh' h'D] cf']].
      rewrite <- (wkn1_mexprD c x0 y); eauto.
      apply (IHm _ _ (h ++ ps)); eauto.
      * unfold Ctx.add; rewrite Ctx.ext_8; apply clg.
      * apply wkn1_closedMExpr; eauto.
    + eapply wkn1_closedHyps; eauto.
    + simpl; rewrite andb_true_iff; split.
      * apply wkn1_closedExpr; eauto.
      * apply Ctx.mem_1; eexists; apply Ctx.ext_1.
    + apply wkn1_hypsD; eauto.
    + simpl; unfold snd in H.
      rewrite H; simpl.
      unfold Ctx.add; rewrite (Ctx.find_1 Ctx.ext_1); simpl; eauto.
Qed.

Lemma unfold_check_refinesM_fuel_either_r m {tl tr t} c h f g x y :
  (forall tl' tr' f' g' e, x = @eitherE _ tl' tr' f' g' e -> False) ->
  check_refinesM_fuel (S m) c h x (@eitherE t tl tr f g y) ->
  introArgAndHyp c h (fun nl => eqP y (LeftE _ _ (varE nl)))
                     (fun nl cl hl => check_refinesM_fuel m cl hl x (f nl)) /\
      introArgAndHyp c h (fun nr => eqP y (RightE _ _ (varE nr)))
                     (fun nr cr hr => check_refinesM_fuel m cr hr x (g nr)).
Proof.
  destruct x; simpl; intros; eauto.
  eapply False_ind, H; easy.
Qed.

Lemma check_refinesM_either_r_sound m {tl tr t} c h f g x y :
  (forall tl' tr' f' g' e, x = @eitherE _ tl' tr' f' g' e -> False) ->
  check_refinesM_fuel_soundness_IH m ->
  check_refinesM_fuel_soundness (S m) c h x (@eitherE t tl tr f g y).
Proof.
  intros neq IHm clh clx [cly [clf clg]] hD cf.
  apply unfold_check_refinesM_fuel_either_r in cf; eauto.
  destruct cf as [cfl cfr]; simpl in *.
  destruct (closedExpr_exprD_eq _ _ cly) as [?x ?H]; rewrite H.
  destruct x0 as [?x|?x]; simpl; unfold Ctx.inExt.
  - specialize (cfl x0); clear cfr.
    rewrite <- (wkn1_exprD _ x0) in H; eauto.
    apply introHyp_sound in cfl.
    + destruct cfl as [?ps [[clh' h'D] cf']].
      rewrite <- (wkn1_mexprD c x0 x); eauto.
      apply (IHm _ _ (h ++ ps)); eauto.
      * apply wkn1_closedMExpr; eauto.
      * unfold Ctx.add; rewrite Ctx.ext_8; apply clf.
    + eapply wkn1_closedHyps; eauto.
    + simpl; rewrite andb_true_iff; split.
      * apply wkn1_closedExpr; eauto.
      * apply Ctx.mem_1; eexists; apply Ctx.ext_1.
    + apply wkn1_hypsD; eauto.
    + simpl; unfold snd in H.
      rewrite H; simpl.
      unfold Ctx.add; rewrite (Ctx.find_1 Ctx.ext_1); simpl; eauto.
  - specialize (cfr x0); clear cfl.
    rewrite <- (wkn1_exprD _ x0) in H; eauto.
    apply introHyp_sound in cfr.
    + destruct cfr as [?ps [[clh' h'D] cf']].
      rewrite <- (wkn1_mexprD c x0 x); eauto.
      apply (IHm _ _ (h ++ ps)); eauto.
      * apply wkn1_closedMExpr; eauto.
      * unfold Ctx.add; rewrite Ctx.ext_8; apply clg.
    + eapply wkn1_closedHyps; eauto.
    + simpl; rewrite andb_true_iff; split.
      * apply wkn1_closedExpr; eauto.
      * apply Ctx.mem_1; eexists; apply Ctx.ext_1.
    + apply wkn1_hypsD; eauto.
    + simpl; unfold snd in H.
      rewrite H; simpl.
      unfold Ctx.add; rewrite (Ctx.find_1 Ctx.ext_1); simpl; eauto.
Qed.

Theorem check_refinesM_fuel_sound m {t} c h (x y : mexpr t) :
  check_refinesM_fuel_soundness m c h x y.
Proof.
  revert t c h x y; induction m; intros t c h x y;
    [| destruct x,y ]; try solve [ simpl in *; eauto ].
  - apply check_refinesM_return_lr_sound; eauto.
  - apply check_refinesM_either_r_sound; eauto.
    intros; discriminate H.
  - apply check_refinesM_either_r_sound; eauto.
    intros; discriminate H.
  - apply check_refinesM_either_r_sound; eauto.
    intros; discriminate H.
  - apply check_refinesM_either_l_sound; eauto.
  - apply check_refinesM_either_l_sound; eauto.
  - apply check_refinesM_either_l_sound; eauto.
  - apply check_refinesM_either_l_sound; eauto.
Qed.

Corollary check_refinesM_sound c {t} (x y : mexpr t) :
  closedMExpr c x -> closedMExpr c y ->
  check_refinesM c [] x y ->
  mexprD c x |= mexprD c y.
Proof.
  intros; eapply check_refinesM_fuel_sound; eauto.
  - reflexivity.
  - constructor; eauto.
Qed.

Theorem check_refinesFun_fuel_sound m {fmt} c h (f g : fmexpr fmt) :
  closedHyps c h = true -> closedFMExpr c f -> closedFMExpr c g ->
  hypsD c h ->
  check_refinesFun_fuel m c h f g ->
  refinesFun (fmexprD c f) (fmexprD c g).
Proof.
  revert fmt c f g; induction fmt; simpl; unfold Ctx.inExt;
    intros c f g clh clf clg hD cf; [intro x|].
  - apply IHfmt; eauto.
    + apply wkn1_closedHyps; eauto.
    + unfold Ctx.add; rewrite Ctx.ext_8; apply clf.
    + unfold Ctx.add; rewrite Ctx.ext_8; apply clg.
    + apply wkn1_hypsD; eauto.
  - eapply check_refinesM_fuel_sound; eauto.
Qed.

Corollary check_refinesFun_sound c {fmt} (f g : fmexpr fmt) :
  closedFMExpr c f -> closedFMExpr c g ->
  check_refinesFun c [] f g ->
  refinesFun (fmexprD c f) (fmexprD c g).
Proof.
  intros; eapply check_refinesFun_fuel_sound; eauto.
  - reflexivity.
  - constructor; eauto.
Qed.

End env.
