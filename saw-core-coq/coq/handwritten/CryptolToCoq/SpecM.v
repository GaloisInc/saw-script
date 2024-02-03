
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From EnTree Require Import EnTreeSpecs TpDesc.


(**
 ** Defining the TpExprOps instance for SAW
 **)

(* NOTE: We must define any operations used in Cryptol types before evalBinOp,
which in turn is defined before the translation of the Cryptol SAW core module,
so we define these operations by hand here rather than automatically translating
them from the Cryptol SAW core module *)

Definition tcAdd (n m: Num) : Num :=
  match n, m with
  | TCNum x, TCNum y => TCNum (addNat x y)
  | _, _ => TCInf
  end.

Definition tcMul (n m: Num) : Num :=
  match n, m with
  | TCNum x, TCNum y => TCNum (mulNat x y)
  | _, _ => TCInf
  end.

Inductive TpExprUnOp : ExprKind -> ExprKind -> Type@{entree_u} :=
| UnOp_BVToNat w : TpExprUnOp (Kind_bv w) Kind_nat
| UnOp_NatToBV w : TpExprUnOp Kind_nat (Kind_bv w)
| UnOp_NatToNum : TpExprUnOp Kind_nat Kind_num
.

Inductive TpExprBinOp : ExprKind -> ExprKind -> ExprKind -> Type@{entree_u} :=
| BinOp_AddNat : TpExprBinOp Kind_nat Kind_nat Kind_nat
| BinOp_MulNat : TpExprBinOp Kind_nat Kind_nat Kind_nat
| BinOp_AddBV w : TpExprBinOp (Kind_bv w) (Kind_bv w) (Kind_bv w)
| BinOp_MulBV w : TpExprBinOp (Kind_bv w) (Kind_bv w) (Kind_bv w)
| BinOp_AddNum : TpExprBinOp Kind_num Kind_num Kind_num
| BinOp_MulNum : TpExprBinOp Kind_num Kind_num Kind_num
.

Lemma dec_eq_UnOp {EK1 EK2} (op1 op2 : TpExprUnOp EK1 EK2) : {op1=op2} + {~op1=op2}.
Admitted.

Lemma dec_eq_BinOp {EK1 EK2 EK3} (op1 op2 : TpExprBinOp EK1 EK2 EK3)
  : {op1=op2} + {~op1=op2}.
Admitted.

Definition evalUnOp {EK1 EK2} (op: TpExprUnOp EK1 EK2) :
  exprKindElem EK1 -> exprKindElem EK2 :=
  match op in TpExprUnOp EK1 EK2 return exprKindElem EK1 -> exprKindElem EK2 with
  | UnOp_BVToNat w => bvToNat w
  | UnOp_NatToBV w => bvNat w
  | UnOp_NatToNum => TCNum
  end.

Definition evalBinOp {EK1 EK2 EK3} (op: TpExprBinOp EK1 EK2 EK3) :
  exprKindElem EK1 -> exprKindElem EK2 -> exprKindElem EK3 :=
  match op in TpExprBinOp EK1 EK2 EK3
        return exprKindElem EK1 -> exprKindElem EK2 -> exprKindElem EK3 with
  | BinOp_AddNat => addNat
  | BinOp_MulNat => mulNat
  | BinOp_AddBV w => bvAdd w
  | BinOp_MulBV w => bvMul w
  | BinOp_AddNum => tcAdd
  | BinOp_MulNum => tcMul
  end.

Global Instance SAWTpExprOps : TpExprOps :=
  {
    TpExprUnOp := TpExprUnOp;
    TpExprBinOp := TpExprBinOp;
    dec_eq_UnOp := @dec_eq_UnOp;
    dec_eq_BinOp := @dec_eq_BinOp;
    evalUnOp := @evalUnOp;
    evalBinOp := @evalBinOp;
  }.


(**
 ** Now we re-export all of TpDesc using the above instance
 **)

(* Num: note that the Num type has to be defined in the TpDesc module, so its
type descriptions can refer to it, so we map the definition in Cryptol.sawcore
to that definition *)
Definition Num := TpDesc.Num.
Definition Num_rect := TpDesc.Num_rect.
Definition TCNum := TpDesc.TCNum.
Definition TCInf := TpDesc.TCInf.

(* EvType *)
Definition EvType := FixTree.EvType.
Definition Build_EvType := FixTree.Build_EvType.
Definition evTypeType := FixTree.evTypeType.
Definition evRetType := FixTree.evRetType.

(* ExprKind *)
Definition ExprKind := ExprKind.
Definition ExprKind_rect := ExprKind_rect.
Definition Kind_unit := Kind_unit.
Definition Kind_bool := Kind_bool.
Definition Kind_nat := Kind_nat.
Definition Kind_num := Kind_num.
Definition Kind_bv := Kind_bv.

(* KindDesc *)
Definition KindDesc := KindDesc.
Definition KindDesc_rect := KindDesc_rect.
Definition Kind_Expr := Kind_Expr.
Definition Kind_Tp := Kind_Tp.

(* TpExpr *)
Definition TpExpr := TpExpr.
Definition TpExpr_rect := TpExpr_rect.
Definition TpExpr_Const := @TpExpr_Const SAWTpExprOps.
Definition TpExpr_Var := @TpExpr_Var SAWTpExprOps.
Definition TpExpr_UnOp := @TpExpr_UnOp SAWTpExprOps.
Definition TpExpr_BinOp := @TpExpr_BinOp SAWTpExprOps.

(* TpDesc *)
Definition TpDesc := TpDesc.
Definition TpDesc_rect := TpDesc_rect.
Definition Tp_M := Tp_M.
Definition Tp_Pi := Tp_Pi.
Definition Tp_Arr := Tp_Arr.
Definition Tp_Kind := Tp_Kind.
Definition Tp_Pair := Tp_Pair.
Definition Tp_Sum := Tp_Sum.
Definition Tp_Sigma := Tp_Sigma.
Definition Tp_Seq := Tp_Seq.
Definition Tp_Void := Tp_Void.
Definition Tp_Ind := Tp_Ind.
Definition Tp_Var := Tp_Var.
Definition Tp_TpSubst := Tp_TpSubst.
Definition Tp_ExprSubst := Tp_ExprSubst.

(* tpElem and friends *)
Definition FunFlag := FunFlag.
Definition IsData := IsData.
Definition IsFun := IsFun.
Definition tpSubst := tpSubst.
Definition elimTpEnvElem := elimTpEnvElem.
Definition tpElemEnv := tpElemEnv.
Definition indElem := indElem.
Definition foldTpElem := @foldTpElem.
Definition unfoldTpElem := @unfoldTpElem.

(* SpecM and its operations *)
Definition SpecM := @SpecM.SpecM SAWTpExprOps.
Definition retS := @SpecM.RetS SAWTpExprOps.
Definition bindS := @SpecM.BindS SAWTpExprOps.
Definition triggerS := @SpecM.TriggerS SAWTpExprOps.
Definition errorS := @SpecM.ErrorS SAWTpExprOps.
Definition forallS := @SpecM.ForallS SAWTpExprOps.
Definition existsS := @SpecM.ExistsS SAWTpExprOps.
Definition assumeS := @SpecM.AssumeS SAWTpExprOps.
Definition assertS := @SpecM.AssertS SAWTpExprOps.
Definition FixS := @SpecM.FixS SAWTpExprOps.
Definition MultiFixS := @SpecM.MultiFixS SAWTpExprOps.
Definition LetRecS := @SpecM.LetRecS SAWTpExprOps.
