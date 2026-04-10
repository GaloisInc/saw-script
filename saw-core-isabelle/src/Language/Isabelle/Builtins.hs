module Language.Isabelle.Builtins where

import qualified Cryptol.TypeCheck.PP as Cry

import qualified Language.Isabelle.Binding as Binding
import qualified Language.Isabelle.Expr as Expr
import           Language.Isabelle.Expr (Expr, Type)
import qualified Language.Isabelle.Name as Name
import           Language.Isabelle.Name (Name)
import qualified Language.Isabelle.Syntax as Syntax
import qualified Language.Isabelle.Panic as Panic

scratchThy :: Name.TheoryName
scratchThy = Name.TheoryName "Scratch" False

unsupportedThy :: Name.TheoryName
unsupportedThy = Name.TheoryName "Unsupported" False

pureThy :: Name.TheoryName
pureThy = Name.TheoryName "Pure" False

holThy :: Name.TheoryName
holThy = Name.TheoryName "HOL" False

word0Thy :: Name.TheoryName
word0Thy = Name.TheoryName "Word0" False


tPredThy :: Name.TheoryName
tPredThy = Name.TheoryName "Type_Predicate" False

tLenThy :: Name.TheoryName
tLenThy = Name.TheoryName "Alt_Type_Length" False

seqThy :: Name.TheoryName
seqThy = Name.TheoryName "Seq" False

cryThy :: Name.TheoryName
cryThy = Name.TheoryName "Cryptol" False

wordThy :: Name.TheoryName
wordThy = Name.TheoryName "Word" False

finThy :: Name.TheoryName
finThy = Name.TheoryName "Fin" False

integralThy :: Name.TheoryName
integralThy = Name.TheoryName "Integral" False

bitListThy :: Name.TheoryName
bitListThy = Name.TheoryName "Reversed_Bit_Lists" False

builtinThys :: [Name.TheoryName]
builtinThys =
  [ scratchThy
  , unsupportedThy
  , pureThy
  , holThy
  , word0Thy
  , tPredThy
  , tLenThy
  , seqThy
  , cryThy
  , wordThy
  , finThy
  , integralThy
  , bitListThy
  ]

isBuiltinThy :: Name.TheoryName -> Bool
isBuiltinThy thynm = elem thynm builtinThys

isBuiltinName :: Name.Name -> Bool
isBuiltinName nm = case nm of
  Name.Name{} -> isBuiltinThy (Name.nmThy nm)
  _ -> False

tFun :: Type -> Type -> Type
tFun e1 e2 = Expr.Ctr [e1, e2] $
  Name.Name pureThy "fun" (Syntax.InfixSyn ("\\<Rightarrow>")) Name.Typ



ifExpr :: Expr -> Expr -> Expr -> Expr
ifExpr eP eT eF = case (eT, eF) of
  (Expr.ConstrainT eT' t, Expr.ConstrainT eF' t') | t == t' -> 
    constrain (Expr.Ctr [eP, eT', eF'] $
      Name.Name holThy "If" (Syntax.MixFix3 "if" "then" "else") Name.Term) t
  _ -> Expr.Ctr [eP, eT, eF] $
    Name.Name holThy "If" (Syntax.MixFix3 "if" "then" "else coerce") Name.Term

letExpr' :: [Expr] -> Expr -> Expr
letExpr' binds (Expr.Let binds' ebody) = letExpr' (binds ++ binds') ebody
letExpr' binds ebody = Expr.Let binds ebody

letExpr :: [(Binding.Binding, Expr)] -> Expr -> Expr
letExpr binds eBody = letExpr' (map bindEq binds) eBody
  where
    bindEq (b,e) = eqExpr (Expr.Var (Binding.bindName b)) (coerceToExpr e (Binding.bindType b))

{-
letExpr :: [(Binding.Binding, Expr)] -> Expr -> Expr
letExpr binds eBody = Expr.Ctr (eBody: map bindEq binds) $
  Name.Name pureThy "Let" (Syntax.ListSyn Syntax.Postfix "; " "let " " in " ) Name.Term
  where
    bindEq (b,e) = eqExpr (Expr.Bind (Binding.bindName b) (Binding.bindType b)) e
-}

tAbs :: [Type] -> Type -> Type
tAbs [] body = body
tAbs ts body = Expr.Ctr (body:ts) $
  Name.Name cryThy "TAbs" (Syntax.ListSyn Syntax.Postfix "," "{" "} ") Name.Typ

tApp :: Expr -> [Type] -> Expr
tApp body [] = body
tApp body ts = Expr.TApp body ts

appExpr :: Expr -> [Expr] -> Expr
appExpr e [] = e
appExpr e args = Expr.App e args

unOp :: Expr -> Expr
unOp e = Expr.Ctr [e] $ Name.Name cryThy "unOp" (Syntax.MixFix1 "\\<lblot>" "\\<rblot>") Name.Term

tGuard :: [Type] -> Type -> Type
tGuard [] body = body
tGuard ts body = Expr.Ctr (body:ts) $
  Name.Name cryThy "TGuard" (Syntax.ListSyn Syntax.Postfix "," "(" ") =?> ") Name.Typ

eAssuming :: [Type] -> Expr -> Expr
eAssuming ts e = Expr.Ctr (e:ts) $
  Name.Name cryThy "assuming" (Syntax.ListSyn Syntax.Postfix "," "(" ") \\<Rightarrow> ") Name.Term

eHolds :: [Type] -> Expr
eHolds ts = Expr.Ctr ts $
  Name.Name cryThy "holds" (Syntax.ListSyn Syntax.Nofix "," "PRED(" ")") Name.Term

tEquals :: Type -> Type -> Type
tEquals= tBinOp $ Name.Name tPredThy "Equals" (Syntax.InfixSyn "=") Name.Typ


eqExpr :: Expr -> Expr -> Expr
eqExpr e1 e2 = Expr.Ctr [e1, e2] $  Name.Name holThy "Eq" (Syntax.InfixSyn "=") Name.Term

tBit :: Type
tBit = Expr.Ctr [] (Name.Name cryThy "Bit" Syntax.NoSyn Name.Typ)

tSeq :: Type -> Type -> Type
tSeq eLen eT = if eT == tBit then tWord eLen else Expr.Ctr [eLen, eT] $
  Name.Name seqThy "Seq" (Syntax.MixFix2 "[" "]") Name.Typ

tWord :: Type -> Type
tWord eLen = Expr.Ctr [eLen] $
  Name.Name wordThy "word" (Syntax.MixFix1 "[" "]") Name.Typ

tInt :: Type
tInt = Expr.Ctr [] (Name.Name cryThy "Integer" Syntax.NoSyn Name.Typ)

tBinOp :: Name.Name -> (Type -> Type -> Type)
tBinOp nm t1 t2 = Expr.BinOp t1 (Expr.Ctr [] nm) t2

tAdd :: Type -> Type -> Type
tAdd = tBinOp $ Name.Name holThy "sum" (Syntax.InfixSyn ("+")) Name.TNum

tMinus :: Type -> Type -> Type
tMinus = tBinOp $ Name.Name tLenThy "Minus" (Syntax.InfixSyn ("-")) Name.TNum

tMod :: Type -> Type -> Type
tMod = tBinOp $ Name.Name tLenThy "Mod" (Syntax.InfixSyn ("%")) Name.TNum

tWidth :: Type -> Type
tWidth t1 = Expr.Ctr [t1]
  (Name.Name tLenThy "Width" (Syntax.Symbol Syntax.Prefix ("width")) Name.TNum)

tGeq :: Type -> Type -> Type
tGeq = tBinOp $ Name.Name tPredThy "Geq" (Syntax.InfixSyn ("\\<ge>")) Name.Typ

tGt :: Type -> Type -> Type
tGt = tBinOp $ Name.Name tPredThy "Gt" (Syntax.InfixSyn (">")) Name.Typ

tMul :: Type -> Type -> Type
tMul = tBinOp $ Name.Name holThy "prod" (Syntax.InfixSyn ("*")) Name.TNum

tDiv :: Type -> Type -> Type
tDiv = tBinOp $ Name.Name tLenThy "Divide" (Syntax.InfixSyn ("/")) Name.TNum

tMin :: Type -> Type -> Type
tMin (Expr.IntLit i1) (Expr.IntLit i2) = Expr.IntLit (min i1 i2)
tMin t1 t2 | t1 == t2 = t1
tMin t1 t2 = Expr.Ctr [t1, t2] (Name.Name tLenThy "Min" Syntax.NoSyn Name.TNum)

tMax :: Type -> Type -> Type
tMax (Expr.IntLit i1) (Expr.IntLit i2) = Expr.IntLit (min i1 i2)
tMax t1 t2 | t1 == t2 = t1
tMax t1 t2 = Expr.Ctr [t1, t2] (Name.Name tLenThy "Max" Syntax.NoSyn Name.TNum)

tExp :: Type -> Type -> Type
tExp = tBinOp $ Name.Name tLenThy "Exp" (Syntax.InfixSyn ("^")) Name.Typ

tTuple :: [Type] -> Type
tTuple ts = Expr.Ctr ts (Name.Name holThy "prod" (Syntax.ListSyn Syntax.Nofix ") \\<times> (" "(" ")") Name.Typ)

tZ :: Type -> Type
tZ t = Expr.Ctr [t] (Name.Name finThy "Z" Syntax.NoSyn Name.Typ)

dummy :: Expr
dummy = Expr.Ctr [] (Name.Name pureThy "dummy" (Syntax.SymbolSyn "_") Name.Term)

tFromThenTo :: Type -> Type -> Type -> Type
tFromThenTo x y z =
  Expr.Ctr [x, y, z] (Name.Name tLenThy "FromThenTo" Syntax.NoSyn Name.Typ)

eAbs :: [Expr] -> Expr -> Expr
eAbs args body = Expr.Binder "\\<lambda>" args body

tupleSelect :: Name.Name -> Expr -> Int -> Int -> Expr
tupleSelect nm e sel len = case splitAt sel (replicate len dummy) of
  (hdr,_:ftr) ->
   let binds = hdr ++ (Expr.Var nm:ftr)
    in appExpr (eAbs [(tupleExpr binds)] (Expr.Var nm)) [e]
  _ -> Panic.panic "Unexpected tuple selection" [show e, show sel, show len]

tupleAbs :: [[(Name.Name,Type)]] -> Expr -> Expr
tupleAbs bs e = eAbs [tupleExpr (map go bs)] e
  where
    go :: [(Name.Name, Type)] -> Expr
    go binds = tupleExpr (map (\(nm,t) -> Expr.ConstrainT (Expr.Var nm) t) binds)

tLiteral :: Type -> Type -> Type
tLiteral t1 t2 = Expr.Ctr [t1, t2]
  (Name.Name cryThy "litT" (Syntax.Symbol Syntax.Prefix "Literal") Name.Typ)

tLogic :: Type -> Type
tLogic t1 = Expr.Ctr [t1]
  (Name.Name cryThy "logic" (Syntax.Symbol Syntax.Prefix "Logic") Name.Typ)

tZero :: Type -> Type
tZero t1 = Expr.Ctr [t1]
  (Name.Name cryThy "zero" (Syntax.Symbol Syntax.Prefix "Zero") Name.Typ)


tFinite :: Type  -> Type
tFinite t1 = Expr.Ctr [t1]
  (Name.Name cryThy "finT" (Syntax.Symbol Syntax.Prefix "fin") Name.Typ)

tSignedCmp :: Type  -> Type
tSignedCmp t1 = Expr.Ctr [t1]
  (Name.Name cryThy "signedCmp" (Syntax.Symbol Syntax.Prefix "SignedCmp") Name.Typ)

tCmp :: Type  -> Type
tCmp t1 = Expr.Ctr [t1]
  (Name.Name holThy "ord" (Syntax.Symbol Syntax.Prefix "Cmp") Name.Typ)

tRing :: Type  -> Type
tRing t1 = Expr.Ctr [t1]
  (Name.Name holThy "ring" (Syntax.Symbol Syntax.Prefix "Ring") Name.Typ)

tIntegral :: Type  -> Type
tIntegral t1 = Expr.Ctr [t1]
  (Name.Name integralThy "integral" (Syntax.Symbol Syntax.Prefix "Integral") Name.Typ)

tEq :: Type -> Type
tEq e1 = Expr.Ctr [e1] $
  Name.Name cryThy "Eq" (Syntax.Symbol Syntax.Prefix "Eq") Name.Typ

tAnd :: Type -> Type -> Type
tAnd t1 t2 = Expr.Ctr [t1, t2] $
  Name.Name tPredThy "And" (Syntax.InfixSyn ("\\<and>")) Name.Typ

tupleExpr :: [Expr] -> Expr
tupleExpr ts = Expr.Ctr ts
 (Name.Name holThy "Pair" (Syntax.ListSyn Syntax.Nofix "," "(" ")") Name.Typ)

-- | This will fail to parse into Isabelle since it is unsupported
tInfinity :: Expr
tInfinity = Expr.Ctr [] (Name.Name cryThy "Unsupported_Infinity" Syntax.NoSyn Name.Typ)

seqExpr :: [Expr] -> Expr
seqExpr es = Expr.Ctr es $
  (Name.Name seqThy "list_to_seq" (Syntax.ListSyn Syntax.Nofix "," "list_to_seq [" "]")  Name.Term)

-- same as seqExpr after changing background word theory to have cryptol
-- words actually be bit-sequences
wordFromBits :: [Expr] -> Expr
wordFromBits es = seqExpr es


fromTo :: Type -> Type -> Type -> Expr
fromTo loT hiT eT =
  tApp (Expr.Var $ Name.Name seqThy "fromTo" Syntax.NoSyn  Name.Term) [loT, hiT, eT]


seqCompr1' :: Type -> Type -> Type -> Expr -> Expr -> Expr
seqCompr1' lenT inT outT body e =
  let f = tApp (Expr.Var $ (Name.Name seqThy "seq_compr" Syntax.NoSyn  Name.Term)) [lenT, inT, outT]
  in appExpr f [body, e]

seqCompr1 :: Type -> Type -> Type -> (Name,Expr) -> Expr -> Expr
seqCompr1 lenT inT outT (nm,lam) e = seqCompr1' lenT inT outT (eAbs [bind nm inT] lam) e

-- | {n, a, m, b} (a -> [m]b) -> [n]a -> [(n * m)]b
seqConcatMap :: Type -> Type -> Type -> Type -> (Name,Expr) -> Expr -> Expr
seqConcatMap n a m b (nm,lam) e =
  let f = tApp (Expr.Var $ (Name.Name seqThy "seq_concat_map" Syntax.NoSyn  Name.Term)) [n, a, m, b]
  in appExpr f [eAbs [bind nm a] lam, e]

seqZip :: Type -> Type -> Type -> Type -> Expr -> Expr -> Expr
seqZip lenT1 lenT2 t1 t2 e1 e2 = snd (seqZip' lenT1 lenT2 t1 t2 e1 e2)

seqZip' :: Type -> Type -> Type -> Type -> Expr -> Expr -> ((Type, Type), Expr)
seqZip' n a m b e1 e2 =
  let f = if n == m then
        tApp (Expr.Ctr [] $ (Name.Name seqThy "zip_seq" (Syntax.Symbol Syntax.Prefix "zip") Name.Term)) [n, a, b]
      else
        tApp (Expr.Ctr [] $ (Name.Name seqThy "zip_seq_mismatched" (Syntax.Symbol Syntax.Prefix "zip_mismatch")  Name.Term)) [n, a, m, b]
  in (((tMin n m),(tTuple [a, b])), appExpr f [e1, e2])

seqZipMany :: [((Type,Type), Expr)] -> ((Type, Type), Expr)
seqZipMany [] = Panic.panic "seqZipMany: empty" []
seqZipMany [x] = x
seqZipMany (((lenT,eT),e):tes) = let ((lenT',eT'),e') = seqZipMany tes in seqZip' lenT eT lenT' eT' e e'

seqSel :: Type -> Type -> Type -> Expr -> Expr -> Expr
seqSel lenT eT idxT e i =
  let f = tApp (Expr.Ctr [] $
        (Name.Name seqThy "seq_select" (Syntax.InfixSyn ("@")) Name.Term)) [lenT, eT, idxT]
  in Expr.BinOp e f i


constrain :: Expr -> Type -> Expr
constrain = Expr.ConstrainT

bind :: Name -> Type -> Expr
bind nm t = Expr.ConstrainT (Expr.Var nm) t

bind' :: Binding.Binding -> Expr
bind' b = bind (Binding.bindName b) (Binding.bindType b)

coerceExpr :: Expr -> Expr
coerceExpr e = Expr.Ctr [e] $
  (Name.Name cryThy "coerce" Syntax.NoSyn Name.Term)

coerceToExpr :: Expr -> Type -> Expr
coerceToExpr e@(Expr.ConstrainT _ t1) t2 | t1 == t2 = e
coerceToExpr e t = Expr.Ctr [e,t] $
  (Name.Name cryThy "coerce_to" (Syntax.InfixSyn ":") Name.Term)

tUnsupported :: Type -> Type
tUnsupported t = Expr.Ctr [t] $
  (Name.Name unsupportedThy "unsupportedT" Syntax.NoSyn  Name.Typ)

recordCtr :: [(Name.Name, Expr)] -> Expr
recordCtr args = Expr.Ctr (map (\(nm,arg) -> eqExpr (Expr.Var nm) arg) args)
  (Name.Name holThy "record" (Syntax.ListSyn Syntax.Nofix "," "\\<lparr>" "\\<rparr>")  Name.Term)

tRecord :: [(Name.Name, Type)] -> Type
tRecord args = Expr.Ctr (map (\(nm,arg) -> bind nm arg) args)
  (Name.Name holThy "recordT" (Syntax.ListSyn Syntax.Nofix "," "\\<lparr>" "\\<rparr>")  Name.Typ)

dots :: Name.Name
dots = Name.Name holThy "dots" (Syntax.InfixSyn "\\<dots>") Name.Term

mapRecord :: String -> [String] -> ((Name.Name, Expr.Expr) -> Expr.Expr) -> Expr.Expr
mapRecord recNm nms f =
  eAbs [x] $ Expr.Case x [(recordCtr nmargs, recordCtr (map (\(nm,arg) -> (nm, f (nm,arg))) nmargs))]
  where
    x = Expr.Var $ Name.SimpleName "x"
    nmargs = zip (map Name.SimpleName nms ++ [dots]) args
    args = map (\n -> Expr.Var (Name.SimpleName (n ++ "__" ++ recNm))) (Cry.nameList [])
