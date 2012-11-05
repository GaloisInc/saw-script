module SAWScript.TypeChecking where

import SAWScript.AST
import Data.List
import Data.Set hiding ( member )
import Data.Map hiding ( member )
import SAWScript.Exception

class Subtypeable expr where
  isSubtypeOf :: expr -> expr -> bool

data SAWType =
  | TypeVariable String
  | Atom Name SAWType
  | BitField [Integer]
  | DirectedMultiset (Set SAWType)
  | Arrow ArrowType [SAWType] SAWType


subsumes :: SAWType -> SAWType -> Bool
  (Atom n1 t1) `subsumes` (Atom n2 t2)   = 
    n1 == n2 && t1 `subsumes` t2

  (BitField d1) `subsumes` (BitField d2) = 
    (foldl1 (*) d1) == (foldl1 (*) d2)

  (DirectedMultiset t1) `subsumes` (DirectedMultiset t2) =

  (Arrow dom cod) `subsumes` (Arrow dom' cod') = 
    dom `subsumes` dom' && cod' `subsumes` cod

type Context = Map String SAWType

freshTypeVariable :: Context -> 
frashTypeVariable ctxt = 
  let names = "'":[name++[c] | name <- names, c <- ['A'..'Z']]
      taken = snd . unzip . assocs $ ctxt
  take . (dropWhile (\v -> elem v taken)) . (drop 1) $ names






















inferType :: Context -> Expr a -> SAWType
inferType ctxt expr = case of
  | Var name _ -> 
    case lookup name ctxt of
      | None   -> typeError ("Unbound variable: " ++ name)
      | Some t -> t 
  | Pattern p _ -> BitField (patternWidth p)
  | Func t args expr _ ->
    let (ctxt',argTypes) = foldl checkArg (ctxt, []) args in
    Arrow t argTypes (check ctxt' expr None)
  | App e1 e2 _ -> 
    let (t1,t2) = (check ctxt e1 None, check ctxt e2 None) in
    case t1 of
      | Arrow t (tA:ts) result -> 
          if tA `subsumes` t2 then
            if ts == [] then result else Arrow t ts result
          else
            typeError ("Expected argument of type " ++ (show tA) ++ 
                       ".  Got value of type " ++ (show t2) ++ " instead.")
      | otherwise -> typeError ("Application of non-function type.")
  | Switch arg matches _ ->
    let t = check arg
      (guards,exprs) = unzip matches
  | DM exprs _ ->
    
      where
        patternWidth p = case p of
          | Wildcard      = 1
          | Literal bits  = length bits
          | Concat p1 p2  = patternWidth p1 + patternWidth p2

check :: Context -> Expr Maybe TypeAnnotation -> Expr SAWType
check ctxt expr None = case expr of
  | Var name None -> 
    case lookup name ctxt of
      | None   -> typeError ("Unbound variable: " ++ name)
      | Some t -> t
  | Pattern p None -> 
    BitField (patternWidth p)
  | Func t args expr None ->
    let (ctxt',argTypes) = foldl checkArg (ctxt, []) args in
    Arrow t argTypes (check ctxt' expr None)
  | App e1 e2 None -> 
    let (t1,t2) = (check ctxt e1 None, check ctxt e2 None) in
    case t1 of
      | Arrow t (tA:ts) result -> 
          if tA `subsumes` t2 then
            if ts == [] then result else Arrow t ts result
          else
            typeError ("Expected argument of type " ++ (show tA) ++ 
                       ".  Got value of type " ++ (show t2) ++ " instead.")
      | otherwise -> typeError ("Application of non-function type.")
  | Switch arg matches None ->
    let t = check arg
      (guards,exprs) = unzip matches
  | DM exprs None

    where

      checkArg :: (Context, [SAWType]) -> (Name, Maybe TypeAnnotation) -> (Context, [SAWType])
      checkArg (ctxt,acc) (n,annotation) = case annotation of
          None   -> 
        | Just t -> 
      checkGuards

check ctxt expr (Just annotation) =
  let exprType = check ctxt expr None in
  if exprType `subsumes` (read annotation) then
    exprType
  else
    typeError ("Expected "++annotation++".  Got "++(show exprType)++".")

