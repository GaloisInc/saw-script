{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Isabelle.Expr
(
  Expr(..)
, pattern IntLit
, Type
, traverseSubExprs
, mapSubExprs
, foldSubExprs
, traverseNames
, foldNames
, mapNames
) where

import           Control.Monad.Identity
import           Control.Monad.State
import           Data.List (intercalate)


import qualified Language.Isabelle.Name as Name
import           Language.Isabelle.Name (Name)
import qualified Language.Isabelle.Output as Output
import           Language.Isabelle.Output (Output(..), out)
import qualified Language.Isabelle.Panic as Panic
import qualified Language.Isabelle.Syntax as Syntax
import Numeric (showHex)


type Type = Expr

data Expr =
    Ctr [Expr] Name
  | Binder String [Expr] Expr
  | BinOp Expr Expr Expr
  | App Expr [Expr]
  | TApp Expr [Type]
  | Var Name
  | ConstrainT Expr Type
  | IntLitCtr
      Integer
      Bool -- true if this should be printed as hex
  | Undefined Type String
  | Let [Expr] Expr
  | Case Expr [(Expr,Expr)]
  | EmptyExpr
  deriving (Eq, Ord, Show)

pattern IntLit :: Integer -> Expr
pattern IntLit i <- IntLitCtr i _ where
  IntLit i = IntLitCtr i False

traverseSubExprs :: forall m. Monad m => (Expr -> m Expr) -> Expr -> m Expr
traverseSubExprs f = go
  where
    go :: Expr -> m Expr
    go e = f =<< case e of
      Ctr es nm -> Ctr <$> mapM go es <*> pure nm
      Binder str nms e1 -> Binder <$> pure str <*> pure nms <*> go e1
      BinOp e1 e2 e3 -> BinOp <$> go e1 <*> go e2 <*> go e3
      App e1 es -> App <$> go e1 <*> mapM go es
      TApp e1 ts -> TApp <$> go e1 <*> mapM go ts
      Var nm -> Var <$> pure nm
      ConstrainT e1 t -> ConstrainT <$> go e1 <*> pure t
      IntLitCtr i b -> IntLitCtr <$> pure i <*> pure b
      Undefined tp msg -> Undefined <$> go tp <*> pure msg
      Let bs e1 -> Let <$> mapM go bs <*> go e1
      Case e1 es -> Case <$> go e1 <*> mapM (\(e2,e3) -> (,) <$> go e2 <*> go e3) es
      EmptyExpr -> pure EmptyExpr

liftIdentity :: (forall m. Monad m => (x -> m x) -> y -> m y) -> (x -> x) -> y -> y
liftIdentity f g e = runIdentity (f (\e' -> Identity (g e')) e)

mapSubExprs :: (Expr -> Expr) -> Expr -> Expr
mapSubExprs = liftIdentity traverseSubExprs

foldSubExprs :: (Expr -> a -> a) -> Expr -> a -> a
foldSubExprs f e st =
  execState (traverseSubExprs (\e' -> modify (\s -> f e' s) >> return e) e) st

traverseNames :: forall m. Monad m => (Name.Name -> m Name.Name) -> Expr -> m Expr
traverseNames f = traverseSubExprs $ \case
  Ctr args nm -> Ctr <$> pure args <*> f nm
  Var nm -> Var <$> f nm
  e -> pure e

mapNames :: (Name.Name -> Name.Name) -> Expr -> Expr
mapNames = liftIdentity traverseNames


foldNames :: (Name.Name -> a -> a) -> Expr -> a -> a
foldNames f e st =
  execState (traverseNames (\nm -> modify (\s -> f nm s) >> return nm) e) st

mkTAppSyn :: Type -> [Type] -> Expr
mkTAppSyn body ts = Ctr (body:ts) $
  Name.Name (Name.TheoryName "Cryptol" False)
    "TApp" (Syntax.ListSyn Syntax.Prefix "," "`{" "}" ) Name.Term

exprToString :: Output.HasOutput => Expr -> String
exprToString = go
  where
    braks :: Expr -> String
    braks te = case te of
      Var{} -> go te
      Ctr [] _ -> go te
      IntLit{} -> go te
      Binder{} -> go te -- adds brackets itself
      _ -> Output.brackets $ go te

    braks_postfix :: Expr -> String
    braks_postfix te = case te of
      Ctr _ nm | Syntax.InfixSyn{} <- Name.nmSyn nm -> braks te
      Ctr _ nm | Syntax.ListSyn{} <- Name.nmSyn nm -> braks te
      BinOp{} -> braks te
      _ -> go te

    abs_arg :: Expr -> String
    abs_arg te = case te of
      ConstrainT{} -> braks te
      _ -> go te

    go :: Expr -> String
    go te = case te of
      Ctr [] nm |
        Syntax.SymbolSyn s <- Name.nmSyn nm -> s
      Ctr [] nm |
        Syntax.InfixSyn s <- Name.nmSyn nm -> s
      Ctr [] nm |
        Syntax.NoSyn <- Name.nmSyn nm -> out nm
      Ctr es nm -> case (Name.nmSyn nm, es) of
        (Syntax.InfixSyn s, [e1,e2]) ->  Output.spaces $
          [ braks e1, s, braks e2 ]
        (Syntax.Symbol Syntax.Prefix s, _) -> Output.spaces $
          (s:(map braks es))
        (Syntax.MixFix1 s1 s2, [e]) -> s1 ++ go e ++ s2
        (Syntax.MixFix2 s1 s2, [e1, e2]) -> s1 ++ go e1 ++ s2 ++ braks_postfix e2
        (Syntax.MixFix3 s1 s2 s3, [e1, e2, e3]) -> Output.spaces $
          [ s1, go e1, s2, braks e2, s3, braks e3 ]
        (Syntax.ListSyn Syntax.Nofix sep start end, _) ->
          start ++ intercalate sep (map go es) ++ end
        (Syntax.ListSyn fix sep start end, (body:es')) -> case fix of
          Syntax.Prefix -> braks body ++ start ++ intercalate sep (map go es') ++ end
          Syntax.Postfix -> start ++ intercalate sep (map go es') ++ end ++ braks body
          _ -> bad
        (Syntax.NoSyn, _) -> case Name.isTypeK (Name.nmKind nm) of
          True -> (Output.brackets $ intercalate "," (map go es)) ++ " " ++ out nm
          False -> out nm ++ " " ++ intercalate " " (map braks es)
        _ -> bad
      Binder bstr nms e ->
        Output.brackets $ bstr
          ++ (Output.spaces $ map abs_arg nms)
          ++ ". " ++ (Output.indent 1 $ braks e)
      BinOp e1 op e2 -> Output.spaces
        ([braks e1, go op, braks e2])
      App e' args->
        go e' ++ " " ++ (Output.spaces (map braks args))
      TApp e ts -> go $ mkTAppSyn e ts
      Var nm -> out nm
      ConstrainT e1 typ -> out e1 ++ " :: " ++ out typ
      IntLitCtr s False -> show s
      IntLitCtr s True -> "0x" ++ (showHex s "")
      Undefined tp msg -> Output.brackets $ "undefined ''" ++ msg ++ "'' :: " ++ out tp
      Let bs e1 ->
        Output.line ++ "let" ++ (Output.indent 1 $ Output.line ++
            Output.lines (Output.addSep ";" (map out bs))) ++ Output.line ++ "in " ++ (Output.indent 1 $ (braks e1))
      Case e [(pat,body)] ->
        Output.spaces $ ["case", Output.out e, "of", Output.out pat, "\\<Rightarrow>", Output.out body]
      Case e es -> Output.lines $
        [ Output.spaces ["case", Output.out e, "of"] ]
        ++
        (Output.indent 1 $ 
          Output.addSepPrefix "| " $ (map (\(pat,body) -> 
            Output.spaces [ Output.out pat, "\\<Rightarrow>", Output.brackets $ Output.out body ]) es))
      EmptyExpr -> ""
      where
        bad = Panic.panic "Output Expr: Unexpected signature" [show te]

instance Output Expr where
  out = exprToString
