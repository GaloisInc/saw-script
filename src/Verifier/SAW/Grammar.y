{
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Grammar 
  ( Decl(..)
  , Expr(..)
  , parseSAW
  ) where

import Control.Applicative ((<$>))
import Control.Monad
import Verifier.SAW.UntypedAST
import Verifier.SAW.Lexer
import System.Directory (getCurrentDirectory)
}

%name parseSAW
--%expect 0
%tokentype { Positioned Token }
%monad { Parser }
%lexer { lexer } { Positioned _ TEnd }
%error { parseError }
%expect 0

%token
  '('     { Positioned _ (TKey "(") }
  ')'     { Positioned _ (TKey ")") }
  '->'    { Positioned _ (TKey "->") }
  '.'     { Positioned _ (TKey ".") }
  ';'     { Positioned _ (TKey ";") }
  '::'    { Positioned _ (TKey "::") }
  '='     { Positioned _ (TKey "=") }
  '?'     { Positioned _ (TKey "?") }
  '??'    { Positioned _ (TKey "??") }
  '???'   { Positioned _ (TKey "???") }
  '\\'    { Positioned _ (TKey "\\") }
  '{'     { Positioned _ (TKey "{") }
  '}'     { Positioned _ (TKey "}") }
  'data'  { Positioned _ (TKey "data") }
  'where' { Positioned _ (TKey "where") }
  var     { Positioned _ (TSym _) }
  nat     { Positioned _ (TNat _) }

%nonassoc IMPLICIT
%nonassoc '(' ')'
%nonassoc '?' '??' '???'
%left APP
%right '->'
%nonassoc '::'
%nonassoc ';'
%%

SAWDecls :: { [Decl] }
SAWDecls : list(SAWDecl) { $1 }

Ident :: { Positioned Ident }
Ident : var { Positioned (pos $1) (tokSym (val $1)) }

SAWDecl :: { Decl }
SAWDecl : Expr '::' Expr ';' { TypeDecl (undefined $1) $3 }
        | 'data' Ident '::' Expr 'where' '{' RCtorDeclList '}' { DataDecl $2 $4 (reverse $7) }
        | Expr '=' Expr ';' { TermDef $1 $3 }

CtorDecl :: { CtorDecl }
CtorDecl : list1(Ident) '::' Expr ';' { Ctor $1 $3 }

RCtorDeclList :: { [CtorDecl] }
RCtorDeclList : {- empty -} { [] }
              | RCtorDeclList CtorDecl { $2 : $1 }

AtomExpr :: { Expr }
AtomExpr : nat                  { IntLit (pos $1) (tokNat (val $1)) }
         | Ident                { Ident $1 }
         |   '(' Expr ')'       { Paren (pos $1) $2 }
         |   '?' AtomExpr       { ParamType (pos $1) ImplicitParam $2 }
         |  '??' AtomExpr       { ParamType (pos $1) InstanceParam $2 }
         | '???' AtomExpr       { ParamType (pos $1)    ProofParam $2 }

Expr :: { Expr }
Expr : AtomExpr { $1 }
     | AtomExpr Expr %prec APP  { App $1 $2 }
     | Expr '::' Expr           { TypeConstraint $1 (pos $2) $3 }
     | Expr '->' Expr           {% mkTypeLambda (pos $2) $1 $3 }
     | '\\' Expr  '->' Expr     {% mkValueLambda (pos $1) $2 $4 }

-- A list of 0 or more p's, terminated by q's
rlist(p) : {- empty -}       { [] }
         | rlist(p) p   { $2 : $1 }

-- A list of 0 or more p's, terminated by q's
list(p) : {- empty -} { [] }
        | rlist1(p) { reverse $1 }

-- A reversed list of at least 1 p's
rlist1(p) : p           { [$1]    }
          | rlist1(p) p { $2 : $1 }

-- A list of at least 1 p's
list1(p) : rlist1(p)   { reverse $1 }

fst(p,q) : p q { $1 }

termBy(p,q) : list(fst(p,q)) { $1 }

{
paramTypeToken :: ParamType -> String
paramTypeToken tp =
  case tp of
    NormalParam -> ""
    ImplicitParam -> "?"
    InstanceParam -> "??"
    ProofParam -> "???"

parseError :: Positioned Token -> Parser a
parseError pt = do
  addError (pos pt) (UnexpectedToken (val pt))
  fail $ (ppPos "" (pos pt)) ++ "\n  " ++ (ppToken (val pt))

addParseError :: Pos -> String -> Parser ()
addParseError p s = addError p (ParseError s)

unexpectedIntLiteral :: Pos -> Integer -> Parser ()
unexpectedIntLiteral p _ = addParseError p "Unexpected integer literal."

unexpectedParameterAnnotation :: Pos -> ParamType -> Parser ()
unexpectedParameterAnnotation p _ = 
  addParseError p "Multiple parameter annotations are not supported."

unexpectedTypeConstraint :: Pos -> Parser ()
unexpectedTypeConstraint p = addParseError p "Unexpected type constraint."

unexpectedLambda :: Pos -> Parser ()
unexpectedLambda p = addParseError p "Unexpected lambda expression"

unexpectedOpenParen :: Pos -> Parser ()
unexpectedOpenParen p = addParseError p "Unexpected parenthesis"

mergeParamType :: ParamType -> Pos -> ParamType -> Parser ParamType
mergeParamType NormalParam _ tp = return tp
mergeParamType pt p mpt = do
  unexpectedParameterAnnotation p mpt >> return pt

-- Attempts to parses an expression as a list of identifiers.
-- Will return a value on all expressions, but may add errors to parser state.
asVarList :: Expr -> Parser [Positioned Ident]
asVarList (IntLit p i) = unexpectedIntLiteral p i >> return []
asVarList (Ident pi) = return [pi]
asVarList (ParamType p pt _) = unexpectedParameterAnnotation p pt >> return []
asVarList (App x y) = liftM2 (++) (asVarList x) (asVarList y)
asVarList (TypeConstraint _ p _) = unexpectedTypeConstraint p >> return []
asVarList (TypeLambda  p _ _) = unexpectedLambda p >> return []
asVarList (ValueLambda p x e) = unexpectedLambda p >> return []
asVarList (Paren p (Paren _ e)) = asVarList (Paren p e)
asVarList (Paren _ (Ident pi)) = return [pi] 
asVarList (Paren p _) = unexpectedOpenParen p >> return []
asVarList BadExpression{} = return []

mkTypeLambda :: Pos -> Expr -> Expr -> Parser Expr
mkTypeLambda ptp l (asTypeLambda -> (l2,r)) = do
  let impl (IntLit p i) _ = unexpectedIntLiteral p i >> return []
      impl (ParamType p pt e) ppt = impl e =<< mergeParamType ppt p pt
      impl (App x y) ppt = liftM2 (++) (impl x ppt) (impl y ppt)
      impl (TypeConstraint e _ t) ppt =
        fmap (\v -> (pos v, ppt, val v, t)) <$> asVarList e
      impl (Paren _ e) ppt = impl e ppt
      impl e ppt = return [(exprPos e, ppt, "_", e)]
  params <- impl l NormalParam   
  return $ TypeLambda ptp (params ++ l2) r

mkValueLambda :: Pos -> Expr -> Expr -> Parser Expr
mkValueLambda _ _ _ = undefined
}
