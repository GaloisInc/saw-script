module Verifier.SAW.UntypedAST
  ( module Verifier.SAW.Position
  , Ident
  , ParamType(..)
  , Expr(..)
  , exprPos
  , asTypeLambda
  , LambdaArg
  , CtorDecl(..)
  , Decl(..)
  ) where

import Verifier.SAW.Position

data ParamType
  = NormalParam
  | ImplicitParam
  | InstanceParam
  | ProofParam
  deriving (Eq, Ord, Show)

type Ident = String

type LambdaArg = (Pos, ParamType, Ident, Expr)

data Expr
  = IntLit Pos Integer
  | Ident (Positioned Ident)
  | ParamType Pos ParamType Expr
  | App Expr Expr
  | TypeConstraint Expr Pos Expr
  | TypeLambda Pos [LambdaArg] Expr -- Lambda not prefixed with backslash (used for type rules)
  | ValueLambda Pos [LambdaArg] Expr -- Lambda prefixed with backslash ('\'')
  | Paren Pos Expr
  | BadExpression Pos
  deriving (Show)

exprPos :: Expr -> Pos
exprPos (IntLit p _) = p
exprPos (Ident i) = pos i
exprPos (ParamType p _ _) = p
exprPos (App x _) = exprPos x
exprPos (TypeConstraint _ p _) = p
exprPos (TypeLambda _ ((p,_,_,_):_) _) = p
exprPos (TypeLambda p [] _) = p
exprPos (ValueLambda p _ _) = p
exprPos (Paren p _) = p
exprPos (BadExpression p) = p

asTypeLambda :: Expr -> ([LambdaArg], Expr)
asTypeLambda (TypeLambda _ l r) = (l,r)
asTypeLambda e = ([],e)

-- | Constructor declaration.
data CtorDecl = Ctor [Positioned Ident] Expr
  deriving (Show)

data Decl
    = TypeDecl [Positioned Ident] Expr
    | DataDecl (Positioned Ident) Expr [CtorDecl]
    | TermDef Expr Expr  
  deriving (Show)