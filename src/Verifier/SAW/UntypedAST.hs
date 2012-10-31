module Verifier.SAW.UntypedAST
  ( module Verifier.SAW.Position
  , Ident
  , ParamType(..)
  , LambdaBinding
  , AppExpr(..)
  , Expr(..)
  , badExpr, badAppExpr
  , CtorDecl(..)
  , Decl(..)
  ) where

import Verifier.SAW.Position

type Ident = String

data ParamType
  = NormalParam
  | ImplicitParam
  | InstanceParam
  | ProofParam
  deriving (Eq, Ord, Show)

data AppExpr
  = IntLit Pos Integer
  | Var (PosPair Ident)
  | Con (PosPair Ident)
    -- | Tuple expressions and their type.
  | TupleValue Pos [Expr]
  | TupleType Pos [Expr]
  | App AppExpr AppExpr
    -- | Record expressions and their type.
  | RecordValue Pos [(PosPair Ident, Expr)]
  | RecordType  Pos [(PosPair Ident, Expr)]
  | RecordSelector AppExpr (PosPair Ident)
    -- | Arguments to an array constructor.
  | ArrayValue Pos [Expr]
  | Paren Pos Expr
  | ParamType Pos ParamType AppExpr
  | BadExpression Pos
 deriving (Eq, Ord, Show)

type LambdaBinding e = (ParamType, e)

data Expr
  = AppExpr AppExpr
    -- | Pi is the type of a lambda expression.
  | Lambda Pos [LambdaBinding AppExpr] Expr
  | Pi ParamType [PosPair Ident] Expr Pos Expr
  -- * Expressions that may appear in parsing, but do not affect value.
  | TypeConstraint Expr Pos Expr
  deriving (Eq, Ord, Show)

instance Positioned AppExpr where
  pos e =
    case e of
      IntLit p _         -> p
      Var i              -> pos i
      Con i              -> pos i
      TupleValue p _     -> p
      TupleType p _      -> p
      App x _            -> pos x
      RecordValue p _    -> p
      RecordType p _     -> p
      RecordSelector _ i -> pos i
      ArrayValue p _     -> p
      Paren p _          -> p
      ParamType p _ _    -> p
      BadExpression p    -> p
 
instance Positioned Expr where
  pos e =
    case e of
      AppExpr ae -> pos ae
      Lambda p _ _    -> p
      Pi _ _ _ p _      -> p
      TypeConstraint _ p _ -> p

badAppExpr :: Pos -> AppExpr
badAppExpr = BadExpression

badExpr :: Pos -> Expr
badExpr = AppExpr . BadExpression

-- | Constructor declaration.
data CtorDecl = Ctor (PosPair Ident) Expr
  deriving (Show)

data Decl
   = TypeDecl [(PosPair Ident)] Expr
   | DataDecl (PosPair Ident) Expr [CtorDecl]
   | TermDef (PosPair Ident) [LambdaBinding AppExpr] Expr
  deriving (Show)