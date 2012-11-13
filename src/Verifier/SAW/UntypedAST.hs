module Verifier.SAW.UntypedAST
  ( module Verifier.SAW.Position
  , Ident, mkIdent, unusedIdent
  , Sort, mkSort, sortOf
  , ParamType(..)
  , LambdaBinding
  , Expr(..)
  , badExpr
  , CtorDecl(..)
  , Decl(..)
  ) where

import Verifier.SAW.Position

newtype Ident = Ident String
  deriving (Eq, Ord, Show)

mkIdent :: String -> Ident
mkIdent = Ident

unusedIdent :: Ident
unusedIdent = Ident "_"

newtype Sort = SortCtor Integer
  deriving (Eq, Ord, Show)

mkSort :: Integer -> Sort
mkSort i | 0 <= i = SortCtor i
         | otherwise = error "Negative index given to sort."

-- | Returns sort of the given sort.
sortOf :: Sort -> Sort
sortOf (SortCtor i) = SortCtor (i + 1)

data ParamType
  = NormalParam
  | ImplicitParam
  | InstanceParam
  | ProofParam
  deriving (Eq, Ord, Show)

data Expr
  = IntLit Pos Integer
  | Var (PosPair Ident)
  | Con (PosPair Ident)
  | Sort Pos Sort
  | Lambda Pos [LambdaBinding Expr] Expr
  | App Expr ParamType Expr
    -- | Pi is the type of a lambda expression.
  | Pi ParamType [PosPair Ident] Expr Pos Expr
    -- | Tuple expressions and their type.
  | TupleValue Pos [Expr]
  | TupleType Pos [Expr]
    -- | A record value.
  | RecordValue Pos [(PosPair Ident, Expr)]
    -- | The value stored in a record.
  | RecordSelector Expr (PosPair Ident)
    -- | Type of a record value.
  | RecordType  Pos [(PosPair Ident, Expr)]
    -- | Arguments to an array constructor.  
  | ArrayValue Pos [Expr]
  | Paren Pos Expr
  -- * Expressions that may appear in parsing, but do not affect value.
  | TypeConstraint Expr Pos Expr
  | BadExpression Pos
 deriving (Eq, Ord, Show)

type LambdaBinding t = (ParamType, t)

instance Positioned Expr where
  pos e =
    case e of
      IntLit p _           -> p
      Var i                -> pos i
      Con i                -> pos i
      TupleValue p _       -> p
      TupleType p _        -> p
      App x _ _            -> pos x
      RecordValue p _      -> p
      RecordType p _       -> p
      RecordSelector _ i   -> pos i
      ArrayValue p _       -> p
      Paren p _            -> p
      Lambda p _ _         -> p
      Pi _ _ _ p _         -> p
      TypeConstraint _ p _ -> p
      Sort p _             -> p
      BadExpression p      -> p

badExpr :: Pos -> Expr
badExpr = BadExpression

-- | Constructor declaration.
data CtorDecl = Ctor (PosPair Ident) Expr
  deriving (Show)

-- Data declarations introduce an operator for each constructor, and an operator for the type.
data Decl
   = TypeDecl [(PosPair Ident)] Expr
   | DataDecl (PosPair Ident) Expr [CtorDecl]
   | TermDef (PosPair Ident) [LambdaBinding Expr] Expr
  deriving (Show)