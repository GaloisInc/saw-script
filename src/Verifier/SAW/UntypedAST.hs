module Verifier.SAW.UntypedAST
  ( module Verifier.SAW.Position
  , Ident, mkIdent, unusedIdent
  , Sort, mkSort, sortOf
  , ParamType(..)
  , LambdaBinding
  , Pat(..)
  , Term(..)
  , badTerm
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

data Term
  = IntLit Pos Integer
  | Var (PosPair Ident)
  | Con (PosPair Ident)
  | Sort Pos Sort
  | Lambda Pos [LambdaBinding Pat] Term
  | App Term ParamType Term
    -- | Pi is the type of a lambda expression.
  | Pi ParamType [PosPair Ident] Term Pos Term
    -- | Tuple expressions and their type.
  | TupleValue Pos [Term]
  | TupleType Pos [Term]
    -- | A record value.
  | RecordValue Pos [(PosPair Ident, Term)]
    -- | The value stored in a record.
  | RecordSelector Term (PosPair Ident)
    -- | Type of a record value.
  | RecordType  Pos [(PosPair Ident, Term)]
    -- | Arguments to an array constructor.  
  | ArrayValue Pos [Term]
  | Paren Pos Term
  -- * Termessions that may appear in parsing, but do not affect value.
  | TypeConstraint Term Pos Term
  | BadTerm Pos
 deriving (Eq, Ord, Show)

-- | A pattern used for matching a variable.
data Pat
  = PVar (PosPair Ident)
  | PCtor (PosPair Ident) [Pat]
  | PTuple Pos [Pat]
  | PRecord Pos [(PosPair Ident, Pat)]
  | PInaccessible Term
  | PTypeConstraint Pat Term
  deriving (Eq, Ord, Show)

type LambdaBinding t = (ParamType, t)

instance Positioned Term where
  pos t =
    case t of
      IntLit p _           -> p
      Var i                -> pos i
      Con i                -> pos i
      Sort p _             -> p
      Lambda p _ _         -> p
      App x _ _            -> pos x
      Pi _ _ _ p _         -> p
      TupleValue p _       -> p
      TupleType p _        -> p
      RecordValue p _      -> p
      RecordSelector _ i   -> pos i
      RecordType p _       -> p
      ArrayValue p _       -> p
      Paren p _            -> p
      TypeConstraint _ p _ -> p
      BadTerm p            -> p

instance Positioned Pat where
  pos pat =
    case pat of
      PVar i      -> pos i
      PCtor i _   -> pos i
      PTuple p _  -> p
      PRecord p _ -> p
      PInaccessible t -> pos t
      PTypeConstraint _ t -> pos t

badTerm :: Pos -> Term
badTerm = BadTerm

-- | Constructor declaration.
data CtorDecl = Ctor (PosPair Ident) Term
  deriving (Show)

-- Data declarations introduce an operator for each constructor, and an operator for the type.
data Decl
   = TypeDecl [(PosPair Ident)] Term
   | DataDecl (PosPair Ident) Term [CtorDecl]
   | TermDef (PosPair Ident) [LambdaBinding Pat] Term
  deriving (Show)