module Verifier.SAW.UntypedAST
  ( module Verifier.SAW.Position
  , Ident, mkIdent, unusedIdent
  , Sort, mkSort, sortOf
  , ParamType(..)
  , Pat(..)
  , FieldName
  , Term(..)
  , badTerm
  , asApp
  , CtorDecl(..)
  , Decl(..)
  ) where

import Verifier.SAW.Position

newtype Ident = Ident String
  deriving (Eq, Ord)

instance Show Ident where
  show (Ident s) = s

mkIdent :: String -> Ident
mkIdent = Ident

unusedIdent :: Ident
unusedIdent = Ident "_"

newtype Sort = SortCtor { _sortIndex :: Integer }
  deriving (Eq, Ord)

instance Show Sort where
  showsPrec p (SortCtor i) = showParen (p >= 10) (showString "sort " . shows i)

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

type FieldName = String

data Term
  = Var (PosPair Ident)
  | Con (PosPair Ident)
  | Sort Pos Sort
  | Lambda Pos [(ParamType,Ident,Term)] Term
  | App Term ParamType Term
    -- | Pi is the type of a lambda expression.
  | Pi ParamType [PosPair Ident] Term Pos Term
    -- | Tuple expressions and their type.
  | TupleValue Pos [Term]
  | TupleType Pos [Term]
    -- | A record value.
  | RecordValue Pos [(PosPair FieldName, Term)]
    -- | The value stored in a record.
  | RecordSelector Term (PosPair FieldName)
    -- | Type of a record value.
  | RecordType  Pos [(PosPair FieldName, Term)]
    -- | Identifies a type constraint on the term.
  | TypeConstraint Term Pos Term
    -- | Arguments to an array constructor.  
  | Paren Pos Term
  | LetTerm Pos [Decl] Term
  | IntLit Pos Integer
  | BadTerm Pos
 deriving (Eq, Ord, Show)

-- | A pattern used for matching a variable.
data Pat
  = PVar (PosPair Ident)
  | PTuple Pos [Pat]
  | PRecord Pos [(PosPair FieldName, Pat)]
  | PCtor (PosPair Ident) [Pat]
  | PInaccessible Term
  deriving (Eq, Ord, Show)

instance Positioned Term where
  pos t =
    case t of
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
--      ArrayValue p _       -> p
      TypeConstraint _ p _ -> p
      Paren p _            -> p
      LetTerm p _ _        -> p
      IntLit p _           -> p
      BadTerm p            -> p
     

instance Positioned Pat where
  pos pat =
    case pat of
      PVar i      -> pos i
      PCtor i _   -> pos i
      PTuple p _  -> p
      PRecord p _ -> p
      PInaccessible t -> pos t
--      PTypeConstraint _ t -> pos t

badTerm :: Pos -> Term
badTerm = BadTerm

-- | Constructor declaration.
data CtorDecl = Ctor (PosPair Ident) Term
  deriving (Eq, Ord, Show)

-- Data declarations introduce an operator for each constructor, and an operator for the type.
data Decl
   = TypeDecl [(PosPair Ident)] Term
   | DataDecl (PosPair Ident) Term [CtorDecl]
   | TermDef (PosPair Ident) [(ParamType, Pat)] Term
  deriving (Eq, Ord, Show)


asApp :: Term -> (Term,[Term])
asApp = go []
  where go l (App t _ u) = go (u:l) t
        go l t = (t,l)