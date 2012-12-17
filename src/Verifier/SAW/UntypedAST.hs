{-# LANGUAGE FlexibleInstances #-}
module Verifier.SAW.UntypedAST
  ( Module(..) 
  , ModuleName, mkModuleName
  , Import(..)
  , Decl(..)
  , ImportConstraint(..)
  , ImportName(..)
  , CtorDecl(..)
  , Term(..)
  , asApp
  , ParamType(..)
  , Pat(..)
  , FieldName
  , Ident, localIdent, asLocalIdent, mkIdent, identModule, setIdentModule
  , Sort, mkSort, sortOf
  , badTerm
  , module Verifier.SAW.Position
  ) where

import Control.Exception (assert)
import Verifier.SAW.Position
import Verifier.SAW.TypedAST 
  ( ModuleName, mkModuleName
  , Sort, mkSort, sortOf
  , FieldName
  , isIdent
  )

-- | Identifiers represent a compound name (e.g., Prelude.add).
data Ident = LocalIdent String
           | Ident ModuleName String
  deriving (Eq, Ord)

instance Show Ident where
  show (LocalIdent s) = s
  show (Ident m s) = shows m ('.':s)

mkIdent :: Maybe ModuleName -> String -> Ident
mkIdent mnm nm = assert (isIdent nm) $ 
  case mnm of
    Nothing -> LocalIdent nm
    Just m -> Ident m nm

localIdent :: String -> Ident
localIdent = mkIdent Nothing

asLocalIdent :: Ident -> Maybe String
asLocalIdent (LocalIdent s) = Just s
asLocalIdent _ = Nothing


identModule :: Ident -> Maybe ModuleName
identModule (Ident m _) = Just m
identModule (LocalIdent _) = Nothing

setIdentModule :: Ident -> ModuleName -> Ident
setIdentModule (LocalIdent nm) m = Ident m nm
setIdentModule (Ident _ nm) m = Ident m nm

-- | Parameter type
data ParamType
  = NormalParam
  | ImplicitParam
  | InstanceParam
  | ProofParam
  deriving (Eq, Ord, Show)

data Term
  = Var (PosPair Ident)
  | Unused (PosPair String)
    -- | References a constructor.
  | Con (PosPair Ident)
  | Sort Pos Sort
  | Lambda Pos [(ParamType,[Pat],Term)] Term
  | App Term ParamType Term
    -- | Pi is the type of a lambda expression.
  | Pi ParamType [Pat] Term Pos Term
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
 deriving (Show)

-- | A pattern used for matching a variable.
data Pat
  = PVar (PosPair String)
  | PUnused (PosPair String)
  | PTuple Pos [Pat]
  | PRecord Pos [(PosPair FieldName, Pat)]
  | PCtor (PosPair Ident) [Pat]
--  | PIntLit Pos Integer
  deriving (Eq, Ord, Show)

instance Positioned Term where
  pos t =
    case t of
      Var i                -> pos i
      Unused i             -> pos i
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
      TypeConstraint _ p _ -> p
      Paren p _            -> p
      LetTerm p _ _        -> p
      IntLit p _           -> p
      BadTerm p            -> p

instance Positioned Pat where
  pos pat =
    case pat of
      PVar i      -> pos i
      PUnused i   -> pos i
      PTuple p _  -> p
      PRecord p _ -> p
      PCtor i _   -> pos i
--      PIntLit p _ -> p

badTerm :: Pos -> Term
badTerm = BadTerm

-- | Constructor declaration.
data CtorDecl = Ctor (PosPair String) Term
  deriving (Show)

data Module = Module (PosPair ModuleName) [Import] [Decl]

data Import = Import Bool
                     (PosPair ModuleName)
                     (Maybe (PosPair String))
                     (Maybe ImportConstraint)

-- Data declarations introduce an operator for each constructor, and an operator for the type.
data Decl
   = TypeDecl [(PosPair String)] Term
   | DataDecl (PosPair String) Term [CtorDecl]
   | TermDef (PosPair String) [(ParamType, Pat)] Term
  deriving (Show)

data ImportConstraint
  = SpecificImports [ImportName]
  | HidingImports [ImportName]
 deriving (Eq, Ord, Show)

data ImportName
  = SingleImport (PosPair String)
  | AllImport    (PosPair String)
  | SelectiveImport (PosPair String) [PosPair String]
  deriving (Eq, Ord, Show)

asApp :: Term -> (Term,[Term])
asApp = go []
  where go l (Paren _ t) = go l t
        go l (App t _ u) = go (u:l) t
        go l t = (t,l)