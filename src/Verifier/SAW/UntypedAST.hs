{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}

{- |
Module      : Verifier.SAW.UntypedAST
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.UntypedAST
  ( Module(..)
  , ModuleName, mkModuleName
  , Import(..)
  , Decl(..)
  , DeclQualifier(..)
  , ImportConstraint(..)
  , ImportName(..)
  , CtorDecl(..)
  , Term(..)
  , TermVar(..)
  , asApp
  , mkTupleValue
  , mkTupleType
  , mkTupleSelector
  , FieldName
  , Sort, mkSort, propSort, sortOf
  , badTerm
  , module Verifier.SAW.Position
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif

import Verifier.SAW.Position
import Verifier.SAW.TypedAST
  ( ModuleName, mkModuleName
  , Sort, mkSort, propSort, sortOf
  , FieldName
  )

data Term
  = Name (PosPair String)
  | Sort Pos Sort
  | App Term Term
  | Lambda Pos TermCtx Term
  | Pi Pos TermCtx Term
  | Recursor (PosPair String)
  | RecursorProj Term (PosPair String)
    -- | New-style records
  | RecordValue Pos [(PosPair String, Term)]
  | RecordType Pos [(PosPair String, Term)]
  | RecordProj Term String
    -- | Old-style pairs
  | OldPairValue Pos Term Term
  | OldPairType Pos Term Term
  | OldPairLeft Term
  | OldPairRight Term
    -- | Identifies a type constraint on the term, i.e., a type ascription
  | TypeConstraint Term Pos Term
  | NatLit Pos Integer
  | StringLit Pos String
    -- | Vector literal.
  | VecLit Pos [Term]
  | BadTerm Pos
 deriving (Show)

-- | A pattern used for matching a variable.
data TermVar
  = TermVar (PosPair String)
  | UnusedVar Pos
  deriving (Eq, Ord, Show)

-- | A context of 0 or more variable bindings, with types
type TermCtx = [(TermVar,Term)]

instance Positioned Term where
  pos t =
    case t of
      Name i               -> pos i
      Sort p _             -> p
      Lambda p _ _         -> p
      App x _              -> pos x
      Pi p _ _             -> p
      Recursor i           -> pos i
      RecursorProj x _     -> pos x
      RecordValue p _      -> p
      RecordType p _       -> p
      RecordProj x _       -> pos x
      OldPairValue p _ _   -> p
      OldPairType p _ _    -> p
      OldPairLeft x        -> pos x
      OldPairRight x       -> pos x
      TypeConstraint _ p _ -> p
      NatLit p _           -> p
      StringLit p _        -> p
      VecLit p _           -> p
      BadTerm p            -> p

instance Positioned TermVar where
  pos (TermVar i) = pos i
  pos (UnusedVar p) = p

badTerm :: Pos -> Term
badTerm = BadTerm

-- | A constructor declaration of the form @c (x1 :: tp1) .. (xn :: tpn) :: tp@
data CtorDecl = Ctor (PosPair String) TermCtx Term deriving (Show)

-- | The "qualifiers" for declarations @foo :: type@
data DeclQualifier
  = NoQualifier
    -- ^ Indicates this declaration should have an accompanying definition
  | PrimitiveQualifier
    -- ^ Indicates a declaration of a primitive
  | AxiomQualifier
    -- ^ Indicates a declaration of an axiom
 deriving (Eq, Show)

-- | A top-level declaration in a saw-core file
data Decl
   = TypeDecl DeclQualifier (PosPair String) Term
     -- ^ A declaration of something having a type, where the declaration
     -- qualifier states what flavor of thing it is
   | DataDecl (PosPair String) [(TermVar, Term)] Term [CtorDecl]
     -- ^ A declaration of an inductive data types, with a name, a parameter
     -- context, a return type, and a list of constructor declarations
   | TermDef (PosPair String) [(TermVar, Maybe Term)] Term
     -- ^ A declaration of a term having a definition, with some variables that
     -- are allowed to have or not have type annotations
  deriving (Show)

-- | A specification of the names imported from another module
data ImportName
  = SingleImport (PosPair String)
    -- ^ Import only a single name
  | AllImport    (PosPair String)
    -- ^ Import a datatype and all its constructors
  | SelectiveImport (PosPair String) [PosPair String]
    -- ^ Import a datatype and some of its constructors
  deriving (Eq, Ord, Show)

-- | A set of constraints on what to import from a module
data ImportConstraint
  = SpecificImports [ImportName]
    -- ^ Only import the given names
  | HidingImports [ImportName]
    -- ^ Import all but the given names
 deriving (Eq, Ord, Show)

-- | An import declaration
data Import = Import { importQualified :: Bool
                       -- ^ Whether the import is marked as "qualified"
                     , importModName :: PosPair ModuleName
                       -- ^ The name of the module to import
                     , importAsName :: Maybe (PosPair String)
                       -- ^ The local name to use for the import
                     , importConstraints :: Maybe ImportConstraint
                       -- ^ The constraints on what to import
                     }

-- | A module declaration gives:
-- * A name for the module;
-- * A list of imports; AND
-- * A list of top-level declarations
data Module = Module (PosPair ModuleName) [Import] [Decl]

asApp :: Term -> (Term,[Term])
asApp = go []
  where go l (App t u)   = go (u:l) t
        go l t = (t,l)

mkTupleAList :: [Term] -> [(PosPair String, Term)]
mkTupleAList ts =
  zipWith (\i t -> (PosPair (pos t) (show i), t)) [1::Integer ..] ts

-- | Build a tuple value @(x1, .., xn)@ as a record value whose fields are named
-- @1@, @2@, etc. Unary tuples are not allowed.
mkTupleValue :: Pos -> [Term] -> Term
mkTupleValue _ [_] = error "mkTupleValue: singleton tuple!"
mkTupleValue p ts = RecordValue p $ mkTupleAList ts

-- | Build a tuple type @#(x1, .., xn)@ as a record type whose fields are named
-- @1@, @2@, etc. Unary tuple types are not allowed.
mkTupleType :: Pos -> [Term] -> Term
mkTupleType _ [_] = error "mkTupleType: singleton type!"
mkTupleType p tps = RecordType p $ mkTupleAList tps

-- | Build a projection @t.i@ of a tuple
mkTupleSelector :: Term -> Integer -> Term
mkTupleSelector t i =
  if i >= 1 then RecordProj t (show i) else
    error "mkTupleSelector: non-positive index"
