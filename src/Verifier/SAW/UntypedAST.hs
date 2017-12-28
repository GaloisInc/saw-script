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
  , asApp
  , mkTupleValue
  , mkTupleType
  , mkTupleSelector
  , mkRecordValue
  , mkRecordType
  , mkFieldNameTerm
  , Pat(..), ppPat
  , mkPTuple
  , mkPRecord
  , mkFieldNamePat
  , SimplePat(..)
  , FieldName
  , Ident, localIdent, asLocalIdent, mkIdent, identModule, setIdentModule
  , Sort, mkSort, sortOf
  , badTerm
  , module Verifier.SAW.Position
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif
import Control.Exception (assert)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Verifier.SAW.Position
import Verifier.SAW.TypedAST
  ( ModuleName, mkModuleName
  , Sort, mkSort, sortOf
  , FieldName
  , isIdent
  , Prec(..), ppAppParens
  , commaSepList
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

data Term
  = Var (PosPair Ident)
  | Unused (PosPair String)
    -- | References a constructor.
  | Con (PosPair Ident)
  | Sort Pos Sort
  | Lambda Pos [([SimplePat],Term)] Term
  | App Term Term
    -- | Pi is the type of a lambda expression.
  | Pi [SimplePat] Term Pos Term
    -- | Tuple expressions and their type.
  | UnitValue Pos
  | UnitType Pos
  | PairValue Pos Term Term
  | PairType Pos Term Term
  | PairLeft Pos Term
  | PairRight Pos Term
    -- | An empty record value.
  | EmptyValue Pos
    -- | A record extended with another field.
  | FieldValue (Term, Term) Term
    -- | The value stored in a record.
  | RecordSelector Term Term
    -- | Type of an empty record value.
  | EmptyType Pos
    -- | Type of a record extended with another field.
  | FieldType (Term, Term) Term
    -- | Identifies a type constraint on the term.
  | TypeConstraint Term Pos Term
    -- | Arguments to an array constructor.
  | Paren Pos Term
  | NatLit Pos Integer
  | StringLit Pos String
    -- | Vector literal.
  | VecLit Pos [Term]
  | BadTerm Pos
 deriving (Show)

-- | A pattern used for matching a variable.
data SimplePat
  = PVar (PosPair String)
  | PUnused (PosPair String)
  deriving (Eq, Ord, Show)

-- | A pattern used for matching a variable.
data Pat
  = PSimple SimplePat
  | PUnit Pos
  | PPair Pos Pat Pat
  | PEmpty Pos
  | PField (Pat, Pat) Pat
  | PCtor (PosPair Ident) [Pat]
  | PString Pos String
  deriving (Eq, Ord, Show)

mkPTuple :: Pos -> [Pat] -> Pat
mkPTuple p = foldr (PPair p) (PUnit p)

mkPRecord :: Pos -> [(Pat, Pat)] -> Pat
mkPRecord p = foldr PField (PEmpty p)

mkFieldNamePat :: PosPair FieldName -> Pat
mkFieldNamePat (PosPair p s) = PString p s

asPTuple :: Pat -> Maybe [Pat]
asPTuple (PUnit _)     = Just []
asPTuple (PPair _ x y) = (x :) <$> asPTuple y
asPTuple _             = Nothing

asPRecord :: Pat -> Maybe [(Pat, Pat)]
asPRecord (PEmpty _)   = Just []
asPRecord (PField x y) = (x :) <$> asPRecord y
asPRecord _            = Nothing

ppPat :: Prec -> Pat -> Doc
ppPat _ (asPTuple -> Just l) = parens $ commaSepList (ppPat PrecNone <$> l)
ppPat _ (PSimple (PVar pnm)) = text (val pnm)
ppPat _ (PSimple (PUnused pnm)) = text (val pnm)
ppPat _ (PUnit _) = text "()"
ppPat _ (PPair _ x y) = parens $ ppPat PrecNone x <+> text "#" <+> ppPat PrecNone y
ppPat _ (asPRecord -> Just fl) = braces $ commaSepList (ppFld <$> fl)
  where ppFld (fld,v) = ppPat PrecNone fld <+> equals <+> ppPat PrecNone v
ppPat _ (PEmpty _) = text "{}"
ppPat _ (PField f p) = braces $ commaSepList [ppFld f, other]
  where ppFld (fld,v) = ppPat PrecNone fld <+> equals <+> ppPat PrecNone v
        other = text "..." <+> equals <+> ppPat PrecNone p
ppPat prec (PCtor pnm l) = ppAppParens prec $
  hsep (text (show (val pnm)) : fmap (ppPat PrecArg) l)
ppPat _ (PString _ s) = text (show s)

instance Positioned Term where
  pos t =
    case t of
      Var i                -> pos i
      Unused i             -> pos i
      Con i                -> pos i
      Sort p _             -> p
      Lambda p _ _         -> p
      App x _              -> pos x
      Pi _ _ p _           -> p
      UnitValue p          -> p
      UnitType p           -> p
      PairValue p _ _      -> p
      PairType p _ _       -> p
      PairLeft p _         -> p
      PairRight p _        -> p
      EmptyValue p         -> p
      FieldValue _ t'      -> pos t'
      RecordSelector _ i   -> pos i
      EmptyType p          -> p
      FieldType _ t'       -> pos t'
      TypeConstraint _ p _ -> p
      Paren p _            -> p
      NatLit p _           -> p
      StringLit p _        -> p
      VecLit p _           -> p
      BadTerm p            -> p

instance Positioned SimplePat where
  pos pat =
    case pat of
      PVar i      -> pos i
      PUnused i   -> pos i

instance Positioned Pat where
  pos pat =
    case pat of
      PSimple i   -> pos i
      PUnit p     -> p
      PPair p _ _ -> p
      PEmpty p    -> p
      PField f _  -> pos (fst f)
      PCtor i _   -> pos i
      PString p _ -> p

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

data DeclQualifier
  = NoQualifier
  | PrimitiveQualifier
  | AxiomQualifier
 deriving (Eq, Show)

-- Data declarations introduce an operator for each constructor, and an operator for the type.
data Decl
   = TypeDecl DeclQualifier [(PosPair String)] Term
   | DataDecl (PosPair String) Term [CtorDecl]
   | TermDef (PosPair String) [Pat] Term
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
        go l (App t u)   = go (u:l) t
        go l t = (t,l)

mkTupleValue :: Pos -> [Term] -> Term
mkTupleValue p = foldr (PairValue p) (UnitValue p)

mkTupleType :: Pos -> [Term] -> Term
mkTupleType p = foldr (PairType p) (UnitType p)

mkTupleSelector :: Term -> PosPair Integer -> Term
mkTupleSelector t i =
  case compare (val i) 1 of
    LT -> error "mkTupleSelector: non-positive index"
    EQ -> PairLeft (_pos i) t
    GT -> mkTupleSelector (PairRight (_pos i) t) i{ val = val i - 1 }

mkRecordValue :: Pos -> [(Term, Term)] -> Term
mkRecordValue p = foldr FieldValue (EmptyValue p)

mkRecordType :: Pos -> [(Term, Term)] -> Term
mkRecordType p = foldr FieldType (EmptyType p)

mkFieldNameTerm :: PosPair FieldName -> Term
mkFieldNameTerm (PosPair p s) = StringLit p s
