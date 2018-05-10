{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

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
  , Decl(..)
  , Import(..)
  , ImportConstraint(..)
  , nameSatsConstraint
  , CtorDecl(..)
  , Term(..)
  , TermVar(..)
  , termVarString
  , TermCtx
  , asApp
  , asPiList
  , mkTupleValue
  , mkTupleType
  , mkTupleSelector
  , FieldName
  , Sort, mkSort, propSort, sortOf
  , badTerm
  , module Verifier.SAW.Position
  , moduleName
  , moduleTypedDecls
  , moduleDataDecls
  , moduleCtorDecls
  , moduleTypedDataDecls
  , moduleTypedCtorDecls
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif

import Verifier.SAW.Position
import Verifier.SAW.TypedAST
  ( ModuleName, mkModuleName
  , Sort, mkSort, propSort, sortOf
  , FieldName, DefQualifier
  )

data Term
  = Name (PosPair String)
  | Sort Pos Sort
  | App Term Term
  | Lambda Pos TermCtx Term
  | Pi Pos TermCtx Term
  | Recursor (Maybe ModuleName) (PosPair String)
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
 deriving (Show,Read)

-- | A pattern used for matching a variable.
data TermVar
  = TermVar (PosPair String)
  | UnusedVar Pos
  deriving (Eq, Ord, Show, Read)

-- | Return the 'String' name associated with a 'TermVar'
termVarString :: TermVar -> String
termVarString (TermVar (PosPair _ str)) = str
termVarString (UnusedVar _) = "_"

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
      Recursor _ i         -> pos i
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
data CtorDecl = Ctor (PosPair String) TermCtx Term deriving (Show,Read)

-- | A top-level declaration in a saw-core file
data Decl
   = TypeDecl DefQualifier (PosPair String) Term
     -- ^ A declaration of something having a type, where the declaration
     -- qualifier states what flavor of thing it is
   | DataDecl (PosPair String) TermCtx Term [CtorDecl]
     -- ^ A declaration of an inductive data types, with a name, a parameter
     -- context, a return type, and a list of constructor declarations
   | TermDef (PosPair String) [(TermVar, Maybe Term)] Term
     -- ^ A declaration of a term having a definition, with some variables that
     -- are allowed to have or not have type annotations
  deriving (Show,Read)

-- | A set of constraints on what 'String' names to import from a module
data ImportConstraint
  = SpecificImports [String]
    -- ^ Only import the given names
  | HidingImports [String]
    -- ^ Import all but the given names
 deriving (Eq, Ord, Show, Read)

-- | An import declaration
data Import = Import { importModName :: PosPair ModuleName
                       -- ^ The name of the module to import
                     , importConstraints :: Maybe ImportConstraint
                       -- ^ The constraints on what to import
                     }
            deriving (Show, Read)

-- | Test whether a 'String' name satisfies the constraints of an 'Import'
nameSatsConstraint :: Maybe ImportConstraint -> String -> Bool
nameSatsConstraint Nothing _ = True
nameSatsConstraint (Just (SpecificImports ns)) n = elem n ns
nameSatsConstraint (Just (HidingImports ns)) n = notElem n ns


-- | A module declaration gives:
-- * A name for the module;
-- * A list of imports; AND
-- * A list of top-level declarations
data Module = Module (PosPair ModuleName) [Import] [Decl] deriving (Show, Read)

moduleName :: Module -> ModuleName
moduleName (Module (PosPair _ mnm) _ _) = mnm

-- | Get a list of all names (i.e., definitions, axioms, or primitives) declared
-- in a module, along with their types and qualifiers
moduleTypedDecls :: Module -> [(String, Term)]
moduleTypedDecls (Module _ _ decls) = concatMap helper decls where
  helper :: Decl -> [(String, Term)]
  helper (TypeDecl _ (PosPair _ nm) tm) = [(nm,tm)]
  helper _ = []

-- | Get a list of all datatypes declared in a module
moduleDataDecls :: Module -> [(String,TermCtx,Term,[CtorDecl])]
moduleDataDecls (Module _ _ decls) = concatMap helper decls where
  helper :: Decl -> [(String,TermCtx,Term,[CtorDecl])]
  helper (DataDecl (PosPair _ nm) params tp ctors) = [(nm, params, tp, ctors)]
  helper _ = []

moduleTypedDataDecls :: Module -> [(String,Term)]
moduleTypedDataDecls =
  map (\(nm,p_ctx,tp,_) ->
        (nm, Pi (pos tp) p_ctx tp)) . moduleDataDecls

-- | Get a list of all constructors declared in a module, along with the context
-- of parameters for each one
moduleCtorDecls :: Module -> [(TermCtx,CtorDecl)]
moduleCtorDecls =
  concatMap (\(_,p_ctx,_,ctors) -> map (p_ctx,) ctors) . moduleDataDecls

-- | Get a list of the names and types of all the constructors in a module
moduleTypedCtorDecls :: Module -> [(String,Term)]
moduleTypedCtorDecls =
  concatMap (\(_,p_ctx,_,ctors) ->
              map (\(Ctor (PosPair _ nm) ctx tp) ->
                    (nm, Pi (pos tp) (p_ctx ++ ctx) tp)) ctors)
  . moduleDataDecls

asPiList :: Term -> (TermCtx,Term)
asPiList (Pi _ ctx1 body1) =
  let (ctx2,body2) = asPiList body1 in
  (ctx1 ++ ctx2, body2)
asPiList t = ([], t)

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
