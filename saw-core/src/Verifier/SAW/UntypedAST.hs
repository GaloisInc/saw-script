{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveLift #-}
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

import qualified Language.Haskell.TH.Syntax as TH
import Numeric.Natural

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
  | UnitValue Pos
  | UnitType Pos
    -- | New-style records
  | RecordValue Pos [(PosPair String, Term)]
  | RecordType Pos [(PosPair String, Term)]
  | RecordProj Term String
    -- | Simple pairs
  | PairValue Pos Term Term
  | PairType Pos Term Term
  | PairLeft Term
  | PairRight Term
    -- | Identifies a type constraint on the term, i.e., a type ascription
  | TypeConstraint Term Pos Term
  | NatLit Pos Natural
  | StringLit Pos String
    -- | Vector literal.
  | VecLit Pos [Term]
  | BadTerm Pos
 deriving (Show, TH.Lift)

-- | A pattern used for matching a variable.
data TermVar
  = TermVar (PosPair String)
  | UnusedVar Pos
  deriving (Eq, Ord, Show, TH.Lift)

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
      UnitValue p          -> p
      UnitType p           -> p
      RecordValue p _      -> p
      RecordType p _       -> p
      RecordProj x _       -> pos x
      PairValue p _ _      -> p
      PairType p _ _       -> p
      PairLeft x           -> pos x
      PairRight x          -> pos x
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
data CtorDecl = Ctor (PosPair String) TermCtx Term
  deriving (Show, TH.Lift)

-- | A top-level declaration in a saw-core file
data Decl
   = TypeDecl DefQualifier (PosPair String) Term
     -- ^ A declaration of something having a type, where the declaration
     -- qualifier states what flavor of thing it is
   | DataDecl (PosPair String) TermCtx Term [CtorDecl]
     -- ^ A declaration of an inductive data types, with a name, a parameter
     -- context, a return type, and a list of constructor declarations
   | TermDef (PosPair String) [TermVar] Term
     -- ^ A declaration of a term having a definition, with variables
   | TypedDef (PosPair String) [(TermVar, Term)] Term Term
     -- ^ A definition of something with a specific type, with parameters
  deriving (Show, TH.Lift)

-- | A set of constraints on what 'String' names to import from a module
data ImportConstraint
  = SpecificImports [String]
    -- ^ Only import the given names
  | HidingImports [String]
    -- ^ Import all but the given names
 deriving (Eq, Ord, Show, TH.Lift)

-- | An import declaration
data Import = Import { importModName :: PosPair ModuleName
                       -- ^ The name of the module to import
                     , importConstraints :: Maybe ImportConstraint
                       -- ^ The constraints on what to import
                     }
            deriving (Show, TH.Lift)

-- | Test whether a 'String' name satisfies the constraints of an 'Import'
nameSatsConstraint :: Maybe ImportConstraint -> String -> Bool
nameSatsConstraint Nothing _ = True
nameSatsConstraint (Just (SpecificImports ns)) n = elem n ns
nameSatsConstraint (Just (HidingImports ns)) n = notElem n ns


-- | A module declaration gives:
-- * A name for the module;
-- * A list of imports; AND
-- * A list of top-level declarations
data Module = Module (PosPair ModuleName) [Import] [Decl]
  deriving (Show, TH.Lift)

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

-- | Build a tuple value @(x1, .., xn)@.
mkTupleValue :: Pos -> [Term] -> Term
mkTupleValue p [] = UnitValue p
mkTupleValue _ [x] = x
mkTupleValue p (x:xs) = PairValue (pos x) x (mkTupleValue p xs)

-- | Build a tuple type @#(x1, .., xn)@.
mkTupleType :: Pos -> [Term] -> Term
mkTupleType p [] = UnitType p
mkTupleType _ [x] = x
mkTupleType p (x:xs) = PairType (pos x) x (mkTupleType p xs)

-- | Build a projection @t.i@ of a tuple. NOTE: This function does not
-- work to access the last component in a tuple, since it always
-- generates a @PairLeft@.
mkTupleSelector :: Term -> Natural -> Term
mkTupleSelector t i
  | i == 1    = PairLeft t
  | i > 1     = mkTupleSelector (PairRight t) (i - 1)
  | otherwise = error "mkTupleSelector: non-positive index"
