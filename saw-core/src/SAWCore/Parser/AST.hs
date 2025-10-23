{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

{- |
Module      : SAWCore.Parser.AST
Copyright   : Galois, Inc. 2012-2025
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Parser.AST
  ( Module(..)
  , ModuleName, mkModuleName
  , DefQualifier(..)
  , Decl(..)
  , Import(..)
  , ImportConstraint(..)
  , nameSatsConstraint
  , CtorDecl(..)
  , UTerm(..)
  , UTermVar(..)
  , termVarString
  , termVarLocalName
  , UTermCtx
  , asApp
  , asPiList
  , mkTupleValue
  , mkTupleType
  , mkTupleSelector
  , FieldName
  , Sort, mkSort, propSort, sortOf
  , SortFlags(..), noFlags, sortFlagsLift2, sortFlagsToList, sortFlagsFromList
  , badTerm
  , module SAWCore.Parser.Position
  , moduleName
  , moduleTypedDecls
  , moduleDataDecls
  , moduleCtorDecls
  , moduleTypedDataDecls
  , moduleTypedCtorDecls
  ) where

import Data.Hashable
import Data.Text (Text)
import qualified Data.Text as Text

import GHC.Generics (Generic)
import qualified Language.Haskell.TH.Syntax as TH
import Numeric.Natural

import SAWCore.Name (ModuleName, mkModuleName)
import SAWCore.Parser.Position
import SAWCore.Term.Functor
  ( Sort, mkSort, propSort, sortOf
  , SortFlags(..), noFlags, sortFlagsLift2, sortFlagsToList, sortFlagsFromList
  , FieldName
  , LocalName
  )

data UTerm
  = Name (PosPair Text)
  | Sort Pos Sort SortFlags
  | App UTerm UTerm
  | Lambda Pos UTermCtx UTerm
  | Pi Pos UTermCtx UTerm
  | Recursor (PosPair Text) Sort
  | UnitValue Pos
  | UnitType Pos
    -- | New-style records
  | RecordValue Pos [(PosPair FieldName, UTerm)]
  | RecordType Pos [(PosPair FieldName, UTerm)]
  | RecordProj UTerm FieldName
    -- | Simple pairs
  | PairValue Pos UTerm UTerm
  | PairType Pos UTerm UTerm
  | PairLeft UTerm
  | PairRight UTerm
    -- | Identifies a type constraint on the term, i.e., a type ascription
  | TypeConstraint UTerm Pos UTerm
  | NatLit Pos Natural
  | StringLit Pos Text
    -- | Vector literal.
  | VecLit Pos [UTerm]
    -- | Bitvector literal.
  | BVLit Pos [Bool]
  | BadTerm Pos
 deriving (Show, TH.Lift)

-- | A pattern used for matching a variable.
data UTermVar
  = TermVar (PosPair LocalName)
  | UnusedVar Pos
  deriving (Eq, Ord, Show, TH.Lift)

-- | Return the 'String' name associated with a 'UTermVar'
termVarString :: UTermVar -> String
termVarString (TermVar (PosPair _ str)) = Text.unpack str
termVarString (UnusedVar _) = "_"

-- | Return the 'LocalName' associated with a 'UTermVar'
termVarLocalName :: UTermVar -> LocalName
termVarLocalName (TermVar (PosPair _ str)) = str
termVarLocalName (UnusedVar _) = "_"

-- | A context of 0 or more variable bindings, with types
type UTermCtx = [(UTermVar, UTerm)]

instance Positioned UTerm where
  pos t =
    case t of
      Name i               -> pos i
      Sort p _ _           -> p
      Lambda p _ _         -> p
      App x _              -> pos x
      Pi p _ _             -> p
      Recursor i _         -> pos i
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
      BVLit p _            -> p
      BadTerm p            -> p

instance Positioned UTermVar where
  pos (TermVar i) = pos i
  pos (UnusedVar p) = p

badTerm :: Pos -> UTerm
badTerm = BadTerm

-- | A constructor declaration of the form @c (x1 :: tp1) .. (xn :: tpn) :: tp@
data CtorDecl = Ctor (PosPair Text) UTermCtx UTerm
  deriving (Show, TH.Lift)

data DefQualifier
  = NoQualifier
  | PrimQualifier
  | AxiomQualifier
 deriving (Eq, Show, Generic, TH.Lift)

instance Hashable DefQualifier -- automatically derived

-- | A top-level declaration in a saw-core file
data Decl
   = TypeDecl DefQualifier (PosPair Text) UTerm
     -- ^ A declaration of something having a type, where the declaration
     -- qualifier states what flavor of thing it is
   | DataDecl (PosPair Text) UTermCtx UTerm [CtorDecl]
     -- ^ A declaration of an inductive data types, with a name, a parameter
     -- context, a return type, and a list of constructor declarations
   | TermDef (PosPair Text) [UTermVar] UTerm
     -- ^ A declaration of a term having a definition, with variables
   | TypedDef (PosPair Text) [(UTermVar, UTerm)] UTerm UTerm
     -- ^ A definition of something with a specific type, with parameters
   | InjectCodeDecl Text Text
     -- ^ Some raw text to inject into a translation
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
moduleTypedDecls :: Module -> [(Text, UTerm)]
moduleTypedDecls (Module _ _ decls) = concatMap helper decls where
  helper :: Decl -> [(Text, UTerm)]
  helper (TypeDecl _ (PosPair _ nm) tm) = [(nm,tm)]
  helper _ = []

-- | Get a list of all datatypes declared in a module
moduleDataDecls :: Module -> [(Text, UTermCtx, UTerm, [CtorDecl])]
moduleDataDecls (Module _ _ decls) = concatMap helper decls where
  helper :: Decl -> [(Text, UTermCtx, UTerm, [CtorDecl])]
  helper (DataDecl (PosPair _ nm) params tp ctors) = [(nm, params, tp, ctors)]
  helper _ = []

moduleTypedDataDecls :: Module -> [(Text, UTerm)]
moduleTypedDataDecls =
  map (\(nm,p_ctx,tp,_) ->
        (nm, Pi (pos tp) p_ctx tp)) . moduleDataDecls

-- | Get a list of all constructors declared in a module, along with the context
-- of parameters for each one
moduleCtorDecls :: Module -> [(UTermCtx, CtorDecl)]
moduleCtorDecls =
  concatMap (\(_,p_ctx,_,ctors) -> map (p_ctx,) ctors) . moduleDataDecls

-- | Get a list of the names and types of all the constructors in a module
moduleTypedCtorDecls :: Module -> [(Text, UTerm)]
moduleTypedCtorDecls =
  concatMap (\(_,p_ctx,_,ctors) ->
              map (\(Ctor (PosPair _ nm) ctx tp) ->
                    (nm, Pi (pos tp) (p_ctx ++ ctx) tp)) ctors)
  . moduleDataDecls

asPiList :: UTerm -> (UTermCtx, UTerm)
asPiList (Pi _ ctx1 body1) =
  let (ctx2,body2) = asPiList body1 in
  (ctx1 ++ ctx2, body2)
asPiList t = ([], t)

asApp :: UTerm -> (UTerm, [UTerm])
asApp = go []
  where go l (App t u)   = go (u:l) t
        go l t = (t,l)

-- | Build a tuple value @(x1, .., xn)@.
mkTupleValue :: Pos -> [UTerm] -> UTerm
mkTupleValue p [] = UnitValue p
mkTupleValue _ [x] = x
mkTupleValue p (x:xs) = PairValue (pos x) x (mkTupleValue p xs)

-- | Build a tuple type @#(x1, .., xn)@.
mkTupleType :: Pos -> [UTerm] -> UTerm
mkTupleType p [] = UnitType p
mkTupleType _ [x] = x
mkTupleType p (x:xs) = PairType (pos x) x (mkTupleType p xs)

-- | Build a projection @t.i@ of a tuple. NOTE: This function does not
-- work to access the last component in a tuple, since it always
-- generates a @PairLeft@.
mkTupleSelector :: UTerm -> Natural -> UTerm
mkTupleSelector t i
  | i == 1    = PairLeft t
  | i > 1     = mkTupleSelector (PairRight t) (i - 1)
  | otherwise = error "mkTupleSelector: non-positive index"
