{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}

{- |
Module      : Verifier.SAW.Module
Copyright   : Galois, Inc. 2012-2017
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Module
  ( -- * Patterns.
    Pat(..)
  , patBoundVars
  , patBoundVarCount
  , patUnusedVarCount
    -- * Data types and definitions.
  , DefQualifier(..)
  , Def(..)
  , DefEqn(..)
  , Ctor(..)
  , TypedCtor
  , DataType(..)
    -- * Modules
  , Module
  , ModuleDecl(..)
  , moduleName
  , moduleImports
  , emptyModule
  , findDataType
  , insImport
  , insDataType
  , moduleDataTypes
  , moduleCtors
  , findCtor
  , moduleDefs
  , allModuleDefs
  , findDef
  , insDef
  , moduleDecls
  , allModuleDecls
  , modulePrimitives
  , allModulePrimitives
  , moduleAxioms
  , allModuleAxioms
  , moduleActualDefs
  , allModuleActualDefs
  ) where

import Control.Lens
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import Data.Foldable (foldl')
import Data.Hashable
import Data.Map (Map)
import qualified Data.Map as Map
import GHC.Generics (Generic)

import Prelude hiding (all, foldr, sum)

import Verifier.SAW.Term.Functor
import Verifier.SAW.Utils (sumBy, internalError)

-- Patterns --------------------------------------------------------------------

-- Patterns are used to match equations.
data Pat = -- | Variable bound by pattern.
           -- Variables may be bound in context in a different order than
           -- a left-to-right traversal.  The DeBruijnIndex indicates the order.
           PVar String DeBruijnIndex Term
         | PUnused DeBruijnIndex Term
         | PUnit
         | PPair Pat Pat
         | PEmpty
         | PField Pat Pat Pat -- ^ Field name, field value, rest of record
         | PString String
         | PCtor Ident [Pat]
  deriving (Eq, Ord, Show, Generic)

instance Hashable Pat -- automatically derived

patBoundVarCount :: Pat -> DeBruijnIndex
patBoundVarCount p =
  case p of
    PVar{} -> 1
    PUnused{} -> 0
    PCtor _ l -> sumBy patBoundVarCount l
    PUnit     -> 0
    PPair x y -> patBoundVarCount x + patBoundVarCount y
    PEmpty    -> 0
    PField f x y -> patBoundVarCount f + patBoundVarCount x + patBoundVarCount y
    PString _ -> 0

patUnusedVarCount :: Pat -> DeBruijnIndex
patUnusedVarCount p =
  case p of
    PVar{}       -> 0
    PUnused{}    -> 1
    PCtor _ l    -> sumBy patUnusedVarCount l
    PUnit        -> 0
    PPair x y    -> patUnusedVarCount x + patUnusedVarCount y
    PEmpty       -> 0
    PField _ x y -> patUnusedVarCount x + patUnusedVarCount y
    PString _    -> 0

patBoundVars :: Pat -> [String]
patBoundVars p =
  case p of
    PVar s _ _   -> [s]
    PCtor _ l    -> concatMap patBoundVars l
    PUnit        -> []
    PPair x y    -> patBoundVars x ++ patBoundVars y
    PEmpty       -> []
    PField _ x y -> patBoundVars x ++ patBoundVars y
    PString _    -> []
    PUnused{}    -> []


-- Definitions -----------------------------------------------------------------

data DefQualifier
  = NoQualifier
  | PrimQualifier
  | AxiomQualifier
 deriving (Eq, Show, Generic)

instance Hashable DefQualifier -- automatically derived

-- | A Definition contains an identifier, the type of the definition, and a list of equations.
data Def =
  Def
  { defIdent :: Ident
  , defQualifier :: DefQualifier
  , defType :: Term
  , defEqs :: [DefEqn]
  }
  deriving (Eq, Show, Generic)

instance Hashable Def -- automatically derived

data DefEqn
  = DefEqn [Pat] Term -- ^ List of patterns and a right hand side
  deriving (Eq, Show, Generic)

instance Hashable DefEqn -- automatically derived


-- Constructors ----------------------------------------------------------------

type TypedCtor = Ctor Term

data Ctor tp =
  Ctor
  { ctorName :: !Ident
  , ctorType :: tp -- ^ The type of the constructor (should contain no free variables).
  }
  deriving (Functor, Foldable, Traversable)

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y)

instance Eq (Ctor tp) where
  (==) = lift2 ctorName (==)

instance Ord (Ctor tp) where
  compare = lift2 ctorName compare

instance Show (Ctor tp) where
  show = show . ctorName


-- Datatypes -------------------------------------------------------------------

data DataType =
  DataType
  { dtName :: Ident
  , dtType :: Term
  , dtCtors :: [Ctor Term]
  }

instance Eq DataType where
  (==) = lift2 dtName (==)

instance Ord DataType where
  compare = lift2 dtName compare

instance Show DataType where
  show = show . dtName


-- Modules ---------------------------------------------------------------------

data ModuleDecl = TypeDecl DataType
                | DefDecl Def

data Module = Module {
          moduleName    :: !ModuleName
        , _moduleImports :: !(Map ModuleName Module)
        , moduleTypeMap :: !(Map String DataType)
        , moduleCtorMap :: !(Map String TypedCtor)
        , moduleDefMap  :: !(Map String Def)
        , moduleRDecls   :: [ModuleDecl] -- ^ All declarations in reverse order they were added.
        }

moduleImports :: Simple Lens Module (Map ModuleName Module)
moduleImports = lens _moduleImports (\m v -> m { _moduleImports = v })

emptyModule :: ModuleName -> Module
emptyModule nm =
  Module { moduleName = nm
         , _moduleImports = Map.empty
         , moduleTypeMap = Map.empty
         , moduleCtorMap = Map.empty
         , moduleDefMap  = Map.empty
         , moduleRDecls = []
         }

findDataType :: Module -> Ident -> Maybe DataType
findDataType m i = do
  m' <- findDeclaringModule m (identModule i)
  Map.lookup (identName i) (moduleTypeMap m')

-- | @insImport i m@ returns module obtained by importing @i@ into @m@.
insImport :: Module -> Module -> Module
insImport i = moduleImports . at (moduleName i) ?~ i

insDataType :: Module -> DataType -> Module
insDataType m dt
    | identModule (dtName dt) == moduleName m =
        m { moduleTypeMap = Map.insert (identName (dtName dt)) dt (moduleTypeMap m)
          , moduleCtorMap = foldl' insCtor (moduleCtorMap m) (dtCtors dt)
          , moduleRDecls = TypeDecl dt : moduleRDecls m
          }
    | otherwise = internalError "insDataType given datatype from another module."
  where insCtor m' c = Map.insert (identName (ctorName c)) c m'

-- | Data types defined in module.
moduleDataTypes :: Module -> [DataType]
moduleDataTypes = Map.elems . moduleTypeMap

-- | Ctors defined in module.
moduleCtors :: Module -> [TypedCtor]
moduleCtors = Map.elems . moduleCtorMap

findDeclaringModule :: Module -> ModuleName -> Maybe Module
findDeclaringModule m nm
  | moduleName m == nm = Just m
  | otherwise = m^.moduleImports^.at nm

findCtor :: Module -> Ident -> Maybe TypedCtor
findCtor m i = do
  m' <- findDeclaringModule m (identModule i)
  Map.lookup (identName i) (moduleCtorMap m')

moduleDefs :: Module -> [Def]
moduleDefs = Map.elems . moduleDefMap

allModuleDefs :: Module -> [Def]
allModuleDefs m = concatMap moduleDefs (m : Map.elems (m^.moduleImports))

findDef :: Module -> Ident -> Maybe Def
findDef m i = do
  m' <- findDeclaringModule m (identModule i)
  Map.lookup (identName i) (moduleDefMap m')

insDef :: Module -> Def -> Module
insDef m d
  | identModule (defIdent d) == moduleName m =
      m { moduleDefMap = Map.insert (identName (defIdent d)) d (moduleDefMap m)
        , moduleRDecls = DefDecl d : moduleRDecls m
        }
  | otherwise = internalError "insDef given def from another module."

moduleDecls :: Module -> [ModuleDecl]
moduleDecls = reverse . moduleRDecls

allModuleDecls :: Module -> [ModuleDecl]
allModuleDecls m = concatMap moduleDecls (m : Map.elems (m^.moduleImports))

modulePrimitives :: Module -> [Def]
modulePrimitives m =
    [ def
    | DefDecl def <- moduleDecls m
    , defQualifier def == PrimQualifier
    ]

moduleAxioms :: Module -> [Def]
moduleAxioms m =
    [ def
    | DefDecl def <- moduleDecls m
    , defQualifier def == AxiomQualifier
    ]

moduleActualDefs :: Module -> [Def]
moduleActualDefs m =
    [ def
    | DefDecl def <- moduleDecls m
    , defQualifier def == NoQualifier
    ]

allModulePrimitives :: Module -> [Def]
allModulePrimitives m =
    [ def
    | DefDecl def <- allModuleDecls m
    , defQualifier def == PrimQualifier
    ]

allModuleAxioms :: Module -> [Def]
allModuleAxioms m =
    [ def
    | DefDecl def <- allModuleDecls m
    , defQualifier def == AxiomQualifier
    ]

allModuleActualDefs :: Module -> [Def]
allModuleActualDefs m =
    [ def
    | DefDecl def <- allModuleDecls m
    , defQualifier def == NoQualifier
    ]
