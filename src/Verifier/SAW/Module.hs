{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

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
  , CtorArg(..)
  , CtorArgStruct(..)
  , Ctor(..)
  , ctorNumParams
  , ctorNumArgs
  , DataType(..)
    -- * Modules
  , Module
  , ModuleDecl(..)
  , ResolvedName(..)
  , resolvedNameIdent
  , moduleName
  , moduleImports
  , moduleImportNames
  , emptyModule
  , resolveName
  , findDataType
  , insImport
  , insDataType
  , beginDataType
  , completeDataType
  , moduleDataTypes
  , moduleCtors
  , findCtor
  , moduleDefs
  , findDef
  , insDef
  , moduleDecls
  , modulePrimitives
  , moduleAxioms
  , moduleActualDefs
    -- * Module Maps
  , ModuleMap
  , allModuleDefs
  , allModuleDecls
  , allModulePrimitives
  , allModuleAxioms
  , allModuleActualDefs
    -- * Pretty-printing
  , ppModule
  ) where

#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import Data.Foldable (foldl')
import Data.Hashable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import GHC.Generics (Generic)
import Text.PrettyPrint.ANSI.Leijen (Doc)

import Prelude hiding (all, foldr, sum)

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty
import Verifier.SAW.Term.CtxTerm
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
 deriving (Eq, Show, Read, Generic)

instance Hashable DefQualifier -- automatically derived

-- | A Definition contains an identifier, the type of the definition, and an
-- optional body (axioms and primitives do not have a body)
data Def =
  Def
  { defIdent :: Ident
  , defQualifier :: DefQualifier
  , defType :: Term
  , defBody :: Maybe Term
  }
  deriving (Eq, Show, Generic)

instance Hashable Def -- automatically derived


-- Constructors ----------------------------------------------------------------

-- | A specification of a constructor
data Ctor =
  forall d params ixs.
  Ctor
  { ctorName :: !Ident
    -- ^ The name of this constructor
  , ctorArgStruct :: CtorArgStruct d params ixs
    -- ^ Arguments to the constructor
  , ctorDataTypeName :: Ident
    -- ^ The datatype this constructor belongs to
  , ctorType :: Term
    -- ^ Cached type of the constructor, which should always be equal to
    --
    -- > (p1::P1) -> .. -> (pn::Pn) -> (x1::arg1) -> .. -> (xm::argm) ->
    -- >  d p1 .. pn ix1 .. ixk
    --
    -- where the @pi@ are the 'ctorParams', the @argi@ are the types specified
    -- by the 'ctorArgs', and the @ixi@ are the 'ctorDataTypeIndices'. Note that
    -- this type should always be top-level, i.e., have no free variables.
  , ctorElimTypeFun :: [Term] -> Term -> IO Term
    -- ^ Cached function for generating the type of an eliminator for this
    -- constructor by passing it a list of parameters and a @p_ret@ function,
    -- also known as the "motive function", which itself must have type
    --
    -- > (x1::ix1) -> .. -> (xm::ixm) -> d p1 .. pn x1 .. xm -> Type i
    --
    -- where the @ps@ are the parameters and the @ix@s are the indices of
    -- datatype @d@
  }

ctorNumParams :: Ctor -> Int
ctorNumParams (Ctor { ctorArgStruct = CtorArgStruct {..}}) =
  bindingsLength ctorParams

ctorNumArgs :: Ctor -> Int
ctorNumArgs (Ctor { ctorArgStruct = CtorArgStruct {..}}) =
  bindingsLength ctorArgs


lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y)

instance Eq Ctor where
  (==) = lift2 ctorName (==)

instance Ord Ctor where
  compare = lift2 ctorName compare

instance Show Ctor where
  show = show . ctorName


-- Datatypes -------------------------------------------------------------------

-- | An inductively-defined datatype
data DataType =
  DataType
  { dtName :: Ident
    -- ^ The name of this datatype
  , dtParams :: [(String,Term)]
    -- ^ The context of parameters of this datatype
  , dtIndices :: [(String,Term)]
    -- ^ The context of indices of this datatype
  , dtSort :: Sort
    -- ^ The universe of this datatype
  , dtCtors :: [Ctor]
    -- ^ The list of constructors of this datatype
  , dtType :: Term
    -- ^ The cached type of this datatype, which should always be equal to
    --
    -- > (p1::P1) -> .. -> (pn::Pn) -> (i1::I1) -> .. -> (im::Im) -> 'dtSort'
    --
    -- where the @pi@ are the 'dtParams' and the @ii@ are the 'dtIndices'. Note
    -- that this type should always be top-level, i.e., have no free variables.
  }

instance Eq DataType where
  (==) = lift2 dtName (==)

instance Ord DataType where
  compare = lift2 dtName compare

instance Show DataType where
  show = show . dtName


-- Modules ---------------------------------------------------------------------

-- | Declarations that can occur in a module
data ModuleDecl = TypeDecl DataType
                | DefDecl Def

-- | The different sorts of things that a 'String' name can be resolved to
data ResolvedName
  = ResolvedCtor Ctor
  | ResolvedDataType DataType
  | ResolvedDef Def

-- | Get the 'Ident' for a 'ResolvedName'
resolvedNameIdent :: ResolvedName -> Ident
resolvedNameIdent (ResolvedCtor ctor) = ctorName ctor
resolvedNameIdent (ResolvedDataType dt) = dtName dt
resolvedNameIdent (ResolvedDef d) = defIdent d

-- | Modules define namespaces of datatypes, constructors, and definitions,
-- i.e., mappings from 'String' names to these objects. A module is allowed to
-- map a 'String' name to an object defined in a different module. Modules also
-- keep a record of the top-level declarations and the imports that were used to
-- build them.
data Module = Module {
          moduleName    :: !ModuleName
        , moduleImports :: !(Map ModuleName Module)
        , moduleResolveMap :: !(Map String ResolvedName)
        , moduleRDecls   :: [ModuleDecl] -- ^ All declarations in reverse order they were added.
        }

-- | Get the names of all modules imported by the given one
moduleImportNames :: Module -> [ModuleName]
moduleImportNames m = Map.keys (moduleImports m)

emptyModule :: ModuleName -> Module
emptyModule nm =
  Module { moduleName = nm
         , moduleImports = Map.empty
         , moduleResolveMap = Map.empty
         , moduleRDecls = []
         }


-- | Resolve a 'String' name in the namespace defined by a 'Module', to either a
-- 'Ctor', 'DataType', or 'Def'
resolveName :: Module -> String -> Maybe ResolvedName
resolveName m str = Map.lookup str (moduleResolveMap m)

-- | Resolve a 'String' name to a 'Ctor'
findCtor :: Module -> String -> Maybe Ctor
findCtor m str =
  resolveName m str >>= \case { ResolvedCtor ctor -> Just ctor; _ -> Nothing }

-- | Resolve a 'String' name to a 'DataType'
findDataType :: Module -> String -> Maybe DataType
findDataType m str =
  resolveName m str >>= \case { ResolvedDataType d -> Just d; _ -> Nothing }

-- | Resolve a 'String' name to a 'Def'
findDef :: Module -> String -> Maybe Def
findDef m str =
  resolveName m str >>= \case { ResolvedDef d -> Just d; _ -> Nothing }


-- | Insert a 'ResolvedName' into a 'Module', adding a mapping from the 'String'
-- name of that resolved name to it. Signal an error in the case of a name
-- clash, i.e., an existing binding for the same 'String' name.
insResolvedName :: Module -> ResolvedName -> Module
insResolvedName m nm =
  let str = identName $ resolvedNameIdent nm in
  if Map.member str (moduleResolveMap m) then
    internalError ("Duplicate name " ++ str ++ " being inserted into module "
                   ++ show (moduleName m))
  else
    m { moduleResolveMap = Map.insert str nm (moduleResolveMap m) }

-- | @insImport i m@ returns the module obtained by importing @i@ into @m@,
-- using a predicate to specify which names are imported from @i@ into @m@. In
-- the case of name clashes, an error is signaled.
insImport :: (ResolvedName -> Bool) -> Module -> Module -> Module
insImport name_p i m =
  (foldl' insResolvedName m $ Map.elems $
   Map.filter name_p (moduleResolveMap i))
  { moduleImports = Map.insert (moduleName i) i (moduleImports m) }

-- | Insert a 'DataType' declaration, along with its 'Ctor's, into a module
insDataType :: Module -> DataType -> Module
insDataType m dt =
  foldl' insResolvedName (m { moduleRDecls = TypeDecl dt : moduleRDecls m}) $
  (ResolvedDataType dt : map ResolvedCtor (dtCtors dt))

-- | Insert an "incomplete" datatype, used as part of building up a 'DataType'
-- to typecheck its constructors. This incomplete datatype must have no
-- constructors, and it will not be added to the 'moduleRDecls' list until it is
-- completed by 'completeDataType'.
beginDataType :: Module -> DataType -> Module
beginDataType m dt =
   if null (dtCtors dt) then insResolvedName m (ResolvedDataType dt) else
     internalError
     "insTempDataType: attempt to insert a non-empty temporary datatype"

-- | Complete a datatype, by adding its constructors
completeDataType :: Module -> Ident -> [Ctor] -> Module
completeDataType m (identName -> str) ctors =
  case resolveName m str of
    Just (ResolvedDataType dt)
      | null (dtCtors dt) ->
        let dt' = dt {dtCtors = ctors} in
        flip (foldl' insResolvedName) (map ResolvedCtor ctors) $
        m { moduleResolveMap =
              Map.insert str (ResolvedDataType dt') (moduleResolveMap m),
              moduleRDecls = TypeDecl dt' : moduleRDecls m }
    Just (ResolvedDataType _) ->
      internalError $ "completeDataType: datatype already completed: " ++ str
    Just _ ->
      internalError $ "completeDataType: not a datatype: " ++ str
    Nothing ->
      internalError $ "completeDataType: datatype not found: " ++ str


-- | Insert a definition into a module
insDef :: Module -> Def -> Module
insDef m d = insResolvedName m (ResolvedDef d)


-- | Get all data types defined in a module
moduleDataTypes :: Module -> [DataType]
moduleDataTypes =
  Map.foldr' (\case { ResolvedDataType dt -> (dt :); _ -> id } ) [] .
  moduleResolveMap

-- | Get all constructors defined in a module
moduleCtors :: Module -> [Ctor]
moduleCtors =
  Map.foldr' (\case { ResolvedCtor ctor -> (ctor :); _ -> id } ) [] .
  moduleResolveMap

-- | Get all definitions defined in a module
moduleDefs :: Module -> [Def]
moduleDefs =
  Map.foldr' (\case { ResolvedDef d -> (d :); _ -> id } ) [] .
  moduleResolveMap

-- | Get all declarations that are local to a module, i.e., that defined names
-- that were not imported from some other module
moduleDecls :: Module -> [ModuleDecl]
moduleDecls = reverse . moduleRDecls

-- | Get all local declarations in a module that are marked as primitives
modulePrimitives :: Module -> [Def]
modulePrimitives m =
    [ def
    | DefDecl def <- moduleDecls m
    , defQualifier def == PrimQualifier
    ]

-- | Get all local declarations in a module that are marked as axioms
moduleAxioms :: Module -> [Def]
moduleAxioms m =
    [ def
    | DefDecl def <- moduleDecls m
    , defQualifier def == AxiomQualifier
    ]

-- | Get all local declarations in a module that are not marked as primitives or
-- axioms
moduleActualDefs :: Module -> [Def]
moduleActualDefs m =
    [ def
    | DefDecl def <- moduleDecls m
    , defQualifier def == NoQualifier
    ]

-- | The type of mappings from module names to modules
type ModuleMap = HashMap ModuleName Module

-- | Get all definitions defined in any module in an entire module map. Note
-- that the returned list might have redundancies if a definition is visible /
-- imported in multiple modules in the module map.
allModuleDefs :: ModuleMap -> [Def]
allModuleDefs modmap = concatMap moduleDefs (HMap.elems modmap)

-- | Get all local declarations from all modules in an entire module map
allModuleDecls :: ModuleMap -> [ModuleDecl]
allModuleDecls modmap = concatMap moduleDecls (HMap.elems modmap)

-- | Get all local declarations from all modules in an entire module map that
-- are marked as primitives
allModulePrimitives :: ModuleMap -> [Def]
allModulePrimitives modmap =
    [ def
    | DefDecl def <- allModuleDecls modmap
    , defQualifier def == PrimQualifier
    ]

-- | Get all local declarations from all modules in an entire module map that
-- are marked as axioms
allModuleAxioms :: ModuleMap -> [Def]
allModuleAxioms modmap =
    [ def
    | DefDecl def <- allModuleDecls modmap
    , defQualifier def == AxiomQualifier
    ]

-- | Get all local declarations from all modules in an entire module map that
-- are marked as neither primitives nor axioms
allModuleActualDefs :: ModuleMap -> [Def]
allModuleActualDefs modmap =
    [ def
    | DefDecl def <- allModuleDecls modmap
    , defQualifier def == NoQualifier
    ]

-- | Pretty-print a 'Module'
ppModule :: PPOpts -> Module -> Doc
ppModule opts m =
  ppPPModule opts (PPModule (moduleImportNames m) (map toDecl $ moduleDecls m))
  where
    toDecl (TypeDecl (DataType {..})) =
      PPTypeDecl dtName dtParams dtIndices dtSort
      (map (\c -> (ctorName c, ctorType c)) dtCtors)
    toDecl (DefDecl (Def {..})) =
      PPDefDecl defIdent defType defBody
