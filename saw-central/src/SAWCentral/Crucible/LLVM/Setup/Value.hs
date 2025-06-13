{- |
Module      : SAWCentral.Crucible.LLVM.Setup.Value
Description : Data types and type family instances for LLVM-specific code
License     : BSD3
Maintainer  : Ryan Scott <rscott@galois.com>
Stability   : provisional

The module exists separately from "SAWCentral.Crucible.LLVM.MethodSpecIR"
primarily to avoid import cycles. You probably want to import
"SAWCentral.Crucible.LLVM.MethodSpecIR" (which re-exports everything from this
module, plus additional functionality) instead.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module SAWCentral.Crucible.LLVM.Setup.Value
  ( LLVM
    -- * LLVMMethodId
  , LLVMMethodId(..)
  , llvmMethodParent
  , llvmMethodName
  , ppLLVMMethodId
    -- * LLVMAllocSpec
  , LLVMAllocSpec(..)
  , LLVMAllocSpecInit(..)
  , allocSpecType
  , allocSpecAlign
  , allocSpecMut
  , allocSpecMd
  , allocSpecBytes
  , allocSpecFresh
  , allocSpecInit
    -- * LLVMModule
  , LLVMModule -- abstract
  , modFilePath
  , modAST
  , modTrans
  , loadLLVMModule
  , showLLVMModule
    -- * CrucibleContext
  , LLVMCrucibleContext(..)
  , ccLLVMSimContext
  , ccLLVMModule
  , ccLLVMGlobals
  , ccBasicSS
  , ccBackend
    -- * PointsTo
  , LLVMPointsTo(..)
  , LLVMPointsToValue(..)
    -- * AllocGlobal
  , LLVMAllocGlobal(..)
  , ppAllocGlobal
    -- * ResolvedState
  , LLVMResolvedState(..)
  , ResolvedPath
  , ResolvedPathItem(..)
  , emptyResolvedState
  , rsAllocs
  , rsGlobals
    -- * @LLVMPtr@
  , LLVMPtr
  ) where

import           Control.Lens
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Sequence (Seq)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality (TestEquality(..))
import           Data.Void (Void)
import qualified Prettyprinter as PPL
import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L
import qualified Text.PrettyPrint.HughesPJ as PP

import qualified Data.LLVM.BitCode as LLVM

import           Data.Parameterized.Some (Some(Some))

import           What4.ProgramLoc (ProgramLoc)

import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible (SimContext)
import qualified Lang.Crucible.Simulator.GlobalState as Crucible (SymGlobalState)
import qualified Lang.Crucible.LLVM.PrettyPrint as Crucible.LLVM

import           SAWCentral.Crucible.Common
import qualified SAWCentral.Crucible.Common.Setup.Value as Setup

import qualified SAWCentral.Crucible.LLVM.CrucibleLLVM as CL

import           SAWCentral.Proof (TheoremNonce)

import           SAWCore.Rewriter (Simpset)
import           SAWCore.SharedTerm
import           CryptolSAWCore.TypedTerm

--------------------------------------------------------------------------------
-- ** Language features

data LLVM (arch :: CL.LLVMArch)

type instance Setup.XSetupNull (LLVM _) = ()
-- 'True' if this is an LLVM packed struct, 'False' otherwise.
type instance Setup.XSetupStruct (LLVM _) = Bool
type instance Setup.XSetupEnum (LLVM _) = Void
type instance Setup.XSetupTuple (LLVM _) = Void
type instance Setup.XSetupSlice (LLVM _) = Void
type instance Setup.XSetupArray (LLVM _) = ()
type instance Setup.XSetupElem (LLVM _) = ()
type instance Setup.XSetupField (LLVM _) = ()
type instance Setup.XSetupCast (LLVM _) = L.Type
type instance Setup.XSetupUnion (LLVM _) = ()
type instance Setup.XSetupGlobal (LLVM _) = ()
type instance Setup.XSetupGlobalInitializer (LLVM _) = ()
type instance Setup.XSetupMux (LLVM _) = Void

type instance Setup.TypeName (LLVM arch) = CL.Ident
type instance Setup.ExtType (LLVM arch) = CL.MemType

--------------------------------------------------------------------------------
-- *** LLVMMethodId

data LLVMMethodId =
  LLVMMethodId
    { _llvmMethodName   :: Text
    , _llvmMethodParent :: Maybe Text -- ^ Something to do with breakpoints...
    } deriving (Eq, Ord, Show)

makeLenses ''LLVMMethodId

instance PPL.Pretty LLVMMethodId where
  pretty = PPL.pretty . view llvmMethodName

ppLLVMMethodId :: LLVMMethodId -> Text
ppLLVMMethodId = view llvmMethodName

type instance Setup.MethodId (LLVM _) = LLVMMethodId

--------------------------------------------------------------------------------
-- *** LLVMAllocSpec

-- | Allocation initialization policy
data LLVMAllocSpecInit
  = LLVMAllocSpecSymbolicInitialization
    -- ^ allocation is initialized with a fresh symbolic array of bytes
  | LLVMAllocSpecNoInitialization
    -- ^ allocation not initialized
  deriving (Eq, Ord, Show)

data LLVMAllocSpec =
  LLVMAllocSpec
    { _allocSpecMut   :: CL.Mutability
    , _allocSpecType  :: CL.MemType
    , _allocSpecAlign :: CL.Alignment
    , _allocSpecBytes :: Term
    , _allocSpecMd    :: Setup.ConditionMetadata
    , _allocSpecFresh :: Bool -- ^ Whether declared with @crucible_fresh_pointer@
    , _allocSpecInit :: LLVMAllocSpecInit
    }
  deriving (Eq, Show)

makeLenses ''LLVMAllocSpec

type instance Setup.AllocSpec (LLVM _) = LLVMAllocSpec

--------------------------------------------------------------------------------
-- *** LLVMModule

-- | An 'LLVMModule' contains an LLVM module that has been parsed from
-- a bitcode file and translated to Crucible.
data LLVMModule arch =
  LLVMModule
  { _modFilePath :: FilePath
  , _modAST :: L.Module
  , _modTrans :: CL.ModuleTranslation arch
  }
-- NOTE: Type 'LLVMModule' is exported as an abstract type, and we
-- maintain the invariant that the 'FilePath', 'Module', and
-- 'ModuleTranslation' fields are all consistent with each other;
-- 'loadLLVMModule' is the only function that is allowed to create
-- values of type 'LLVMModule'.

-- | The file path that the LLVM module was loaded from.
modFilePath :: LLVMModule arch -> FilePath
modFilePath = _modFilePath

-- | The parsed AST of the LLVM module.
modAST :: LLVMModule arch -> L.Module
modAST = _modAST

-- | The Crucible translation of an LLVM module.
modTrans :: LLVMModule arch -> CL.ModuleTranslation arch
modTrans = _modTrans

-- | Load an LLVM module from the given bitcode file, then parse and
-- translate to Crucible.
loadLLVMModule ::
  (?transOpts :: CL.TranslationOptions) =>
  FilePath ->
  Crucible.HandleAllocator ->
  IO (Either LLVM.Error (Some LLVMModule, Seq LLVM.ParseWarning))
loadLLVMModule file halloc =
  do parseResult <- LLVM.parseBitCodeFromFileWithWarnings file
     case parseResult of
       Left err -> return (Left err)
       Right (llvm_mod, warnings) ->
         do memVar <- CL.mkMemVar (Text.pack "saw:llvm_memory") halloc
            Some mtrans <- CL.translateModule halloc memVar llvm_mod
            return (Right (Some (LLVMModule file llvm_mod mtrans), warnings))

instance TestEquality LLVMModule where
  -- As 'LLVMModule' is an abstract type, we know that the values must
  -- have been created by a call to 'loadLLVMModule'. Furthermore each
  -- call to 'translateModule' generates a 'ModuleTranslation' that
  -- contains a fresh nonce; thus comparison of the 'modTrans' fields
  -- is sufficient to guarantee equality of two 'LLVMModule' values.
  testEquality m1 m2 = testEquality (modTrans m1) (modTrans m2)

type instance Setup.Codebase (LLVM arch) = LLVMModule arch

showLLVMModule :: LLVMModule arch -> String
showLLVMModule (LLVMModule name m _) =
  unlines [ "Module: " ++ name
          , "Types:"
          , showParts (Crucible.LLVM.ppLLVMLatest L.ppTypeDecl) (L.modTypes m)
          , "Globals:"
          , showParts (Crucible.LLVM.ppLLVMLatest ppGlobal') (L.modGlobals m)
          , "External references:"
          , showParts Crucible.LLVM.ppDeclare (L.modDeclares m)
          , "Definitions:"
          , showParts (Crucible.LLVM.ppLLVMLatest ppDefine') (L.modDefines m)
          ]
  where
    showParts pp xs = unlines $ map (show . PP.nest 2 . pp) xs
    ppGlobal' g =
      L.ppSymbol (L.globalSym g) PP.<+> PP.char '=' PP.<+>
      L.ppGlobalAttrs (isJust $ L.globalValue g) (L.globalAttrs g) PP.<+>
      L.ppType (L.globalType g)
    ppDefine' d =
      L.ppMaybe L.ppLinkage (L.defLinkage d) PP.<+>
      L.ppType (L.defRetType d) PP.<+>
      L.ppSymbol (L.defName d) PP.<>
      L.ppArgList (L.defVarArgs d) (map (L.ppTyped L.ppIdent) (L.defArgs d)) PP.<+>
      L.ppMaybe (\gc -> PP.text "gc" PP.<+> L.ppGC gc) (L.defGC d)

--------------------------------------------------------------------------------
-- ** CrucibleContext

type instance Setup.CrucibleContext (LLVM arch) = LLVMCrucibleContext arch

data LLVMCrucibleContext arch =
  LLVMCrucibleContext
  { _ccLLVMModule      :: LLVMModule arch
  , _ccBackend         :: SomeOnlineBackend
  , _ccLLVMSimContext  :: Crucible.SimContext (SAWCruciblePersonality Sym) Sym CL.LLVM
  , _ccLLVMGlobals     :: Crucible.SymGlobalState Sym
  , _ccBasicSS         :: Simpset TheoremNonce
  }

makeLenses ''LLVMCrucibleContext

--------------------------------------------------------------------------------
-- ** PointsTo

type instance Setup.PointsTo (LLVM arch) = LLVMPointsTo arch

data LLVMPointsTo arch
  = LLVMPointsTo Setup.ConditionMetadata (Maybe TypedTerm) (Setup.SetupValue (LLVM arch)) (LLVMPointsToValue arch)
    -- | A variant of 'LLVMPointsTo' tailored to the @llvm_points_to_bitfield@
    -- command, which doesn't quite fit into the 'LLVMPointsToValue' paradigm.
    -- The 'String' represents the name of the field within the bitfield.
  | LLVMPointsToBitfield Setup.ConditionMetadata (Setup.SetupValue (LLVM arch)) String (Setup.SetupValue (LLVM arch))

data LLVMPointsToValue arch
  = ConcreteSizeValue (Setup.SetupValue (LLVM arch))
  | SymbolicSizeValue TypedTerm TypedTerm

--------------------------------------------------------------------------------
-- ** AllocGlobal

type instance Setup.AllocGlobal (LLVM arch) = LLVMAllocGlobal arch

data LLVMAllocGlobal arch = LLVMAllocGlobal ProgramLoc L.Symbol

ppAllocGlobal :: LLVMAllocGlobal arch -> PPL.Doc ann
ppAllocGlobal (LLVMAllocGlobal _loc (L.Symbol name)) =
  PPL.pretty "allocate global"
  PPL.<+> PPL.pretty name

instance PPL.Pretty (LLVMAllocGlobal arch) where
  pretty = ppAllocGlobal

--------------------------------------------------------------------------------
-- *** ResolvedState

type instance Setup.ResolvedState (LLVM arch) = LLVMResolvedState

data ResolvedPathItem
  = ResolvedField Text
  | ResolvedElem Int
  | ResolvedCast L.Type
 deriving (Show, Eq, Ord)

type ResolvedPath = [ResolvedPathItem]

-- | A datatype to keep track of which parts of the simulator state
-- have been initialized already. For each allocation unit or global,
-- we keep a list of element-paths that identify the initialized
-- sub-components.
--
-- Note that the data collected and maintained by this datatype
-- represents a \"best-effort\" check that attempts to prevent
-- the user from stating unsatisfiable method specifications.
--
-- It will not prevent all cases of overlapping points-to
-- specifications, especially in the presence of pointer casts.
-- A typical result of overlapping specifications will be
-- successful (vacuous) verifications of functions resulting in
-- overrides that cannot be used at call sites (as their
-- preconditions are unsatisfiable).
data LLVMResolvedState =
  ResolvedState
    { _rsAllocs :: Map Setup.AllocIndex [ResolvedPath]
    , _rsGlobals :: Map Text [ResolvedPath]
    }
  deriving (Eq, Ord, Show)

emptyResolvedState :: LLVMResolvedState
emptyResolvedState = ResolvedState Map.empty Map.empty

makeLenses ''LLVMResolvedState

--------------------------------------------------------------------------------
-- *** Pointers

type instance Setup.Pointer' (LLVM arch) Sym = LLVMPtr (CL.ArchWidth arch)

type LLVMPtr wptr = CL.LLVMPtr Sym wptr
