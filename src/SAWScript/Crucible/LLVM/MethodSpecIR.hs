{- |
Module      : SAWScript.Crucible.LLVM.MethodSpecIR
Description : Provides type-checked representation for Crucible/LLVM function
              specifications and function for creating it from AST
              representation.
Maintainer  : atomb
Stability   : provisional
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
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module SAWScript.Crucible.LLVM.MethodSpecIR
  ( -- * LLVMMethodId
    LLVMMethodId(..)
  , llvmMethodParent
  , llvmMethodName
  , csName
  , csParentName
    -- * LLVMAllocSpec
  , LLVMAllocSpec(..)
  , allocSpecType
  , allocSpecAlign
  , allocSpecMut
  , allocSpecLoc
  , allocSpecBytes
  , mutIso
  , isMut
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
  , ccLLVMModuleAST
  , ccLLVMModuleTrans
  , ccLLVMContext
  , ccTypeCtx
    -- * PointsTo
  , LLVMPointsTo(..)
  , ppPointsTo
    -- * AllocGlobal
  , LLVMAllocGlobal(..)
  , ppAllocGlobal
    -- * Intrinsics
  , intrinsics
    -- * Initial CrucibleSetupMethodSpec
  , SetupError(..)
  , ppSetupError
  , resolveArgs
  , resolveRetTy
  , initialDefCrucibleMethodSpecIR
  , initialDeclCrucibleMethodSpecIR
  , initialCrucibleSetupState
  , initialCrucibleSetupStateDecl
    -- * AllLLVM
  , AllLLVM
  , mkAllLLVM
  , getAllLLVM
  , anySetupTerm
  , anySetupArray
  , anySetupStruct
  , anySetupElem
  , anySetupField
  , anySetupNull
  , anySetupGlobal
  , anySetupGlobalInitializer
    -- * SomeLLVM
  , SomeLLVM
  , pattern SomeLLVM
  , mkSomeLLVM
  , getSomeLLVM
  ) where

import           Control.Lens
import           Control.Monad (when)
import           Data.Functor.Compose (Compose(..))
import           Data.IORef
import           Data.Type.Equality (TestEquality(..))
import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L
import qualified Text.PrettyPrint.ANSI.Leijen as PPL hiding ((<$>), (<>))
import qualified Text.PrettyPrint.HughesPJ as PP

import qualified Data.LLVM.BitCode as LLVM

import qualified Cryptol.Utils.PP as Cryptol (pp)

import           Data.Parameterized.All (All(All))
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.Map as MapF

import qualified What4.Expr.Builder as B
import           What4.ProgramLoc (ProgramLoc)

import qualified Lang.Crucible.Backend.SAWCore as Crucible
  (SAWCoreBackend, saw_ctx, toSC, SAWCruciblePersonality)
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible (SimContext)
import qualified Lang.Crucible.Simulator.GlobalState as Crucible (SymGlobalState)
import qualified Lang.Crucible.Types as Crucible (SymbolRepr, knownSymbol)
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
  (IntrinsicClass(Intrinsic, muxIntrinsic), IntrinsicMuxFn(IntrinsicMuxFn))
import           SAWScript.Crucible.Common (Sym)
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup

import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as CL

import           Verifier.SAW.Rewriter (Simpset)
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedTerm

--------------------------------------------------------------------------------
-- ** Language features

type instance MS.HasSetupNull (CL.LLVM _) = 'True
type instance MS.HasSetupStruct (CL.LLVM _) = 'True
type instance MS.HasSetupArray (CL.LLVM _) = 'True
type instance MS.HasSetupElem (CL.LLVM _) = 'True
type instance MS.HasSetupField (CL.LLVM _) = 'True
type instance MS.HasSetupGlobal (CL.LLVM _) = 'True
type instance MS.HasSetupGlobalInitializer (CL.LLVM _) = 'True

type instance MS.HasGhostState (CL.LLVM _) = 'True

type instance MS.TypeName (CL.LLVM arch) = CL.Ident
type instance MS.ExtType (CL.LLVM arch) = CL.MemType

--------------------------------------------------------------------------------
-- *** LLVMMethodId

data LLVMMethodId =
  LLVMMethodId
    { _llvmMethodName   :: String
    , _llvmMethodParent :: Maybe String -- ^ Something to do with breakpoints...
    } deriving (Eq, Ord, Show)

makeLenses ''LLVMMethodId

csName :: Lens' (MS.CrucibleMethodSpecIR (CL.LLVM arch)) String
csName = MS.csMethod . llvmMethodName

csParentName :: Lens' (MS.CrucibleMethodSpecIR (CL.LLVM arch)) (Maybe String)
csParentName = MS.csMethod . llvmMethodParent

instance PPL.Pretty LLVMMethodId where
  pretty = PPL.text . view llvmMethodName

type instance MS.MethodId (CL.LLVM _) = LLVMMethodId

--------------------------------------------------------------------------------
-- *** LLVMAllocSpec

data LLVMAllocSpec =
  LLVMAllocSpec
    { _allocSpecMut   :: CL.Mutability
    , _allocSpecType  :: CL.MemType
    , _allocSpecAlign :: CL.Alignment
    , _allocSpecBytes :: CL.Bytes
    , _allocSpecLoc   :: ProgramLoc
    }
  deriving (Eq, Show)

makeLenses ''LLVMAllocSpec

type instance MS.AllocSpec (CL.LLVM _) = LLVMAllocSpec

mutIso :: Iso' CL.Mutability Bool
mutIso =
  iso
    (\case
      CL.Mutable -> True
      CL.Immutable -> False)
    (\case
      True -> CL.Mutable
      False -> CL.Immutable)

isMut :: Lens' LLVMAllocSpec Bool
isMut = allocSpecMut . mutIso

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
  (?laxArith :: Bool) =>
  FilePath ->
  Crucible.HandleAllocator ->
  IO (Either LLVM.Error (Some LLVMModule))
loadLLVMModule file halloc =
  do parseResult <- LLVM.parseBitCodeFromFile file
     case parseResult of
       Left err -> return (Left err)
       Right llvm_mod ->
         do Some mtrans <- CL.translateModule halloc llvm_mod
            return (Right (Some (LLVMModule file llvm_mod mtrans)))

instance TestEquality LLVMModule where
  -- As 'LLVMModule' is an abstract type, we know that the values must
  -- have been created by a call to 'loadLLVMModule'. Furthermore each
  -- call to 'translateModule' generates a 'ModuleTranslation' that
  -- contains a fresh nonce; thus comparison of the 'modTrans' fields
  -- is sufficient to guarantee equality of two 'LLVMModule' values.
  testEquality m1 m2 = testEquality (modTrans m1) (modTrans m2)

type instance MS.Codebase (CL.LLVM arch) = LLVMModule arch

showLLVMModule :: LLVMModule arch -> String
showLLVMModule (LLVMModule name m _) =
  unlines [ "Module: " ++ name
          , "Types:"
          , showParts L.ppTypeDecl (L.modTypes m)
          , "Globals:"
          , showParts ppGlobal' (L.modGlobals m)
          , "External references:"
          , showParts L.ppDeclare (L.modDeclares m)
          , "Definitions:"
          , showParts ppDefine' (L.modDefines m)
          ]
  where
    showParts pp xs = unlines $ map (show . PP.nest 2 . pp) xs
    ppGlobal' g =
      L.ppSymbol (L.globalSym g) PP.<+> PP.char '=' PP.<+>
      L.ppGlobalAttrs (L.globalAttrs g) PP.<+>
      L.ppType (L.globalType g)
    ppDefine' d =
      L.ppMaybe L.ppLinkage (L.defLinkage d) PP.<+>
      L.ppType (L.defRetType d) PP.<+>
      L.ppSymbol (L.defName d) PP.<>
      L.ppArgList (L.defVarArgs d) (map (L.ppTyped L.ppIdent) (L.defArgs d)) PP.<+>
      L.ppMaybe (\gc -> PP.text "gc" PP.<+> L.ppGC gc) (L.defGC d)

--------------------------------------------------------------------------------
-- ** Ghost state

instance Crucible.IntrinsicClass (Crucible.SAWCoreBackend n solver (B.Flags B.FloatReal)) MS.GhostValue where
  type Intrinsic (Crucible.SAWCoreBackend n solver (B.Flags B.FloatReal)) MS.GhostValue ctx = TypedTerm
  muxIntrinsic sym _ _namerep _ctx prd thn els =
    do when (ttSchema thn /= ttSchema els) $ fail $ unlines $
         [ "Attempted to mux ghost variables of different types:"
         , show (Cryptol.pp (ttSchema thn))
         , show (Cryptol.pp (ttSchema els))
         ]
       st <- readIORef (B.sbStateManager sym)
       let sc  = Crucible.saw_ctx st
       prd' <- Crucible.toSC sym prd
       typ  <- scTypeOf sc (ttTerm thn)
       res  <- scIte sc typ prd' (ttTerm thn) (ttTerm els)
       return thn { ttTerm = res }

--------------------------------------------------------------------------------
-- ** CrucibleContext

type instance MS.CrucibleContext (CL.LLVM arch) = LLVMCrucibleContext arch

data LLVMCrucibleContext arch =
  LLVMCrucibleContext
  { _ccLLVMModule      :: LLVMModule arch
  , _ccBackend         :: Sym
  , _ccLLVMSimContext  :: Crucible.SimContext (Crucible.SAWCruciblePersonality Sym) Sym (CL.LLVM arch)
  , _ccLLVMGlobals     :: Crucible.SymGlobalState Sym
  , _ccBasicSS         :: Simpset
  }

makeLenses ''LLVMCrucibleContext

ccLLVMModuleAST :: LLVMCrucibleContext arch -> L.Module
ccLLVMModuleAST = modAST . _ccLLVMModule

ccLLVMModuleTrans :: LLVMCrucibleContext arch -> CL.ModuleTranslation arch
ccLLVMModuleTrans = modTrans . _ccLLVMModule

ccLLVMContext :: LLVMCrucibleContext arch -> CL.LLVMContext arch
ccLLVMContext = view CL.transContext . ccLLVMModuleTrans

ccTypeCtx :: LLVMCrucibleContext arch -> CL.TypeContext
ccTypeCtx = view CL.llvmTypeCtx . ccLLVMContext

--------------------------------------------------------------------------------
-- ** PointsTo

type instance MS.PointsTo (CL.LLVM arch) = LLVMPointsTo arch

data LLVMPointsTo arch =
  LLVMPointsTo ProgramLoc (Maybe TypedTerm) (MS.SetupValue (CL.LLVM arch)) (MS.SetupValue (CL.LLVM arch))

ppPointsTo :: LLVMPointsTo arch -> PPL.Doc
ppPointsTo (LLVMPointsTo _loc cond ptr val) =
  MS.ppSetupValue ptr
  PPL.<+> PPL.text "points to"
  PPL.<+> MS.ppSetupValue val
  PPL.<+> maybe PPL.empty (\tt -> PPL.text "if" PPL.<+> MS.ppTypedTerm tt) cond

instance PPL.Pretty (LLVMPointsTo arch) where
  pretty = ppPointsTo

--------------------------------------------------------------------------------
-- ** AllocGlobal

type instance MS.AllocGlobal (CL.LLVM arch) = LLVMAllocGlobal arch

data LLVMAllocGlobal arch = LLVMAllocGlobal ProgramLoc L.Symbol

ppAllocGlobal :: LLVMAllocGlobal arch -> PPL.Doc
ppAllocGlobal (LLVMAllocGlobal _loc (L.Symbol name)) =
  PPL.text "allocate global"
  PPL.<+> PPL.text name

instance PPL.Pretty (LLVMAllocGlobal arch) where
  pretty = ppAllocGlobal

--------------------------------------------------------------------------------
-- ** ???

intrinsics :: MapF.MapF Crucible.SymbolRepr (Crucible.IntrinsicMuxFn Sym)
intrinsics =
  MapF.insert
    (Crucible.knownSymbol :: Crucible.SymbolRepr MS.GhostValue)
    Crucible.IntrinsicMuxFn
    CL.llvmIntrinsicTypes

-------------------------------------------------------------------------------
-- ** Initial CrucibleSetupMethodSpec

data SetupError
  = InvalidReturnType L.Type
  | InvalidArgTypes [L.Type]

ppSetupError :: SetupError -> PPL.Doc
ppSetupError (InvalidReturnType t) =
  PPL.text "Can't lift return type" PPL.<+>
  PPL.text (show (L.ppType t)) PPL.<+>
  PPL.text "to a Crucible type."
ppSetupError (InvalidArgTypes ts) =
  PPL.text "Can't lift argument types " PPL.<+>
  PPL.encloseSep PPL.lparen PPL.rparen PPL.comma (map (PPL.text . show . L.ppType) ts) PPL.<+>
  PPL.text "to Crucible types."

resolveArgs ::
  (?lc :: CL.TypeContext) =>
  [L.Type] ->
  Either SetupError [CL.MemType]
resolveArgs args = do
  -- TODO: make sure we resolve aliases
  let mtys = traverse CL.liftMemType args
  -- TODO: should the error message be propagated?
  either (\_ -> Left (InvalidArgTypes args)) Right mtys

resolveRetTy ::
  (?lc :: CL.TypeContext) =>
  L.Type ->
  Either SetupError (Maybe CL.MemType)
resolveRetTy ty = do
  -- TODO: make sure we resolve aliases
  let ret = CL.liftRetType ty
  -- TODO: should the error message be propagated?
  either (\_ -> Left (InvalidReturnType ty)) Right ret

initialDefCrucibleMethodSpecIR ::
  (?lc :: CL.TypeContext) =>
  LLVMModule arch ->
  L.Define ->
  ProgramLoc ->
  Maybe String ->
  Either SetupError (MS.CrucibleMethodSpecIR (CL.LLVM arch))
initialDefCrucibleMethodSpecIR llvmModule def loc parent = do
  args <- resolveArgs (L.typedType <$> L.defArgs def)
  ret <- resolveRetTy (L.defRetType def)
  let L.Symbol nm = L.defName def
  let methId = LLVMMethodId nm parent
  return $ MS.makeCrucibleMethodSpecIR methId args ret loc llvmModule

initialDeclCrucibleMethodSpecIR ::
  (?lc :: CL.TypeContext) =>
  LLVMModule arch ->
  L.Declare ->
  ProgramLoc ->
  Maybe String ->
  Either SetupError (MS.CrucibleMethodSpecIR (CL.LLVM arch))
initialDeclCrucibleMethodSpecIR llvmModule dec loc parent = do
  args <- resolveArgs (L.decArgs dec)
  ret <- resolveRetTy (L.decRetType dec)
  let L.Symbol nm = L.decName dec
  let methId = LLVMMethodId nm parent
  return $ MS.makeCrucibleMethodSpecIR methId args ret loc llvmModule

initialCrucibleSetupState ::
  (?lc :: CL.TypeContext) =>
  LLVMCrucibleContext arch ->
  L.Define ->
  ProgramLoc ->
  Maybe String ->
  Either SetupError (Setup.CrucibleSetupState (CL.LLVM arch))
initialCrucibleSetupState cc def loc parent = do
  ms <- initialDefCrucibleMethodSpecIR (cc ^. ccLLVMModule) def loc parent
  return $ Setup.makeCrucibleSetupState cc ms

initialCrucibleSetupStateDecl ::
  (?lc :: CL.TypeContext) =>
  LLVMCrucibleContext arch ->
  L.Declare ->
  ProgramLoc ->
  Maybe String ->
  Either SetupError (Setup.CrucibleSetupState (CL.LLVM arch))
initialCrucibleSetupStateDecl cc dec loc parent = do
  ms <- initialDeclCrucibleMethodSpecIR (cc ^. ccLLVMModule) dec loc parent
  return $ Setup.makeCrucibleSetupState cc ms

--------------------------------------------------------------------------------
-- ** AllLLVM/SomeLLVM

--------------------------------------------------------------------------------
-- *** AllLLVM

-- | Universal/polymorphic quantification over an 'LLVMArch'
--
-- The following type synonym and associated constructor/destructor are
-- equivalent to this definition:
-- @
-- data AllLLVM t =
--   MkAllLLVM { getAllLLVM :: forall arch. t (CL.LLVM arch) }
-- @
-- But they preserve the instances from 'All' and 'Compose'.
type AllLLVM t = All (Compose t CL.LLVM)

-- This doesn't work :(
--
-- pattern AllLLVM :: (forall arch. t (CL.LLVM arch)) -> AllLLVM t
-- pattern AllLLVM x = All (Compose x)

mkAllLLVM :: forall t. (forall arch. t (CL.LLVM arch)) -> AllLLVM t
mkAllLLVM x = All (Compose x)

getAllLLVM :: forall t. AllLLVM t -> (forall arch. t (CL.LLVM arch))
getAllLLVM (All (Compose x)) = x

-- Constructors for 'SetupValue' which are architecture-polymorphic

anySetupTerm :: TypedTerm -> AllLLVM MS.SetupValue
anySetupTerm typedTerm = mkAllLLVM (MS.SetupTerm typedTerm)

anySetupArray :: [AllLLVM MS.SetupValue] -> AllLLVM MS.SetupValue
anySetupArray vals = mkAllLLVM (MS.SetupArray () $ map getAllLLVM vals)

anySetupStruct :: Bool -> [AllLLVM MS.SetupValue] -> AllLLVM MS.SetupValue
anySetupStruct b vals = mkAllLLVM (MS.SetupStruct () b $ map getAllLLVM vals)

anySetupElem :: AllLLVM MS.SetupValue -> Int -> AllLLVM MS.SetupValue
anySetupElem val idx = mkAllLLVM (MS.SetupElem () (getAllLLVM val) idx)

anySetupField :: AllLLVM MS.SetupValue -> String -> AllLLVM MS.SetupValue
anySetupField val field = mkAllLLVM (MS.SetupField () (getAllLLVM val) field)

anySetupNull :: AllLLVM MS.SetupValue
anySetupNull = mkAllLLVM (MS.SetupNull ())

anySetupGlobal :: String -> AllLLVM MS.SetupValue
anySetupGlobal globalName = mkAllLLVM (MS.SetupGlobal () globalName)

anySetupGlobalInitializer :: String -> AllLLVM MS.SetupValue
anySetupGlobalInitializer globalName =
  mkAllLLVM (MS.SetupGlobalInitializer () globalName)

--------------------------------------------------------------------------------
-- *** SomeLLVM

-- | Existential quantification over an 'LLVMArch'
--
-- The following type synonym and associated constructor/destructor are
-- equivalent to this definition:
-- @
-- data SomeLLVM t = forall arch. MkSomeLLVM (t (CL.LLVM arch))
-- @
-- But they preserve the instances from 'Some' and 'Compose'.
type SomeLLVM t = Some (Compose t CL.LLVM)

pattern SomeLLVM :: t (CL.LLVM arch) -> SomeLLVM t
pattern SomeLLVM x = Some (Compose x)
{-# COMPLETE SomeLLVM #-}

mkSomeLLVM :: t (CL.LLVM arch) -> SomeLLVM t
mkSomeLLVM x = Some (Compose x)

getSomeLLVM :: forall t. (forall arch. t (CL.LLVM arch)) -> AllLLVM t
getSomeLLVM x = All (Compose x)
