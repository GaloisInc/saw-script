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

module SAWScript.Crucible.LLVM.MethodSpecIR where

import           Control.Lens
import           Data.Functor.Compose (Compose(..))
import           Data.Monoid ((<>))
import           Data.Type.Equality (TestEquality(..), (:~:)(Refl))
import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L
import qualified Text.PrettyPrint.ANSI.Leijen as PPL hiding ((<$>), (<>))
import qualified Text.PrettyPrint.HughesPJ as PP

import           Data.Parameterized.All (All(All))
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.Map as MapF

import           What4.ProgramLoc (ProgramLoc)

import qualified Lang.Crucible.Backend.SAWCore as Crucible
  (SAWCruciblePersonality)
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible (SimContext)
import qualified Lang.Crucible.Simulator.GlobalState as Crucible (SymGlobalState)
import qualified Lang.Crucible.Types as Crucible (SymbolRepr, knownSymbol)
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
  (IntrinsicMuxFn(IntrinsicMuxFn))
import           SAWScript.Crucible.Common (Sym)
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup

import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as CL

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

data LLVMModule arch =
  LLVMModule
  { _modName :: String
  , _modAST :: L.Module
  , _modTrans :: CL.ModuleTranslation arch
  }

makeLenses ''LLVMModule

instance TestEquality LLVMModule where
  testEquality (LLVMModule nm1 lm1 mt1) (LLVMModule nm2 lm2 mt2) =
    case testEquality mt1 mt2 of
      Nothing -> Nothing
      r@(Just Refl) ->
        if nm1 == nm2 && lm1 == lm2
        then r
        else Nothing

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
-- ** CrucibleContext

type instance MS.CrucibleContext (CL.LLVM arch) = LLVMCrucibleContext arch

data LLVMCrucibleContext arch =
  LLVMCrucibleContext
  { _ccLLVMModule      :: LLVMModule arch
  , _ccBackend         :: Sym
  , _ccLLVMEmptyMem    :: CL.MemImpl Sym -- ^ A heap where LLVM globals are allocated, but not initialized.
  , _ccLLVMSimContext  :: Crucible.SimContext (Crucible.SAWCruciblePersonality Sym) Sym (CL.LLVM arch)
  , _ccLLVMGlobals     :: Crucible.SymGlobalState Sym
  }

makeLenses ''LLVMCrucibleContext

ccLLVMModuleAST :: Simple Lens (LLVMCrucibleContext arch) L.Module
ccLLVMModuleAST = ccLLVMModule . modAST

ccLLVMModuleTrans :: Simple Lens (LLVMCrucibleContext arch) (CL.ModuleTranslation arch)
ccLLVMModuleTrans = ccLLVMModule . modTrans

ccLLVMContext :: Simple Lens (LLVMCrucibleContext arch) (CL.LLVMContext arch)
ccLLVMContext = ccLLVMModuleTrans . CL.transContext

ccTypeCtx :: Simple Lens (LLVMCrucibleContext arch) CL.TypeContext
ccTypeCtx = ccLLVMContext . CL.llvmTypeCtx

--------------------------------------------------------------------------------
-- ** PointsTo

type instance MS.PointsTo (CL.LLVM arch) = LLVMPointsTo arch

data LLVMPointsTo arch =
  LLVMPointsTo ProgramLoc (MS.SetupValue (CL.LLVM arch)) (MS.SetupValue (CL.LLVM arch))

ppPointsTo :: LLVMPointsTo arch -> PPL.Doc
ppPointsTo (LLVMPointsTo _loc ptr val) =
  MS.ppSetupValue ptr
  PPL.<+> PPL.text "points to"
  PPL.<+> MS.ppSetupValue val

instance PPL.Pretty (LLVMPointsTo arch) where
  pretty = ppPointsTo

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
