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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module SAWScript.Crucible.LLVM.MethodSpecIR where

import           Control.Lens
import           Data.IORef
import           Data.Monoid ((<>))
import           Data.Type.Equality (TestEquality(..), (:~:)(Refl))
import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L
import qualified Text.PrettyPrint.ANSI.Leijen as PPL hiding ((<$>), (<>))
import qualified Text.PrettyPrint.HughesPJ as PP

import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableF (FunctorF(..), FoldableF(..))

import qualified What4.Expr.Builder as B
import           What4.ProgramLoc (ProgramLoc)

import qualified Lang.Crucible.Backend.SAWCore as Crucible
  (SAWCoreBackend, saw_ctx, toSC, SAWCruciblePersonality)
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible (SimContext)
import qualified Lang.Crucible.Simulator.GlobalState as Crucible (SymGlobalState)
import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx, SymbolRepr, knownSymbol)
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
  (IntrinsicClass(Intrinsic, muxIntrinsic), IntrinsicMuxFn(IntrinsicMuxFn))
import           SAWScript.Crucible.Common (Sym)
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup

import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as CL

import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedTerm

--------------------------------------------------------------------------------
-- ** Language features

type instance MS.HasSetupNull (CL.LLVM arch) = 'True
type instance MS.HasSetupStruct (CL.LLVM arch) = 'True
type instance MS.HasSetupArray (CL.LLVM arch) = 'True
type instance MS.HasSetupElem (CL.LLVM arch) = 'True
type instance MS.HasSetupField (CL.LLVM arch) = 'True
type instance MS.HasSetupGlobal (CL.LLVM arch) = 'True
type instance MS.HasSetupGlobalInitializer (CL.LLVM arch) = 'True

type instance MS.HasGhostState (CL.LLVM arch) = 'True

type instance MS.TypeName ext = CL.Ident
type instance MS.ExtType (CL.LLVM arch) = CL.MemType

--------------------------------------------------------------------------------
-- *** LLVMMethodId

data LLVMMethodId =
  LLVMMethodId
    { _llvmMethodName   :: String
    , _llvmMethodParent :: Maybe String -- ^ Something to do with breakpoints...
    } deriving (Eq, Ord, Show) -- TODO: deriving

makeLenses ''LLVMMethodId

csName :: Lens' (MS.CrucibleMethodSpecIR (CL.LLVM arch)) String
csName = MS.csMethod . llvmMethodName

csParentName :: Lens' (MS.CrucibleMethodSpecIR (CL.LLVM arch)) (Maybe String)
csParentName = MS.csMethod . llvmMethodParent

instance PPL.Pretty LLVMMethodId where
  pretty = PPL.text . view llvmMethodName

instance PPL.Pretty CL.MemType where
  pretty = CL.ppMemType

type instance MS.MethodId (CL.LLVM _) = LLVMMethodId

--------------------------------------------------------------------------------
-- *** LLVMAllocSpec

-- Is this LLVM-specific? what could we do for java?
data LLVMAllocSpec =
  LLVMAllocSpec
    { _allocSpecMut   :: CL.Mutability
    , _allocSpecType  :: CL.MemType
    , _allocSpecBytes :: CL.Bytes
    , _allocSpecLoc   :: ProgramLoc
    } -- TODO: deriving

makeLenses ''LLVMAllocSpec

type instance MS.AllocSpec (CL.LLVM _) = LLVMAllocSpec

--------------------------------------------------------------------------------
-- *** LLVMModule

data LLVMModule arch =
  LLVMModule
  { modName :: String
  , modMod :: L.Module
  , modTrans :: CL.ModuleTranslation arch
  }

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
-- ** Ghost state

instance Crucible.IntrinsicClass (Crucible.SAWCoreBackend n solver (B.Flags B.FloatReal)) MS.GhostValue where
  type Intrinsic (Crucible.SAWCoreBackend n solver (B.Flags B.FloatReal)) MS.GhostValue ctx = TypedTerm
  muxIntrinsic sym _ _namerep _ctx prd thn els =
    do st <- readIORef (B.sbStateManager sym)
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
  { _ccLLVMModule      :: L.Module
  , _ccLLVMModuleTrans :: CL.ModuleTranslation arch
  , _ccBackend         :: Sym
  , _ccLLVMEmptyMem    :: CL.MemImpl Sym -- ^ A heap where LLVM globals are allocated, but not initialized.
  , _ccLLVMSimContext  :: Crucible.SimContext (Crucible.SAWCruciblePersonality Sym) Sym (CL.LLVM arch)
  , _ccLLVMGlobals     :: Crucible.SymGlobalState Sym
  }

makeLenses ''LLVMCrucibleContext

ccLLVMContext :: Simple Lens (LLVMCrucibleContext wptr) (CL.LLVMContext wptr)
ccLLVMContext = ccLLVMModuleTrans . CL.transContext

ccTypeCtx :: Simple Lens (LLVMCrucibleContext wptr) CL.TypeContext
ccTypeCtx = ccLLVMContext . CL.llvmTypeCtx

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
  L.Define ->
  ProgramLoc ->
  Maybe String ->
  Either SetupError (MS.CrucibleMethodSpecIR (CL.LLVM arch))
initialDefCrucibleMethodSpecIR def loc parent = do
  args <- resolveArgs (L.typedType <$> L.defArgs def)
  ret <- resolveRetTy (L.defRetType def)
  let L.Symbol nm = L.defName def
  let methId = LLVMMethodId nm parent
  return $ MS.makeCrucibleMethodSpecIR methId args ret loc

initialDeclCrucibleMethodSpecIR ::
  (?lc :: CL.TypeContext) =>
  L.Declare ->
  ProgramLoc ->
  Maybe String ->
  Either SetupError (MS.CrucibleMethodSpecIR (CL.LLVM arch))
initialDeclCrucibleMethodSpecIR dec loc parent = do
  args <- resolveArgs (L.decArgs dec)
  ret <- resolveRetTy (L.decRetType dec)
  let L.Symbol nm = L.decName dec
  let methId = LLVMMethodId nm parent
  return $ MS.makeCrucibleMethodSpecIR methId args ret loc

initialCrucibleSetupState ::
  (?lc :: CL.TypeContext) =>
  LLVMCrucibleContext arch ->
  L.Define ->
  ProgramLoc ->
  Maybe String ->
  Either SetupError (Setup.CrucibleSetupState (CL.LLVM arch))
initialCrucibleSetupState cc def loc parent = do
  ms <- initialDefCrucibleMethodSpecIR def loc parent
  return $ Setup.makeCrucibleSetupState cc ms

initialCrucibleSetupStateDecl ::
  (?lc :: CL.TypeContext) =>
  LLVMCrucibleContext arch ->
  L.Declare ->
  ProgramLoc ->
  Maybe String ->
  Either SetupError (Setup.CrucibleSetupState (CL.LLVM arch))
initialCrucibleSetupStateDecl cc dec loc parent = do
  ms <- initialDeclCrucibleMethodSpecIR dec loc parent
  return $ Setup.makeCrucibleSetupState cc ms

--------------------------------------------------------------------------------
-- ** AnyLLVM/SomeLLVM

-- TODO: Upstream to crucible-llvm

-- | Universal/polymorphic quantification over an 'LLVMArch'
data AnyLLVM t =
  AnyLLVM { getAnyLLVM :: forall arch. t (CL.LLVM arch) }

instance FunctorF AnyLLVM where
  fmapF nat (AnyLLVM a) = AnyLLVM (nat a)

instance FoldableF AnyLLVM where
  foldMapF tom (AnyLLVM x) = tom x

constAnyLLVM :: a -> AnyLLVM (Const a)
constAnyLLVM a = AnyLLVM (Const a)

-- | Existential quantification over an 'LLVMArch'
data SomeLLVM t = forall arch. SomeLLVM { getSomeLLVM :: t (CL.LLVM arch) }


-- Constructors for 'SetupValue' which are architecture-polymorphic

anySetupArray :: [AnyLLVM MS.SetupValue] -> AnyLLVM MS.SetupValue
anySetupArray svs = AnyLLVM (MS.SetupArray () $ map getAnyLLVM svs)

anySetupStruct :: Bool -> [AnyLLVM MS.SetupValue] -> AnyLLVM MS.SetupValue
anySetupStruct b svs = AnyLLVM (MS.SetupStruct () b $ map getAnyLLVM svs)
