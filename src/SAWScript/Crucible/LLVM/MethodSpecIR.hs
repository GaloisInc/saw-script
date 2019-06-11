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
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))

import           Data.IORef
import           Data.Monoid ((<>))
import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L

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
--import qualified Lang.Crucible.LLVM.MemModel as CL (MemImpl)
--import qualified Lang.Crucible.LLVM.Translation as CL
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
  (IntrinsicClass(Intrinsic, muxIntrinsic))
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

instance PP.Pretty LLVMMethodId where
  pretty = PP.text . view llvmMethodName

instance PP.Pretty CL.MemType where
  pretty = CL.ppMemType

type instance MS.MethodId (CL.LLVM _) = LLVMMethodId

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

ppSetupError :: SetupError -> PP.Doc
ppSetupError (InvalidReturnType t) =
  text "Can't lift return type" <+>
  text (show (L.ppType t)) <+>
  text "to a Crucible type."
ppSetupError (InvalidArgTypes ts) =
  text "Can't lift argument types " <+>
  encloseSep lparen rparen comma (map (text . show . L.ppType) ts) <+>
  text "to Crucible types."

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

-- TODO: Is this really the right place for these?

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
