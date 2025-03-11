{- |
Module      : SAWCentral.Crucible.LLVM.MethodSpecIR
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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
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

module SAWCentral.Crucible.LLVM.MethodSpecIR
  ( LLVM
    -- * LLVMMethodId
  , LLVMMethodId(..)
  , llvmMethodParent
  , llvmMethodName
  , csName
  , csParentName
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
  , ccWithBackend
  , ccSym
    -- * PointsTo
  , LLVMPointsTo(..)
  , LLVMPointsToValue(..)
  , llvmPointsToProgramLoc
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
  , anySetupCast
  , anySetupStruct
  , anySetupElem
  , anySetupField
  , anySetupUnion
  , anySetupNull
  , anySetupGlobal
  , anySetupGlobalInitializer
    -- * SomeLLVM
  , SomeLLVM
  , pattern SomeLLVM
  , mkSomeLLVM
  , getSomeLLVM
    -- * ResolvedState
  , LLVMResolvedState
  , ResolvedPath
  , ResolvedPathItem(..)
  , emptyResolvedState
  , rsAllocs
  , rsGlobals
  , markResolved
  , testResolved
  ) where

import           Control.Lens
import           Data.Functor.Compose (Compose(..))
import qualified Data.Map as Map
import qualified Prettyprinter as PPL
import qualified Text.LLVM.AST as L

import           Data.Parameterized.All (All(All))
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.Map as MapF

import           What4.ProgramLoc (ProgramLoc)

import qualified Lang.Crucible.Types as Crucible (SymbolRepr, knownSymbol)
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
  (IntrinsicMuxFn(IntrinsicMuxFn))
import qualified Lang.Crucible.LLVM.PrettyPrint as Crucible.LLVM

import           SAWCentral.Crucible.Common
import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import qualified SAWCentral.Crucible.Common.Setup.Type as Setup

import qualified SAWCentral.Crucible.LLVM.CrucibleLLVM as CL
import           SAWCentral.Crucible.LLVM.Setup.Value

import           Verifier.SAW.TypedTerm


--------------------------------------------------------------------------------
-- *** LLVMMethodId

csName :: Lens' (MS.CrucibleMethodSpecIR (LLVM arch)) String
csName = MS.csMethod . llvmMethodName

csParentName :: Lens' (MS.CrucibleMethodSpecIR (LLVM arch)) (Maybe String)
csParentName = MS.csMethod . llvmMethodParent

--------------------------------------------------------------------------------
-- *** LLVMAllocSpec

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
-- ** CrucibleContext

ccLLVMModuleAST :: LLVMCrucibleContext arch -> L.Module
ccLLVMModuleAST = modAST . _ccLLVMModule

ccLLVMModuleTrans :: LLVMCrucibleContext arch -> CL.ModuleTranslation arch
ccLLVMModuleTrans = modTrans . _ccLLVMModule

ccLLVMContext :: LLVMCrucibleContext arch -> CL.LLVMContext arch
ccLLVMContext = view CL.transContext . ccLLVMModuleTrans

ccTypeCtx :: LLVMCrucibleContext arch -> CL.TypeContext
ccTypeCtx = view CL.llvmTypeCtx . ccLLVMContext

ccWithBackend ::
  LLVMCrucibleContext arch ->
  (forall solver. OnlineSolver solver => Backend solver -> a) ->
  a
ccWithBackend cc k =
  case cc^.ccBackend of SomeOnlineBackend bak -> k bak

ccSym :: Getter (LLVMCrucibleContext arch) Sym
ccSym = to (\cc -> ccWithBackend cc backendGetSym)

--------------------------------------------------------------------------------
-- ** PointsTo

-- | Return the 'ProgramLoc' corresponding to an 'LLVMPointsTo' statement.
llvmPointsToProgramLoc :: LLVMPointsTo arch -> ProgramLoc
llvmPointsToProgramLoc (LLVMPointsTo md _ _ _) = MS.conditionLoc md
llvmPointsToProgramLoc (LLVMPointsToBitfield md _ _ _) = MS.conditionLoc md

ppPointsTo :: LLVMPointsTo arch -> PPL.Doc ann
ppPointsTo (LLVMPointsTo _md cond ptr val) =
  MS.ppSetupValue ptr
  PPL.<+> PPL.pretty "points to"
  PPL.<+> PPL.pretty val
  PPL.<+> maybe PPL.emptyDoc (\tt -> PPL.pretty "if" PPL.<+> MS.ppTypedTerm tt) cond
ppPointsTo (LLVMPointsToBitfield _md ptr fieldName val) =
  MS.ppSetupValue ptr <> PPL.pretty ("." ++ fieldName)
  PPL.<+> PPL.pretty "points to (bitfield)"
  PPL.<+> MS.ppSetupValue val

instance PPL.Pretty (LLVMPointsTo arch) where
  pretty = ppPointsTo

instance PPL.Pretty (LLVMPointsToValue arch) where
  pretty = \case
    ConcreteSizeValue val -> MS.ppSetupValue val
    SymbolicSizeValue arr sz ->
      MS.ppTypedTerm arr PPL.<+> PPL.pretty "[" PPL.<+> MS.ppTypedTerm sz PPL.<+> PPL.pretty "]"

--------------------------------------------------------------------------------
-- ** SAW LLVM intrinsics

-- | The default LLVM intrinsics extended with the 'MS.GhostValue' intrinsic,
-- which powers ghost state.
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

ppSetupError :: SetupError -> PPL.Doc ann
ppSetupError (InvalidReturnType t) =
  PPL.pretty "Can't lift return type" PPL.<+>
  PPL.viaShow (Crucible.LLVM.ppType t) PPL.<+>
  PPL.pretty "to a Crucible type."
ppSetupError (InvalidArgTypes ts) =
  PPL.pretty "Can't lift argument types " PPL.<+>
  PPL.encloseSep PPL.lparen PPL.rparen PPL.comma (map (PPL.viaShow . Crucible.LLVM.ppType) ts) PPL.<+>
  PPL.pretty "to Crucible types."

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
  Either SetupError (MS.CrucibleMethodSpecIR (LLVM arch))
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
  Either SetupError (MS.CrucibleMethodSpecIR (LLVM arch))
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
  Either SetupError (Setup.CrucibleSetupState (LLVM arch))
initialCrucibleSetupState cc def loc parent = do
  ms <- initialDefCrucibleMethodSpecIR (cc ^. ccLLVMModule) def loc parent
  return $ Setup.makeCrucibleSetupState emptyResolvedState cc ms

initialCrucibleSetupStateDecl ::
  (?lc :: CL.TypeContext) =>
  LLVMCrucibleContext arch ->
  L.Declare ->
  ProgramLoc ->
  Maybe String ->
  Either SetupError (Setup.CrucibleSetupState (LLVM arch))
initialCrucibleSetupStateDecl cc dec loc parent = do
  ms <- initialDeclCrucibleMethodSpecIR (cc ^. ccLLVMModule) dec loc parent
  return $ Setup.makeCrucibleSetupState emptyResolvedState cc ms

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
--   MkAllLLVM { getAllLLVM :: forall arch. t (LLVM arch) }
-- @
-- But they preserve the instances from 'All' and 'Compose'.
type AllLLVM t = All (Compose t LLVM)

-- This doesn't work :(
--
-- pattern AllLLVM :: (forall arch. t (LLVM arch)) -> AllLLVM t
-- pattern AllLLVM x = All (Compose x)

mkAllLLVM :: forall t. (forall arch. t (LLVM arch)) -> AllLLVM t
mkAllLLVM x = All (Compose x)

getAllLLVM :: forall t. AllLLVM t -> (forall arch. t (LLVM arch))
getAllLLVM (All (Compose x)) = x

-- Constructors for 'SetupValue' which are architecture-polymorphic

anySetupTerm :: TypedTerm -> AllLLVM MS.SetupValue
anySetupTerm typedTerm = mkAllLLVM (MS.SetupTerm typedTerm)

anySetupArray :: [AllLLVM MS.SetupValue] -> AllLLVM MS.SetupValue
anySetupArray vals = mkAllLLVM (MS.SetupArray () $ map (\a -> getAllLLVM a) vals)

anySetupStruct :: Bool -> [AllLLVM MS.SetupValue] -> AllLLVM MS.SetupValue
anySetupStruct b vals = mkAllLLVM (MS.SetupStruct b $ map (\a -> getAllLLVM a) vals)

anySetupElem :: AllLLVM MS.SetupValue -> Int -> AllLLVM MS.SetupValue
anySetupElem val idx = mkAllLLVM (MS.SetupElem () (getAllLLVM val) idx)

anySetupCast :: AllLLVM MS.SetupValue -> L.Type -> AllLLVM MS.SetupValue
anySetupCast val ty = mkAllLLVM (MS.SetupCast ty (getAllLLVM val))

anySetupField :: AllLLVM MS.SetupValue -> String -> AllLLVM MS.SetupValue
anySetupField val field = mkAllLLVM (MS.SetupField () (getAllLLVM val) field)

anySetupUnion :: AllLLVM MS.SetupValue -> String -> AllLLVM MS.SetupValue
anySetupUnion val uname = mkAllLLVM (MS.SetupUnion () (getAllLLVM val) uname)

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
-- data SomeLLVM t = forall arch. MkSomeLLVM (t (LLVM arch))
-- @
-- But they preserve the instances from 'Some' and 'Compose'.
type SomeLLVM t = Some (Compose t LLVM)

pattern SomeLLVM :: t (LLVM arch) -> SomeLLVM t
pattern SomeLLVM x = Some (Compose x)
{-# COMPLETE SomeLLVM #-}

mkSomeLLVM :: t (LLVM arch) -> SomeLLVM t
mkSomeLLVM x = Some (Compose x)

getSomeLLVM :: forall t. (forall arch. t (LLVM arch)) -> AllLLVM t
getSomeLLVM x = All (Compose x)

--------------------------------------------------------------------------------
-- *** ResolvedState

-- | Record the initialization of the pointer represented by the given
-- SetupValue.
markResolved ::
  MS.SetupValue (LLVM arch) ->
  ResolvedPath {-^ path within this object (if any) -} ->
  LLVMResolvedState ->
  LLVMResolvedState
markResolved val0 path0 rs = go path0 val0
  where
    go path val =
      case val of
        MS.SetupVar n         -> rs & rsAllocs %~ Map.alter (ins path) n
        MS.SetupGlobal _ name -> rs & rsGlobals %~ Map.alter (ins path) name
        MS.SetupElem _ v idx  -> go (ResolvedElem idx : path) v
        MS.SetupField _ v fld -> go (ResolvedField fld : path) v
        MS.SetupCast tp v     -> go (ResolvedCast tp : path) v
        _                     -> rs

    ins path Nothing = Just [path]
    ins path (Just paths) = Just (path : paths)

-- | Test whether the pointer represented by the given SetupValue has
-- been initialized already.
testResolved ::
  MS.SetupValue (LLVM arch) ->
  ResolvedPath {-^ path within this object (if any) -} ->
  LLVMResolvedState ->
  Bool
testResolved val0 path0 rs = go path0 val0
  where
    go path val =
      case val of
        MS.SetupVar n         -> test path (Map.lookup n (_rsAllocs rs))
        MS.SetupGlobal _ c    -> test path (Map.lookup c (_rsGlobals rs))
        MS.SetupElem _ v idx  -> go (ResolvedElem idx : path) v
        MS.SetupField _ v fld -> go (ResolvedField fld : path) v
        MS.SetupCast tp v     -> go (ResolvedCast tp : path) v
        _                     -> False

    test _ Nothing = False
    test path (Just paths) = any (overlap path) paths

    overlap (x : xs) (y : ys) = x == y && overlap xs ys
    overlap [] _ = True
    overlap _ [] = True
