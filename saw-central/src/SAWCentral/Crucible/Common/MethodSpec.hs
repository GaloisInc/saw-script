{- |
Module      : SAWCentral.Crucible.Common.MethodSpec
Description : Language-neutral method specifications
License     : BSD3
Maintainer  : langston
Stability   : provisional

This module uses GADTs & type families to distinguish syntax-extension- (source
language-) specific code. This technique is described in the paper \"Trees That
Grow\", and is prevalent across the Crucible codebase.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SAWCentral.Crucible.Common.MethodSpec
  ( AllocIndex(..)
  , prettyAllocIndex
  , nextAllocIndex

  , PrePost(..)
  , stateCond

  , CrucibleContext
  , AllocSpec
  , TypeName
  , ExtType
  , PointsTo
  , AllocGlobal
  , ResolvedState

  , XSetupNull
  , XSetupStruct
  , XSetupTuple
  , XSetupSlice
  , XSetupArray
  , XSetupElem
  , XSetupField
  , XSetupGlobal
  , XSetupCast
  , XSetupUnion
  , XSetupGlobalInitializer
  , XSetupMux

  , SetupValue(..)
  , SetupValueHas

  , prettySetupValue
  , ppSetupValue

  , setupToTypedTerm
  , setupToTerm

  , GhostValue
  , GhostType
  , GhostGlobal

  , ConditionMetadata(..)

  , SetupCondition(..)
  , StateSpec(..)
  , csAllocs
  , csPointsTos
  , csConditions
  , csFreshVars
  , csVarTypeNames
  , initialStateSpec
  , prettySetupCondition

  , MethodId
  , Codebase

  , CrucibleMethodSpecIR(..)
  , csMethod
  , csArgs
  , csRet
  , csPreState
  , csPostState
  , csArgBindings
  , csRetValue
  , csGlobalAllocs
  , csCodebase
  , csLoc
  , ProofMethod(..)
  , SpecNonce
  , VCStats(..)
  , ProvedSpec(..)
  , psSpecIdent
  , psProofMethod
  , psSpec
  , psSolverStats
  , psVCStats
  , psSpecDeps
  , psElapsedTime
  , mkProvedSpec
  , prettyPosition
  , prettyMethodSpec
  , csAllocations
  , csTypeNames
  , makeCrucibleMethodSpecIR
  ) where

import           Data.Kind (Type)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Text as Text
import           Data.Text (Text)
import           Data.Time.Clock
import           Data.Void (absurd)

import           Control.Monad (when)
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans (lift)
import           Control.Lens
import qualified Prettyprinter as PP
import           Prettyprinter ((<+>))

import           Data.Parameterized.Nonce

-- what4
import           What4.ProgramLoc (ProgramLoc(plSourceLoc), Position)

import           Lang.Crucible.JVM (JVM)
import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx)
import qualified Lang.Crucible.CFG.Common as Crucible (GlobalVar)
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
import           Mir.Intrinsics (MIR)

import qualified Cryptol.TypeCheck.Type as Cryptol (Schema)

import qualified SAWSupport.Pretty as PPS

import qualified CryptolSAWCore.Pretty as CryPP
import           CryptolSAWCore.TypedTerm as SAWVerifier
import           SAWCore.SharedTerm as SAWVerifier
import           SAWCoreWhat4.ReturnTrip as SAWVerifier

import           SAWCentral.Crucible.Common (Sym, sawCoreState)
import           SAWCentral.Crucible.Common.Setup.Value
import           SAWCentral.Crucible.LLVM.Setup.Value (LLVM)
import           SAWCentral.Crucible.JVM.Setup.Value ()
import           SAWCentral.Crucible.MIR.Setup.Value
  ( MirSetupEnum(..), MirSetupSlice(..), MirIndexingMode(..)
  , MirFieldAccessMode(..)
  )
import           SAWCentral.Options
import           SAWCentral.Prover.SolverStats
import           SAWCentral.Utils (bullets)
import           SAWCentral.Proof (TheoremNonce, TheoremSummary)

-- | Are we writing preconditions or postconditions?
data PrePost
  = PreState | PostState
  deriving (Eq, Ord, Show)

stateCond :: PrePost -> String
stateCond PreState = "precondition"
stateCond PostState = "postcondition"

--------------------------------------------------------------------------------
-- ** SetupValue

-- | A singleton type that encodes the extensions used for each SAW backend.
-- Matching on a value of type @'SAWExt' ext@ allows one to learn which backend
-- is currently in use.
data SAWExt :: Type -> Type where
  LLVMExt :: SAWExt (LLVM arch)
  JVMExt  :: SAWExt JVM
  MIRExt  :: SAWExt MIR

-- | This allows checking which SAW backend we are using at runtime.
class IsExt ext where
  sawExt :: SAWExt ext

instance IsExt (LLVM arch) where
  sawExt = LLVMExt
instance IsExt JVM where
  sawExt = JVMExt
instance IsExt MIR where
  sawExt = MIRExt

-- | Note that most 'SetupValue' concepts (like allocation indices)
--   are implementation details and won't be familiar to users.
--   Consider using 'resolveSetupValue' and printing the language-specific value
--   (e.g., an 'LLVMVal') with @PP.pretty@ instead.
--
--   This needs the `SharedContext` and `Opts` and prints in `IO` so it can
--   print SAWCore `Term`s correctly.
prettySetupValue ::
    forall ext. IsExt ext =>
    SharedContext -> PPS.Opts -> SetupValue ext -> IO PPS.Doc
prettySetupValue sc opts setupval = case setupval of
  SetupTerm tm   -> prettyTypedTerm sc opts tm
  SetupVar i     -> pure $ prettyAllocIndex i
  SetupNull _    -> pure $ "NULL"
  SetupStruct x vs ->
    case (ext, x) of
      (LLVMExt, packed) ->
        prettySetupStructLLVM packed vs
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, _defId) ->
        prettySetupStructDefault vs
  SetupEnum x ->
    case (ext, x) of
      (LLVMExt, empty) ->
        absurd empty
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, enum_) ->
        prettyMirSetupEnum enum_
  SetupTuple x vs ->
    case (ext, x) of
      (LLVMExt, empty) ->
        absurd empty
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, ()) ->
        prettySetupTuple vs
  SetupSlice x ->
    case (ext, x) of
      (LLVMExt, empty) ->
        absurd empty
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, slice) ->
        prettyMirSetupSlice slice
  SetupArray _ vs  -> do
    vs' <- mapM (prettySetupValue sc opts) vs
    pure $ PP.brackets $ PP.hsep $ PP.punctuate "," vs'
  SetupElem x v i  -> do
    v' <- PP.parens <$> prettySetupValue sc opts v
    let i' :: PPS.Doc  -- required to avoid type errors on at least GHC 9.4
        i' = PP.pretty i
    case (ext, x) of
      (LLVMExt, ()) ->
        pure $ v' <> "." <> i'
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, m) ->
        case m of
          MirIndexIntoVal ->
            pure $ v' <> PP.brackets i'
          MirIndexIntoRef ->
            pure $ v' <> ".add" <> PP.parens i'
          MirIndexOffsetRef ->
            pure $ v' <> ".offset" <> PP.parens i'
  SetupField x v f -> do
    v' <- prettySetupValue sc opts v
    let vf' = PP.parens v' <> "." <> PP.pretty f
    case (ext, x) of
      (LLVMExt, ()) ->
        pure vf'
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, m) ->
        case m of
          MirFieldAccessByVal ->
            pure vf'
          MirFieldAccessByRef ->
            pure $ "&" <> vf'
  SetupUnion _ v u -> do
    v' <- prettySetupValue sc opts v
    pure $ PP.parens v' <> "." <> PP.pretty u
  SetupCast x v ->
    case (ext, x) of
      (LLVMExt, tp) ->
        prettyCast v tp
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, ty) ->
        prettyCast v ty
  SetupGlobal _ nm ->
    pure $ "global" <> PP.parens (PP.pretty nm)
  SetupGlobalInitializer _ nm ->
    pure $ "global_initializer" <> PP.parens (PP.pretty nm)
  SetupMux x c t f -> do
    c' :: PPS.Doc <- prettyTypedTerm sc opts c
    t' <- prettySetupValue sc opts t
    f' <- prettySetupValue sc opts f
    case (ext, x) of
      (LLVMExt, empty) ->
        absurd empty
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, ()) ->
        pure $ "mux" <> PP.parens (c' <> PP.comma <+> t' <> PP.comma <+> f')
  where
    ext :: SAWExt ext
    ext = sawExt @ext

    prettySetupStructLLVM ::
         Bool
         -- ^ 'True' if this is an LLVM packed struct, 'False' otherwise.
      -> [SetupValue ext] -> IO PPS.Doc
    prettySetupStructLLVM packed vs
      | packed    = PP.angles <$> prettySetupStructDefault vs
      | otherwise = prettySetupStructDefault vs

    prettySetupStructDefault :: forall ext'. IsExt ext' => [SetupValue ext'] -> IO PPS.Doc
    prettySetupStructDefault vs = do
        vs' <- mapM (prettySetupValue sc opts) vs
        pure $ PP.braces $ PP.hsep $ PP.punctuate "," vs'

    prettySetupTuple :: [SetupValue MIR] -> IO PPS.Doc
    prettySetupTuple vs = do
        vs' <- mapM (prettySetupValue sc opts) vs
        pure $ PP.parens $ PP.hsep $ PP.punctuate "," vs'

    prettyMirSetupEnum :: MirSetupEnum -> IO PPS.Doc
    prettyMirSetupEnum (MirSetupEnumVariant _defId variantName _varIdx fields) = do
        fields' <- prettySetupStructDefault fields
        pure $ PP.pretty variantName <+> fields'
    prettyMirSetupEnum (MirSetupEnumSymbolic _defId _discr _variants) =
        pure $ "<symbolic enum>"

    prettyMirSetupSlice :: MirSetupSlice -> IO PPS.Doc
    prettyMirSetupSlice (MirSetupSliceRaw ref len) = do
        reflen' <- prettySetupTuple [ref, len]
        pure $ "SliceRaw" <> reflen'
    prettyMirSetupSlice (MirSetupSlice _ arr) = do
        arr' <- prettySetupValue sc opts arr
        pure $ arr' <> "[..]"
    prettyMirSetupSlice (MirSetupSliceRange _ arr start end) = do
        arr' <- prettySetupValue sc opts arr
        pure $ arr' <> "[" <> PP.pretty start <> ".." <> PP.pretty end <> "]"

    prettyCast :: Show ty => SetupValue ext -> ty -> IO PPS.Doc
    prettyCast v ty = do
        v' <- prettySetupValue sc opts v
        pure $ PP.parens v' <+> "AS" <+> PP.viaShow ty

ppSetupValue ::
    forall ext. IsExt ext =>
    SharedContext -> PPS.Opts -> SetupValue ext -> IO Text
ppSetupValue sc opts v =
    PPS.renderText opts <$> prettySetupValue sc opts v

setupToTypedTerm ::
  Options {-^ Printing options -} ->
  SharedContext ->
  SetupValue ext ->
  MaybeT IO TypedTerm
setupToTypedTerm opts sc sv =
  case sv of
    SetupTerm term -> return term
    _ -> do t <- setupToTerm opts sc sv
            lift $ mkTypedTerm sc t

-- | Convert a setup value to a SAW-Core term. This is a partial
-- function, as certain setup values ---SetupVar, SetupNull and
-- SetupGlobal--- don't have semantics outside of the symbolic
-- simulator.
setupToTerm ::
  Options ->
  SharedContext ->
  SetupValue ext ->
  MaybeT IO Term
setupToTerm opts sc =
  \case
    SetupTerm term -> return (ttTerm term)

    SetupStruct _ fields ->
      do ts <- mapM (setupToTerm opts sc) fields
         lift $ scTuple sc ts

    SetupArray _ elems@(_:_) ->
      do ts@(t:_) <- mapM (setupToTerm opts sc) elems
         typt <- lift $ scTypeOf sc t
         vec <- lift $ scVector sc typt ts
         typ <- lift $ scTypeOf sc vec
         -- XXX what is this code for?
         vec' <- lift $ prettyTerm sc PPS.defaultOpts vec
         typ' <- lift $ prettyTerm sc PPS.defaultOpts typ
         lift $ printOutLn opts Info $ PPS.render PPS.defaultOpts vec'
         lift $ printOutLn opts Info $ PPS.render PPS.defaultOpts typ'
         return vec

    SetupElem _ base ind ->
      case base of
        SetupArray _ elems@(e:_) ->
          do let intToNat = fromInteger . toInteger
             art <- setupToTerm opts sc base
             ixt <- lift $ scNat sc $ intToNat ind
             lent <- lift $ scNat sc $ intToNat $ length elems
             et <- setupToTerm opts sc e
             typ <- lift $ scTypeOf sc et
             lift $ scAt sc lent typ art ixt

        SetupStruct _ fs ->
          do st <- setupToTerm opts sc base
             lift $ scTupleSelector sc st ind (length fs)

        _ -> MaybeT $ return Nothing

    -- SetupVar, SetupNull, SetupGlobal
    _ -> MaybeT $ return Nothing

--------------------------------------------------------------------------------
-- ** Ghost state

type GhostValue  = "GhostValue"
type GhostType   = Crucible.IntrinsicType GhostValue Crucible.EmptyCtx
type GhostGlobal = Crucible.GlobalVar GhostType

instance Crucible.IntrinsicClass Sym GhostValue where
  type Intrinsic Sym GhostValue ctx = (Cryptol.Schema, Term)
  muxIntrinsic sym _ _namerep _ctx prd (thnSch,thn) (elsSch,els) =
    do when (thnSch /= elsSch) $ fail $ unlines $
         [ "Attempted to mux ghost variables of different types:"
         , Text.unpack (CryPP.pp thnSch)
         , Text.unpack (CryPP.pp elsSch)
         ]
       st <- sawCoreState sym
       let sc  = saw_sc st
       prd' <- toSC sym st prd
       typ  <- scTypeOf sc thn
       res  <- scIte sc typ prd' thn els
       return (thnSch, res)

--------------------------------------------------------------------------------
-- *** StateSpec

data SetupCondition ext where
  SetupCond_Equal    :: ConditionMetadata -> SetupValue ext -> SetupValue ext -> SetupCondition ext
  SetupCond_Pred     :: ConditionMetadata -> TypedTerm -> SetupCondition ext
  SetupCond_Ghost    :: ConditionMetadata ->
                        GhostGlobal ->
                        TypedTerm ->
                        SetupCondition ext

deriving instance SetupValueHas Show ext => Show (SetupCondition ext)

prettySetupCondition :: IsExt ext =>
      SharedContext -> PPS.Opts -> SetupCondition ext -> IO PPS.Doc
prettySetupCondition sc opts cond = case cond of
  SetupCond_Equal meta val1 val2 -> do
    let meta' = PP.viaShow meta
    val1' <- prettySetupValue sc opts val1
    val2' <- prettySetupValue sc opts val2
    pure $ "equal" <+> PP.braces meta' <+> val1' <+> "==" <+> val2'
  SetupCond_Pred meta tt -> do
    let meta' = PP.viaShow meta
    tt' <- prettyTypedTerm sc opts tt
    pure $ "pred" <+> PP.braces meta' <+> tt'
  SetupCond_Ghost meta ghost tt -> do
    let meta' = PP.viaShow meta
        ghost' = PP.viaShow ghost
    tt' <- prettyTypedTerm sc opts tt
    pure $ "ghost" <+> PP.braces meta' <+> ghost' <+> ":" <+> tt'

-- | Verification state (either pre- or post-) specification
data StateSpec ext = StateSpec
  { _csAllocs        :: Map AllocIndex (AllocSpec ext)
    -- ^ allocated or declared pointers
  , _csPointsTos     :: [PointsTo ext]
    -- ^ points-to statements
  , _csConditions    :: [SetupCondition ext]
    -- ^ equality, propositions, and ghost-variable conditions
  , _csFreshVars     :: [TypedVariable]
    -- ^ fresh variables created in this state
  , _csVarTypeNames  :: !(Map AllocIndex (TypeName ext))
    -- ^ names for types of variables, for diagnostics
  }

makeLenses ''StateSpec

initialStateSpec :: StateSpec ext
initialStateSpec =  StateSpec
  { _csAllocs        = Map.empty
  , _csPointsTos     = []
  , _csConditions    = []
  , _csFreshVars     = []
  , _csVarTypeNames  = Map.empty
  }

--------------------------------------------------------------------------------
-- *** Method specs

data CrucibleMethodSpecIR ext =
  CrucibleMethodSpec
  { _csMethod          :: MethodId ext
  , _csArgs            :: [ExtType ext]
  , _csRet             :: Maybe (ExtType ext)
  , _csPreState        :: StateSpec ext -- ^ state before the function runs
  , _csPostState       :: StateSpec ext -- ^ state after the function runs
  , _csArgBindings     :: Map Integer (ExtType ext, SetupValue ext) -- ^ function arguments
  , _csRetValue        :: Maybe (SetupValue ext) -- ^ function return value
  , _csGlobalAllocs    :: [AllocGlobal ext] -- ^ globals allocated
  , _csCodebase        :: Codebase ext -- ^ the codebase this spec was verified against
  , _csLoc             :: ProgramLoc -- ^ where in the SAWscript was this spec?
  }

makeLenses ''CrucibleMethodSpecIR

data ProofMethod
  = SpecAdmitted
  | SpecProved

type SpecNonce ext = Nonce GlobalNonceGenerator (ProvedSpec ext)

-- | Data collected about discharged verification conditions (VCs).
--   Verification conditions arise when proving function specifications
--   due to, e.g., safety conditions, specification postconditions, and
--   preconditions of called override functions.
data VCStats =
  VCStats
  { vcMetadata    :: ConditionMetadata -- ^ Metadata describing why the VC arose
  , vcSolverStats :: SolverStats       -- ^ Statistics about any solvers used when proving this VC
  , vcThmSummary  :: TheoremSummary    -- ^ A summary of the proof status of this VC
  , vcIdent       :: TheoremNonce      -- ^ A unique identifier for this VC
  , vcDeps        :: Set TheoremNonce  -- ^ A collection of the theorems the proof of this VC relied on
  , vcElapsedTime :: NominalDiffTime   -- ^ The time required to prove this VC
  }

data ProvedSpec ext =
  ProvedSpec
  { _psSpecIdent   :: Nonce GlobalNonceGenerator (ProvedSpec ext)
  , _psProofMethod :: ProofMethod
  , _psSpec        :: CrucibleMethodSpecIR ext
  , _psSolverStats :: SolverStats -- ^ statistics about the proof that produced this
  , _psVCStats     :: [VCStats]
       -- ^ Stats about the individual verification conditions produced
       --   by the proof of this specification
  , _psSpecDeps    :: Set (SpecNonce ext)
                        -- ^ Other proved specifications this proof depends on
  , _psElapsedTime :: NominalDiffTime -- ^ The time elapsed during the proof of this specification
  }

makeLenses ''ProvedSpec

mkProvedSpec ::
  ProofMethod ->
  CrucibleMethodSpecIR ext ->
  SolverStats ->
  [VCStats] ->
  Set (SpecNonce ext) ->
  NominalDiffTime ->
  IO (ProvedSpec ext)
mkProvedSpec m mspec stats vcStats sps elapsed =
  do n <- freshNonce globalNonceGenerator
     let ps = ProvedSpec n m mspec stats vcStats sps elapsed
     return ps

-- TODO: remove when what4 switches to prettyprinter
prettyPosition :: Position -> PP.Doc ann
prettyPosition = PP.viaShow

prettyMethodSpec ::
  ( PP.Pretty (MethodId ext)
  , PP.Pretty (ExtType ext)
  ) =>
  CrucibleMethodSpecIR ext ->
  PP.Doc ann
prettyMethodSpec methodSpec =
  PP.vcat
  [ "Name: " <> PP.pretty (methodSpec ^. csMethod)
  , "Location: " <> prettyPosition (plSourceLoc (methodSpec ^. csLoc))
  , "Argument types: "
  , bullets '-' (map PP.pretty (methodSpec ^. csArgs))
  , "Return type: " <> case methodSpec ^. csRet of
                                       Nothing  -> "<void>"
                                       Just ret -> PP.pretty ret
  ]

csAllocations :: CrucibleMethodSpecIR ext -> Map AllocIndex (AllocSpec ext)
csAllocations
  = Map.unions
  . toListOf ((csPreState <> csPostState) . csAllocs)

csTypeNames :: CrucibleMethodSpecIR ext -> Map AllocIndex (TypeName ext)
csTypeNames
  = Map.unions
  . toListOf ((csPreState <> csPostState) . csVarTypeNames)

makeCrucibleMethodSpecIR ::
  MethodId ext ->
  [ExtType ext] ->
  Maybe (ExtType ext) ->
  ProgramLoc ->
  Codebase ext ->
  CrucibleMethodSpecIR ext
makeCrucibleMethodSpecIR meth args ret loc code = do
  CrucibleMethodSpec
    {_csMethod          = meth
    ,_csArgs            = args
    ,_csRet             = ret
    ,_csPreState        = initialStateSpec
    ,_csPostState       = initialStateSpec
    ,_csArgBindings     = Map.empty
    ,_csRetValue        = Nothing
    ,_csGlobalAllocs    = []
    ,_csLoc             = loc
    ,_csCodebase        = code
    }
