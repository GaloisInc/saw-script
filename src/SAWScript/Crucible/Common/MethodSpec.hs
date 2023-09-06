{- |
Module      : SAWScript.Crucible.Common.MethodSpec
Description : Language-neutral method specifications
License     : BSD3
Maintainer  : langston
Stability   : provisional

This module uses GADTs & type families to distinguish syntax-extension- (source
language-) specific code. This technique is described in the paper \"Trees That
Grow\", and is prevalent across the Crucible codebase.
-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Crucible.Common.MethodSpec
  ( AllocIndex(..)
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
  , XSetupArray
  , XSetupElem
  , XSetupField
  , XSetupGlobal
  , XSetupCast
  , XSetupUnion
  , XSetupGlobalInitializer

  , SetupValue(..)
  , SetupValueHas

  , ppSetupValue
  , ppAllocIndex
  , ppTypedTerm
  , ppTypedTermType
  , ppTypedExtCns

  , setupToTypedTerm
  , setupToTerm

  , XGhostState
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
  , ppMethodSpec
  , csAllocations
  , csTypeNames
  , makeCrucibleMethodSpecIR
  ) where

import           Data.Kind (Type)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import           Data.Time.Clock
import           Data.Void (absurd)

import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans (lift)
import           Control.Lens
import qualified Prettyprinter as PP

import           Data.Parameterized.Nonce

-- what4
import           What4.ProgramLoc (ProgramLoc(plSourceLoc), Position)

import           Lang.Crucible.JVM (JVM)
import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx)
import qualified Lang.Crucible.CFG.Common as Crucible (GlobalVar)
import           Mir.Intrinsics (MIR)

import qualified Cryptol.Utils.PP as Cryptol

import           Verifier.SAW.TypedTerm as SAWVerifier
import           Verifier.SAW.SharedTerm as SAWVerifier

import           SAWScript.Crucible.Common.Setup.Value
import           SAWScript.Crucible.LLVM.Setup.Value (LLVM)
import           SAWScript.Crucible.JVM.Setup.Value ()
import           SAWScript.Crucible.MIR.Setup.Value ()
import           SAWScript.Options
import           SAWScript.Prover.SolverStats
import           SAWScript.Utils (bullets)
import           SAWScript.Proof (TheoremNonce, TheoremSummary)

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
ppSetupValue :: forall ext ann. IsExt ext => SetupValue ext -> PP.Doc ann
ppSetupValue setupval = case setupval of
  SetupTerm tm   -> ppTypedTerm tm
  SetupVar i     -> ppAllocIndex i
  SetupNull _    -> PP.pretty "NULL"
  SetupStruct x vs ->
    case (ext, x) of
      (LLVMExt, packed) ->
        ppSetupStructLLVM packed vs
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, ()) ->
        ppSetupStructDefault vs
  SetupArray _ vs  -> PP.brackets (commaList (map ppSetupValue vs))
  SetupElem _ v i  -> PP.parens (ppSetupValue v) PP.<> PP.pretty ("." ++ show i)
  SetupField _ v f -> PP.parens (ppSetupValue v) PP.<> PP.pretty ("." ++ f)
  SetupUnion _ v u -> PP.parens (ppSetupValue v) PP.<> PP.pretty ("." ++ u)
  SetupCast x v ->
    case (ext, x) of
      (LLVMExt, tp) ->
        PP.parens (ppSetupValue v) PP.<> PP.pretty (" AS " ++ show tp)
      (JVMExt, empty) ->
        absurd empty
      (MIRExt, empty) ->
        absurd empty
  SetupGlobal _ nm -> PP.pretty ("global(" ++ nm ++ ")")
  SetupGlobalInitializer _ nm -> PP.pretty ("global_initializer(" ++ nm ++ ")")
  where
    ext :: SAWExt ext
    ext = sawExt @ext

    commaList :: [PP.Doc ann] -> PP.Doc ann
    commaList []     = PP.emptyDoc
    commaList (x:xs) = x PP.<> PP.hcat (map (\y -> PP.comma PP.<+> y) xs)

    ppSetupStructLLVM ::
         Bool
         -- ^ 'True' if this is an LLVM packed struct, 'False' otherwise.
      -> [SetupValue ext] -> PP.Doc ann
    ppSetupStructLLVM packed vs
      | packed    = PP.angles (ppSetupStructDefault vs)
      | otherwise = ppSetupStructDefault vs

    ppSetupStructDefault :: [SetupValue ext] -> PP.Doc ann
    ppSetupStructDefault vs = PP.braces (commaList (map ppSetupValue vs))

ppAllocIndex :: AllocIndex -> PP.Doc ann
ppAllocIndex i = PP.pretty '@' <> PP.viaShow i

ppTypedTerm :: TypedTerm -> PP.Doc ann
ppTypedTerm (TypedTerm tp tm) =
  PP.unAnnotate (ppTerm defaultPPOpts tm)
  PP.<+> PP.pretty ":" PP.<+>
  ppTypedTermType tp

ppTypedTermType :: TypedTermType -> PP.Doc ann
ppTypedTermType (TypedTermSchema sch) =
  PP.viaShow (Cryptol.ppPrec 0 sch)
ppTypedTermType (TypedTermKind k) =
  PP.viaShow (Cryptol.ppPrec 0 k)
ppTypedTermType (TypedTermOther tp) =
  PP.unAnnotate (ppTerm defaultPPOpts tp)

ppTypedExtCns :: TypedExtCns -> PP.Doc ann
ppTypedExtCns (TypedExtCns tp ec) =
  PP.unAnnotate (ppName (ecName ec))
  PP.<+> PP.pretty ":" PP.<+>
  PP.viaShow (Cryptol.ppPrec 0 tp)

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
         lift $ printOutLn opts Info $ show vec
         lift $ printOutLn opts Info $ show typ
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

--------------------------------------------------------------------------------
-- *** StateSpec

data SetupCondition ext where
  SetupCond_Equal    :: ConditionMetadata -> SetupValue ext -> SetupValue ext -> SetupCondition ext
  SetupCond_Pred     :: ConditionMetadata -> TypedTerm -> SetupCondition ext
  SetupCond_Ghost    :: XGhostState ext ->
                        ConditionMetadata ->
                        GhostGlobal ->
                        TypedTerm ->
                        SetupCondition ext

deriving instance ( SetupValueHas Show ext
                  , Show (XGhostState ext)
                  ) => Show (SetupCondition ext)

-- | Verification state (either pre- or post-) specification
data StateSpec ext = StateSpec
  { _csAllocs        :: Map AllocIndex (AllocSpec ext)
    -- ^ allocated or declared pointers
  , _csPointsTos     :: [PointsTo ext]
    -- ^ points-to statements
  , _csConditions    :: [SetupCondition ext]
    -- ^ equality, propositions, and ghost-variable conditions
  , _csFreshVars     :: [TypedExtCns]
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

ppMethodSpec ::
  ( PP.Pretty (MethodId ext)
  , PP.Pretty (ExtType ext)
  ) =>
  CrucibleMethodSpecIR ext ->
  PP.Doc ann
ppMethodSpec methodSpec =
  PP.vcat
  [ PP.pretty "Name: " <> PP.pretty (methodSpec ^. csMethod)
  , PP.pretty "Location: " <> prettyPosition (plSourceLoc (methodSpec ^. csLoc))
  , PP.pretty "Argument types: "
  , bullets '-' (map PP.pretty (methodSpec ^. csArgs))
  , PP.pretty "Return type: " <> case methodSpec ^. csRet of
                                       Nothing  -> PP.pretty "<void>"
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
