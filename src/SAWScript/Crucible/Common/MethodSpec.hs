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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Crucible.Common.MethodSpec where

import           Data.Constraint (Constraint)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import           Data.Time.Clock
import           Data.Void (Void)

import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans (lift)
import           Control.Lens
import           Data.Kind (Type)
import qualified Prettyprinter as PP

import           Data.Parameterized.Nonce

-- what4
import           What4.ProgramLoc (ProgramLoc(plSourceLoc), Position)

import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx)
import qualified Lang.Crucible.CFG.Common as Crucible (GlobalVar)

import qualified Cryptol.Utils.PP as Cryptol

import           Verifier.SAW.TypedTerm as SAWVerifier
import           Verifier.SAW.SharedTerm as SAWVerifier

import           SAWScript.Options
import           SAWScript.Prover.SolverStats
import           SAWScript.Utils (bullets)
import           SAWScript.Proof (TheoremNonce, TheoremSummary)

-- | How many allocations have we made in this method spec?
newtype AllocIndex = AllocIndex Int
  deriving (Eq, Ord, Show)

nextAllocIndex :: AllocIndex -> AllocIndex
nextAllocIndex (AllocIndex n) = AllocIndex (n + 1)

-- | Are we writing preconditions or postconditions?
data PrePost
  = PreState | PostState
  deriving (Eq, Ord, Show)

stateCond :: PrePost -> String
stateCond PreState = "precondition"
stateCond PostState = "postcondition"

--------------------------------------------------------------------------------
-- *** Extension-specific information

type family CrucibleContext ext :: Type

-- | How to specify allocations in this syntax extension
type family AllocSpec ext :: Type

-- | The type of identifiers for types in this syntax extension
type family TypeName ext :: Type

-- | The type of types of the syntax extension we're dealing with
type family ExtType ext :: Type

-- | The types that can appear in casts
type family CastType ext :: Type

-- | The type of points-to assertions
type family PointsTo ext :: Type

-- | The type of global allocations
type family AllocGlobal ext :: Type

-- | The type of \"resolved\" state
type family ResolvedState ext :: Type

--------------------------------------------------------------------------------
-- ** SetupValue

-- | An injective type family mapping type-level booleans to types
type family BoolToType (b :: Bool) = (t :: Type) | t -> b where
  BoolToType 'True  = ()
  BoolToType 'False = Void

type B b = BoolToType b

 -- The following type families describe what SetupValues are legal for which
 -- languages.
type family HasSetupNull ext :: Bool
type family HasSetupStruct ext :: Bool
type family HasSetupArray ext :: Bool
type family HasSetupElem ext :: Bool
type family HasSetupField ext :: Bool
type family HasSetupGlobal ext :: Bool
type family HasSetupCast ext :: Bool
type family HasSetupUnion ext :: Bool
type family HasSetupGlobalInitializer ext :: Bool

-- | From the manual: \"The SetupValue type corresponds to values that can occur
-- during symbolic execution, which includes both 'Term' values, pointers, and
-- composite types consisting of either of these (both structures and arrays).\"
data SetupValue ext where
  SetupVar    :: AllocIndex -> SetupValue ext
  SetupTerm   :: TypedTerm -> SetupValue ext
  SetupNull   :: B (HasSetupNull ext) -> SetupValue ext
  -- | If the 'Bool' is 'True', it's a (LLVM) packed struct
  SetupStruct :: B (HasSetupStruct ext) -> Bool -> [SetupValue ext] -> SetupValue ext
  SetupArray  :: B (HasSetupArray ext) -> [SetupValue ext] -> SetupValue ext
  SetupElem   :: B (HasSetupElem ext) -> SetupValue ext -> Int -> SetupValue ext
  SetupField  :: B (HasSetupField ext) -> SetupValue ext -> String -> SetupValue ext
  SetupCast   :: B (HasSetupCast ext) -> SetupValue ext -> CastType ext -> SetupValue ext
  SetupUnion  :: B (HasSetupUnion ext) -> SetupValue ext -> String -> SetupValue ext

  -- | A pointer to a global variable
  SetupGlobal :: B (HasSetupGlobal ext) -> String -> SetupValue ext
  -- | This represents the value of a global's initializer.
  SetupGlobalInitializer ::
    B (HasSetupGlobalInitializer ext) -> String -> SetupValue ext

-- | This constraint can be solved for any ext so long as '()' and 'Void' have
--   the constraint. Unfortunately, GHC can't (yet?) reason over the equations
--   in our closed type family, and realize that
type SetupValueHas (c :: Type -> Constraint) ext =
  ( c (B (HasSetupNull ext))
  , c (B (HasSetupStruct ext))
  , c (B (HasSetupArray ext))
  , c (B (HasSetupElem ext))
  , c (B (HasSetupField ext))
  , c (B (HasSetupCast ext))
  , c (B (HasSetupUnion ext))
  , c (B (HasSetupGlobal ext))
  , c (B (HasSetupGlobalInitializer ext))
  , c (CastType ext)
  )

deriving instance (SetupValueHas Show ext) => Show (SetupValue ext)

-- TypedTerm is neither Eq nor Ord
-- deriving instance (SetupValueHas Eq ext) => Eq (SetupValue ext)
-- deriving instance (SetupValueHas Ord ext) => Ord (SetupValue ext)

-- | Note that most 'SetupValue' concepts (like allocation indices)
--   are implementation details and won't be familiar to users.
--   Consider using 'resolveSetupValue' and printing an 'LLVMVal'
--   with @PP.pretty@ instead.
ppSetupValue :: Show (CastType ext) => SetupValue ext -> PP.Doc ann
ppSetupValue setupval = case setupval of
  SetupTerm tm   -> ppTypedTerm tm
  SetupVar i     -> ppAllocIndex i
  SetupNull _    -> PP.pretty "NULL"
  SetupStruct _ packed vs
    | packed     -> PP.angles (PP.braces (commaList (map ppSetupValue vs)))
    | otherwise  -> PP.braces (commaList (map ppSetupValue vs))
  SetupArray _ vs  -> PP.brackets (commaList (map ppSetupValue vs))
  SetupElem _ v i  -> PP.parens (ppSetupValue v) PP.<> PP.pretty ("." ++ show i)
  SetupField _ v f -> PP.parens (ppSetupValue v) PP.<> PP.pretty ("." ++ f)
  SetupUnion _ v u -> PP.parens (ppSetupValue v) PP.<> PP.pretty ("." ++ u)
  SetupCast _ v tp -> PP.parens (ppSetupValue v) PP.<> PP.pretty (" AS " ++ show tp)
  SetupGlobal _ nm -> PP.pretty ("global(" ++ nm ++ ")")
  SetupGlobalInitializer _ nm -> PP.pretty ("global_initializer(" ++ nm ++ ")")
  where
    commaList :: [PP.Doc ann] -> PP.Doc ann
    commaList []     = PP.emptyDoc
    commaList (x:xs) = x PP.<> PP.hcat (map (\y -> PP.comma PP.<+> y) xs)

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

    SetupStruct _ _ fields ->
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

        SetupStruct _ _ fs ->
          do st <- setupToTerm opts sc base
             lift $ scTupleSelector sc st ind (length fs)

        _ -> MaybeT $ return Nothing

    -- SetupVar, SetupNull, SetupGlobal
    _ -> MaybeT $ return Nothing

--------------------------------------------------------------------------------
-- ** Ghost state

-- TODO: This is language-independent, it should be always-true rather than a
-- toggle.

-- TODO: documentation

type family HasGhostState ext :: Bool

type GhostValue  = "GhostValue"
type GhostType   = Crucible.IntrinsicType GhostValue Crucible.EmptyCtx
type GhostGlobal = Crucible.GlobalVar GhostType

--------------------------------------------------------------------------------
-- ** Pre- and post-conditions

data ConditionMetadata =
  ConditionMetadata
  { conditionLoc  :: ProgramLoc
  , conditionTags :: Set String
  , conditionType :: String
  , conditionContext :: String
  }
 deriving (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- *** StateSpec

data SetupCondition ext where
  SetupCond_Equal    :: ConditionMetadata -> SetupValue ext -> SetupValue ext -> SetupCondition ext
  SetupCond_Pred     :: ConditionMetadata -> TypedTerm -> SetupCondition ext
  SetupCond_Ghost    :: B (HasGhostState ext) ->
                        ConditionMetadata ->
                        GhostGlobal ->
                        TypedTerm ->
                        SetupCondition ext

deriving instance ( SetupValueHas Show ext
                  , Show (B (HasGhostState ext))
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

-- | How to identify methods in a codebase
type family MethodId ext :: Type

-- | A body of code in which a method resides
--
-- Examples: An 'LLVMModule', a Java 'Codebase'
type family Codebase ext :: Type

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
