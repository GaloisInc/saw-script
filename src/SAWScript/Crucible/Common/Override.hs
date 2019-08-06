{- |
Module      : SAWScript.Crucible.Common.Override
Description : Language-neutral overrides
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Crucible.Common.Override
  ( Pointer
  , OverrideState(..)
  , osAsserts
  , osArgAsserts
  , osAssumes
  , osFree
  , osLocation
  , overrideGlobals
  , syminterface
  , setupValueSub
  , termSub
  --
  , OverrideFailureReason(..)
  , ppOverrideFailureReason
  , OverrideFailure(..)
  , ppOverrideFailure
  --
  , OverrideMatcher(..)
  , runOverrideMatcher
  , RO
  , RW
  , addAssert
  , addAssume
  , readGlobal
  , writeGlobal
  , failure
  , getSymInterface
  --
  , assignmentToList
  ) where

import qualified Control.Exception as X
import           Control.Lens
import           Control.Monad.Trans.State hiding (get, put)
import           Control.Monad.State.Class (MonadState(..))
import           Control.Monad.Error.Class (MonadError)
import           Control.Monad.Fail (MonadFail)
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class
import           Control.Monad.IO.Class
import           Data.Kind (Type)
import           Data.Map (Map)
import           Data.Set (Set)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic, Generic1)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some)
import           Data.Parameterized.TraversableFC (toListFC)

import           Verifier.SAW.SharedTerm as SAWVerifier
import           Verifier.SAW.TypedTerm as SAWVerifier

import qualified Lang.Crucible.CFG.Core as Crucible (TypeRepr, GlobalVar)
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.ProgramLoc as W4

import           SAWScript.Crucible.Common (Sym)
import           SAWScript.Crucible.Common.MethodSpec as MS

--------------------------------------------------------------------------------
-- ** OverrideState

type LabeledPred sym = W4.LabeledPred (W4.Pred sym) Crucible.SimError

type family Pointer ext :: Type

data OverrideState ext = OverrideState
  { -- | Substitution for memory allocations
    _setupValueSub :: Map AllocIndex (Pointer ext)

    -- | Substitution for SAW Core external constants
  , _termSub :: Map VarIndex Term

    -- | Free variables available for unification
  , _osFree :: Set VarIndex

    -- | Accumulated assertions
  , _osAsserts :: [LabeledPred Sym]

    -- | Assertions about the values of function arguments
    --
    -- These come from @crucible_execute_func@.
  , _osArgAsserts :: [[LabeledPred Sym]]

    -- | Accumulated assumptions
  , _osAssumes :: [W4.Pred Sym]

    -- | Symbolic simulation state
  , _syminterface :: Sym

    -- | Global variables
  , _overrideGlobals :: Crucible.SymGlobalState Sym

    -- | Source location to associated with this override
  , _osLocation :: W4.ProgramLoc
  }

makeLenses ''OverrideState

-- | The initial override matching state starts with an empty substitution
-- and no assertions or assumptions.
initialState ::
  Sym                           {- ^ simulator                      -} ->
  Crucible.SymGlobalState Sym   {- ^ initial global variables       -} ->
  Map AllocIndex (Pointer ext) {- ^ initial allocation substituion -} ->
  Map VarIndex Term             {- ^ initial term substituion       -} ->
  Set VarIndex                  {- ^ initial free terms             -} ->
  W4.ProgramLoc                 {- ^ location information for the override -} ->
  OverrideState ext
initialState sym globals allocs terms free loc = OverrideState
  { _osAsserts       = []
  , _osArgAsserts    = []
  , _osAssumes       = []
  , _syminterface    = sym
  , _overrideGlobals = globals
  , _termSub         = terms
  , _osFree          = free
  , _setupValueSub   = allocs
  , _osLocation      = loc
  }

--------------------------------------------------------------------------------
-- ** OverrideFailureReason

data OverrideFailureReason ext
  = AmbiguousPointsTos [MS.PointsTo ext]
  | AmbiguousVars [TypedTerm]
  | BadTermMatch Term Term -- ^ simulated and specified terms did not match
  | BadPointerCast -- ^ Pointer required to process points-to
  | BadReturnSpecification (Some Crucible.TypeRepr)
    -- ^ type mismatch in return specification
  | NonlinearPatternNotSupported
  | BadEqualityComparison -- ^ Comparison on an undef value
  | BadPointerLoad (Either (MS.PointsTo ext) PP.Doc) PP.Doc
    -- ^ @loadRaw@ failed due to type error
  | StructuralMismatch PP.Doc PP.Doc (Maybe (ExtType ext)) (ExtType ext)
    -- ^
    -- * pretty-printed simulated value
    -- * pretty-printed specified value
    -- * type of specified value
    -- * type of simulated value

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         ) => PP.Pretty (OverrideFailureReason ext) where
  pretty = ppOverrideFailureReason

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         ) => Show (OverrideFailureReason ext) where
  show = show . PP.pretty

ppOverrideFailureReason ::
  ( PP.Pretty (ExtType ext)
  , PP.Pretty (MS.PointsTo ext)
  ) => OverrideFailureReason ext -> PP.Doc
ppOverrideFailureReason rsn = case rsn of
  AmbiguousPointsTos pts ->
    PP.text "ambiguous collection of points-to assertions" PP.<$$>
    (PP.indent 2 $ PP.vcat (map PP.pretty pts))
  AmbiguousVars vs ->
    PP.text "ambiguous collection of variables" PP.<$$>
    (PP.indent 2 $ PP.vcat (map MS.ppTypedTerm vs))
  BadTermMatch x y ->
    PP.text "terms do not match" PP.<$$>
    (PP.indent 2 (ppTerm defaultPPOpts x)) PP.<$$>
    (PP.indent 2 (ppTerm defaultPPOpts y))
  BadPointerCast ->
    PP.text "bad pointer cast"
  BadReturnSpecification ty -> PP.vcat $ map PP.text $
    [ "Spec had no return value, but the function returns a value of type:"
    , show ty
    ]
  NonlinearPatternNotSupported ->
    PP.text "nonlinear pattern not supported"
  BadEqualityComparison ->
    PP.text "value containing `undef` compared for equality"
  BadPointerLoad pointsTo msg ->
    PP.text "error when loading through pointer that" PP.<+>
    PP.text "appeared in the override's points-to precondition(s):" PP.<$$>
    PP.text "Precondition:" PP.<$$>
      PP.indent 2 (either PP.pretty id pointsTo) PP.<$$>
    PP.text "Failure reason: " PP.<$$> PP.indent 2 msg -- this can be long
  StructuralMismatch simVal setupVal setupValTy ty ->
    PP.text "could not match specified value with actual value:" PP.<$$>
    PP.vcat (map (PP.indent 2) $
              [ PP.text "actual (simulator) value:" PP.<+> simVal
              , PP.text "specified value:         " PP.<+> setupVal
              , PP.text "type of actual value:   " PP.<+> PP.pretty ty
              ] ++ let msg ty_ =
                         [PP.text "type of specified value:"
                          PP.<+> PP.pretty ty_]
                   in maybe [] msg setupValTy)

--------------------------------------------------------------------------------
-- ** OverrideFailure

data OverrideFailure ext = OF W4.ProgramLoc (OverrideFailureReason ext)

ppOverrideFailure :: ( PP.Pretty (ExtType ext)
                     , PP.Pretty (MS.PointsTo ext)
                     ) => OverrideFailure ext -> PP.Doc
ppOverrideFailure (OF loc rsn) =
  PP.text "at" PP.<+> PP.pretty (W4.plSourceLoc loc) PP.<$$>
  ppOverrideFailureReason rsn

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         ) => PP.Pretty (OverrideFailure ext) where
  pretty = ppOverrideFailure

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         ) => Show (OverrideFailure ext) where
  show = show . PP.pretty

instance ( PP.Pretty (ExtType ext)
         , PP.Pretty (MS.PointsTo ext)
         , Typeable ext 
         ) => X.Exception (OverrideFailure ext)

--------------------------------------------------------------------------------
-- ** OverrideMatcher

data RO
data RW

-- | The 'OverrideMatcher' type provides the operations that are needed
-- to match a specification's arguments with the arguments provided by
-- the Crucible simulation in order to compute the variable substitution
-- and side-conditions needed to proceed.
newtype OverrideMatcher ext rorw a =
  OM (StateT (OverrideState ext) (ExceptT (OverrideFailure ext) IO) a)
  deriving (Applicative, Functor, Generic, Generic1, Monad, MonadIO, MonadFail)

instance Wrapped (OverrideMatcher ext rorw a) where

deriving instance MonadState (OverrideState ext) (OverrideMatcher ext rorw)
deriving instance MonadError (OverrideFailure ext) (OverrideMatcher ext rorw)

-- | "Run" function for OverrideMatcher. The final result and state
-- are returned. The state will contain the updated globals and substitutions
runOverrideMatcher ::
   Sym                         {- ^ simulator                       -} ->
   Crucible.SymGlobalState Sym {- ^ initial global variables        -} ->
   Map AllocIndex (Pointer ext) {- ^ initial allocation substitution -} ->
   Map VarIndex Term           {- ^ initial term substitution       -} ->
   Set VarIndex                {- ^ initial free variables          -} ->
   W4.ProgramLoc               {- ^ override location information   -} ->
   OverrideMatcher ext md a   {- ^ matching action                 -} ->
   IO (Either (OverrideFailure ext) (a, OverrideState ext))
runOverrideMatcher sym g a t free loc (OM m) =
  runExceptT (runStateT m (initialState sym g a t free loc))

addAssert ::
  W4.Pred Sym       {- ^ property -} ->
  Crucible.SimError {- ^ reason   -} ->
  OverrideMatcher ext rorw ()
addAssert p r =
  OM (osAsserts %= cons (W4.LabeledPred p r))

addAssume ::
  W4.Pred Sym       {- ^ property -} ->
  OverrideMatcher ext rorw ()
addAssume p = OM (osAssumes %= cons p)

readGlobal ::
  Crucible.GlobalVar tp ->
  OverrideMatcher ext rorw (Crucible.RegValue Sym tp)
readGlobal k =
  do mb <- OM (uses overrideGlobals (Crucible.lookupGlobal k))
     case mb of
       Nothing -> fail ("No such global: " ++ show k)
       Just v  -> return v

writeGlobal ::
  Crucible.GlobalVar    tp ->
  Crucible.RegValue Sym tp ->
  OverrideMatcher ext RW ()
writeGlobal k v = OM (overrideGlobals %= Crucible.insertGlobal k v)

-- | Abort the current computation by raising the given 'OverrideFailure'
-- exception.
failure ::
  W4.ProgramLoc ->
  OverrideFailureReason ext ->
  OverrideMatcher ext md a
failure loc e = OM (lift (throwE (OF loc e)))

getSymInterface :: OverrideMatcher ext md Sym
getSymInterface = OM (use syminterface)

------------------------------------------------------------------------

-- | Forget the type indexes and length of the arguments.
assignmentToList ::
  Ctx.Assignment (Crucible.RegEntry sym) ctx ->
  [Crucible.AnyValue sym]
assignmentToList = toListFC (\(Crucible.RegEntry x y) -> Crucible.AnyValue x y)
