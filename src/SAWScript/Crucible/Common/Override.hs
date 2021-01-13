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
  , Pointer'
  , OverrideState
  , OverrideState'(..)
  , osAsserts
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
  , OverrideMatcher
  , OverrideMatcher'(..)
  , throwOverrideMatcher
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
import           Control.Monad.Catch (MonadThrow)
import qualified Control.Monad.Fail as Fail
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class
import           Control.Monad.IO.Class
import           Data.Kind (Type)
import           Data.Map (Map)
import           Data.Set (Set)
import           Data.Typeable (Typeable)
import           Data.Void
import           GHC.Generics (Generic, Generic1)
import qualified Prettyprinter as PP

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

import           SAWScript.Exceptions
import           SAWScript.Crucible.Common (Sym)
import           SAWScript.Crucible.Common.MethodSpec as MS

--------------------------------------------------------------------------------
-- ** OverrideState

type LabeledPred sym = W4.LabeledPred (W4.Pred sym) Crucible.SimError

type family Pointer' ext sym :: Type

type Pointer ext = Pointer' ext Sym

data OverrideState' sym ext = OverrideState
  { -- | Substitution for memory allocations
    _setupValueSub :: Map AllocIndex (Pointer' ext sym)

    -- | Substitution for SAW Core external constants
  , _termSub :: Map VarIndex Term

    -- | Free variables available for unification
  , _osFree :: Set VarIndex

    -- | Accumulated assertions
  , _osAsserts :: [LabeledPred sym]

    -- | Accumulated assumptions
  , _osAssumes :: [W4.Pred sym]

    -- | Symbolic simulation state
  , _syminterface :: sym

    -- | Global variables
  , _overrideGlobals :: Crucible.SymGlobalState sym

    -- | Source location to associated with this override
  , _osLocation :: W4.ProgramLoc
  }

type OverrideState = OverrideState' Sym

makeLenses ''OverrideState'

-- | The initial override matching state starts with an empty substitution
-- and no assertions or assumptions.
initialState ::
  sym                           {- ^ simulator                      -} ->
  Crucible.SymGlobalState sym   {- ^ initial global variables       -} ->
  Map AllocIndex (Pointer' ext sym) {- ^ initial allocation substituion -} ->
  Map VarIndex Term             {- ^ initial term substituion       -} ->
  Set VarIndex                  {- ^ initial free terms             -} ->
  W4.ProgramLoc                 {- ^ location information for the override -} ->
  OverrideState' sym ext
initialState sym globals allocs terms free loc = OverrideState
  { _osAsserts       = []
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
  | AmbiguousVars [TypedExtCns]
  | BadTermMatch Term Term -- ^ simulated and specified terms did not match
  | BadPointerCast -- ^ Pointer required to process points-to
  | BadReturnSpecification (Some Crucible.TypeRepr)
    -- ^ type mismatch in return specification
  | NonlinearPatternNotSupported
  | BadEqualityComparison -- ^ Comparison on an undef value
  | BadPointerLoad (Either (MS.PointsTo ext) (PP.Doc Void)) (PP.Doc Void)
    -- ^ @loadRaw@ failed due to type error
  | StructuralMismatch (PP.Doc Void) (PP.Doc Void) (Maybe (ExtType ext)) (ExtType ext)
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
  ) => OverrideFailureReason ext -> PP.Doc ann
ppOverrideFailureReason rsn = case rsn of
  AmbiguousPointsTos pts ->
    PP.vcat
    [ PP.pretty "LHS of points-to assertion(s) not reachable via points-tos from inputs/outputs:"
    , PP.indent 2 $ PP.vcat (map PP.pretty pts)
    ]
  AmbiguousVars vs ->
    PP.vcat
    [ PP.pretty "Fresh variable(s) not reachable via points-tos from function inputs/outputs:"
    , PP.indent 2 $ PP.vcat (map MS.ppTypedExtCns vs)
    ]
  BadTermMatch x y ->
    PP.vcat
    [ PP.pretty "terms do not match"
    , PP.indent 2 (PP.unAnnotate (ppTerm defaultPPOpts x))
    , PP.indent 2 (PP.unAnnotate (ppTerm defaultPPOpts y))
    ]
  BadPointerCast ->
    PP.pretty "bad pointer cast"
  BadReturnSpecification ty ->
    PP.vcat
    [ PP.pretty "Spec had no return value, but the function returns a value of type:"
    , PP.viaShow ty
    ]
  NonlinearPatternNotSupported ->
    PP.pretty "nonlinear pattern not supported"
  BadEqualityComparison ->
    PP.pretty "value containing `undef` compared for equality"
  BadPointerLoad pointsTo msg ->
    PP.vcat
    [ PP.pretty "error when loading through pointer that" PP.<+>
      PP.pretty "appeared in the override's points-to precondition(s):"
    , PP.pretty "Precondition:"
    , PP.indent 2 (either PP.pretty PP.unAnnotate pointsTo)
    , PP.pretty "Failure reason: "
    , PP.indent 2 (PP.unAnnotate msg) -- this can be long
    ]
  StructuralMismatch simVal setupVal setupValTy ty ->
    PP.vcat
    [ PP.pretty "could not match specified value with actual value:"
    , PP.vcat (map (PP.indent 2) $
              [ PP.pretty "actual (simulator) value:" PP.<+> PP.unAnnotate simVal
              , PP.pretty "specified value:         " PP.<+> PP.unAnnotate setupVal
              , PP.pretty "type of actual value:   " PP.<+> PP.pretty ty
              ] ++ let msg ty_ =
                         [PP.pretty "type of specified value:"
                          PP.<+> PP.pretty ty_]
                   in maybe [] msg setupValTy)
    ]

--------------------------------------------------------------------------------
-- ** OverrideFailure

data OverrideFailure ext = OF W4.ProgramLoc (OverrideFailureReason ext)

ppOverrideFailure :: ( PP.Pretty (ExtType ext)
                     , PP.Pretty (MS.PointsTo ext)
                     ) => OverrideFailure ext -> PP.Doc ann
ppOverrideFailure (OF loc rsn) =
  PP.vcat
  [ PP.pretty "at" PP.<+> PP.viaShow (W4.plSourceLoc loc) -- TODO: fix when what4 switches to prettyprinter
  , ppOverrideFailureReason rsn
  ]

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
newtype OverrideMatcher' sym ext rorw a =
  OM (StateT (OverrideState' sym ext) (ExceptT (OverrideFailure ext) IO) a)
  deriving (Applicative, Functor, Generic, Generic1, Monad, MonadIO, MonadThrow)

type OverrideMatcher = OverrideMatcher' Sym

instance Wrapped (OverrideMatcher' sym ext rorw a) where

deriving instance MonadState (OverrideState' sym ext) (OverrideMatcher' sym ext rorw)
deriving instance MonadError (OverrideFailure ext) (OverrideMatcher' sym ext rorw)

throwOverrideMatcher :: String -> OverrideMatcher' sym ext rorw a
throwOverrideMatcher msg = do
  loc <- use osLocation
  X.throw $ OverrideMatcherException loc msg

instance Fail.MonadFail (OverrideMatcher' sym ext rorw) where
  fail = throwOverrideMatcher

-- | "Run" function for OverrideMatcher. The final result and state
-- are returned. The state will contain the updated globals and substitutions
runOverrideMatcher ::
   sym                         {- ^ simulator                       -} ->
   Crucible.SymGlobalState sym {- ^ initial global variables        -} ->
   Map AllocIndex (Pointer' ext sym) {- ^ initial allocation substitution -} ->
   Map VarIndex Term           {- ^ initial term substitution       -} ->
   Set VarIndex                {- ^ initial free variables          -} ->
   W4.ProgramLoc               {- ^ override location information   -} ->
   OverrideMatcher' sym ext md a {- ^ matching action                 -} ->
   IO (Either (OverrideFailure ext) (a, OverrideState' sym ext))
runOverrideMatcher sym g a t free loc (OM m) =
  runExceptT (runStateT m (initialState sym g a t free loc))

addAssert ::
  W4.Pred sym       {- ^ property -} ->
  Crucible.SimError {- ^ reason   -} ->
  OverrideMatcher' sym ext rorw ()
addAssert p r =
  OM (osAsserts %= cons (W4.LabeledPred p r))

addAssume ::
  W4.Pred sym       {- ^ property -} ->
  OverrideMatcher' sym ext rorw ()
addAssume p = OM (osAssumes %= cons p)

readGlobal ::
  Crucible.GlobalVar tp ->
  OverrideMatcher' sym ext rorw (Crucible.RegValue sym tp)
readGlobal k =
  do mb <- OM (uses overrideGlobals (Crucible.lookupGlobal k))
     case mb of
       Nothing -> throwOverrideMatcher ("No such global: " ++ show k)
       Just v  -> return v

writeGlobal ::
  Crucible.GlobalVar    tp ->
  Crucible.RegValue sym tp ->
  OverrideMatcher' sym ext RW ()
writeGlobal k v = OM (overrideGlobals %= Crucible.insertGlobal k v)

-- | Abort the current computation by raising the given 'OverrideFailure'
-- exception.
failure ::
  W4.ProgramLoc ->
  OverrideFailureReason ext ->
  OverrideMatcher' sym ext md a
failure loc e = OM (lift (throwE (OF loc e)))

getSymInterface :: OverrideMatcher' sym ext md sym
getSymInterface = OM (use syminterface)

------------------------------------------------------------------------

-- | Forget the type indexes and length of the arguments.
assignmentToList ::
  Ctx.Assignment (Crucible.RegEntry sym) ctx ->
  [Crucible.AnyValue sym]
assignmentToList = toListFC (\(Crucible.RegEntry x y) -> Crucible.AnyValue x y)
