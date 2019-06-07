{-# LANGUAGE DataKinds #-}
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

{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Crucible.Common.MethodSpec where

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Void (Void(..), absurd)
import           Control.Monad.ST (RealWorld)
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans (lift)
import           Control.Lens

import           Data.IORef
import           Data.Monoid ((<>))
import           Data.Type.Equality (TestEquality(..), (:~:)(..))

-- what4
import qualified What4.Expr.Builder as B
import           What4.ProgramLoc (ProgramLoc)

import           Data.Parameterized.NatRepr (NatRepr(..))
import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx)
import qualified Lang.Crucible.CFG.Common as Crucible (GlobalVar)
import qualified Lang.Crucible.Backend.SAWCore as Crucible
  (SAWCoreBackend, saw_ctx, toSC)
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
  (IntrinsicClass(Intrinsic, muxIntrinsic){-, IntrinsicMuxFn(IntrinsicMuxFn)-})

-- Language extension tags
import           Lang.Crucible.LLVM.Extension (LLVM(..), X86)
import           Lang.Crucible.JVM.Types (JVM)

import           Verifier.SAW.TypedTerm as SAWVerifier
import           Verifier.SAW.SharedTerm as SAWVerifier

import           SAWScript.Options

import SAWScript.Crucible.Common


--------------------------------------------------------------------------------

-- | A singleton type representing a language extension
--
-- While Crucible supports extensibly adding and simulating new languages, we can
-- exhaustively enumerate all the languages SAW supports verifying.
data ExtRepr ext where
  ExtJVM :: ExtRepr JVM
  ExtLLVM :: NatRepr n -> ExtRepr (LLVM (X86 n))

instance TestEquality ExtRepr where
  testEquality (ExtLLVM n) (ExtLLVM m) =
    case testEquality n m of
      Just Refl -> Just Refl
      Nothing -> Nothing
  testEquality ExtJVM ExtJVM = Just Refl
  testEquality _ _ = Nothing

--------------------------------------------------------------------------------

 -- The following type families describe what SetupValues are legal for which
 -- languages.

type family HasSetupStruct ext where
  HasSetupStruct (LLVM arch) = ()
  HasSetupStruct JVM = Void

type family HasSetupArray ext where
  HasSetupArray (LLVM arch) = ()
  HasSetupArray JVM = Void

type family HasSetupElem ext where
  HasSetupElem (LLVM arch) = ()
  HasSetupElem JVM = Void

type family HasSetupField ext where
  HasSetupField (LLVM arch) = ()
  HasSetupField JVM = Void

type family HasSetupGlobalInitializer ext where
  HasSetupGlobalInitializer (LLVM arch) = ()
  HasSetupGlobalInitializer JVM = Void

-- | From the manual: \"The SetupValue type corresponds to values that can occur
-- during symbolic execution, which includes both 'Term' values, pointers, and
-- composite types consisting of either of these (both structures and arrays).\"
data SetupValue ext where
  SetupVar    :: AllocIndex -> SetupValue ext
  SetupTerm   :: TypedTerm -> SetupValue ext
  SetupNull   :: SetupValue ext
  -- | If the 'Bool' is 'True', it's a (LLVM) packed struct
  SetupStruct :: HasSetupStruct ext -> Bool -> [SetupValue ext] -> SetupValue ext
  SetupArray  :: HasSetupArray ext -> [SetupValue ext] -> SetupValue ext
  SetupElem   :: HasSetupElem ext -> SetupValue ext -> Int -> SetupValue ext
  SetupField  :: HasSetupField ext -> SetupValue ext -> String -> SetupValue ext
  -- | A pointer to a global variable
  SetupGlobal :: String -> SetupValue ext
  -- | This represents the value of a global's initializer.
  SetupGlobalInitializer :: HasSetupGlobalInitializer ext -> String -> SetupValue ext

deriving instance ( Show (HasSetupStruct ext)
                  , Show (HasSetupArray ext)
                  , Show (HasSetupElem ext)
                  , Show (HasSetupField ext)
                  , Show (HasSetupGlobalInitializer ext)
                  ) => Show (SetupValue ext)

-- TypedTerm is neither Eq nor Ord

-- deriving instance ( Eq (HasSetupStruct ext)
--                   , Eq (HasSetupArray ext)
--                   , Eq (HasSetupElem ext)
--                   , Eq (HasSetupField ext)
--                   , Eq (HasSetupGlobalInitializer ext)
--                   ) => Eq (SetupValue ext)

-- deriving instance ( Ord (HasSetupStruct ext)
--                   , Ord (HasSetupArray ext)
--                   , Ord (HasSetupElem ext)
--                   , Ord (HasSetupField ext)
--                   , Ord (HasSetupGlobalInitializer ext)
--                   ) => Ord (SetupValue ext)

setupToTypedTerm ::
  ExtRepr ext {-^ Which language/syntax extension are we using? -} ->
  Options {-^ Printing options -} ->
  SharedContext ->
  SetupValue ext ->
  MaybeT IO TypedTerm
setupToTypedTerm ext opts sc sv =
  case sv of
    SetupTerm term -> return term
    _ -> do t <- setupToTerm ext opts sc sv
            lift $ mkTypedTerm sc t

-- | Convert a setup value to a SAW-Core term. This is a partial
-- function, as certain setup values ---SetupVar, SetupNull and
-- SetupGlobal--- don't have semantics outside of the symbolic
-- simulator.
setupToTerm ::
  ExtRepr ext {-^ Which language/syntax extension are we using? -} ->
  Options ->
  SharedContext ->
  SetupValue ext ->
  MaybeT IO Term
setupToTerm ext opts sc sv =
  case (ext, sv) of
    (_, SetupTerm term) -> return (ttTerm term)

    -- LLVM-specific cases
    (ExtLLVM _ptrWidth, SetupStruct () _ fields) ->
      do ts <- mapM (setupToTerm ext opts sc) fields
         lift $ scTuple sc ts

    (ExtLLVM _ptrWidth, SetupArray () elems@(_:_)) ->
      do ts@(t:_) <- mapM (setupToTerm ext opts sc) elems
         typt <- lift $ scTypeOf sc t
         vec <- lift $ scVector sc typt ts
         typ <- lift $ scTypeOf sc vec
         lift $ printOutLn opts Info $ show vec
         lift $ printOutLn opts Info $ show typ
         return vec

    (ExtLLVM _ptrWidth, SetupElem () base ind) ->
      case base of
        SetupArray () elems@(e:_) ->
          do let intToNat = fromInteger . toInteger
             art <- setupToTerm ext opts sc base
             ixt <- lift $ scNat sc $ intToNat ind
             lent <- lift $ scNat sc $ intToNat $ length elems
             et <- setupToTerm ext opts sc e
             typ <- lift $ scTypeOf sc et
             lift $ scAt sc lent typ art ixt

        SetupStruct () _ fs ->
          do st <- setupToTerm ext opts sc base
             lift $ scTupleSelector sc st ind (length fs)

        _ -> MaybeT $ return Nothing

    -- SetupVar, SetupNull, SetupGlobal
    _ -> MaybeT $ return Nothing

--------------------------------------------------------------------------------

{-
setupToTypedTerm :: Options -> SharedContext -> SetupValue -> MaybeT IO TypedTerm
setupToTypedTerm opts sc sv =
  case sv of
    SetupTerm term -> return term
    _ -> do t <- setupToTerm opts sc sv
            lift $ mkTypedTerm sc t

-- | Convert a setup value to a SAW-Core term. This is a partial
-- function, as certain setup values ---SetupVar, SetupNull and
-- SetupGlobal--- don't have semantics outside of the symbolic
-- simulator.
setupToTerm :: Options -> SharedContext -> SetupValue -> MaybeT IO Term
setupToTerm _opts _sc sv =
  case sv of
    SetupTerm term -> return (ttTerm term)
    _ -> MaybeT $ return Nothing


data SetupCondition where
  SetupCond_Equal :: ProgramLoc -> SetupValue -> SetupValue -> SetupCondition
  SetupCond_Pred :: ProgramLoc -> TypedTerm -> SetupCondition
  deriving (Show)

data PointsTo
  = PointsToField ProgramLoc SetupValue String SetupValue
  | PointsToElem ProgramLoc SetupValue Int SetupValue
  deriving (Show)

-- | Verification state (either pre- or post-) specification
data StateSpec' t = StateSpec
  { _csAllocs        :: Map AllocIndex t
    -- ^ allocated pointers
  , _csPointsTos     :: [PointsTo]
    -- ^ points-to statements
  , _csConditions    :: [SetupCondition]
    -- ^ equalities and propositions
  , _csFreshVars     :: [TypedTerm]
    -- ^ fresh variables created in this state
  , _csVarTypeNames  :: Map AllocIndex JIdent
    -- ^ names for types of variables, for diagnostics
  }
  deriving (Show)

type StateSpec = StateSpec' (ProgramLoc, Allocation)

data CrucibleMethodSpecIR' t =
  CrucibleMethodSpec
  { _csClassName       :: J.ClassName
  , _csMethodName      :: String
  , _csArgs            :: [t]
  , _csRet             :: Maybe t
  , _csPreState        :: StateSpec -- ^ state before the function runs
  , _csPostState       :: StateSpec -- ^ state after the function runs
  , _csArgBindings     :: Map Integer (t, SetupValue) -- ^ function arguments
  , _csRetValue        :: Maybe SetupValue            -- ^ function return value
  , _csSolverStats     :: SolverStats                 -- ^ statistics about the proof that produced this
  , _csLoc             :: ProgramLoc
  }
  deriving (Show)
-}
