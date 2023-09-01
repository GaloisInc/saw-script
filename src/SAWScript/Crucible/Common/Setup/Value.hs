{- |
Module      : SAWScript.Crucible.Common.Setup.Value
Description : Language-neutral method specifications
License     : BSD3
Maintainer  : langston
Stability   : provisional

This module uses GADTs & type families to distinguish syntax-extension- (source
language-) specific code. This technique is described in the paper \"Trees That
Grow\", and is prevalent across the Crucible codebase.

The module exists separately from "SAWScript.Crucible.Common.MethodSpecIR"
primarily to avoid import cycles. You probably want to import
"SAWScript.Crucible.Common.MethodSpecIR" (which re-exports everything from this
module, plus additional functionality) instead.
-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Crucible.Common.Setup.Value
  ( AllocIndex(..)
  , nextAllocIndex

  , CrucibleContext
  , AllocSpec
  , TypeName
  , ExtType
  , CastType
  , PointsTo
  , AllocGlobal
  , ResolvedState

  , BoolToType
  , B

  , HasSetupNull
  , HasSetupStruct
  , HasSetupArray
  , HasSetupElem
  , HasSetupField
  , HasSetupGlobal
  , HasSetupCast
  , HasSetupUnion
  , HasSetupGlobalInitializer

  , SetupValue(..)
  , SetupValueHas

  , HasGhostState

  , ConditionMetadata(..)

  , MethodId
  , Codebase

  , Pointer'
  ) where

import           Data.Constraint (Constraint)
import           Data.Kind (Type)
import           Data.Set (Set)
import           Data.Void (Void)

import           What4.ProgramLoc (ProgramLoc)

import           Verifier.SAW.TypedTerm

-- | How many allocations have we made in this method spec?
newtype AllocIndex = AllocIndex Int
  deriving (Eq, Ord, Show)

nextAllocIndex :: AllocIndex -> AllocIndex
nextAllocIndex (AllocIndex n) = AllocIndex (n + 1)

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

--------------------------------------------------------------------------------
-- ** Ghost state

-- TODO: This is language-independent, it should be always-true rather than a
-- toggle.

-- TODO: documentation

type family HasGhostState ext :: Bool

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
-- *** Method specs

-- | How to identify methods in a codebase
type family MethodId ext :: Type

-- | A body of code in which a method resides
--
-- Examples: An 'LLVMModule', a Java 'Codebase'
type family Codebase ext :: Type

--------------------------------------------------------------------------------
-- *** Pointers

type family Pointer' ext sym :: Type
