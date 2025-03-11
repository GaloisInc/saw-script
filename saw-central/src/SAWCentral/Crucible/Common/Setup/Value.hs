{- |
Module      : SAWCentral.Crucible.Common.Setup.Value
Description : Language-neutral method specifications
License     : BSD3
Maintainer  : langston
Stability   : provisional

This module uses GADTs & type families to distinguish syntax-extension- (source
language-) specific code. This technique is described in the paper \"Trees That
Grow\", and is prevalent across the Crucible codebase.

The module exists separately from "SAWCentral.Crucible.Common.MethodSpecIR"
primarily to avoid import cycles. You probably want to import
"SAWCentral.Crucible.Common.MethodSpecIR" (which re-exports everything from this
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

module SAWCentral.Crucible.Common.Setup.Value
  ( AllocIndex(..)
  , nextAllocIndex

  , CrucibleContext
  , AllocSpec
  , TypeName
  , ExtType
  , PointsTo
  , AllocGlobal
  , ResolvedState

  , XSetupNull
  , XSetupStruct
  , XSetupEnum
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

  , ConditionMetadata(..)

  , MethodId
  , Codebase

  , Pointer'
  ) where

import           Data.Constraint (Constraint)
import           Data.Kind (Type)
import           Data.Set (Set)

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

-- | The type of points-to assertions
type family PointsTo ext :: Type

-- | The type of global allocations
type family AllocGlobal ext :: Type

-- | The type of \"resolved\" state
type family ResolvedState ext :: Type

--------------------------------------------------------------------------------
-- ** SetupValue

-- The following type families are extension fields, which describe what
-- SetupValues are legal for which language backends. Instances for these type
-- families adhere to the following conventions:
--
-- - If a SetupValue constructor is used in a particular backend and there is
--   some data that is /only/ used by that backend, then the corresponding
--   extension field should have a @type instance@ that evaluates to the type of
--   that data. For instance, the @XSetupCast@ instance for @LLVM@ might
--   evaluate to an LLVM @Type@ to represent the type to cast to.
--
-- - If a SetupValue constructor is used in a particular backend but there is
--   no backend-specific information, then the corresponding extension field
--   should have a @type instance@ that evaluates to @()@.
--
-- - If a SetupValue constructor is not used in a particular backend, its
--   corresponding extension field should have a @type instance@ that evaluates
--   to Void. Any code that pattern matches on the constructor should then
--   dispatch on the Void value using the 'absurd' function.

type family XSetupNull ext
type family XSetupStruct ext
type family XSetupEnum ext
type family XSetupTuple ext
type family XSetupSlice ext
type family XSetupArray ext
type family XSetupElem ext
type family XSetupField ext
type family XSetupGlobal ext
type family XSetupCast ext
type family XSetupUnion ext
type family XSetupGlobalInitializer ext
type family XSetupMux ext

-- | From the manual: \"The SetupValue type corresponds to values that can occur
-- during symbolic execution, which includes both 'Term' values, pointers, and
-- composite types consisting of either of these (both structures and arrays).\"
data SetupValue ext where
  SetupVar    :: AllocIndex -> SetupValue ext
  SetupTerm   :: TypedTerm -> SetupValue ext
  SetupNull   :: XSetupNull ext -> SetupValue ext
  SetupStruct :: XSetupStruct ext -> [SetupValue ext] -> SetupValue ext
  SetupArray  :: XSetupArray ext -> [SetupValue ext] -> SetupValue ext
  SetupElem   :: XSetupElem ext -> SetupValue ext -> Int -> SetupValue ext
  SetupField  :: XSetupField ext -> SetupValue ext -> String -> SetupValue ext
  SetupCast   :: XSetupCast ext -> SetupValue ext -> SetupValue ext
  SetupUnion  :: XSetupUnion ext -> SetupValue ext -> String -> SetupValue ext

  -- | A tuple value. At the moment, this is only ever used for MIR
  -- verification.
  SetupTuple :: XSetupTuple ext -> [SetupValue ext] -> SetupValue ext
  -- | A slice value. At the moment, this is only ever used for MIR
  -- verification.
  SetupSlice :: XSetupSlice ext -> SetupValue ext
  -- | An enumeration value. At the moment, this is only ever used for MIR
  -- verification.
  SetupEnum :: XSetupEnum ext -> SetupValue ext

  -- | A pointer to a global variable
  SetupGlobal :: XSetupGlobal ext -> String -> SetupValue ext
  -- | This represents the value of a global's initializer.
  SetupGlobalInitializer ::
    XSetupGlobalInitializer ext -> String -> SetupValue ext
  -- | A mux of two 'SetupValue's based on a boolean-typed 'TypedTerm'.
  SetupMux ::
    XSetupMux ext ->
    TypedTerm
      {- ^ The conditional expression. Must be of Cryptol type @Bit@. -} ->
    SetupValue ext
      {- ^ The value to use if the conditional expression is true. -} ->
    SetupValue ext
      {- ^ The value to use if the conditional expression is false. -} ->
    SetupValue ext

-- | This constraint can be solved for any ext so long as '()', 'Void', and any
--   other types used in the right-hand sides of extension field
--   @type instance@s have the constraint. Unfortunately, GHC can't (yet?)
--   reason over the equations in our closed type family and realize that, so we
--   must explicitly abstract this reasoning out into a type synonym.
type SetupValueHas (c :: Type -> Constraint) ext =
  ( c (XSetupNull ext)
  , c (XSetupStruct ext)
  , c (XSetupEnum ext)
  , c (XSetupTuple ext)
  , c (XSetupSlice ext)
  , c (XSetupArray ext)
  , c (XSetupElem ext)
  , c (XSetupField ext)
  , c (XSetupCast ext)
  , c (XSetupUnion ext)
  , c (XSetupGlobal ext)
  , c (XSetupGlobalInitializer ext)
  , c (XSetupMux ext)
  )

deriving instance (SetupValueHas Show ext) => Show (SetupValue ext)

-- TypedTerm is neither Eq nor Ord
-- deriving instance (SetupValueHas Eq ext) => Eq (SetupValue ext)
-- deriving instance (SetupValueHas Ord ext) => Ord (SetupValue ext)

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
