{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ConstraintKinds #-}

module SAWScript.Heapster.TypedCrucible where

import Data.Text
import Data.Type.Equality
import GHC.TypeLits
-- import Data.Functor.Product
-- import Data.Parameterized.Context
import What4.ProgramLoc

import Control.Monad.State
import Control.Monad.Reader

import Data.Parameterized.Context hiding ((:>), empty, take)

-- import Data.Parameterized.TraversableFC
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.Analysis.Fixpoint.Components

import Data.Binding.Hobbits
import SAWScript.Heapster.Permissions
import SAWScript.Heapster.Implication


----------------------------------------------------------------------
-- * Building 'NuMatching' Instances for Crucible Types
----------------------------------------------------------------------

-- | An object containing a 'KnownRepr' instance; used to build 'NuMatching'
-- instances for the various @Repr@ types
data KnownReprObj f a = KnownRepr f a => KnownReprObj

$(mkNuMatching [t| forall f a. KnownReprObj f a |])

mkKnownReprObj :: WithKnownRepr f => f a -> KnownReprObj f a
mkKnownReprObj repr = withKnownRepr repr KnownReprObj

getKnownReprObj :: KnownReprObj f a -> f a
getKnownReprObj KnownReprObj = knownRepr

instance NuMatching (SymbolRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (NatRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (TypeRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (BaseTypeRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

-- NOTE: this is handled by the Assignment instance
-- instance NuMatching (CtxRepr ctx) where
--   nuMatchingProof = isoMbTypeRepr mkKnownReprObj getKnownReprObj

instance NuMatching (Index ctx a) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching Text where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching ProgramLoc where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (FnHandle args ret) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (FloatInfoRepr fi) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching RoundingMode where
  nuMatchingProof = unsafeMbTypeRepr


class NuMatchingAny1 (f :: k -> *) where
  nuMatchingAny1Proof :: MbTypeRepr (f a)

instance NuMatchingAny1 BaseTypeRepr where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 TypeRepr where
  nuMatchingAny1Proof = nuMatchingProof

instance {-# INCOHERENT #-} NuMatchingAny1 f => NuMatching (f a) where
  nuMatchingProof = nuMatchingAny1Proof

instance NuMatchingAny1 f => NuMatching (Assignment f ctx) where
  nuMatchingProof =
    error "FIXME HERE"
    -- isoMbTypeRepr assignToMapRList mapRListToAssign

$(mkNuMatching [t| forall f tp. NuMatchingAny1 f => BaseTerm f tp |])

instance NuMatchingAny1 f => NuMatchingAny1 (BaseTerm f) where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| forall ext f tp.
                (NuMatchingAny1 f, NuMatchingAny1 (ExprExtension ext f)) =>
                App ext f tp |])


----------------------------------------------------------------------
-- * Typed Jump Targets and Function Handles
----------------------------------------------------------------------

-- | During type-checking, we convert Crucible registers to variables
newtype TypedReg tp = TypedReg { unTypedReg :: ExprVar tp }

-- | A type-checked Crucible expression is a Crucible 'Expr' that uses
-- 'TypedReg's for variables
newtype TypedExpr ext tp = TypedExpr (App ext TypedReg tp)

-- | A "typed" function handle is a normal function handle plus ghost arguments
data TypedFnHandle ghosts args ret =
  TypedFnHandle (CruCtx ghosts) (FnHandle (RListToCtx args) ret)

-- | All of our blocks have multiple entry points, for different inferred types,
-- so a "typed" 'BlockID' is a normal Crucible 'BlockID' (which is just an index
-- into the @blocks@ context of contexts) plus an 'Int' specifying which entry
-- point to that block. Each entry point also takes an extra set of "ghost"
-- arguments, not extant in the original program, that are needed to express
-- input and output permissions.
data TypedEntryID blocks ghosts args =
  TypedEntryID { entryBlockID :: Member blocks args,
                 entryGhosts :: CruCtx ghosts,
                 entryIndex :: Int }

-- | A collection of arguments to a function or jump target
data TypedArgs args where
  TypedArgsNil :: TypedArgs RNil
  TypedArgsCons :: KnownRepr TypeRepr a => TypedArgs args -> TypedReg a ->
                   TypedArgs (args :> a)

-- | A typed target for jump and branch statements, including arguments and a
-- proof of the required permissions on those arguments
data TypedJumpTarget blocks where
     TypedJumpTarget ::
       TypedEntryID blocks ghosts args ->
       PermImpl (TypedArgs (args :++: ghosts)) (args :++: ghosts) ->
       TypedJumpTarget blocks


$(mkNuMatching [t| forall tp. TypedReg tp |])

instance NuMatchingAny1 TypedReg where
  nuMatchingAny1Proof = nuMatchingProof

type NuMatchingExtC ext =
  (NuMatchingAny1 (ExprExtension ext TypedReg),
   NuMatchingAny1 (StmtExtension ext TypedReg))

$(mkNuMatching [t| forall ext tp. NuMatchingExtC ext => TypedExpr ext tp |])
$(mkNuMatching [t| forall ghosts args ret. TypedFnHandle ghosts args ret |])
$(mkNuMatching [t| forall blocks ghosts args. TypedEntryID blocks ghosts args |])
$(mkNuMatching [t| forall args. TypedArgs args |])
$(mkNuMatching [t| forall blocks. TypedJumpTarget blocks |])


----------------------------------------------------------------------
-- * Typed Crucible Statements and Sequences of Statements
----------------------------------------------------------------------

-- | Typed Crucible statements with the given Crucible syntax extension and the
-- given set of return values
data TypedStmt ext rets where
  -- | Assign the value of a register
  TypedSetReg :: TypeRepr tp -> TypedExpr ext tp -> TypedStmt ext (RNil :> tp)

  -- | Assign a register via a statement in a syntax extension
  ExtendAssign :: StmtExtension ext TypedReg tp -> TypedStmt ext (RNil :> tp)

  -- | Assert a boolean condition, printing the given string on failure
  TypedAssert :: TypedReg BoolType -> TypedReg StringType -> TypedStmt ext RNil

  -- | Destruct an LLVM value into its block and offset
  DestructLLVMPtr :: (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
                     TypedStmt (LLVM arch) (RNil :> NatType :> BVType w)


-- | Typed Crucible block termination statements
data TypedTermStmt blocks inits (ret :: CrucibleType) where
  -- | Jump to the given jump target
  TypedJump :: TypedJumpTarget blocks -> TypedTermStmt blocks inits ret

  -- | Branch on condition: if true, jump to the first jump target, and
  -- otherwise jump to the second jump target
  TypedBr :: TypedReg BoolType ->
             TypedJumpTarget blocks ->
             TypedJumpTarget blocks ->
             TypedTermStmt blocks inits ret

  -- | Return from function, providing the return value and also proof that the
  -- current permissions the required return permissions
  TypedReturn :: PermImpl (TypedReg ret) (inits :> ret) ->
                 TypedTermStmt blocks inits ret

  -- | Block ends with an error
  TypedErrorStmt :: TypedReg StringType -> TypedTermStmt blocks inits ret


-- | A typed sequence of Crucible statements
data TypedStmtSeq ext blocks inits (ret :: CrucibleType) where
  -- | A permission implication step, which modifies the current permission
  -- set. This can include pattern-matches and/or assertion failures.
  TypedImplStmt :: PermImpl (TypedStmtSeq ext blocks inits ret) RNil ->
                   TypedStmtSeq ext blocks inits ret

  -- | Typed version of 'ConsStmt', which binds new variables for the return
  -- value(s) of each statement
  TypedConsStmt :: ProgramLoc ->
                   TypedStmt ext rets ->
                   Mb (ExprVarCtx rets) (TypedStmtSeq ext blocks inits ret) ->
                   TypedStmtSeq ext blocks inits ret

  -- | Typed version of 'TermStmt', which terminates the current block
  TypedTermStmt :: ProgramLoc ->
                   TypedTermStmt blocks inits ret ->
                   TypedStmtSeq ext blocks inits ret

$(mkNuMatching [t| forall ext rets. NuMatchingExtC ext => TypedStmt ext rets |])
$(mkNuMatching [t| forall blocks inits ret. TypedTermStmt blocks inits ret |])
$(mkNuMatching [t| forall ext blocks inits ret.
                NuMatchingExtC ext => TypedStmtSeq ext blocks inits ret |])
