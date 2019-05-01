{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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

module SAWScript.Heapster.TypedCrucible where

import           SAWScript.Heapster.Permissions

import           Data.Parameterized.Context
import           What4.ProgramLoc
import           Lang.Crucible.Types
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.CFG.Core


----------------------------------------------------------------------
-- * Typed Crucible Statements
----------------------------------------------------------------------

-- | Typed Crucible statements
data TypedStmt ext ctx ctx' where
  TypedStmt :: PermSet ctx -> PermSet ctx' -> Stmt ext ctx ctx' ->
               TypedStmt ext ctx ctx'
  -- ^ A normal Crucible statement annotated with input and output permissions

  DestructLLVMPtr :: (1 <= w) => NatRepr w -> Index ctx (LLVMPointerType w) ->
                     TypedStmt ext ctx (ctx ::> NatType ::> BVType w)
  -- ^ Destruct an LLVM value into its block and offset

-- | A collection of arguments to a function or jump target, including
-- introduction rules to prove the necessary permissions for those arguments
data TypedArgs args ctx =
  TypedArgs (CtxRepr args) (Assignment (PermVar ctx) args)
  (PermSet ctx) (PermSet args) (PermIntro ctx)


-- | A target for jump and branch statements that has been typed. This inlucdes
-- a 'BlockID' of the block we are going to jump to, and the types, values, and
-- permissions for the arguments to that block. The 'Int' specifies which of the
-- @n@ disjunctive input permission of the given block are being satisfied; see
-- 'buildJumpTargetIntro'.
data TypedJumpTarget blocks ctx where
     TypedJumpTarget :: BlockID blocks args ->
                        TypedArgs args ctx -> Int ->
                        TypedJumpTarget blocks ctx

-- | Extend the 'PermIntro' in a 'TypedJumpTarget' from a proof of the @i@th
-- permissions to a proof of the entire permission set @P1 \/ ... \/ Pn@
-- required for the block being jumped to. This is done because we may not know
-- all of the @Pi@ when we type a jump target, so we allow the rest of them to
-- be passed in later to this function, after they have been determined.
-- buildJumpTargetIntro :: [PermSet args] FIXME HERE

-- | Typed Crucible block termination statements
data TypedTermStmt blocks (ret :: CrucibleType) (ctx :: Ctx CrucibleType) where
  -- | Jump to the given jump target
  TypedJump :: TypedJumpTarget blocks ctx ->
               TypedTermStmt blocks ret ctx

  -- | Branch on condition.  If true, jump to the first jump target; otherwise
  -- jump to the second jump target.
  TypedBr :: PermVar ctx BoolType ->
             TypedJumpTarget blocks ctx ->
             TypedJumpTarget blocks ctx ->
             TypedTermStmt blocks ret ctx

  -- | Return from function, providing the return value(s), along with an
  -- introduction rule that proves the return permissions
  TypedReturn :: PermVar ctx ret ->
                 PermSet ctx ->
                 PermIntro ctx ->
                 TypedTermStmt blocks ret ctx

  -- Block ends with an error.
  TypedErrorStmt :: PermVar ctx StringType -> TypedTermStmt blocks ret ctx


data TypedStmtSeq ext blocks (ret :: CrucibleType) ctx where
  TypedElimStmt :: PermElim (TypedStmtSeq ext blocks ret) ctx ->
                   TypedStmtSeq ext blocks ret ctx
  -- ^ A collection of sequences of statements inside a permission elimination,
  -- the "execution" of which depends on the elimination

  TypedConsStmt :: ProgramLoc ->
                   TypedStmt ext ctx ctx' ->
                   TypedStmtSeq ext blocks ret ctx' ->
                   TypedStmtSeq ext blocks ret ctx'
  -- ^ Typed version of 'ConsStmt'

  TypedTermStmt :: ProgramLoc ->
                   TypedTermStmt blocks ret ctx ->
                   TypedStmtSeq ext blocks ret ctx
  -- ^ Typed version of 'TermStmt'
