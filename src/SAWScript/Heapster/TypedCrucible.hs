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

module SAWScript.Heapster.TypedCrucible where

import           SAWScript.Heapster.Permissions

import           Control.Monad.State
import           Data.Parameterized.Context
import           What4.ProgramLoc
import qualified Control.Category as Cat
import           Data.Parameterized.TraversableFC
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension


----------------------------------------------------------------------
-- * Typed Crucible Statements
----------------------------------------------------------------------

-- | Typed Crucible statements
data TypedStmt ext ctx ctx' where
  TypedStmt :: PermSet ctx -> PermSet ctx' -> Stmt ext ctx ctx' ->
               TypedStmt ext ctx ctx'
  -- ^ A normal Crucible statement annotated with input and output permissions

  DestructLLVMPtr :: (1 <= w) => NatRepr w -> Index ctx (LLVMPointerType w) ->
                     TypedStmt (LLVM arch) ctx (ctx ::> NatType ::> BVType w)
  -- ^ Destruct an LLVM value into its block and offset

-- | All of our blocks have multiple entry points, for different inferred types,
-- so a "typed" 'BlockID' is a normal Crucible 'BlockID' plus an 'Int'
-- specifying which entry point to that block
data TypedBlockID blocks tp = TypedBlockID (BlockID blocks tp) Int

-- | A collection of arguments to a function or jump target, including
-- introduction rules to prove the necessary permissions for those arguments
data TypedArgs args ctx =
  TypedArgs (CtxRepr args) (Assignment (PermVar ctx) args)
  (PermSet ctx) (PermSet args) (PermIntro ctx)

instance ExtendContext (TypedArgs args) where
  extendContext diff (TypedArgs args_ctx args perms req_perms intro) =
    TypedArgs args_ctx (fmapFC (extendContext' diff) args)
    (extPermSet diff perms) req_perms (extendContext diff intro)

argsInputPerms :: TypedArgs args ctx -> PermSet ctx
argsInputPerms (TypedArgs _ _ perms _ _) = perms

-- | A target for jump and branch statements whose arguments have been typed
data TypedJumpTarget blocks ctx where
     TypedJumpTarget :: TypedBlockID blocks args -> TypedArgs args ctx ->
                        TypedJumpTarget blocks ctx

targetInputPerms :: TypedJumpTarget blocks ctx -> PermSet ctx
targetInputPerms (TypedJumpTarget _ args) = argsInputPerms args

instance ExtendContext (TypedJumpTarget blocks) where
  extendContext diff (TypedJumpTarget block args) =
    TypedJumpTarget block $ extendContext diff args

-- | Typed Crucible block termination statements
data TypedTermStmt blocks (ret :: CrucibleType) (ctx :: Ctx CrucibleType) where
  -- | Jump to the given jump target
  TypedJump :: TypedJumpTarget blocks ctx ->
               TypedTermStmt blocks ret ctx

  -- | Branch on condition. If true, jump to the first jump target; otherwise
  -- jump to the second jump target
  TypedBr :: PermVar ctx BoolType ->
             TypedJumpTarget blocks ctx ->
             TypedJumpTarget blocks ctx ->
             TypedTermStmt blocks ret ctx

  -- | Return from function, providing the return value(s) along with an
  -- introduction rule that proves the return permissions
  TypedReturn :: PermVar ctx ret ->
                 PermSet ctx ->
                 PermIntro ctx ->
                 TypedTermStmt blocks ret ctx

  -- | Block ends with an error
  TypedErrorStmt :: PermVar ctx StringType -> TypedTermStmt blocks ret ctx


-- | A typed sequence of Crucible statements
data TypedStmtSeq ext blocks (ret :: CrucibleType) ctx where
  TypedElimStmt :: PermSet ctx ->
                   PermElim (TypedStmtSeq ext blocks ret) ctx ->
                   TypedStmtSeq ext blocks ret ctx
  -- ^ A collection of sequences of statements inside a permission elimination,
  -- which intuitively determines a set of pattern-matches on the current
  -- permissions that are held at the current point in execution

  TypedConsStmt :: ProgramLoc ->
                   TypedStmt ext ctx ctx' ->
                   TypedStmtSeq ext blocks ret ctx' ->
                   TypedStmtSeq ext blocks ret ctx
  -- ^ Typed version of 'ConsStmt'

  TypedTermStmt :: ProgramLoc ->
                   TypedTermStmt blocks ret ctx ->
                   TypedStmtSeq ext blocks ret ctx
  -- ^ Typed version of 'TermStmt'

-- | Smart constructor for 'TypedElimStmt', which avoids inserting an
-- elimination for trivial eliminations
typedElimStmt :: PermSet ctx ->
                 PermElim (TypedStmtSeq ext blocks ret) ctx ->
                 TypedStmtSeq ext blocks ret ctx
typedElimStmt _ (Elim_Done stmts) = stmts
typedElimStmt perms elim_stmts = TypedElimStmt perms elim_stmts


-- | Typed version of a Crucible block ID
data TypedBlock ext blocks ret ctx 
  = TypedBlock (TypedBlockID blocks ctx) (CtxRepr ctx)
    (TypedStmtSeq ext blocks ret ctx)

-- | A list of typed blocks, one for each entry point of a given 'BlockID'
newtype TypedBlockList ext blocks ret ctx
  = TypedBlockList [TypedBlock ext blocks ret ctx]

-- | A map assigning a 'TypedBlockList' to each 'BlockID'
type TypedBlockMap ext blocks ret =
  Assignment (TypedBlockList ext blocks ret) blocks

-- | A typed Crucible CFG
data TypedCFG
     (ext :: *)
     (blocks :: Ctx (Ctx CrucibleType))
     (init :: Ctx CrucibleType)
     (ret :: CrucibleType)
  = TypedCFG { tpcfgHandle :: FnHandle init ret
             , tpcfgInputPerms :: PermSet init
             , tpcfgOutputPerms :: PermSet (init ::> ret)
             , tpcfgBlockMap :: !(TypedBlockMap ext blocks ret)
             , tpcfgEntryBlockID :: !(TypedBlockID blocks init)
             }


----------------------------------------------------------------------
-- * Permission Type-Checking for Crucible
----------------------------------------------------------------------

data PermCheckState =
  PermCheckState
  {
  }

-- | The monad for permission type-checking
newtype PermCheckM a =
  PermCheckM { unPermCheckM :: State PermCheckState a }
  deriving (Functor, Applicative, Monad)

-- | The input and output permissions for an expression in the current branch of
-- a permission elimination
data ExprPerms ret ctx =
  ExprPerms (PermSet ctx) (PermSet (ctx ::> ret))

-- | Type-check a Crucible expression
tcExpr :: PermSet ctx -> Expr ext ctx tp ->
          PermCheckM (PermElim (ExprPerms ret) ctx)
tcExpr _ _ = error "FIXME: tcExpr"


----------------------------------------------------------------------
-- * Type-Checking Crucible Statements
----------------------------------------------------------------------

-- | Weaken a 'StmtSeq'
weakenStmtSeq :: TraverseExt ext =>
                 Size ctx -> Weakening ctx ctx' -> StmtSeq ext blocks ret ctx ->
                 StmtSeq ext blocks ret ctx'
weakenStmtSeq sz w = applyEmbedding (embeddingOfWeakening sz w)


tcJumpTarget :: PermSet ctx -> JumpTarget blocks ctx ->
                PermCheckM (PermElim (TypedJumpTarget blocks) ctx)
tcJumpTarget = error "FIXME: tcJumpTarget"

-- | Type-check a sequence of statements. This includes type-checking for
-- individual statements and termination statements, which are both easier to do
-- when we have the whole statement sequence there.
tcStmtSeq :: TraverseExt ext =>
             PermSet ctx -> StmtSeq ext blocks ret ctx ->
             PermCheckM (TypedStmtSeq ext blocks ret ctx)

tcStmtSeq perms (ConsStmt l (SetReg tp expr) stmts') =
  do perms_elim <- tcExpr perms expr
     typed_stmts_elim <-
       traverseElim
       (\diff (ExprPerms perms_in perms_out) ->
         TypedConsStmt l
         (TypedStmt perms_in perms_out
          (SetReg tp $ extendContext' diff expr)) <$>
         tcStmtSeq perms_out (weakenStmtSeq (incSize $ size perms)
                              (weakenWeakening1 $ weakeningOfDiff diff) stmts'))
       perms_elim
     return $ typedElimStmt perms typed_stmts_elim

tcStmtSeq perms (TermStmt l (Jump tgt)) =
  do typed_tgt_elim <- tcJumpTarget perms tgt
     return $ typedElimStmt perms $
       cmap (\_ -> TypedTermStmt l . TypedJump) typed_tgt_elim

tcStmtSeq perms (TermStmt l (Br reg tgt1 tgt2)) =
  do elim_tgt1 <- tcJumpTarget perms tgt1
     typedElimStmt perms <$> cjoin <$>
       traverseElim
       (\diff1 typed_tgt1 ->
         do elim_tgt2 <-
              tcJumpTarget (targetInputPerms typed_tgt1)
              (extendContext diff1 tgt2)
            traverseElim
              (\diff2 typed_tgt2 ->
                return $ TypedTermStmt l $
                TypedBr (extendContext' (diff2 Cat.. diff1)
                         (PermVar (size perms) $ regIndex reg))
                (extendContext diff2 typed_tgt1)
                typed_tgt2
                )
              elim_tgt2)
       elim_tgt1
