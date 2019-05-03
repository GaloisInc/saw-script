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

module SAWScript.Heapster.TypedCrucible where

import           SAWScript.Heapster.Permissions

import           Data.Type.Equality
import           Data.Parameterized.Context
import           What4.ProgramLoc
import qualified Control.Category as Cat

import           Control.Monad.State
import           Control.Monad.Reader

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
-- specifying which entry point to that block. Each entry point also takes an
-- extra set of "ghost" arguments, not existant in the original program, that
-- are useful to express input and output permissions.
data TypedBlockID blocks ghosts args =
  TypedBlockID (BlockID blocks args) (CtxRepr ghosts) Int

-- | Test if two 'TypedBlockID's are equal, returning a proof that their ghost
-- arguments are equaal when they are
typedBlockIDEq :: TypedBlockID blocks ghosts1 args ->
                  TypedBlockID blocks ghosts2 args ->
                  Maybe (ghosts1 :~: ghosts2)
typedBlockIDEq (TypedBlockID id1 ghosts1 i1) (TypedBlockID id2 ghosts2 i2)
  | id1 == id2 && i1 == i2 = testEquality ghosts1 ghosts2

-- | A collection of arguments to a function or jump target, including
-- introduction rules to prove the necessary permissions for those arguments
data TypedArgs args ctx =
  TypedArgs (CtxRepr args) (Assignment (PermVar ctx) args) (AnnotIntro ctx)

instance ExtendContext (TypedArgs args) where
  extendContext diff (TypedArgs args_ctx args intro) =
    TypedArgs args_ctx (fmapFC (extendContext' diff) args)
    (extendContext diff intro)

argsInputPerms :: TypedArgs args ctx -> PermSet ctx
argsInputPerms (TypedArgs _ _ intro) = introInPerms intro

-- | A target for jump and branch statements whose arguments have been typed
data TypedJumpTarget blocks ctx where
     TypedJumpTarget :: TypedBlockID blocks ghosts args ->
                        TypedArgs (ghosts <+> args) ctx ->
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

  -- | Return from function, providing the return value(s) and also a permission
  -- introduction that maps the current permissions to the return permissions
  TypedReturn :: PermVar ctx ret ->
                 AnnotIntro ctx ->
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


-- | Typed version of a Crucible block ID. Note that our blocks implicitly take
-- extra "ghost" arguments, that are needed to express the input and output
-- permissions.
--
-- FIXME: add a @ghostss@ type argument that associates a @ghosts@ type with
-- each index of each block, rather than having @ghost@ existentially bound
-- here.
data TypedBlock ext blocks ret args where
  TypedBlock :: TypedBlockID blocks ghosts args -> CtxRepr args ->
                TypedStmtSeq ext blocks ret (ghosts <+> args) ->
                TypedBlock ext blocks ret args

-- | A list of typed blocks, one for each entry point of a given 'BlockID'
newtype TypedBlockList ext blocks ret args
  = TypedBlockList [TypedBlock ext blocks ret args]

-- | A map assigning a 'TypedBlockList' to each 'BlockID'
type TypedBlockMap ext blocks ret =
  Assignment (TypedBlockList ext blocks ret) blocks

-- | A typed Crucible CFG
data TypedCFG
     (ext :: *)
     (blocks :: Ctx (Ctx CrucibleType))
     (ghosts :: Ctx CrucibleType)
     (init :: Ctx CrucibleType)
     (ret :: CrucibleType)
  = TypedCFG { tpcfgHandle :: FnHandle init ret
             , tpcfgInputPerms :: PermSet init
             , tpcfgOutputPerms :: PermSet (init ::> ret)
             , tpcfgBlockMap :: !(TypedBlockMap ext blocks ret)
             , tpcfgEntryBlockID :: !(TypedBlockID blocks ghosts init)
             }


----------------------------------------------------------------------
-- * Permission Type-Checking for Crucible
----------------------------------------------------------------------

data PermCheckEnv ret ctx =
  PermCheckEnv
  {
    envCurPerms :: PermSet ctx,
    envRetPerms :: PermSetSpec EmptyCtx (ctx ::> ret)
  }

instance Weakenable (PermCheckEnv ret) where
  weaken w (PermCheckEnv { .. }) =
    PermCheckEnv { envCurPerms = weakenPermSet w envCurPerms,
                   envRetPerms = map (weaken (weakenWeakening1 w)) envRetPerms }

instance ExtendContext (PermCheckEnv ret) where
  extendContext diff = weaken (weakeningOfDiff diff)


-- | Information about the current state of type-checking for a block
data BlockTypeInfo blocks ret args where
  BlockTypeInfo :: {
    blockInfoID :: TypedBlockID blocks ghosts args,
    blockInfoArgs :: CtxRepr args,
    blockInfoVisited :: Bool,
    blockInfoPermsIn :: PermSetSpec EmptyCtx (ghosts <+> args),
    blockInfoPermsOut :: PermSetSpec EmptyCtx (ghosts <+> args ::> ret)
  } -> BlockTypeInfo blocks ret args

data PermCheckState blocks ret =
  PermCheckState
  {
    stTypedTargets :: Assignment (BlockTypeInfo blocks ret) blocks
  }

-- | The monad for permission type-checking a function with inputs @init@ and
-- return value @ret@ where the local context (where we are currently
-- type-checking) is @ctx@
newtype PermCheckM blocks ret ctx a =
  PermCheckM { unPermCheckM ::
                 ReaderT (PermCheckEnv ret ctx)
                 (State (PermCheckState blocks ret)) a }
  deriving (Functor, Applicative, Monad)

instance MonadReader (PermCheckEnv ret ctx) (PermCheckM blocks ret ctx) where
  ask = PermCheckM ask
  local f (PermCheckM m) = PermCheckM $ local f m

instance MonadState (PermCheckState blocks ret) (PermCheckM blocks ret ctx) where
  get = PermCheckM get
  put s = PermCheckM $ put s

-- | Run a computation with an updated permission set
withPerms :: PermSet ctx -> PermCheckM blocks ret ctx a ->
             PermCheckM blocks ret ctx a
withPerms perms = local (\env -> env { envCurPerms = perms })

-- | Run a computation in an extended context
inExtCtxM :: Diff ctx ctx' -> PermCheckM blocks ret ctx' a ->
             PermCheckM blocks ret ctx a
inExtCtxM diff (PermCheckM m) =
  PermCheckM $ ReaderT $ \env -> runReaderT m $ extendContext diff env

-- | Map a function over a permission elimination
mapElimM :: (forall ctx'. Diff ctx ctx' -> f ctx' ->
             PermCheckM blocks ret ctx' (g ctx')) ->
            PermElim f ctx ->
            PermCheckM blocks ret ctx (PermElim g ctx)
mapElimM f elim = traverseElim (\diff x -> inExtCtxM diff (f diff x)) elim

getCurPerms :: PermCheckM blocks ret ctx (PermSet ctx)
getCurPerms = envCurPerms <$> ask

getRetPerms :: PermCheckM blocks ret ctx (PermSetSpec EmptyCtx (ctx ::> ret))
getRetPerms = envRetPerms <$> ask


-- | "Type-check" a 'Reg' by converting it to a 'PermVar'
tcReg :: Reg ctx a -> PermCheckM blocks ret ctx (PermVar ctx a)
tcReg reg = PermVar <$> (size <$> getCurPerms) <*> return (regIndex reg)

-- | The input and output permissions for an expression in the current branch of
-- a permission elimination
data ExprPerms ret ctx =
  ExprPerms (PermSet ctx) (PermSet (ctx ::> ret))

-- | Type-check a Crucible expression
tcExpr :: Expr ext ctx tp ->
          PermCheckM blocks ret ctx (PermElim (ExprPerms tp) ctx)
tcExpr _ = error "FIXME: tcExpr"


----------------------------------------------------------------------
-- * Type-Checking Crucible Statements
----------------------------------------------------------------------

-- | Weaken a 'StmtSeq'
weakenStmtSeq :: TraverseExt ext =>
                 Size ctx -> Weakening ctx ctx' -> StmtSeq ext blocks ret ctx ->
                 StmtSeq ext blocks ret ctx'
weakenStmtSeq sz w = applyEmbedding (embeddingOfWeakening sz w)


-- | Smart constructor for 'TypedElimStmt', which avoids inserting an
-- elimination for trivial eliminations
typedElimStmt :: PermElim (TypedStmtSeq ext blocks ret) ctx ->
                 PermCheckM blocks ret ctx (TypedStmtSeq ext blocks ret ctx)
typedElimStmt (Elim_Done stmts) = return stmts
typedElimStmt elim_stmts =
  do perms <- getCurPerms
     return $ TypedElimStmt perms elim_stmts


-- FIXME HERE: type-check jump targets:
--
-- 1. If visited, try all N possible input perms
--
-- 2. If unvisited, need to infer some new input perms by starting with the
-- argument vars and recursively adding any vars in their perms

tcJumpTarget :: JumpTarget blocks ctx ->
                PermCheckM blocks ret ctx (PermElim (TypedJumpTarget blocks) ctx)
tcJumpTarget = error "FIXME: tcJumpTarget"

-- | Type-check a sequence of statements. This includes type-checking for
-- individual statements and termination statements, which are both easier to do
-- when we have the whole statement sequence there.
tcStmtSeq :: TraverseExt ext =>
             StmtSeq ext blocks ret ctx ->
             PermCheckM blocks ret ctx (TypedStmtSeq ext blocks ret ctx)

tcStmtSeq (ConsStmt l (SetReg tp expr) stmts') =
  do perms_elim <- tcExpr expr
     perms <- getCurPerms
     typed_stmts_elim <-
       mapElimM
       (\diff (ExprPerms perms_in perms_out) ->
         TypedConsStmt l
         (TypedStmt perms_in perms_out
          (SetReg tp $ extendContext' diff expr)) <$>
         (inExtCtxM oneDiff $ withPerms perms_out $
          tcStmtSeq (weakenStmtSeq (incSize $ size perms)
                     (weakenWeakening1 $ weakeningOfDiff diff) stmts')))
       perms_elim
     typedElimStmt typed_stmts_elim

tcStmtSeq (TermStmt l (Jump tgt)) =
  do typed_tgt_elim <- tcJumpTarget tgt
     typedElimStmt $ cmap (\_ -> TypedTermStmt l . TypedJump) typed_tgt_elim

tcStmtSeq (TermStmt l (Br reg tgt1 tgt2)) =
  do x <- tcReg reg
     elim_tgt1 <- tcJumpTarget tgt1
     elim_stmts <-
       cjoin <$> mapElimM
       (\diff1 typed_tgt1 ->
         withPerms (targetInputPerms typed_tgt1) $
         do elim_tgt2 <- tcJumpTarget (extendContext diff1 tgt2)
            mapElimM
              (\diff2 typed_tgt2 ->
                return $ TypedTermStmt l $
                TypedBr (extendContext' (diff2 Cat.. diff1) x)
                (extendContext diff2 typed_tgt1)
                typed_tgt2
                )
              elim_tgt2)
       elim_tgt1
     typedElimStmt elim_stmts

tcStmtSeq (TermStmt l (Return reg)) =
  do perms <- getCurPerms
     retPerms <- getRetPerms
     x <- tcReg reg
     let spec_s = mkSubst1 (size perms) (PExpr_Var x)
         specs = map (substPermSpec spec_s) retPerms
         elim_intro = provePermImpl perms empty specs
     elim_stmts <-
       mapElimM (\diff (ImplRet _ _ intro) ->
                  return $ TypedTermStmt l $
                  TypedReturn (extendContext' diff x) intro)
       elim_intro
     typedElimStmt elim_stmts
