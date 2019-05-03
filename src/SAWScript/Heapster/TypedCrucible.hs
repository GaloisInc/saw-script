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
import           Data.Functor.Product
import           Data.Parameterized.Context
import           What4.ProgramLoc
import qualified Control.Category as Cat
import qualified Control.Lens as Lens

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

data TypedFnHandle ghosts init ret =
  TypedFnHandle (CtxRepr ghosts) (FnHandle init ret)

-- | All of our blocks have multiple entry points, for different inferred types,
-- so a "typed" 'BlockID' is a normal Crucible 'BlockID' plus an 'Int'
-- specifying which entry point to that block. Each entry point also takes an
-- extra set of "ghost" arguments, not existant in the original program, that
-- are useful to express input and output permissions.
data TypedEntryID blocks ghosts args =
  TypedEntryID (BlockID blocks args) (CtxRepr ghosts) Int

entryBlockID :: TypedEntryID blocks ghosts args -> BlockID blocks args
entryBlockID (TypedEntryID blkID _ _) = blkID

entryIndex :: TypedEntryID blocks ghosts args -> Int
entryIndex (TypedEntryID _ _ ix) = ix


-- | Test if two 'TypedEntryID's are equal, returning a proof that their ghost
-- arguments are equaal when they are
typedBlockIDEq :: TypedEntryID blocks ghosts1 args ->
                  TypedEntryID blocks ghosts2 args ->
                  Maybe (ghosts1 :~: ghosts2)
typedBlockIDEq (TypedEntryID id1 ghosts1 i1) (TypedEntryID id2 ghosts2 i2)
  | id1 == id2 && i1 == i2 = testEquality ghosts1 ghosts2

-- | A collection of arguments to a function or jump target, including
-- introduction rules to prove the necessary permissions for those arguments
data TypedArgs args ctx =
  TypedArgs (CtxRepr args) (Assignment (PermVar ctx) args) (AnnotIntro ctx)

instance WeakenableWithCtx (TypedArgs args) where
  weakenWithCtx ctx w (TypedArgs args_ctx args intro) =
    TypedArgs args_ctx (fmapFC (weaken' w) args)
    (weakenWithCtx ctx w intro)

argsInputPerms :: TypedArgs args ctx -> PermSet ctx
argsInputPerms (TypedArgs _ _ intro) = introInPerms intro

-- | A target for jump and branch statements whose arguments have been typed
data TypedJumpTarget blocks ctx where
     TypedJumpTarget :: TypedEntryID blocks ghosts args ->
                        TypedArgs (ghosts <+> args) ctx ->
                        TypedJumpTarget blocks ctx

targetInputPerms :: TypedJumpTarget blocks ctx -> PermSet ctx
targetInputPerms (TypedJumpTarget _ args) = argsInputPerms args

instance WeakenableWithCtx (TypedJumpTarget blocks) where
  weakenWithCtx ctx w (TypedJumpTarget block args) =
    TypedJumpTarget block $ weakenWithCtx ctx w args

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


-- | A single, typed entrypoint to a Crucible block. Note that our blocks
-- implicitly take extra "ghost" arguments, that are needed to express the input
-- and output permissions.
--
-- FIXME: add a @ghostss@ type argument that associates a @ghosts@ type with
-- each index of each block, rather than having @ghost@ existentially bound
-- here.
data TypedEntry ext blocks ret args where
  TypedEntry :: TypedEntryID blocks ghosts args -> CtxRepr args ->
                PermSetSpec EmptyCtx (ghosts <+> args) ->
                TypedStmtSeq ext blocks ret (ghosts <+> args) ->
                TypedEntry ext blocks ret args

-- | A typed Crucible block is a list of typed entrypoints to that block
newtype TypedBlock ext blocks ret args
  = TypedBlock [TypedEntry ext blocks ret args]

-- | A map assigning a 'TypedBlock' to each 'BlockID'
type TypedBlockMap ext blocks ret =
  Assignment (TypedBlock ext blocks ret) blocks

-- | A typed Crucible CFG
data TypedCFG
     (ext :: *)
     (blocks :: Ctx (Ctx CrucibleType))
     (ghosts :: Ctx CrucibleType)
     (init :: Ctx CrucibleType)
     (ret :: CrucibleType)
  = TypedCFG { tpcfgHandle :: TypedFnHandle ghosts init ret
             , tpcfgInputPerms :: PermSet (ghosts <+> init)
             , tpcfgOutputPerms :: PermSet (ghosts <+> init ::> ret)
             , tpcfgBlockMap :: !(TypedBlockMap ext blocks ret)
             , tpcfgEntryBlockID :: !(TypedEntryID blocks ghosts init)
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

instance HasPerms (PermCheckEnv ret) where
  hasPerms = envCurPerms

weakenEnvSetPerms :: PermSet ctx' -> Weakening ctx ctx' ->
                     PermCheckEnv ret ctx -> PermCheckEnv ret ctx'
weakenEnvSetPerms perms w (PermCheckEnv { .. }) =
  PermCheckEnv { envCurPerms = perms,
                 envRetPerms = map (weaken (weakenWeakening1 w)) envRetPerms }

instance WeakenableWithCtx (PermCheckEnv ret) where
  weakenWithCtx ctx w env =
    weakenEnvSetPerms (weakenWithCtx ctx w $ envCurPerms env) w env

{-
instance Weakenable (PermCheckEnv ret) where
  weaken w (PermCheckEnv { .. }) =
    PermCheckEnv { envCurPerms = weakenPermSet w envCurPerms,
                   envRetPerms = map (weaken (weakenWeakening1 w)) envRetPerms }

instance ExtendContext (PermCheckEnv ret) where
  extendContext diff = weaken (weakeningOfDiff diff)
-}

extEnv1 :: TypeRepr tp -> PermCheckEnv ret ctx -> PermCheckEnv ret (ctx ::> tp)
extEnv1 tp env =
  weakenWithCtx (extend (hasCtx env) tp) mkWeakening1 env

-- | Information about one entry point of a block
data BlockEntryInfo blocks ret args where
  BlockEntryInfo :: {
    entryInfoID :: TypedEntryID blocks ghosts args,
    entryInfoPermsIn :: PermSetSpec EmptyCtx (ghosts <+> args),
    entryInfoPermsOut :: PermSetSpec EmptyCtx (ghosts <+> args ::> ret)
  } -> BlockEntryInfo blocks ret args

entryInfoBlockID :: BlockEntryInfo blocks ret args -> BlockID blocks args
entryInfoBlockID (BlockEntryInfo entryID _ _) = entryBlockID entryID

entryInfoIndex :: BlockEntryInfo blocks ret args -> Int
entryInfoIndex (BlockEntryInfo entryID _ _) = entryIndex entryID

-- | Information about the current state of type-checking for a block
data BlockInfo blocks ret args =
  BlockInfo
  {
    blockInfoVisited :: Bool,
    blockInfoEntries :: [BlockEntryInfo blocks ret args]
  }

data PermCheckState blocks ret =
  PermCheckState
  {
    stBlockInfo :: Assignment (BlockInfo blocks ret) blocks
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
inExtCtxM :: TypeRepr tp -> PermCheckM blocks ret (ctx ::> tp) a ->
             PermCheckM blocks ret ctx a
inExtCtxM tp (PermCheckM m) =
  PermCheckM $ ReaderT $ \env -> runReaderT m $ extEnv1 tp env

-- | Type constructors from which we can extract a permission set
class HasPerms f where
  hasPerms :: f ctx -> PermSet ctx

hasCtx :: HasPerms f => f ctx -> CtxRepr ctx
hasCtx = permSetCtx . hasPerms

instance HasPerms PermSet where
  hasPerms = id

instance HasPerms (ImplRet vars) where
  hasPerms = implPermsRem

instance HasPerms (TypedJumpTarget blocks) where
  hasPerms = targetInputPerms

instance HasPerms (ExprPerms ret) where
  hasPerms (ExprPerms perms _) = perms

-- | Map a function over a permission elimination
mapElimM :: HasPerms f =>
            (forall ctx'. Diff ctx ctx' -> f ctx' ->
             PermCheckM blocks ret ctx' (g ctx')) ->
            PermElim f ctx ->
            PermCheckM blocks ret ctx (PermElim g ctx)
mapElimM f elim =
  PermCheckM $ ReaderT $ \env ->
  traverseElim (\diff x ->
                 runReaderT (unPermCheckM $ f diff x) $
                 weakenEnvSetPerms (hasPerms x) (weakeningOfDiff diff) env)
  elim

getCurPerms :: PermCheckM blocks ret ctx (PermSet ctx)
getCurPerms = envCurPerms <$> ask

getCtx :: PermCheckM blocks ret ctx (CtxRepr ctx)
getCtx = permSetCtx <$> getCurPerms

getRetPerms :: PermCheckM blocks ret ctx (PermSetSpec EmptyCtx (ctx ::> ret))
getRetPerms = envRetPerms <$> ask

getBlockInfo :: BlockID blocks args ->
                PermCheckM blocks ret ctx (BlockInfo blocks ret args)
getBlockInfo blkID = (! blockIDIndex blkID) <$> stBlockInfo <$> get

-- | Get the index for the next entrypoint for a block, returning 'Nothing' if
-- this block has already been visited
blockNextEntryIndex :: BlockID blocks args ->
                       PermCheckM blocks ret ctx (Maybe Int)
blockNextEntryIndex blkID =
  getBlockInfo blkID >>= \info ->
  if blockInfoVisited info then return Nothing else
    return $ Just $ length $ blockInfoEntries info

-- | Add a new entry point for a block, or raise an error if that block has
-- already been visited
addBlockEntry :: BlockEntryInfo blocks ret args ->
                 PermCheckM blocks ret ctx ()
addBlockEntry info =
  modify $ \st ->
  st { stBlockInfo =
         Lens.over
         (ixF $ blockIDIndex $ entryInfoBlockID info)
         (\blkInfo ->
           if blockInfoVisited blkInfo then
             error "addBlockEntry: block already visited"
           else
             if entryInfoIndex info == length (blockInfoEntries blkInfo) then
               blkInfo { blockInfoEntries =
                           blockInfoEntries blkInfo ++ [info]}
             else
               error "addBlockEntry: incorrect index for newly-added entrypoint")
         (stBlockInfo st)
     }


-- | "Type-check" a 'Reg' by converting it to a 'PermVar'
tcReg :: Reg ctx a -> PermCheckM blocks ret ctx (PermVar ctx a)
tcReg reg = PermVar <$> (permSetSize <$> getCurPerms) <*> return (regIndex reg)

-- | The input and output permissions for an expression in the current branch of
-- a permission elimination
data ExprPerms ret ctx =
  ExprPerms (PermSet ctx) (PermSet (ctx ::> ret))

-- | Type-check a Crucible expression
tcExpr :: Expr ext ctx tp ->
          PermCheckM blocks ret ctx (PermElim (ExprPerms tp) ctx)
tcExpr _ = error "FIXME HERE: tcExpr"


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


data VarPair ctx a = VarPair (PermVar ctx a) (PermVar ctx a)

-- FIXME: figure out how to "thin out" the input permissions to a jump target
buildInputSpecs :: PermSet ctx -> CtxRepr args ->
                   Assignment (Reg ctx) args ->
                   (PermSetSpec EmptyCtx (ctx <+> args), AnnotIntro ctx)
buildInputSpecs perms args_ctx (args :: Assignment (Reg ctx) args) =
  let sz_ctx = permSetSize perms
      sz_args = size args
      sz_ctx_args = addSize sz_ctx sz_args
      args_xs :: [Some (Product (PermVar (ctx <+> args))
                        (PermVar (ctx <+> args)))]
      args_xs =
        toListFC Some $
        generate (size args) $ \ix ->
        Pair (PermVar sz_ctx_args $ extendIndexLeft sz_ctx ix)
        (PermVar sz_ctx_args $
         extendIndex' (appendDiff sz_args) $ regIndex $ args ! ix)
      perm_specs =
        -- Build a list of permission specs arg:eq(x) for each arg |-> x in args
        map (\(Some (Pair arg x)) ->
              PermSpec zeroSize (PExpr_Var arg) (ValPerm_Eq $ PExpr_Var x))
        args_xs
        ++
        -- Build a list of permissions x:p for all the permissions in perms
        map (extendContext $ appendDiff (size args))
        (permSpecOfPerms zeroSize (permSetAsgn perms)) in
  (perm_specs
  , AnnotIntro perms (map
                      (substPermSpec
                       (mkSubstMulti sz_ctx sz_args $
                        fmapFC (PExpr_Var . PermVar sz_ctx . regIndex) args))
                      perm_specs) $
    foldrFC
    (\x -> Intro_Eq (EqProof_Refl (PExpr_Var x)))
    (Intro_Id $ varPermsOfPermSet perms)
    (generate sz_ctx (\ix -> PermVar sz_ctx ix))
  )


-- | Type-check a 'JumpTarget' as follows:
--
-- 1. If the target block has not already been visited, add a new entry point
-- with all the current variables as ghost inputs and all the current
-- permissions as the permissions.
--
-- 2. Otherwise, if the target block has already been visited, build an
-- elimination that tries all of the possible entry points.
tcJumpTarget :: JumpTarget blocks ctx ->
                PermCheckM blocks ret ctx (PermElim (TypedJumpTarget blocks) ctx)
tcJumpTarget (JumpTarget blkID args_ctx args) =
  blockNextEntryIndex blkID >>= \maybe_ix ->
  case maybe_ix of
    Just ix ->
      do perms <- getCurPerms
         retPerms <- getRetPerms
         let ghosts = permSetCtx perms
             diff_ctx_args =
               appendDiff (size args_ctx) -- :: Diff ctx (ctx <+> args)
             entryInfoID = TypedEntryID blkID ghosts ix
             (entryInfoPermsIn, intro) = buildInputSpecs perms args_ctx args
         entryInfoPermsOut <-
           map (weaken $ Weakening diff_ctx_args $ incSize zeroSize) <$>
           getRetPerms
         let entry = BlockEntryInfo { .. }
         addBlockEntry entry
         return $ Elim_Done $
           TypedJumpTarget entryInfoID
           (TypedArgs (ghosts <++> args_ctx)
            (generate (size ghosts) (PermVar (size ghosts)) <++>
             fmapFC (PermVar (size ghosts) . regIndex) args)
            intro)
    Nothing ->
      error "FIXME HERE: cannot yet handle back edges!"

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
         (inExtCtxM tp $ withPerms perms_out $
          tcStmtSeq (weakenStmtSeq (incSize $ permSetSize perms)
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
                (extendWithCtx (hasCtx typed_tgt2) diff2 typed_tgt1)
                typed_tgt2
                )
              elim_tgt2)
       elim_tgt1
     typedElimStmt elim_stmts

tcStmtSeq (TermStmt l (Return reg)) =
  do perms <- getCurPerms
     retPerms <- getRetPerms
     x <- tcReg reg
     let spec_s = mkSubst1 (permSetSize perms) (PExpr_Var x)
         specs = map (substPermSpec spec_s) retPerms
         elim_intro = provePermImpl perms empty specs
     elim_stmts <-
       mapElimM (\diff (ImplRet _ _ intro) ->
                  return $ TypedTermStmt l $
                  TypedReturn (extendContext' diff x) intro)
       elim_intro
     typedElimStmt elim_stmts
