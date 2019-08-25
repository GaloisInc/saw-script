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
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ConstraintKinds #-}

module SAWScript.Heapster.TypedCrucible where

import Data.Maybe
import Data.Text hiding (length)
import Data.Type.Equality
import Data.Functor.Identity
import Data.Functor.Compose
-- import Data.Functor.Const
-- import Data.Functor.Product
-- import Data.Parameterized.Context
import Data.Kind
import GHC.TypeLits
import What4.ProgramLoc

import Control.Lens hiding ((:>),Index)
import Control.Monad.State
import Control.Monad.Reader

import Text.PrettyPrint.ANSI.Leijen (pretty)

import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Data.Parameterized.Context hiding ((:>), empty, take, view)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

-- import Data.Parameterized.TraversableFC
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Arch.X86
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.Analysis.Fixpoint.Components

import SAWScript.Heapster.CruUtil
import SAWScript.Heapster.Permissions
import SAWScript.Heapster.Implication


----------------------------------------------------------------------
-- * Typed Jump Targets and Function Handles
----------------------------------------------------------------------

-- | During type-checking, we convert Crucible registers to variables
newtype TypedReg tp = TypedReg { typedRegVar :: ExprVar tp }

-- | A type-checked Crucible expression is a Crucible 'Expr' that uses
-- 'TypedReg's for variables
newtype TypedExpr ext tp = TypedExpr (App ext TypedReg tp)

-- | A "typed" function handle is a normal function handle along with an index
-- of which typing of that function handle we are using, in case there are
-- multiples (just like 'TypedEntryID', below)
data TypedFnHandle ghosts args ret where
  TypedFnHandle :: CruCtx ghosts -> FnHandle cargs ret -> Int ->
                   TypedFnHandle ghosts (CtxToRList cargs) ret

-- | All of our blocks have multiple entry points, for different inferred types,
-- so a "typed" 'BlockID' is a normal Crucible 'BlockID' (which is just an index
-- into the @blocks@ context of contexts) plus an 'Int' specifying which entry
-- point to that block. Each entry point also takes an extra set of "ghost"
-- arguments, not extant in the original program, that are needed to express
-- input and output permissions.
data TypedEntryID (blocks :: RList (RList CrucibleType)) args ghosts =
  TypedEntryID { entryBlockID :: Member blocks args,
                 entryGhosts :: CruCtx ghosts,
                 entryIndex :: Int }

instance TestEquality (TypedEntryID blocks args) where
  testEquality (TypedEntryID memb1 ghosts1 i1) (TypedEntryID memb2 ghosts2 i2)
    | memb1 == memb2 && i1 == i2 = testEquality ghosts1 ghosts2
  testEquality _ _ = Nothing

-- | A typed target for jump and branch statements, where the arguments
-- (including ghost arguments) are given with their permissions as a 'DistPerms'
data TypedJumpTarget blocks ps where
     TypedJumpTarget ::
       TypedEntryID blocks args ghosts ->
       CruCtx args ->
       DistPerms (ghosts :++: args) ->
       TypedJumpTarget blocks ps_in


$(mkNuMatching [t| forall tp. TypedReg tp |])

instance NuMatchingAny1 TypedReg where
  nuMatchingAny1Proof = nuMatchingProof

type NuMatchingExtC ext =
  (NuMatchingAny1 (ExprExtension ext TypedReg)
   -- , NuMatchingAny1 (StmtExtension ext TypedReg)
  )

$(mkNuMatching [t| forall ext tp. NuMatchingExtC ext => TypedExpr ext tp |])
$(mkNuMatching [t| forall ghosts args ret. TypedFnHandle ghosts args ret |])
$(mkNuMatching [t| forall blocks ghosts args. TypedEntryID blocks args ghosts |])
$(mkNuMatching [t| forall blocks ps_in. TypedJumpTarget blocks ps_in |])

instance NuMatchingAny1 (TypedJumpTarget blocks) where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| AVXOp1 |])
$(mkNuMatching [t| forall f tp. NuMatchingAny1 f => ExtX86 f tp |])
$(mkNuMatching [t| forall arch f tp. NuMatchingAny1 f =>
                LLVMExtensionExpr arch f tp |])

instance NuMatchingAny1 f => NuMatchingAny1 (LLVMExtensionExpr arch f) where
  nuMatchingAny1Proof = nuMatchingProof

{-
$(mkNuMatching [t| forall w f tp. NuMatchingAny1 f => LLVMStmt w f tp |])
-}


----------------------------------------------------------------------
-- * Typed Crucible Statements
----------------------------------------------------------------------

-- | Typed Crucible statements with the given Crucible syntax extension and the
-- given set of return values
data TypedStmt ext (rets :: RList CrucibleType) ps_out ps_in where

  -- | Assign a pure value to a register, where pure here means that its
  -- translation to SAW will be pure (i.e., no LLVM pointer operations)
  TypedSetReg :: TypeRepr tp -> TypedExpr ext tp ->
                 TypedStmt ext (RNil :> tp) RNil RNil

  -- | Assert a boolean condition, printing the given string on failure
  TypedAssert :: TypedReg BoolType -> TypedReg StringType ->
                 TypedStmt ext RNil RNil RNil

  TypedLLVMStmt :: TypedLLVMStmt (ArchWidth arch) ret ps_out ps_in ->
                   TypedStmt (LLVM arch) (RNil :> ret) ps_out ps_in


data TypedLLVMStmt wptr ret ps_out ps_in where
  -- | Assign an LLVM word (i.e., a pointer with block 0) to a register
  ConstructLLVMWord :: (1 <= w, KnownNat w) =>
                       TypedReg (BVType w) ->
                       TypedLLVMStmt wptr (LLVMPointerType w) RNil RNil

  -- | Assert that an LLVM pointer is a word, and return 0 (this is the typed
  -- version of 'LLVM_PointerBlock' on words)
  AssertLLVMWord :: (1 <= w, KnownNat w) =>
                    TypedReg (LLVMPointerType w) ->
                    TypedLLVMStmt wptr NatType
                    (RNil :> LLVMPointerType w)
                    (RNil :> LLVMPointerType w)

  -- | Destruct an LLVM word into its bitvector value, which should equal the
  -- given expression
  DestructLLVMWord :: (1 <= w, KnownNat w) =>
                      TypedReg (LLVMPointerType w) -> PermExpr (BVType w) ->
                      TypedLLVMStmt wptr (BVType w)
                      (RNil :> LLVMPointerType w)
                      (RNil :> LLVMPointerType w)

  -- FIXME: add Alignment to loads and stores
  TypedLLVMLoad :: (TypedReg (LLVMPointerType wptr)) ->
                   TypedLLVMStmt wptr (LLVMPointerType wptr)
                   (RNil :> LLVMPointerType wptr :> LLVMPointerType wptr)
                   (RNil :> LLVMPointerType wptr)

  TypedLLVMStore :: (TypedReg (LLVMPointerType wptr)) ->
                    (TypedReg (LLVMPointerType wptr)) ->
                    TypedLLVMStmt wptr UnitType
                    (RNil :> LLVMPointerType wptr)
                    (RNil :> LLVMPointerType wptr)

  -- | Allocate an object of the given size on the given LLVM frame
  TypedLLVMAlloca :: TypedReg (LLVMFrameType wptr) -> Integer ->
                     TypedLLVMStmt wptr (LLVMPointerType wptr)
                     (RNil :> LLVMPointerType wptr) RNil

  -- | Create a new LLVM frame
  TypedLLVMCreateFrame :: TypedLLVMStmt wptr (LLVMFrameType wptr) RNil RNil

  -- | Delete an LLVM frame and deallocate all memory objects allocated in it,
  -- assuming that the current distinguished permissions @ps@ correspond to the
  -- write permissions to all those objects allocated on the frame
  TypedLLVMDeleteFrame :: TypedReg (LLVMFrameType wptr) ->
                          TypedLLVMStmt wptr UnitType RNil ps


-- | A @'StmtPermFun' rets ps_out ps_in@ is a function on permissions that
-- specifies how a typed statement with the given type arguments manipulates the
-- current permission set. Specifically, such a function takes a permission set
-- with distinguished permissions given by @ps_in@ to one with distinguished
-- permissions given by @ps_out@. The latter can also refer to the return values
-- of types @rets@ of the statement, and so takes in bound variables for these.
type StmtPermFun rets ps_out ps_in =
  (MapRList Name rets -> PermSet ps_in -> PermSet ps_out)

-- | The trivial permission function that does nothing
nullPermFun :: StmtPermFun rets RNil RNil
nullPermFun = const id

-- | Add permission @x:eq(expr)@
eqPermFun :: PermExpr tp -> StmtPermFun (RNil :> tp) ps ps
eqPermFun e (_ :>: x) = set (varPerm x) (ValPerm_Eq e)

-- | Take in permission @x:ptr((0,spl) |-> eq(e))@ and return that permission
-- along with permission @ret:eq(e)@, where @ret@ is the return value
llvmLoadPermFun :: (1 <= w, KnownNat w) => (TypedReg (LLVMPointerType w)) ->
                   StmtPermFun (RNil :> LLVMPointerType w)
                   (RNil :> LLVMPointerType w :> LLVMPointerType w)
                   (RNil :> LLVMPointerType w)
llvmLoadPermFun (TypedReg x) (_ :>: ret) perms =
  case llvmPtrIsField0 (perms ^. topDistPerm x ^. llvmPtrPerm 0) of
    Just (_, ValPerm_Eq e) -> pushPerm ret (ValPerm_Eq e) perms
    _ -> error "llvmLoadPermFun"

-- | Take in write permission @p:ptr((0,All) |-> _)@ and return the permission
-- @p:ptr((0,All) |-> eq(val))@, where @val@ is the value being stored
llvmStorePermFun :: (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
                    TypedReg (LLVMPointerType w) ->
                    StmtPermFun (RNil :> UnitType) (RNil :> LLVMPointerType w)
                    (RNil :> LLVMPointerType w)
llvmStorePermFun (TypedReg p) (TypedReg val) _ =
  over (topDistPerm p . llvmPtrPerm 0) $ \pp ->
  case llvmPtrIsField0 pp of
    Just (SplExpr_All, _) -> llvmFieldPerm0Eq SplExpr_All (PExpr_Var val)
    _ -> error "llvmLoadPermFun"

-- | Take in permissions @fp:frame(xs_lens)@ for the given frame pointer @fp@
-- and return permissions @fp:frame((ret,sz):xs_lens)@ and permissions
-- @ret:ptr((0,All) |-> true * .. * (sz - w/8,All) |-> true)@
llvmAllocaPermFun :: TypedReg (LLVMFrameType w) -> Integer ->
                     StmtPermFun (RNil :> LLVMPointerType w)
                     (RNil :> LLVMPointerType w) RNil
llvmAllocaPermFun (TypedReg fp) sz (_ :>: ret) perms =
  case perms ^. varPerm fp of
    ValPerm_LLVMFrame frm ->
      set (varPerm fp) (ValPerm_LLVMFrame ((PExpr_Var ret,sz):frm)) $
      pushPerm ret (llvmPtrPermOfSize sz) perms

-- | Add permissions to allocate on the newly-created frame
llvmCreateFramePermFun :: (1 <= w, KnownNat w) =>
                          StmtPermFun (RNil :> LLVMFrameType w) RNil RNil
llvmCreateFramePermFun (_ :>: fp) =
  set (varPerm fp) (ValPerm_LLVMFrame [])

-- | Ensure that the current distinguished permissions equal those required to
-- delete the given frame, and then delete those distinguished permissions and
-- the frame permissions
llvmDeleteFramePermFun :: TypedReg (LLVMFrameType wptr) ->
                          StmtPermFun (RNil :> UnitType) RNil ps
llvmDeleteFramePermFun (TypedReg fp) _  = deleteLLVMFrame fp


----------------------------------------------------------------------
-- * Typed Sequences of Crucible Statements
----------------------------------------------------------------------

-- | Typed return argument
data TypedRet ret ps = TypedRet (TypedReg ret) (DistPerms ps)


-- | Typed Crucible block termination statements
data TypedTermStmt blocks ret ps_in where
  -- | Jump to the given jump target
  TypedJump :: PermImpl (TypedJumpTarget blocks) ps_in ->
               TypedTermStmt blocks ret ps_in

  -- | Branch on condition: if true, jump to the first jump target, and
  -- otherwise jump to the second jump target
  TypedBr :: TypedReg BoolType ->
             PermImpl (TypedJumpTarget blocks) ps_in ->
             PermImpl (TypedJumpTarget blocks) ps_in ->
             TypedTermStmt blocks ret ps_in

  -- | Return from function, providing the return value and also proof that the
  -- current permissions imply the required return permissions
  TypedReturn :: PermImpl (TypedRet ret) ps_in ->
                 TypedTermStmt blocks ret ps_in

  -- | Block ends with an error
  TypedErrorStmt :: TypedReg StringType -> TypedTermStmt blocks ret ps_in


-- | A typed sequence of Crucible statements
data TypedStmtSeq ext blocks ret ps_in where
  -- | A permission implication step, which modifies the current permission
  -- set. This can include pattern-matches and/or assertion failures.
  TypedImplStmt :: PermImpl (TypedStmtSeq ext blocks ret) ps_in ->
                   TypedStmtSeq ext blocks ret ps_in

  -- | Typed version of 'ConsStmt', which binds new variables for the return
  -- value(s) of each statement
  TypedConsStmt :: ProgramLoc ->
                   TypedStmt ext rets ps_next ps_in ->
                   Mb rets (TypedStmtSeq ext blocks ret ps_next) ->
                   TypedStmtSeq ext blocks ret ps_in

  -- | Typed version of 'TermStmt', which terminates the current block
  TypedTermStmt :: ProgramLoc ->
                   TypedTermStmt blocks ret ps_in ->
                   TypedStmtSeq ext blocks ret ps_in


$(mkNuMatching [t| forall wptr tp ps_out ps_in.
                TypedLLVMStmt wptr tp ps_out ps_in |])
$(mkNuMatching [t| forall ext rets ps_out ps_in. NuMatchingExtC ext =>
                TypedStmt ext rets ps_out ps_in |])
$(mkNuMatching [t| forall ret ps. TypedRet ret ps |])

instance NuMatchingAny1 (TypedRet ret) where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| forall blocks ret ps_in. TypedTermStmt blocks ret ps_in |])
$(mkNuMatching [t| forall ext blocks ret ps_in.
                NuMatchingExtC ext => TypedStmtSeq ext blocks ret ps_in |])

instance NuMatchingExtC ext => NuMatchingAny1 (TypedStmtSeq ext blocks ret) where
  nuMatchingAny1Proof = nuMatchingProof


----------------------------------------------------------------------
-- * Typed Control-Flow Graphs
----------------------------------------------------------------------

-- | A single, typed entrypoint to a Crucible block. Note that our blocks
-- implicitly take extra "ghost" arguments, that are needed to express the input
-- and output permissions.
--
-- FIXME: add a @ghostss@ type argument that associates a @ghosts@ type with
-- each index of each block, rather than having @ghost@ existentially bound
-- here.
data TypedEntry ext blocks ret args where
  TypedEntry ::
    TypedEntryID blocks args ghosts -> CruCtx args ->
    MbDistPerms (ghosts :++: args) ->
    Mb (ghosts :++: args) (TypedStmtSeq ext blocks ret (ghosts :++: args)) ->
    TypedEntry ext blocks ret args

-- | A typed Crucible block is a list of typed entrypoints to that block
newtype TypedBlock ext blocks ret args
  = TypedBlock [TypedEntry ext blocks ret args]

-- | A map assigning a 'TypedBlock' to each 'BlockID'
type TypedBlockMap ext blocks ret =
  MapRList (TypedBlock ext blocks ret) blocks

-- | A typed Crucible CFG
data TypedCFG
     (ext :: Type)
     (blocks :: RList (RList CrucibleType))
     (ghosts :: RList CrucibleType)
     (inits :: RList CrucibleType)
     (ret :: CrucibleType)
  = TypedCFG { tpcfgHandle :: TypedFnHandle ghosts inits ret
             , tpcfgInputPerms :: MbValuePerms (ghosts :++: inits)
             , tpcfgOutputPerms :: MbValuePerms (ghosts :++: inits :> ret)
             , tpcfgBlockMap :: TypedBlockMap ext blocks ret
             , tpcfgEntryBlockID :: TypedEntryID blocks inits ghosts
             }


----------------------------------------------------------------------
-- * Monad(s) for Permission Checking
----------------------------------------------------------------------

-- | A translation of a Crucible context to 'TypedReg's that exist in the local
-- Hobbits context
type CtxTrans ctx = Assignment TypedReg ctx

-- | Build a Crucible context translation from a set of variables
mkCtxTrans :: Assignment f ctx -> MapRList Name (CtxToRList ctx) -> CtxTrans ctx
mkCtxTrans (viewAssign -> AssignEmpty) _ = Ctx.empty
mkCtxTrans (viewAssign -> AssignExtend ctx' _) (ns :>: n) =
  extend (mkCtxTrans ctx' ns) (TypedReg n)

-- | Add a variable to the current Crucible context translation
addCtxName :: CtxTrans ctx -> ExprVar tp -> CtxTrans (ctx ::> tp)
addCtxName ctx x = extend ctx (TypedReg x)

-- | GADT telling us that @ext@ is a syntax extension we can handle
data ExtRepr ext where
  ExtRepr_Unit :: ExtRepr ()
  ExtRepr_LLVM :: (1 <= ArchWidth arch, KnownNat (ArchWidth arch)) =>
                  ExtRepr (LLVM arch)

instance KnownRepr ExtRepr () where
  knownRepr = ExtRepr_Unit

instance (1 <= ArchWidth arch, KnownNat (ArchWidth arch)) =>
         KnownRepr ExtRepr (LLVM arch) where
  knownRepr = ExtRepr_LLVM

-- | The constraints for a Crucible syntax extension that supports permission
-- checking
type PermCheckExtC ext =
  (NuMatchingExtC ext, IsSyntaxExtension ext, KnownRepr ExtRepr ext)

-- | Extension-specific state
data PermCheckExtState ext where
  -- | The extension-specific state for LLVM is the current frame pointer, if it
  -- exists
  PermCheckExtState_Unit :: PermCheckExtState ()
  PermCheckExtState_LLVM :: Maybe (TypedReg (LLVMFrameType (ArchWidth arch))) ->
                            PermCheckExtState (LLVM arch)

-- | Create a default empty extension-specific state object
emptyPermCheckExtState :: ExtRepr ext -> PermCheckExtState ext
emptyPermCheckExtState ExtRepr_Unit = PermCheckExtState_Unit
emptyPermCheckExtState ExtRepr_LLVM = PermCheckExtState_LLVM Nothing

-- | Permissions needed on return from a function
newtype RetPerms (ret :: CrucibleType) ps =
  RetPerms { unRetPerms :: Binding ret (DistPerms ps) }

-- | The local state maintained while type-checking is the current permission
-- set and the permissions required on return from the entire function.
data PermCheckState ext args ret ps =
  PermCheckState
  {
    stCurPerms :: PermSet ps,
    stExtState :: PermCheckExtState ext,
    stRetPerms :: Some (RetPerms ret),
    stVarTypes :: NameMap CruType
  }

-- | Like the 'set' method of a lens, but allows the @ps@ argument to change
setSTCurPerms :: PermSet ps2 -> PermCheckState ext args ret ps1 ->
                 PermCheckState ext args ret ps2
setSTCurPerms perms (PermCheckState {..}) =
  PermCheckState { stCurPerms = perms, .. }

modifySTCurPerms :: (PermSet ps1 -> PermSet ps2) ->
                    PermCheckState ext args ret ps1 ->
                    PermCheckState ext args ret ps2
modifySTCurPerms f_perms st = setSTCurPerms (f_perms $ stCurPerms st) st

-- | The information needed to type-check a single entrypoint of a block
data BlockEntryInfo blocks ret args where
  BlockEntryInfo :: {
    entryInfoID :: TypedEntryID blocks args ghosts,
    entryInfoArgs :: CruCtx args,
    entryInfoPermsIn :: MbDistPerms (ghosts :++: args),
    entryInfoPermsOut :: Mb (ghosts :++: args) (RetPerms ret ret_ps)
  } -> BlockEntryInfo blocks ret args

-- | Extract the 'BlockID' from entrypoint info
entryInfoBlockID :: BlockEntryInfo blocks ret args -> Member blocks args
entryInfoBlockID (BlockEntryInfo entryID _ _ _) = entryBlockID entryID

-- | Extract the entry id from entrypoint info
entryInfoIndex :: BlockEntryInfo blocks ret args -> Int
entryInfoIndex (BlockEntryInfo entryID _ _ _) = entryIndex entryID

-- | Information about the current state of type-checking for a block
data BlockInfo ext blocks ret args =
  BlockInfo
  {
    blockInfoMember :: Member blocks args,
    blockInfoEntries :: [BlockEntryInfo blocks ret args],
    blockInfoBlock :: Maybe (TypedBlock ext blocks ret args)
  }

-- | Test if a block has been type-checked yet, which is true iff its
-- translation has been stored in its info yet
blockInfoVisited :: BlockInfo ext blocks ret args -> Bool
blockInfoVisited (BlockInfo { blockInfoBlock = Just _ }) = True
blockInfoVisited _ = False

-- | Add a new 'BlockEntryInfo' to a 'BlockInfo' and return its 'TypedEntryID'.
-- This assumes that the block has not been visited; if it has, it is an error.
blockInfoAddEntry :: CruCtx args -> CruCtx ghosts ->
                     MbDistPerms (ghosts :++: args) ->
                     Mb (ghosts :++: args) (RetPerms ret ret_ps) ->
                     BlockInfo ext blocks ret args ->
                     (BlockInfo ext blocks ret args,
                      TypedEntryID blocks args ghosts)
blockInfoAddEntry args ghosts perms_in perms_out info =
  if blockInfoVisited info then error "blockInfoAddEntry" else
    let entries = blockInfoEntries info
        entryID = TypedEntryID (blockInfoMember info) ghosts (length entries) in
    (info { blockInfoEntries =
              entries ++ [BlockEntryInfo entryID args perms_in perms_out] },
     entryID)

type BlockInfoMap ext blocks ret = MapRList (BlockInfo ext blocks ret) blocks

-- | Build an empty 'BlockInfoMap' from an assignment
emptyBlockInfoMap :: Assignment f blocks ->
                     BlockInfoMap ext (CtxCtxToRList blocks) ret
emptyBlockInfoMap asgn =
  mapMapRList (\memb -> BlockInfo memb [] Nothing) (helper asgn)
  where
    helper :: Assignment f ctx ->
              MapRList (Member (CtxCtxToRList ctx)) (CtxCtxToRList ctx)
    helper (viewAssign -> AssignEmpty) = MNil
    helper (viewAssign -> AssignExtend asgn _) =
      mapMapRList Member_Step (helper asgn) :>: Member_Base

-- | Add a new 'BlockEntryInfo' to a block info map, returning the newly updated
-- map and the new 'TypedEntryID'. This assumes that the block has not been
-- visited; if it has, it is an error.
blockInfoMapAddEntry :: Member blocks args -> CruCtx args -> CruCtx ghosts ->
                        MbDistPerms (ghosts :++: args) ->
                        Mb (ghosts :++: args) (RetPerms ret ret_ps) ->
                        BlockInfoMap ext blocks ret ->
                        (BlockInfoMap ext blocks ret,
                         TypedEntryID blocks args ghosts)
blockInfoMapAddEntry memb args ghosts perms_in perms_out blkMap =
  let blkInfo = mapRListLookup memb blkMap
      (blkInfo', entryID) =
        blockInfoAddEntry args ghosts perms_in perms_out blkInfo in
  (mapRListSet memb blkInfo' blkMap, entryID)

-- | Set the 'TypedBlock' for a given block id, thereby marking it as
-- visited. It is an error if it is already set.
blockInfoMapSetBlock :: Member blocks args -> TypedBlock ext blocks ret args ->
                        BlockInfoMap ext blocks ret ->
                        BlockInfoMap ext blocks ret
blockInfoMapSetBlock memb blk =
  mapRListModify memb $ \info ->
  if blockInfoVisited info then
    error "blockInfoMapSetBlock: block already set"
  else
    info { blockInfoBlock = Just blk }


-- | The translation of a Crucible block id
newtype BlockIDTrans blocks args =
  BlockIDTrans { unBlockIDTrans :: Member blocks (CtxToRList args) }

extendBlockIDTrans :: BlockIDTrans blocks args ->
                      BlockIDTrans (blocks :> tp) args
extendBlockIDTrans (BlockIDTrans memb) = BlockIDTrans $ Member_Step memb

-- | Build a map from Crucible block IDs to 'Member' proofs
buildBlockIDMap :: Assignment f cblocks ->
                   Assignment (BlockIDTrans (CtxCtxToRList cblocks)) cblocks
buildBlockIDMap (viewAssign -> AssignEmpty) = Ctx.empty
buildBlockIDMap (viewAssign -> AssignExtend asgn _) =
  Ctx.extend (fmapFC extendBlockIDTrans $ buildBlockIDMap asgn)
  (BlockIDTrans Member_Base)

-- | Top-level state, maintained outside of permission-checking single blocks
data TopPermCheckState ext cblocks blocks ret =
  TopPermCheckState
  {
    stBlockTrans :: Closed (Assignment (BlockIDTrans blocks) cblocks),
    stBlockInfo :: Closed (BlockInfoMap ext blocks ret)
  }

$(mkNuMatching [t| forall ext cblocks blocks ret.
                TopPermCheckState ext cblocks blocks ret |])

instance Closable (TopPermCheckState ext cblocks blocks ret) where
  toClosed (TopPermCheckState {..}) =
    $(mkClosed [| TopPermCheckState |]) `clApplyCl` stBlockTrans
    `clApplyCl` stBlockInfo

instance BindState (TopPermCheckState ext cblocks blocks ret) where
  bindState [nuP| TopPermCheckState bt i |] =
    TopPermCheckState (mbLift bt) (mbLift i)

-- | Build an empty 'TopPermCheckState' from a Crucible 'BlockMap'
emptyTopPermCheckState ::
  BlockMap ext cblocks ret ->
  TopPermCheckState ext cblocks (CtxCtxToRList cblocks) ret
emptyTopPermCheckState blkMap =
  TopPermCheckState
  { stBlockTrans =
    $(mkClosed [| buildBlockIDMap |]) `clApply` (closeAssign toClosed blkMap)
  , stBlockInfo =
    $(mkClosed [| emptyBlockInfoMap |]) `clApply` (closeAssign toClosed blkMap)
  }


-- | Look up a Crucible block id in a top-level perm-checking state
stLookupBlockID :: BlockID cblocks args ->
                   TopPermCheckState ext cblocks blocks ret ->
                   Member blocks (CtxToRList args)
stLookupBlockID (BlockID ix) st=
  unBlockIDTrans $ unClosed (stBlockTrans st) Ctx.! ix

-- | The top-level monad for permission-checking CFGs
type TopPermCheckM ext cblocks blocks ret =
  State (TopPermCheckState ext cblocks blocks ret)

{-
-- | A datakind for the type-level parameters needed to define blocks, including
-- the @ext@, @blocks@, @ret@ and @args@ arguments
data BlkParams =
  BlkParams Type (RList (RList CrucibleType)) CrucibleType (RList CrucibleType)

type family BlkExt (args :: BlkParams) :: Type where
  BlkExt ('BlkParams ext _ _ _) = ext

type family BlkBlocks (args :: BlkParams) :: (RList (RList CrucibleType)) where
  BlkBlocks ('BlkParams _ blocks _ _) = blocks

type family BlkRet (args :: BlkParams) :: CrucibleType where
  BlkRet ('BlkParams _ _ ret _) = ret

type family BlkArgs (args :: BlkParams) :: RList CrucibleType where
  BlkArgs ('BlkParams _ _ _ args) = args
-}

-- | The generalized monad for permission-checking
type PermCheckM ext cblocks blocks ret args r1 ps1 r2 ps2 =
  GenStateContM (PermCheckState ext args ret ps1)
  (TopPermCheckM ext cblocks blocks ret r1)
  (PermCheckState ext args ret ps2)
  (TopPermCheckM ext cblocks blocks ret r2)

-- | The generalized monad for permission-checking statements
type StmtPermCheckM ext cblocks blocks ret args ps1 ps2 =
  PermCheckM ext cblocks blocks ret args
   (TypedStmtSeq ext blocks ret ps1) ps1
   (TypedStmtSeq ext blocks ret ps2) ps2

liftPermCheckM :: TopPermCheckM ext cblocks blocks ret a ->
                  PermCheckM ext cblocks blocks ret args r ps r ps a
liftPermCheckM m = gcaptureCC $ \k -> m >>= k

runPermCheckM :: KnownRepr ExtRepr ext =>
                 PermSet ps_in -> RetPerms ret ret_ps ->
                 PermCheckM ext cblocks blocks ret args () ps_out r ps_in () ->
                 TopPermCheckM ext cblocks blocks ret r
runPermCheckM perms ret_perms m =
  let st = PermCheckState {
        stCurPerms = perms,
        stExtState = emptyPermCheckExtState knownRepr,
        stRetPerms = Some ret_perms,
        stVarTypes = NameMap.empty } in
  runGenContM (runGenStateT m st) (const $ return ())


-- | Get the current top-level state
top_get :: PermCheckM ext cblocks blocks ret args r ps r ps
           (TopPermCheckState ext cblocks blocks ret)
top_get = gcaptureCC $ \k -> get >>= k

-- | Set the current top-level state
top_put :: TopPermCheckState ext cblocks blocks ret ->
           PermCheckM ext cblocks blocks ret args r ps r ps ()
top_put s = gcaptureCC $ \k -> put s >>= k

lookupBlockInfo :: Member blocks args ->
                   PermCheckM ext cblocks blocks ret args_in r ps r ps
                   (BlockInfo ext blocks ret args)
lookupBlockInfo memb =
  top_get >>>= \top_st ->
  greturn (mapRListLookup memb $ unClosed $ stBlockInfo top_st)

insNewBlockEntry :: Member blocks args -> CruCtx args -> CruCtx ghosts ->
                    Closed (MbDistPerms (ghosts :++: args)) ->
                    Closed (Mb (ghosts :++: args) (RetPerms ret ret_ps)) ->
                    TopPermCheckM ext cblocks blocks ret
                    (TypedEntryID blocks args ghosts)
insNewBlockEntry memb arg_tps ghost_tps perms_in perms_ret =
  do st <- get
     let cl_blkMap_entryID =
           $(mkClosed [| blockInfoMapAddEntry |])
           `clApply` toClosed memb `clApply` toClosed arg_tps
           `clApply` toClosed ghost_tps
           `clApply` perms_in `clApply` perms_ret `clApply` 
           stBlockInfo st
     put (st { stBlockInfo =
                 $(mkClosed [| fst |]) `clApply` cl_blkMap_entryID })
     return (snd $ unClosed cl_blkMap_entryID)


getVarPerm :: ExprVar a ->
              PermCheckM ext cblocks blocks ret args r ps r ps (ValuePerm a)
getVarPerm x = view (varPerm x) <$> stCurPerms <$> gget

getRegPerm :: TypedReg a ->
              PermCheckM ext cblocks blocks ret args r ps r ps (ValuePerm a)
getRegPerm (TypedReg x) = getVarPerm x

-- | Get the current frame pointer on LLVM architectures
getFramePtr :: PermCheckM (LLVM arch) cblocks blocks ret args r ps r ps
               (Maybe (TypedReg (LLVMFrameType (ArchWidth arch))))
getFramePtr = gget >>>= \st -> case stExtState st of
  PermCheckExtState_LLVM maybe_fp -> greturn maybe_fp

-- | Set the current frame pointer on LLVM architectures
setFramePtr :: TypedReg (LLVMFrameType (ArchWidth arch)) ->
               PermCheckM (LLVM arch) cblocks blocks ret args r ps r ps ()
setFramePtr fp =
  gmodify (\st -> st { stExtState = PermCheckExtState_LLVM (Just fp) })

-- | Look up the type of a free variable, or raise an error if it is unknown
getVarType :: ExprVar a ->
              PermCheckM ext cblocks blocks ret args r ps r ps (CruType a)
getVarType x =
  maybe (error "getVarType") id <$> NameMap.lookup x <$> stVarTypes <$> gget

-- | Look up the types of multiple free variables
getVarTypes :: MapRList Name tps ->
               PermCheckM ext cblocks blocks ret args r ps r ps (CruCtx tps)
getVarTypes MNil = greturn CruCtxNil
getVarTypes (xs :>: x) = CruCtxCons <$> getVarTypes xs <*> getVarType x

-- | Remember the type of a free variable
setVarType :: ExprVar a -> CruType a ->
              PermCheckM ext cblocks blocks ret args r ps r ps ()
setVarType x tp =
  gmodify $ \st ->
  st { stVarTypes = NameMap.insert x tp (stVarTypes st) }

-- | Remember the types of a sequence of free variables
setVarTypes :: MapRList Name tps -> CruCtx tps ->
               PermCheckM ext cblocks blocks ret args r ps r ps ()
setVarTypes _ CruCtxNil = greturn ()
setVarTypes (xs :>: x) (CruCtxCons tps tp) =
  setVarTypes xs tps >>> setVarType x tp

-- | Failure in the statement permission-checking monad
stmtFailM :: PermCheckM ext cblocks blocks ret args r1 ps1
             (TypedStmtSeq ext blocks ret ps2) ps2 a
stmtFailM = gabortM (return $ TypedImplStmt Impl_Fail)

-- | Smart constructor for applying a function on 'PermImpl's
applyImplFun :: (PermImpl r ps -> r ps) -> PermImpl r ps -> r ps
applyImplFun _ (Impl_Done r) = r
applyImplFun f impl = f impl

-- | Embed an implication computation inside a permission-checking computation
embedImplM :: (forall ps. PermImpl r ps -> r ps) -> CruCtx vars ->
              ImplM vars r ps_out ps_in a ->
              PermCheckM ext cblocks blocks ret args
              (r ps_out) ps_out (r ps_in) ps_in (PermSubst vars, a)
embedImplM f_impl vars m =
  top_get >>>= \top_st ->
  gget >>>= \st ->
  gmapRet (return . applyImplFun f_impl) >>>
  gput (mkImplState vars $ stCurPerms st) >>>
  m >>>= \a ->
  gget >>>= \implSt ->
  gput (setSTCurPerms (implSt ^. implStatePerms) st) >>>
  gmapRet (Impl_Done . flip evalState top_st) >>>
  greturn (completePSubst vars (implSt ^. implStatePSubst), a)

-- | Recombine any outstanding distinguished permissions back into the main
-- permission set, in the context of type-checking statements
stmtRecombinePerms :: StmtPermCheckM ext cblocks blocks ret args RNil ps_in ()
stmtRecombinePerms =
  embedImplM TypedImplStmt emptyCruCtx recombinePerms >>>= \_ ->
  greturn ()

-- | Prove permissions in the context of type-checking statements
stmtProvePerm :: (PermCheckExtC ext, KnownRepr CruCtx vars) =>
                 TypedReg a -> Mb vars (ValuePerm a) ->
                 StmtPermCheckM ext cblocks blocks ret args
                 (ps :> a) ps (PermSubst vars)
stmtProvePerm (TypedReg x) mb_p =
  embedImplM TypedImplStmt knownRepr (proveVarImpl x mb_p) >>>= \(s,_) ->
  greturn s

-- | Try to prove that a register equals a constant integer
resolveConstant :: KnownRepr TypeRepr tp => TypedReg tp ->
                   StmtPermCheckM ext cblocks blocks ret args ps ps
                   (Maybe Integer)
resolveConstant = error "FIXME HERE: resolveConstant"


----------------------------------------------------------------------
-- * Permission Checking for Expressions and Statements
----------------------------------------------------------------------

-- | Get a dynamic representation of a architecture's width
archWidth :: KnownNat (ArchWidth arch) => f arch -> NatRepr (ArchWidth arch)
archWidth _ = knownNat

-- | Translate a Crucible register by looking it up in the translated context
tcReg :: CtxTrans ctx -> Reg ctx tp -> TypedReg tp
tcReg ctx (Reg ix) = ctx ! ix

-- | Type-check a sequence of Crucible arguments into a 'TypedArgs' list
{-
tcArgs :: CtxTrans ctx -> CtxRepr args -> Assignment (Reg ctx) args ->
          TypedArgs (CtxToRList args)
tcArgs _ _ (viewAssign -> AssignEmpty) = TypedArgsNil
tcArgs ctx (viewAssign ->
            AssignExtend arg_tps' tp) (viewAssign -> AssignExtend args' reg) =
  withKnownRepr tp $
  TypedArgsCons (tcArgs ctx arg_tps' args') (tcReg ctx reg)
-}

-- | Type-check a Crucibe block id into a 'Member' proof
tcBlockID :: BlockID cblocks args ->
             StmtPermCheckM ext cblocks blocks ret args' ps ps
             (Member blocks (CtxToRList args))
tcBlockID blkID = stLookupBlockID blkID <$> top_get

-- | Translate a 'TypedExpr' to a permission expression, if possible
exprToPermExpr :: TypedExpr ext tp -> Maybe (PermExpr tp)
exprToPermExpr _ = error "FIXME HERE: exprToPermExpr!"

-- | Translate a Crucible expression
tcExpr :: PermCheckExtC ext => CtxTrans ctx -> Expr ext ctx tp ->
          StmtPermCheckM ext cblocks blocks ret args ps ps (TypedExpr ext tp)
tcExpr ctx (App (ExtensionApp e_ext :: App ext (Reg ctx) tp))
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = error "tcExpr: unexpected LLVM expression"
tcExpr ctx (App app) = greturn $ TypedExpr $ fmapFC (tcReg ctx) app


-- | Emit a statement in the current statement sequence, where the supplied
-- function says how that statement modifies the current permissions, given the
-- freshly-bound names for the return values. Return those freshly-bound names
-- for the return values.
emitStmt :: TypeCtx rets => CruCtx rets -> ProgramLoc ->
            StmtPermFun rets ps_out ps_in ->
            TypedStmt ext rets ps_out ps_in ->
            StmtPermCheckM ext cblocks blocks ret args ps_out ps_in
            (MapRList Name rets)
emitStmt tps loc f_perms stmt =
  gopenBinding
  ((TypedConsStmt loc stmt <$>) . strongMbM)
  (nuMulti typeCtxProxies $ \vars -> ()) >>>= \(ns, ()) ->
  setVarTypes ns tps >>>
  gmodify (modifySTCurPerms $ f_perms ns) >>>
  greturn ns

-- | Call emitStmt with a 'TypedLLVMStmt'
emitLLVMStmt :: TypeRepr tp -> ProgramLoc ->
                StmtPermFun (RNil :> tp) ps_out ps_in ->
                TypedLLVMStmt (ArchWidth arch) tp ps_out ps_in ->
                StmtPermCheckM (LLVM arch) cblocks blocks ret args ps_out ps_in
                (Name tp)
emitLLVMStmt tp loc f_perms stmt =
  emitStmt (singletonCruCtx tp)
  loc f_perms (TypedLLVMStmt stmt) >>>= \(_ :>: n) -> greturn n


-- | Typecheck a statement and emit it in the current statement sequence,
-- starting and ending with an empty stack of distinguished permissions
tcEmitStmt :: PermCheckExtC ext => CtxTrans ctx -> ProgramLoc ->
              Stmt ext ctx ctx' ->
              StmtPermCheckM ext cblocks blocks ret args RNil RNil
              (CtxTrans ctx')
tcEmitStmt ctx loc (SetReg tp e) =
  tcExpr ctx e >>>= \typed_e ->
  let perm_f = maybe nullPermFun eqPermFun (exprToPermExpr typed_e) in
  emitStmt (singletonCruCtx tp) loc
  perm_f (TypedSetReg tp typed_e) >>>= \(_ :>: x) ->
  greturn $ addCtxName ctx x

tcEmitStmt ctx loc (ExtendAssign stmt_ext :: Stmt ext ctx ctx')
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = tcEmitLLVMStmt Proxy ctx loc stmt_ext

tcEmitStmt _ _ _ = error "FIXME: tcEmitStmt!"


-- | Translate a Crucible assignment of an LLVM expression
tcEmitLLVMSetExpr ::
  (1 <= ArchWidth arch, KnownNat (ArchWidth arch)) => Proxy arch ->
  CtxTrans ctx -> ProgramLoc -> LLVMExtensionExpr arch (Reg ctx) tp ->
  StmtPermCheckM (LLVM arch) cblocks blocks ret args RNil RNil
  (CtxTrans (ctx ::> tp))

-- Type-check a pointer-building expression, which is only valid when the block
-- = 0, i.e., when building a word
tcEmitLLVMSetExpr arch ctx loc (LLVM_PointerExpr w blk_reg off_reg) =
  let toff_reg = tcReg ctx off_reg
      tblk_reg = tcReg ctx blk_reg in
  resolveConstant tblk_reg >>>= \maybe_const ->
  case maybe_const of
    Just 0 ->
      withKnownNat w $
      emitLLVMStmt knownRepr loc
      (eqPermFun $ PExpr_LLVMWord $ PExpr_Var $ typedRegVar toff_reg)
      (ConstructLLVMWord toff_reg) >>>= \x ->
      greturn $ addCtxName ctx x
    _ -> stmtFailM

-- Type-check the LLVM pointer destructor that gets the block, which is only
-- valid on LLVM words, i.e., when the block = 0
tcEmitLLVMSetExpr arch ctx loc (LLVM_PointerBlock w ptr_reg) =
  let tptr_reg = tcReg ctx ptr_reg in
  withKnownNat w $
  stmtProvePerm tptr_reg llvmExEqWord >>>= \_ ->
  emitLLVMStmt knownRepr loc
  (eqPermFun $ PExpr_Nat 0) (AssertLLVMWord tptr_reg) >>>= \x ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx x)

-- Type-check the LLVM pointer destructor that gets the offset, which is only
-- valid on LLVM words, i.e., when the block = 0
tcEmitLLVMSetExpr arch ctx loc (LLVM_PointerOffset w ptr_reg) =
  let tptr_reg = tcReg ctx ptr_reg in
  withKnownNat w $
  stmtProvePerm tptr_reg llvmExEqWord >>>= \subst ->
  let e = substLookup subst Member_Base in
  emitLLVMStmt knownRepr loc
  (eqPermFun e) (DestructLLVMWord tptr_reg e) >>>= \x ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx x)


-- | Typecheck a statement and emit it in the current statement sequence,
-- starting and ending with an empty stack of distinguished permissions
tcEmitLLVMStmt ::
  (1 <= ArchWidth arch, KnownNat (ArchWidth arch)) => Proxy arch ->
  CtxTrans ctx -> ProgramLoc -> LLVMStmt (ArchWidth arch) (Reg ctx) tp ->
  StmtPermCheckM (LLVM arch) cblocks blocks ret args RNil RNil
  (CtxTrans (ctx ::> tp))

-- Type-check a load of an LLVM pointer
tcEmitLLVMStmt arch ctx loc (LLVM_Load _ reg (LLVMPointerRepr w) _ _)
  | Just Refl <- testEquality w (archWidth arch)
  = let treg = tcReg ctx reg in
    stmtProvePerm treg llvmExRead0Perm >>>= \_ ->
    (emitLLVMStmt knownRepr loc
     (llvmLoadPermFun treg) (TypedLLVMLoad treg)) >>>= \y ->
    stmtRecombinePerms >>>
    greturn (addCtxName ctx y)

-- Type-check a load of a value that can be cast from an LLVM pointer, by
-- loading an LLVM pointer and then performing the cast
tcEmitLLVMStmt arch ctx loc (LLVM_Load _ reg tp storage _)
  | bytesToBits (storageTypeSize storage) <= natValue (archWidth arch)
  = error "FIXME HERE: call tcEmitLLVMStmt with LLVMPointerRepr (ArchWidth arch) and then coerce to tp!"

-- We canot yet handle other loads
tcEmitLLVMStmt _ _ _ (LLVM_Load _ _ _ _ _) =
  error "FIXME: tcEmitLLVMStmt cannot yet handle loads larger than the size of LLVM pointers"

-- Type-check a store of an LLVM pointer
tcEmitLLVMStmt arch ctx loc (LLVM_Store _ ptr (LLVMPointerRepr w) _ _ val)
  | Just Refl <- testEquality w (archWidth arch)
  = let tptr = tcReg ctx ptr
        tval = tcReg ctx val in
    stmtProvePerm tptr llvmExWrite0Perm >>>= \_ ->
    (emitLLVMStmt knownRepr loc (llvmStorePermFun tptr tval)
     (TypedLLVMStore tptr tval)) >>>= \y ->
    stmtRecombinePerms >>>
    greturn (addCtxName ctx y)

-- FIXME HERE: handle stores of values that can be converted to/from pointers

-- Type-check an alloca instruction
tcEmitLLVMStmt arch ctx loc (LLVM_Alloca w _ sz_reg _ _) =
  let sz_treg = tcReg ctx sz_reg in
  getFramePtr >>>= \maybe_fp ->
  resolveConstant sz_treg >>>= \maybe_sz ->
  case (maybe_fp, maybe_sz) of
    (Just fp, Just sz) ->
      (emitLLVMStmt knownRepr loc (llvmAllocaPermFun fp sz)
       (TypedLLVMAlloca fp sz)) >>>= \y ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx y)
    _ ->
      stmtFailM

-- Type-check a push frame instruction
tcEmitLLVMStmt arch ctx loc (LLVM_PushFrame _) =
  emitLLVMStmt knownRepr loc llvmCreateFramePermFun TypedLLVMCreateFrame >>>= \fp ->
  setFramePtr (TypedReg fp) >>>
  emitStmt knownRepr loc (eqPermFun PExpr_Unit)
  (TypedSetReg knownRepr $ TypedExpr EmptyApp) >>>= \(_ :>: y) ->
  greturn (addCtxName ctx y)

-- Type-check a pop frame instruction
tcEmitLLVMStmt arch ctx loc (LLVM_PopFrame _) =
  getFramePtr >>>= \maybe_fp ->
  maybe (greturn ValPerm_True) getRegPerm maybe_fp >>>= \fp_perm ->
  case (maybe_fp, fp_perm) of
    (Just fp, ValPerm_LLVMFrame fperms)
      | Just (Some del_perms) <- llvmFrameDeletionPerms fperms ->
        emitLLVMStmt knownRepr loc (llvmDeleteFramePermFun fp)
        (TypedLLVMDeleteFrame fp) >>>= \y ->
        gmodify (\st -> st { stExtState = PermCheckExtState_LLVM Nothing }) >>>
        greturn (addCtxName ctx y)
    _ -> stmtFailM

tcEmitLLVMStmt _arch _ctx _loc _stmt = error "FIXME: tcEmitLLVMStmt"

-- FIXME HERE: need to handle PtrEq, PtrLe, PtrAddOffset, and PtrSubtract


----------------------------------------------------------------------
-- * Permission Checking for Jump Targets and Termination Statements
----------------------------------------------------------------------

argsToEqPerms :: CtxTrans ctx -> Assignment (Reg ctx) args ->
                 DistPerms (CtxToRList args)
argsToEqPerms _ (viewAssign -> AssignEmpty) = DistPermsNil
argsToEqPerms ctx (viewAssign -> AssignExtend args reg) =
  let x = typedRegVar (tcReg ctx reg) in
  DistPermsCons (argsToEqPerms ctx args) x (ValPerm_Eq $ PExpr_Var x)

abstractPermsIn :: MapRList Name (ghosts :: RList CrucibleType) ->
                   MapRList f args -> DistPerms (ghosts :++: args) ->
                   Closed (MbDistPerms (ghosts :++: args))
abstractPermsIn xs args perms =
  $(mkClosed [| \args -> mbCombine . fmap (nuMulti args . const) |])
  `clApply` closedProxies args
  `clApply` maybe (error "abstractPermsIn") id (abstractVars xs perms)

abstractPermsRet :: MapRList Name (ghosts :: RList CrucibleType) ->
                    MapRList f args -> RetPerms ret ret_ps ->
                    Closed (Mb (ghosts :++: args) (RetPerms ret ret_ps))
abstractPermsRet xs args (RetPerms mb_perms) =
  $(mkClosed [| \args -> fmap RetPerms . mbCombine
                         . fmap (nuMulti args . const) |])
  `clApply` closedProxies args
  `clApply` maybe (error "abstractPermsRet") id (abstractVars xs mb_perms)


-- | Type-check a Crucible jump target
tcJumpTarget :: CtxTrans ctx -> JumpTarget cblocks ctx ->
                StmtPermCheckM ext cblocks blocks ret args RNil RNil
                (PermImpl (TypedJumpTarget blocks) RNil)
tcJumpTarget ctx (JumpTarget blkID arg_tps args) =
  gget >>>= \st ->
  tcBlockID blkID >>>= \memb ->
  lookupBlockInfo memb >>>= \blkInfo ->

  -- First test if we have already visited the given block
  if blockInfoVisited blkInfo then
    -- If so, then this is a reverse jump, i.e., a loop
    error "Cannot handle reverse jumps (FIXME)"

  else
    -- If not, we can make a new entrypoint that takes all of the current
    -- permissions as input
    case (getAllPerms (stCurPerms st), stRetPerms st) of
      (Some ghost_perms, Some ret_perms) ->
        -- Get the types of all variables we hold permissions on, and then use
        -- these to make a new entrypoint into the given block, whose ghost
        -- arguments are all those that we hold permissions on
        getVarTypes (distPermsVars ghost_perms) >>>= \ghost_tps ->

        -- Translate each "real" argument x into an eq(x) permission, and then
        -- form the append of (ghosts :++: real_args) for the types and the
        -- permissions. These are all used to build the TypedJumpTarget.
        let arg_eq_perms = argsToEqPerms ctx args
            perms = appendDistPerms ghost_perms arg_eq_perms in        

        -- Insert a new block entrypoint that has all the permissions we
        -- constructed above as input permissions
        liftPermCheckM
        (insNewBlockEntry memb (mkCruCtx arg_tps) ghost_tps
         (abstractPermsIn (distPermsVars ghost_perms)
          (distPermsVars arg_eq_perms) perms)
         (abstractPermsRet (distPermsVars ghost_perms)
          (distPermsVars arg_eq_perms) ret_perms)) >>>= \entryID ->

        -- Build the typed jump target for this jump target
        let target_t = TypedJumpTarget entryID (mkCruCtx arg_tps) perms in

        -- Finally, build the PermImpl that proves all the required permissions
        -- from the current permission set. This proof just copies the existing
        -- permissions into the current distinguished perms, and then proves
        -- that each "real" argument register equals itself.
        greturn $
        runImplM CruCtxNil (stCurPerms st) target_t
        (implPushDelMultiM ghost_perms >>>
         proveVarsImplAppend (distPermsToExDistPerms arg_eq_perms))


-- | Type-check a termination statement
tcTermStmt :: PermCheckExtC ext => CtxTrans ctx ->
              TermStmt cblocks ret ctx ->
              StmtPermCheckM ext cblocks blocks ret args RNil RNil
              (TypedTermStmt blocks ret RNil)
tcTermStmt ctx (Jump tgt) =
  TypedJump <$> tcJumpTarget ctx tgt
tcTermStmt ctx (Br reg tgt1 tgt2) =
  TypedBr (tcReg ctx reg) <$> tcJumpTarget ctx tgt1 <*> tcJumpTarget ctx tgt2
tcTermStmt ctx (Return reg) =
  let treg = tcReg ctx reg in
  gget >>>= \st ->
  case stRetPerms st of
    Some (RetPerms mb_ret_perms) ->
      let ret_perms =
            varSubst (singletonVarSubst $ typedRegVar treg) mb_ret_perms in
      greturn $ TypedReturn $
      runImplM CruCtxNil (stCurPerms st) (TypedRet treg ret_perms) $
      proveVarsImpl $ distPermsToExDistPerms ret_perms
tcTermStmt ctx (ErrorStmt reg) = greturn $ TypedErrorStmt $ tcReg ctx reg
tcTermStmt _ tstmt =
  error ("tcTermStmt: unhandled termination statement: "
         ++ show (pretty tstmt))


----------------------------------------------------------------------
-- * Permission Checking for Blocks and Sequences of Statements
----------------------------------------------------------------------

-- | Translate and emit a Crucible statement sequence, starting and ending with
-- an empty stack of distinguished permissions
tcEmitStmtSeq :: PermCheckExtC ext => CtxTrans ctx ->
                 StmtSeq ext cblocks ret ctx ->
                 PermCheckM ext cblocks blocks ret args
                 () RNil
                 (TypedStmtSeq ext blocks ret RNil) RNil
                 ()
tcEmitStmtSeq ctx (ConsStmt loc stmt stmts) =
  tcEmitStmt ctx loc stmt >>>= \ctx' ->
  tcEmitStmtSeq ctx' stmts
tcEmitStmtSeq ctx (TermStmt loc tstmt) =
  tcTermStmt ctx tstmt >>>= \typed_tstmt ->
  gmapRet (const $ return $ TypedTermStmt loc typed_tstmt)

-- | Type-check a single block entrypoint
tcBlockEntry :: PermCheckExtC ext => Block ext cblocks ret args ->
                BlockEntryInfo blocks ret (CtxToRList args) ->
                TopPermCheckM ext cblocks blocks ret
                (TypedEntry ext blocks ret (CtxToRList args))
tcBlockEntry blk (BlockEntryInfo {..}) =
  fmap (TypedEntry entryInfoID entryInfoArgs entryInfoPermsIn) $
  strongMbM $
  flip nuMultiWithElim (MNil :>: entryInfoPermsIn :>:
                        entryInfoPermsOut) $ \ns (_ :>: perms :>: ret_perms) ->
  runPermCheckM (distPermSet $ runIdentity perms) (runIdentity ret_perms) $
  let ctx =
        mkCtxTrans (blockInputs blk) $ snd $
        splitMapRList (entryGhosts entryInfoID) (ctxToMap $ entryInfoArgs) ns in
  stmtRecombinePerms >>>
  setVarTypes ns (appendCruCtx (entryGhosts entryInfoID) entryInfoArgs) >>>
  tcEmitStmtSeq ctx (blk ^. blockStmts)

-- | Type-check a Crucible block and add it to a block info map
tcAddBlock :: PermCheckExtC ext => Block ext cblocks ret args ->
              BlockInfoMap ext blocks ret ->
              TopPermCheckM ext cblocks blocks ret (BlockInfoMap ext blocks ret)
tcAddBlock blk info_map =
  do memb <- stLookupBlockID (blockID blk) <$> get
     blk_t <- TypedBlock <$> mapM (tcBlockEntry blk)
       (blockInfoEntries $ mapRListLookup memb info_map)
     return $ blockInfoMapSetBlock memb blk_t info_map

-- | Type-check a Crucible block and put its translation into the 'BlockInfo'
-- for that block
tcEmitBlock :: PermCheckExtC ext => Block ext cblocks ret args ->
               TopPermCheckM ext cblocks blocks ret ()
tcEmitBlock blk =
  do st <- get
     clMap <- closedM ( $(mkClosed [| tcAddBlock |])
                        `clApply` toClosed blk
                        `clApply` stBlockInfo st)
     put (st { stBlockInfo = clMap })

makeRetPerms :: Mb (ctx :> ret) (DistPerms ps) ->
                Mb ctx (RetPerms ret ps)
makeRetPerms mb_perms =
  fmap RetPerms $ mbSeparate (MNil :>: Proxy) mb_perms

-- | Type-check a Crucible CFG
tcCFG :: PermCheckExtC ext => CFG ext blocks inits ret ->
         Closed (FunPerm ghosts inits ret) ->
         TypedCFG ext (CtxCtxToRList blocks) ghosts (CtxToRList inits) ret
tcCFG cfg [clP| FunPerm _ perms_in perms_out :: FunPerm ghosts args ret |] =
  flip evalState (emptyTopPermCheckState (cfgBlockMap cfg)) $
  do init_memb <- stLookupBlockID (cfgEntryBlockID cfg) <$> get
     init_entry <-
       insNewBlockEntry init_memb (mkCruCtx $ handleArgTypes $ cfgHandle cfg)
       (knownRepr :: CruCtx ghosts)
       ($(mkClosed [| mbValuePermsToDistPerms |]) `clApply` perms_in)
       ($(mkClosed [| makeRetPerms
                    . mbValuePermsToDistPerms |]) `clApply` perms_out)
     mapM_ (visit cfg) (cfgWeakTopologicalOrdering cfg)
     final_st <- get
     return $ TypedCFG
       { tpcfgHandle =
           -- FIXME: figure out the index for the TypedFnHandle
           TypedFnHandle (knownRepr :: CruCtx ghosts) (cfgHandle cfg) 0
       , tpcfgInputPerms = unClosed perms_in
       , tpcfgOutputPerms = unClosed perms_out
       , tpcfgBlockMap =
           mapMapRList
           (maybe (error "tcCFG: unvisited block!") id . blockInfoBlock)
           (unClosed $ stBlockInfo final_st)
       , tpcfgEntryBlockID = init_entry }
  where
    visit :: PermCheckExtC ext => CFG ext cblocks inits ret ->
             WTOComponent (Some (BlockID cblocks)) ->
             TopPermCheckM ext cblocks blocks ret ()
    visit cfg (Vertex (Some blkID)) =
      tcEmitBlock (getBlock blkID (cfgBlockMap cfg))
    visit cfg (SCC (Some blkID) comps) =
      tcEmitBlock (getBlock blkID (cfgBlockMap cfg)) >>
      mapM_ (visit cfg) comps

{-
-- FIXME HERE NOW:
-- + translate -> SAW
-- + handle function calls and a function call context
-- + top-level interface / add to interpreter
-}
