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
import Data.Text
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


instance NuMatchingAny1 BaseTypeRepr where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 TypeRepr where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| forall f ctx . NuMatchingAny1 f => AssignView f ctx |])

viewToAssign :: AssignView f ctx -> Assignment f ctx
viewToAssign AssignEmpty = Ctx.empty
viewToAssign (AssignExtend asgn' f) = extend asgn' f

instance NuMatchingAny1 f => NuMatching (Assignment f ctx) where
  nuMatchingProof =
    -- FIXME: inefficient to map a whole Assignment step by step to ViewAssigns,
    -- freshen each element, and then map back to the Assignment again; maybe we
    -- need to figure out how to use the TraversableFC instance for Assignment
    -- here?
    isoMbTypeRepr viewAssign viewToAssign

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
newtype TypedReg tp = TypedReg { typedRegVar :: ExprVar tp }

-- | A type-checked Crucible expression is a Crucible 'Expr' that uses
-- 'TypedReg's for variables
newtype TypedExpr ext tp = TypedExpr (App ext TypedReg tp)

-- | A "typed" function handle is a normal function handle along with an index
-- of which typing of that function handle we are using, in case there are
-- multiples (just like 'TypedEntryID', below)
data TypedFnHandle ghosts args ret =
  TypedFnHandle (CruCtx ghosts) (FnHandle (RListToCtx args) ret) Int

-- | All of our blocks have multiple entry points, for different inferred types,
-- so a "typed" 'BlockID' is a normal Crucible 'BlockID' (which is just an index
-- into the @blocks@ context of contexts) plus an 'Int' specifying which entry
-- point to that block. Each entry point also takes an extra set of "ghost"
-- arguments, not extant in the original program, that are needed to express
-- input and output permissions.
data TypedEntryID blocks args ghosts =
  TypedEntryID { entryBlockID :: Member blocks args,
                 entryGhosts :: CruCtx ghosts,
                 entryIndex :: Int }

instance TestEquality (TypedEntryID blocks args) where
  testEquality (TypedEntryID memb1 ghosts1 i1) (TypedEntryID memb2 ghosts2 i2)
    | memb1 == memb2 && i1 == i2 = testEquality ghosts1 ghosts2
  testEquality _ _ = Nothing

-- | A collection of arguments to a function or jump target
data TypedArgs args where
  TypedArgsNil :: TypedArgs RNil
  TypedArgsCons :: KnownRepr TypeRepr a => TypedArgs args -> TypedReg a ->
                   TypedArgs (args :> a)

-- | A typed target for jump and branch statements, including arguments and a
-- proof of the required permissions on those arguments
data TypedJumpTarget blocks ps where
     TypedJumpTarget ::
       TypedEntryID blocks args ghosts ->
       CruCtx (ghosts :++: args) ->
       TypedArgs (ghosts :++: args) ->
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
$(mkNuMatching [t| forall args. TypedArgs args |])
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
      set (varPerm fp) (ValPerm_LLVMFrame ((ret,sz):frm)) $
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
     (ext :: *)
     (blocks :: RList (RList CrucibleType))
     (ghosts :: RList CrucibleType)
     (inits :: RList CrucibleType)
     (ret :: CrucibleType)
  = TypedCFG { tpcfgHandle :: TypedFnHandle ghosts inits ret
             , tpcfgInputPerms :: MbDistPerms (ghosts :++: inits)
             , tpcfgOutputPerms :: MbDistPerms (ghosts :++: inits :> ret)
             , tpcfgBlockMap :: TypedBlockMap ext blocks ret
             , tpcfgEntryBlockID :: TypedEntryID blocks inits ghosts
             }


----------------------------------------------------------------------
-- * Monad(s) for Permission Checking
----------------------------------------------------------------------

-- | A translation of a Crucible context to 'TypedReg's that exist in the local
-- Hobbits context
type CtxTrans ctx = Assignment TypedReg ctx

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

data PermCheckExtState ext where
  -- | The extension-specific state for LLVM is the current frame pointer, if it
  -- exists
  PermCheckExtState_LLVM :: Maybe (TypedReg (LLVMFrameType (ArchWidth arch))) ->
                            PermCheckExtState (LLVM arch)
  PermCheckExtState_Unit :: PermCheckExtState ()

data SomeLLVMFrame where
  SomeLLVMFrame :: NatRepr w -> TypedReg (LLVMFrameType w) -> SomeLLVMFrame

-- | The local state maintained while type-checking is the current permission
-- set and the permissions required on return from the entire function.
data PermCheckState ext args ret ps =
  PermCheckState
  {
    stCurPerms :: PermSet ps,
    stExtState :: PermCheckExtState ext,
    stRetPerms :: Binding ret (DistPerms (args :> ret))
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
    entryInfoPermsIn :: MbDistPerms (ghosts :++: args),
    entryInfoPermsOut :: MbDistPerms (ghosts :++: args :> ret)
  } -> BlockEntryInfo blocks ret args

-- | Extract the 'BlockID' from entrypoint info
entryInfoBlockID :: BlockEntryInfo blocks ret args -> Member blocks args
entryInfoBlockID (BlockEntryInfo entryID _ _) = entryBlockID entryID

-- | Extract the entry id from entrypoint info
entryInfoIndex :: BlockEntryInfo blocks ret args -> Int
entryInfoIndex (BlockEntryInfo entryID _ _) = entryIndex entryID

-- | Information about the current state of type-checking for a block
data BlockInfo ext blocks ret args =
  BlockInfo
  {
    blockInfoVisited :: Bool,
    blockInfoEntries :: [BlockEntryInfo blocks ret args],
    blockInfoBlock :: Maybe (TypedBlock ext blocks ret args)
  }

-- | Top-level state, maintained outside of permission-checking single blocks
data TopPermCheckState ext blocks ret =
  TopPermCheckState
  {
    stBlockInfo ::
      Closed (MapRList (BlockInfo ext blocks ret) blocks)
  }

$(mkNuMatching [t| forall ext blocks ret. TopPermCheckState ext blocks ret |])

instance BindState (TopPermCheckState ext blocks ret) where
  bindState [nuP| TopPermCheckState i |] = TopPermCheckState (mbLift i)

-- | The top-level monad for permission-checking CFGs
type TopPermCheckM ext blocks ret =
  State (TopPermCheckState ext blocks ret)

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
type PermCheckM ext blocks ret args r1 ps1 r2 ps2 =
  GenStateContM (PermCheckState ext args ret ps1)
  (TopPermCheckM ext blocks ret r1)
  (PermCheckState ext args ret ps2)
  (TopPermCheckM ext blocks ret r2)

-- | The generalized monad for permission-checking statements
type StmtPermCheckM ext blocks ret args ps1 ps2 =
  PermCheckM ext blocks ret args
   (TypedStmtSeq ext blocks ret ps1) ps1
   (TypedStmtSeq ext blocks ret ps2) ps2

-- | Get the current top-level state
top_get :: PermCheckM ext blocks ret args r ps r ps
           (TopPermCheckState ext blocks ret)
top_get = gcaptureCC $ \k -> get >>= k

lookupBlockInfo :: BlockID blocks args' ->
                   PermCheckM ext (CtxCtxToRList blocks) ret args r ps r ps
                   (BlockInfo ext (CtxCtxToRList blocks) ret (CtxToRList args'))
lookupBlockInfo = error "FIXME HERE"


getVarPerm :: ExprVar a ->
              PermCheckM ext blocks ret args r ps r ps (ValuePerm a)
getVarPerm x = view (varPerm x) <$> stCurPerms <$> gget

getRegPerm :: TypedReg a ->
              PermCheckM ext blocks ret args r ps r ps (ValuePerm a)
getRegPerm (TypedReg x) = getVarPerm x

-- | Get the current frame pointer on LLVM architectures
getFramePtr :: PermCheckM (LLVM arch) blocks ret args r ps r ps
               (Maybe (TypedReg (LLVMFrameType (ArchWidth arch))))
getFramePtr = gget >>>= \st -> case stExtState st of
  PermCheckExtState_LLVM maybe_fp -> greturn maybe_fp

setFramePtr :: TypedReg (LLVMFrameType (ArchWidth arch)) ->
               PermCheckM (LLVM arch) blocks ret args r ps r ps ()
setFramePtr fp =
  gmodify (\st -> st { stExtState = PermCheckExtState_LLVM (Just fp) })

-- | Failure in the statement permission-checking monad
stmtFailM :: PermCheckM ext blocks ret args r1 ps1
             (TypedStmtSeq ext blocks ret ps2) ps2 a
stmtFailM = gabortM (return $ TypedImplStmt Impl_Fail)

-- | Smart constructor for applying a function on 'PermImpl's
applyImplFun :: (PermImpl r ps -> r ps) -> PermImpl r ps -> r ps
applyImplFun _ (Impl_Done r) = r
applyImplFun f impl = f impl

-- | Embed an implication computation inside a permission-checking computation
embedImplM :: (forall ps. PermImpl r ps -> r ps) -> CruCtx vars ->
              ImplM vars r ps_out ps_in a ->
              PermCheckM ext blocks ret args (r ps_out) ps_out (r ps_in) ps_in
              (PermSubst vars, a)
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
stmtRecombinePerms :: StmtPermCheckM ext blocks ret args RNil ps_in ()
stmtRecombinePerms =
  embedImplM TypedImplStmt emptyCruCtx recombinePerms >>>= \_ ->
  greturn ()

-- | Prove permissions in the context of type-checking statements
stmtProvePerm :: (PermCheckExtC ext, KnownRepr CruCtx vars) =>
                 TypedReg a -> Mb vars (ValuePerm a) ->
                 StmtPermCheckM ext blocks ret args
                 (ps :> a) ps (PermSubst vars)
stmtProvePerm (TypedReg x) mb_p =
  embedImplM TypedImplStmt knownRepr (proveVarImpl x mb_p) >>>= \(s,_) ->
  greturn s

-- | Try to prove that a register equals a constant integer
resolveConstant :: KnownRepr TypeRepr tp => TypedReg tp ->
                   StmtPermCheckM ext blocks ret args ps ps (Maybe Integer)
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
tcArgs :: CtxTrans ctx -> CtxRepr args -> Assignment (Reg ctx) args ->
          TypedArgs (CtxToRList args)
tcArgs _ _ (viewAssign -> AssignEmpty) = TypedArgsNil
tcArgs ctx (viewAssign ->
            AssignExtend arg_tps' tp) (viewAssign -> AssignExtend args' reg) =
  withKnownRepr tp $
  TypedArgsCons (tcArgs ctx arg_tps' args') (tcReg ctx reg)

-- | Translate a 'TypedExpr' to a permission expression, if possible
exprToPermExpr :: TypedExpr ext tp -> Maybe (PermExpr tp)
exprToPermExpr _ = error "FIXME HERE: exprToPermExpr!"

-- | Translate a Crucible expression
tcExpr :: PermCheckExtC ext => CtxTrans ctx -> Expr ext ctx tp ->
          StmtPermCheckM ext blocks ret args ps ps (TypedExpr ext tp)
tcExpr ctx (App (ExtensionApp e_ext :: App ext (Reg ctx) tp))
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = error "tcExpr: unexpected LLVM expression"
tcExpr ctx (App app) = greturn $ TypedExpr $ fmapFC (tcReg ctx) app


-- | Emit a statement in the current statement sequence, where the supplied
-- function says how that statement modifies the current permissions, given the
-- freshly-bound names for the return values. Return those freshly-bound names
-- for the return values.
emitStmt :: TypeCtx rets => ProgramLoc ->
            StmtPermFun rets ps_out ps_in ->
            TypedStmt ext rets ps_out ps_in ->
            StmtPermCheckM ext blocks ret args ps_out ps_in
            (MapRList Name rets)
emitStmt loc f_perms stmt =
  gopenBinding
  ((TypedConsStmt loc stmt <$>) . strongMbM)
  (nuMulti typeCtxProxies $ \vars -> ()) >>>= \(ns, ()) ->
  gmodify (modifySTCurPerms $ f_perms ns) >>>
  greturn ns

-- | Call emitStmt with a 'TypedLLVMStmt'
emitLLVMStmt :: ProgramLoc ->
                StmtPermFun (RNil :> tp) ps_out ps_in ->
                TypedLLVMStmt (ArchWidth arch) tp ps_out ps_in ->
                StmtPermCheckM (LLVM arch) blocks ret args ps_out ps_in (Name tp)
emitLLVMStmt loc f_perms stmt =
  emitStmt loc f_perms (TypedLLVMStmt stmt) >>>= \(_ :>: n) -> greturn n


-- | Typecheck a statement and emit it in the current statement sequence,
-- starting and ending with an empty stack of distinguished permissions
tcEmitStmt :: PermCheckExtC ext => CtxTrans ctx -> ProgramLoc ->
              Stmt ext ctx ctx' ->
              StmtPermCheckM ext blocks ret args RNil RNil (CtxTrans ctx')
tcEmitStmt ctx loc (SetReg tp e) =
  tcExpr ctx e >>>= \typed_e ->
  let perm_f = maybe nullPermFun eqPermFun (exprToPermExpr typed_e) in
  emitStmt loc perm_f (TypedSetReg tp typed_e) >>>= \(_ :>: x) ->
  greturn $ addCtxName ctx x

tcEmitStmt ctx loc (ExtendAssign stmt_ext :: Stmt ext ctx ctx')
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = tcEmitLLVMStmt Proxy ctx loc stmt_ext

tcEmitStmt _ _ _ = error "FIXME: tcEmitStmt!"


-- | Translate a Crucible assignment of an LLVM expression
tcEmitLLVMSetExpr ::
  (1 <= ArchWidth arch, KnownNat (ArchWidth arch)) => Proxy arch ->
  CtxTrans ctx -> ProgramLoc -> LLVMExtensionExpr arch (Reg ctx) tp ->
  StmtPermCheckM (LLVM arch) blocks ret args RNil RNil (CtxTrans (ctx ::> tp))

-- Type-check a pointer-building expression, which is only valid when the block
-- = 0, i.e., when building a word
tcEmitLLVMSetExpr arch ctx loc (LLVM_PointerExpr w blk_reg off_reg) =
  let toff_reg = tcReg ctx off_reg
      tblk_reg = tcReg ctx blk_reg in
  resolveConstant tblk_reg >>>= \maybe_const ->
  case maybe_const of
    Just 0 ->
      withKnownNat w $
      emitLLVMStmt loc
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
  emitLLVMStmt loc
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
  emitLLVMStmt loc
  (eqPermFun e) (DestructLLVMWord tptr_reg e) >>>= \x ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx x)


-- | Typecheck a statement and emit it in the current statement sequence,
-- starting and ending with an empty stack of distinguished permissions
tcEmitLLVMStmt ::
  (1 <= ArchWidth arch, KnownNat (ArchWidth arch)) => Proxy arch ->
  CtxTrans ctx -> ProgramLoc -> LLVMStmt (ArchWidth arch) (Reg ctx) tp ->
  StmtPermCheckM (LLVM arch) blocks ret args RNil RNil (CtxTrans (ctx ::> tp))

-- Type-check a load of an LLVM pointer
tcEmitLLVMStmt arch ctx loc (LLVM_Load _ reg (LLVMPointerRepr w) _ _)
  | Just Refl <- testEquality w (archWidth arch)
  = let treg = tcReg ctx reg in
    stmtProvePerm treg llvmExRead0Perm >>>= \_ ->
    (emitLLVMStmt loc (llvmLoadPermFun treg) (TypedLLVMLoad treg)) >>>= \y ->
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
    (emitLLVMStmt loc (llvmStorePermFun tptr tval)
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
      (emitLLVMStmt loc (llvmAllocaPermFun fp sz)
       (TypedLLVMAlloca fp sz)) >>>= \y ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx y)
    _ ->
      stmtFailM

-- Type-check a push frame instruction
tcEmitLLVMStmt arch ctx loc (LLVM_PushFrame _) =
  emitLLVMStmt loc llvmCreateFramePermFun TypedLLVMCreateFrame >>>= \fp ->
  setFramePtr (TypedReg fp) >>>
  emitStmt loc (eqPermFun PExpr_Unit)
  (TypedSetReg knownRepr $ TypedExpr EmptyApp) >>>= \(_ :>: y) ->
  greturn (addCtxName ctx y)

-- Type-check a pop frame instruction
tcEmitLLVMStmt arch ctx loc (LLVM_PopFrame _) =
  getFramePtr >>>= \maybe_fp ->
  maybe (greturn ValPerm_True) getRegPerm maybe_fp >>>= \fp_perm ->
  case (maybe_fp, fp_perm) of
    (Just fp, ValPerm_LLVMFrame fperms)
      | Some del_perms <- llvmFrameDeletionPerms fperms ->
        emitLLVMStmt loc (llvmDeleteFramePermFun fp)
        (TypedLLVMDeleteFrame fp) >>>= \y ->
        gmodify (\st -> st { stExtState = PermCheckExtState_LLVM Nothing }) >>>
        greturn (addCtxName ctx y)
    _ -> stmtFailM

tcEmitLLVMStmt _arch _ctx _loc _stmt = error "FIXME: tcEmitLLVMStmt"

-- FIXME HERE: need to handle PtrEq, PtrLe, PtrAddOffset, and PtrSubtract


----------------------------------------------------------------------
-- * Permission Checking for Jump Targets
----------------------------------------------------------------------

tcJumpTarget :: CtxTrans ctx -> JumpTarget blocks ctx ->
                StmtPermCheckM ext (CtxCtxToRList blocks) ret args RNil RNil
                (PermImpl (TypedJumpTarget (CtxCtxToRList blocks)) RNil)
tcJumpTarget ctx (JumpTarget blkID _ args) =
  lookupBlockInfo blkID >>>= \blkInfo ->
  if blockInfoVisited blkInfo then
    error "Cannot handle backwards jumps (FIXME)"
  else
    error "FIXME HERE NOW"


{-
FIXME HERE NOW: Put DistPerms into TypedArgs? How does translation work?
- get all args with perms
- add eq perms for the real args
- make a PermImpl that pushes all these perms into the dist perms
- create a TypedArgs from this
-}

tcTermStmt :: PermCheckExtC ext => CtxTrans ctx ->
              TermStmt blocks ret ctx ->
              StmtPermCheckM ext (CtxCtxToRList blocks) ret args RNil RNil
              (TypedTermStmt (CtxCtxToRList blocks) ret RNil)
tcTermStmt ctx (Jump tgt) =
  TypedJump <$> tcJumpTarget ctx tgt
tcTermStmt ctx (Br reg tgt1 tgt2) =
  TypedBr (tcReg ctx reg) <$> tcJumpTarget ctx tgt1 <*> tcJumpTarget ctx tgt2
tcTermStmt ctx (Return reg) =
  let treg = tcReg ctx reg in
  gget >>>= \st ->
  let ret_perms =
        varSubst (singletonVarSubst $ typedRegVar treg) (stRetPerms st) in
  greturn $ TypedReturn $
  runImplM CruCtxNil (stCurPerms st) (TypedRet treg ret_perms) $
  proveVarsImpl $ distPermsToExDistPerms ret_perms
tcTermStmt ctx (ErrorStmt reg) = greturn $ TypedErrorStmt $ tcReg ctx reg
tcTermStmt _ tstmt =
  error ("tcTermStmt: unhandled termination statement: "
         ++ show (pretty tstmt))


----------------------------------------------------------------------
-- * Permission Checking for Sequences of Statements
----------------------------------------------------------------------

-- | Translate and emit a Crucible statement sequence, starting and ending with
-- an empty stack of distinguished permissions
tcEmitStmtSeq :: PermCheckExtC ext => CtxTrans ctx ->
                 StmtSeq ext blocks ret ctx ->
                 PermCheckM ext (CtxCtxToRList blocks) ret args
                 () RNil
                 (TypedStmtSeq ext (CtxCtxToRList blocks) ret RNil) RNil
                 ()
tcEmitStmtSeq ctx (ConsStmt loc stmt stmts) =
  tcEmitStmt ctx loc stmt >>>= \ctx' ->
  tcEmitStmtSeq ctx' stmts
tcEmitStmtSeq ctx (TermStmt loc tstmt) =
  tcTermStmt ctx tstmt >>>= \typed_tstmt ->
  gmapRet (const $ return $ TypedTermStmt loc typed_tstmt)

-- FIXME HERE NOW:
-- + type-check CFGs
-- + translate -> SAW
-- + handle function calls and a function call context
-- + top-level interface / add to interpreter
