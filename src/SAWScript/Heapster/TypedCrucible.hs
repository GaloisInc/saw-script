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

import Data.Text
import Data.Type.Equality
import Data.Functor.Identity
-- import Data.Functor.Const
-- import Data.Functor.Product
-- import Data.Parameterized.Context
import GHC.TypeLits
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


instance NuMatchingAny1 BaseTypeRepr where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 TypeRepr where
  nuMatchingAny1Proof = nuMatchingProof

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
data TypedArgs args ps where
  TypedArgsNil :: TypedArgs RNil ps
  TypedArgsCons :: KnownRepr TypeRepr a => TypedArgs args ps -> TypedReg a ->
                   TypedArgs (args :> a) ps

-- | A typed target for jump and branch statements, including arguments and a
-- proof of the required permissions on those arguments
data TypedJumpTarget blocks ps_in where
     TypedJumpTarget ::
       TypedEntryID blocks args ghosts ->
       PermImpl (TypedArgs (ghosts :++: args)) ps_in ->
       TypedJumpTarget blocks ps_in


$(mkNuMatching [t| forall tp. TypedReg tp |])

instance NuMatchingAny1 TypedReg where
  nuMatchingAny1Proof = nuMatchingProof

type NuMatchingExtC ext =
  (NuMatchingAny1 (ExprExtension ext TypedReg),
   NuMatchingAny1 (StmtExtension ext TypedReg))

$(mkNuMatching [t| forall ext tp. NuMatchingExtC ext => TypedExpr ext tp |])
$(mkNuMatching [t| forall ghosts args ret. TypedFnHandle ghosts args ret |])
$(mkNuMatching [t| forall blocks ghosts args. TypedEntryID blocks args ghosts |])
$(mkNuMatching [t| forall args ps. TypedArgs args ps |])

instance NuMatchingAny1 (TypedArgs args) where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| forall blocks ps_in. TypedJumpTarget blocks ps_in |])


----------------------------------------------------------------------
-- * Typed Crucible Statements and Sequences of Statements
----------------------------------------------------------------------

-- | Typed Crucible statements with the given Crucible syntax extension and the
-- given set of return values
data TypedStmt ext rets ps_out ps_in where
  -- | Assign the value of a register
  TypedSetReg :: TypeRepr tp -> TypedExpr ext tp ->
                 TypedStmt ext (RNil :> tp) (RNil :> tp) RNil

  -- | Assert a boolean condition, printing the given string on failure
  TypedAssert :: TypedReg BoolType -> TypedReg StringType ->
                 TypedStmt ext RNil RNil RNil

  -- FIXME: add Alignment to loads and stores
  TypedLLVMLoad :: (TypedReg (LLVMPointerType w)) ->
                   TypedStmt (LLVM arch) (RNil :> LLVMPointerType w)
                   (RNil :> LLVMPointerType w :> LLVMPointerType w)
                   (RNil :> LLVMPointerType w)

  TypedLLVMStore :: (TypedReg (LLVMPointerType w)) ->
                    (TypedReg (LLVMPointerType w)) ->
                    TypedStmt (LLVM arch) (RNil :> LLVMPointerType w)
                    (RNil :> LLVMPointerType w)
                    (RNil :> LLVMPointerType w)

  -- | Destruct an LLVM value into its block and offset
  DestructLLVMPtr :: (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
                     TypedStmt (LLVM arch) (RNil :> NatType :> BVType w)
                     (RNil :> LLVMPointerType w)
                     (RNil :> LLVMPointerType w)


-- | Typed return argument
data TypedRet ret ps = TypedRet (TypedReg ret)


-- | Typed Crucible block termination statements
data TypedTermStmt blocks ret ps_in where
  -- | Jump to the given jump target
  TypedJump :: TypedJumpTarget blocks ps_in -> TypedTermStmt blocks ret ps_in

  -- | Branch on condition: if true, jump to the first jump target, and
  -- otherwise jump to the second jump target
  TypedBr :: TypedReg BoolType ->
             TypedJumpTarget blocks ps_in ->
             TypedJumpTarget blocks ps_in ->
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
                   Mb (ExprVarCtx rets) (TypedStmtSeq ext blocks ret ps_next) ->
                   TypedStmtSeq ext blocks ret ps_in

  -- | Typed version of 'TermStmt', which terminates the current block
  TypedTermStmt :: ProgramLoc ->
                   TypedTermStmt blocks ret ps_in ->
                   TypedStmtSeq ext blocks ret ps_in

$(mkNuMatching [t| forall ext rets  ps_out ps_in. NuMatchingExtC ext =>
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
    TypedEntryID blocks ghosts args -> CruCtx args ->
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

-- | The local state maintained while type-checking is the current permission
-- set and the permissions required on return from the entire function.
data PermCheckState args ret ps =
  PermCheckState
  {
    stCurPerms :: PermSet ps,
    stRetPerms :: Binding ret (DistPerms (args :> ret))
  }

-- | Like the 'set' method of a lens, but allows the @ps@ argument to change
setSTCurPerms :: PermSet ps2 -> PermCheckState args ret ps1 ->
                 PermCheckState args ret ps2
setSTCurPerms perms (PermCheckState {..}) =
  PermCheckState { stCurPerms = perms, .. }

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
    stBlockInfo :: Closed (MapRList (BlockInfo ext blocks ret) blocks)
  }

$(mkNuMatching [t| forall ext blocks ret. TopPermCheckState ext blocks ret |])

instance BindState (TopPermCheckState ext blocks ret) where
  bindState [nuP| TopPermCheckState i |] = TopPermCheckState (mbLift i)

-- | The top-level monad for permission-checking CFGs
type TopPermCheckM ext blocks ret =
  State (TopPermCheckState ext blocks ret)

-- | The generalized monad for permission-checking
type PermCheckM r ext blocks args ret =
  GenStateT (PermCheckState args ret)
  (GenContT r (TopPermCheckM ext blocks ret))

type StmtPermCheckM ext blocks args ret =
  PermCheckM (TypedStmtSeq ext blocks ret) ext blocks args ret

top_get :: PermCheckM r ext blocks args ret ps ps (TopPermCheckState ext blocks ret)
top_get = error "FIXME HERE"

{-
-- | Run an implication computation inside a permission-checking computation
runImplM :: (forall ps. PermImpl r ps -> r ps) -> CruCtx vars ->
            ImplM vars tp ps_out ps_in a ->
            PermCheckM r ext blocks args ret ps_out ps_in a
runImplM f_impl vars m =
  top_get >>>= \top_st ->
  gget >>>= \st ->
  liftGenStateT id
  (withAltContM (Identity . Impl_Done . runIdentity . flip evalState top_st)
   (\(implm :: Identity (PermImpl tp RNil)) -> case runIdentity implm of
       Impl_Done x -> return $ Identity x
       impl -> return $ Identity $ f_impl impl) $
   runGenStateT m (mkImplState vars $ stCurPerms st)) >>>= \(a, impl_st) ->
  modify (setSTCurPerms (_implStatePerms impl_st)) >>>
  greturn a
-}
