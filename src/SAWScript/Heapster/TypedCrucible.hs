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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

module SAWScript.Heapster.TypedCrucible where

import Data.Maybe
import Data.Text hiding (length, map, concat, findIndex)
import Data.List (findIndex)
import Data.Type.Equality
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Kind
import GHC.TypeLits
import What4.ProgramLoc
import What4.FunctionName

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

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), empty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

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

import Debug.Trace


-- | Make a program location with "internal" posiotion that has the same
-- function name as another location
-- FIXME: figure out where to put this
internalLoc :: ProgramLoc -> ProgramLoc
internalLoc loc = mkProgramLoc (plFunction loc) InternalPos


----------------------------------------------------------------------
-- * Typed Jump Targets and Function Handles
----------------------------------------------------------------------

-- | During type-checking, we convert Crucible registers to variables
newtype TypedReg tp = TypedReg { typedRegVar :: ExprVar tp }

instance PermPretty (TypedReg tp) where
  permPrettyM = permPrettyM . typedRegVar

-- | A sequence of typed registers
data TypedRegs ctx where
  TypedRegsNil :: TypedRegs RNil
  TypedRegsCons :: TypedRegs ctx -> TypedReg a -> TypedRegs (ctx :> a)

-- | Extract out a sequence of variables from a 'TypedRegs'
typedRegsToVars :: TypedRegs ctx -> MapRList Name ctx
typedRegsToVars TypedRegsNil = MNil
typedRegsToVars (TypedRegsCons regs (TypedReg x)) = typedRegsToVars regs :>: x

-- | Turn a sequence of typed registers into a variable substitution
typedRegsToVarSubst :: TypedRegs ctx -> PermVarSubst ctx
typedRegsToVarSubst = PermVarSubst . typedRegsToVars

-- | A typed register along with its value if that is known statically
data RegWithVal a
  = RegWithVal (TypedReg a) (PermExpr a)
  | RegNoVal (TypedReg a)

-- | Get the expression for a 'RegWithVal', even if it is only the variable for
-- its register value when it has no statically-known value
regWithValExpr :: RegWithVal a -> PermExpr a
regWithValExpr (RegWithVal _ e) = e
regWithValExpr (RegNoVal (TypedReg x)) = PExpr_Var x

-- | A type-checked Crucible expression is a Crucible 'Expr' that uses
-- 'TypedReg's for variables. As part of type-checking, these typed registers
-- (which are the inputs to the expression) as well as the final output value of
-- the expression are annotated with equality permissions @eq(e)@ if their
-- values can be statically represented as permission expressions @e@.
data TypedExpr ext tp =
  TypedExpr (App ext RegWithVal tp) (Maybe (PermExpr tp))

-- | A "typed" function handle is a normal function handle along with a context
-- of ghost variables
data TypedFnHandle ghosts args ret where
  TypedFnHandle :: CruCtx ghosts -> FnHandle cargs ret ->
                   TypedFnHandle ghosts (CtxToRList cargs) ret

-- | Extract out the context of ghost arguments from a 'TypedFnHandle'
typedFnHandleGhosts :: TypedFnHandle ghosts args ret -> CruCtx ghosts
typedFnHandleGhosts (TypedFnHandle ghosts _) = ghosts

-- | Extract out the context of regular arguments from a 'TypedFnHandle'
typedFnHandleArgs :: TypedFnHandle ghosts args ret -> CruCtx args
typedFnHandleArgs (TypedFnHandle _ h) = mkCruCtx $ handleArgTypes h

-- | Extract out the context of all arguments of a 'TypedFnHandle', including
-- the lifetime argument
typedFnHandleAllArgs :: TypedFnHandle ghosts args ret ->
                        CruCtx (ghosts :> LifetimeType :++: args)
typedFnHandleAllArgs h =
  appendCruCtx (CruCtxCons (typedFnHandleGhosts h) LifetimeRepr)
  (typedFnHandleArgs h)


-- | Extract out the return type of a 'TypedFnHandle'
typedFnHandleRetType :: TypedFnHandle ghosts args ret -> TypeRepr ret
typedFnHandleRetType (TypedFnHandle _ h) = handleReturnType h


-- | All of our blocks have multiple entry points, for different inferred types,
-- so a "typed" 'BlockID' is a normal Crucible 'BlockID' (which is just an index
-- into the @blocks@ context of contexts) plus an 'Int' specifying which entry
-- point to that block. Each entry point also takes an extra set of "ghost"
-- arguments, not extant in the original program, that are needed to express
-- input and output permissions.
data TypedEntryID (blocks :: RList (RList CrucibleType))
     (args :: RList CrucibleType) ghosts =
  TypedEntryID { entryBlockID :: Member blocks args,
                 entryGhosts :: CruCtx ghosts,
                 entryIndex :: Int }

memberLength :: Member a as -> Int
memberLength Member_Base = 0
memberLength (Member_Step memb) = 1 + memberLength memb

entryIDIndices :: TypedEntryID blocks args ghosts -> (Int, Int)
entryIDIndices (TypedEntryID memb _ ix) = (memberLength memb, ix)

instance Show (TypedEntryID blocks args ghosts) where
  show entryID = "<entryID " ++ show (entryIDIndices entryID) ++ ">"

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
       TypedJumpTarget blocks (ghosts :++: args)


$(mkNuMatching [t| forall tp. TypedReg tp |])
$(mkNuMatching [t| forall tp. RegWithVal tp |])
$(mkNuMatching [t| forall ctx. TypedRegs ctx |])

instance NuMatchingAny1 TypedReg where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 RegWithVal where
  nuMatchingAny1Proof = nuMatchingProof

type NuMatchingExtC ext =
  (NuMatchingAny1 (ExprExtension ext RegWithVal)
  -- (NuMatchingAny1 (ExprExtension ext TypedReg)
   -- , NuMatchingAny1 (StmtExtension ext TypedReg))
  )

$(mkNuMatching [t| forall ext tp. NuMatchingExtC ext => TypedExpr ext tp |])
$(mkNuMatching [t| forall ghosts args ret. TypedFnHandle ghosts args ret |])
$(mkNuMatching [t| forall blocks ghosts args. TypedEntryID blocks args ghosts |])
$(mkNuMatching [t| forall blocks ps_in. TypedJumpTarget blocks ps_in |])

instance NuMatchingAny1 (TypedJumpTarget blocks) where
  nuMatchingAny1Proof = nuMatchingProof

-- FIXME: Hobbits mkNuMatching cannot handle empty types
-- $(mkNuMatching [t| forall f tp. EmptyExprExtension f tp |])

instance NuMatching (EmptyExprExtension f tp) where
  nuMatchingProof = unsafeMbTypeRepr


instance NuMatchingAny1 (EmptyExprExtension f) where
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

instance Liftable (TypedEntryID blocks args ghosts) where
  mbLift [nuP| TypedEntryID entryBlockID entryGhosts entryIndex |] =
    TypedEntryID { entryBlockID = mbLift entryBlockID,
                   entryGhosts = mbLift entryGhosts,
                   entryIndex = mbLift entryIndex }


----------------------------------------------------------------------
-- * Typed Crucible Statements
----------------------------------------------------------------------

-- | Typed Crucible statements with the given Crucible syntax extension and the
-- given set of return values
data TypedStmt ext (rets :: RList CrucibleType) ps_in ps_out where

  -- | Assign a pure value to a register, where pure here means that its
  -- translation to SAW will be pure (i.e., no LLVM pointer operations)
  TypedSetReg :: TypeRepr tp -> TypedExpr ext tp ->
                 TypedStmt ext (RNil :> tp) RNil (RNil :> tp)

  -- | Function call (FIXME: document the type here)
  TypedCall :: args ~ CtxToRList cargs =>
               TypedReg (FunctionHandleType cargs ret) ->
               FunPerm ghosts args ret ->
               PermExprs ghosts -> TypedRegs args ->
               ExprVar LifetimeType -> PermExpr PermListType ->
               TypedStmt ext (RNil :> ret)
               (args :> LifetimeType :> FunctionHandleType cargs ret)
               (args :> ret :> LifetimeType)

  -- | Begin a new lifetime:
  --
  -- > . -o ret:lowned(nil)
  BeginLifetime :: TypedStmt ext (RNil :> LifetimeType)
                   RNil (RNil :> LifetimeType)

  -- | End a lifetime, consuming the minimal lifetime ending permissions for the
  -- lifetime as well as all permissions that still contain the lifetime, and
  -- returning the permissions stored in the @lowned@ permission:
  --
  -- > minLtEndperms(ps) * ps_l * l:lowned(ps) -o ps
  EndLifetime :: ExprVar LifetimeType -> DistPerms ps ->
                 PermExpr PermListType -> DistPerms ps_l ->
                 TypedStmt ext RNil (ps :> LifetimeType :++: ps_l) ps

  -- | Assert a boolean condition, printing the given string on failure
  TypedAssert :: TypedReg BoolType -> TypedReg StringType ->
                 TypedStmt ext RNil RNil RNil

  -- | LLVM-specific statement
  TypedLLVMStmt :: TypedLLVMStmt (ArchWidth arch) ret ps_in ps_out ->
                   TypedStmt (LLVM arch) (RNil :> ret) ps_in ps_out


data TypedLLVMStmt w ret ps_in ps_out where
  -- | Assign an LLVM word (i.e., a pointer with block 0) to a register
  --
  -- Type: @. -o ret:eq(word(x))@
  ConstructLLVMWord :: (1 <= w2, KnownNat w2) =>
                       TypedReg (BVType w2) ->
                       TypedLLVMStmt w (LLVMPointerType w2)
                       RNil
                       (RNil :> LLVMPointerType w2)

  -- | Assert that an LLVM pointer is a word, and return 0. This is the typed
  -- version of 'LLVM_PointerBlock' when we know the input is a word, i.e., has
  -- a pointer block value of 0.
  --
  -- Type: @x:eq(word(y)) -o ret:eq(0)@
  AssertLLVMWord :: (1 <= w2, KnownNat w2) =>
                    TypedReg (LLVMPointerType w2) -> PermExpr (BVType w2) ->
                    TypedLLVMStmt w NatType
                    (RNil :> LLVMPointerType w2)
                    (RNil :> NatType)


  -- | Assert that an LLVM pointer is a pointer
  --
  -- Type: @x:is_llvmptr -o .@
  AssertLLVMPtr :: (1 <= w2, KnownNat w2) => TypedReg (LLVMPointerType w2) ->
                   TypedLLVMStmt w UnitType (RNil :> LLVMPointerType w2) RNil

  -- | Destruct an LLVM word into its bitvector value, which should equal the
  -- given expression
  --
  -- Type: @x:eq(word(e)) -o ret:eq(e)@
  DestructLLVMWord :: (1 <= w2, KnownNat w2) =>
                      TypedReg (LLVMPointerType w2) -> PermExpr (BVType w2) ->
                      TypedLLVMStmt w (BVType w2)
                      (RNil :> LLVMPointerType w2)
                      (RNil :> BVType w2)

  -- | Add an offset to an LLVM value
  --
  -- Type: @. -o ret:eq(x &+ off)@
  OffsetLLVMValue :: (1 <= w2, KnownNat w2) =>
                     TypedReg (LLVMPointerType w2) -> TypedReg (BVType w2) ->
                     TypedLLVMStmt w (LLVMPointerType w2)
                     RNil
                     (RNil :> LLVMPointerType w2)

  -- | Load a machine value from the address pointed to by the given pointer
  -- using the supplied field permission. Some set of permissions @ps@ can be on
  -- the stack below the field permission, and these are preserved. The lifetime
  -- of the field permission must also be proved to be current; the permissions
  -- for this are on the top of the stack and are also preserved.
  --
  -- Type:
  -- > ps, x:ptr((rw,0) |-> p), cur_ps
  -- > -o ps, x:ptr((rw,0) |-> eq(ret)), ret:p, cur_ps
  TypedLLVMLoad :: (1 <= w, KnownNat w) =>
                   TypedReg (LLVMPointerType w) -> LLVMFieldPerm w ->
                   DistPerms ps -> LifetimeCurrentPerms ps_l ->
                   TypedLLVMStmt w (LLVMPointerType w)
                   (ps :> LLVMPointerType w :++: ps_l)
                   (ps :> LLVMPointerType w :> LLVMPointerType w :++: ps_l)

  -- | Store a machine value to the address pointed to by the given pointer
  -- using the supplied field permission, which also specifies the offset from
  -- the pointer where the store occurs. Some set of permissions @ps@ can be on
  -- the stack below the field permission, and these are preserved. The lifetime
  -- of the field permission must also be proved to be current; the permissions
  -- for this are on the top of the stack and are also preserved.
  --
  -- Type:
  -- > ps, x:ptr((rw,0) |-> p), cur_ps
  -- > -o ps, x:ptr((rw,0) |-> eq(e)), cur_ps
  TypedLLVMStore :: (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
                    LLVMFieldPerm w -> PermExpr (LLVMPointerType w) ->
                    DistPerms ps -> LifetimeCurrentPerms ps_l ->
                    TypedLLVMStmt w UnitType
                    (ps :> LLVMPointerType w :++: ps_l)
                    (ps :> LLVMPointerType w :++: ps_l)

  -- | Allocate an object of the given size on the given LLVM frame
  --
  -- Type:
  -- > fp:frame(ps) -o fp:frame(ps,(ret,i)),
  -- >                 ret:ptr((w,0) |-> true, (w,M) |-> true,
  -- >                         ..., (w,M*(i-1)) |-> true)
  --
  -- where @M@ is the machine word size in bytes
  TypedLLVMAlloca :: (1 <= w, KnownNat w) => TypedReg (LLVMFrameType w) ->
                     LLVMFramePerm w -> Integer ->
                     TypedLLVMStmt w (LLVMPointerType w)
                     (RNil :> LLVMFrameType w)
                     (RNil :> LLVMFrameType w :> LLVMPointerType w)

  -- | Create a new LLVM frame
  --
  -- Type: @. -o ret:frame()@
  TypedLLVMCreateFrame :: (1 <= w, KnownNat w) =>
                          TypedLLVMStmt w (LLVMFrameType w) RNil
                          (RNil :> LLVMFrameType w)

  -- | Delete an LLVM frame and deallocate all memory objects allocated in it,
  -- assuming that the current distinguished permissions @ps@ correspond to the
  -- write permissions to all those objects allocated on the frame
  --
  -- Type: @ps, fp:frame(ps) -o .@
  TypedLLVMDeleteFrame :: (1 <= w, KnownNat w) => TypedReg (LLVMFrameType w) ->
                          LLVMFramePerm w -> DistPerms ps ->
                          TypedLLVMStmt w UnitType (ps :> LLVMFrameType w) RNil


-- | Return the input permissions for a 'TypedStmt'
typedStmtIn :: TypedStmt ext rets ps_in ps_out -> DistPerms ps_in
typedStmtIn (TypedSetReg _ _) = DistPermsNil
typedStmtIn (TypedCall (TypedReg f) fun_perm ghosts args l ps) =
  DistPermsCons
  (DistPermsCons
   (funPermDistIns fun_perm (typedRegsToVars args) l ghosts)
   l (ValPerm_Conj1 $ Perm_LOwned ps))
  f (ValPerm_Conj1 $ Perm_Fun fun_perm)
typedStmtIn BeginLifetime = DistPermsNil
typedStmtIn (EndLifetime l perms ps end_perms) =
  case permListToDistPerms ps of
    Some perms'
      | Just Refl <- testEquality perms' perms ->
        appendDistPerms
        (DistPermsCons (minLtEndPerms (PExpr_Var l) perms)
         l (ValPerm_Conj [Perm_LOwned ps]))
        end_perms
    _ -> error "typedStmtIn: EndLifetime: malformed arguments"
typedStmtIn (TypedAssert _ _) = DistPermsNil
typedStmtIn (TypedLLVMStmt llvmStmt) = typedLLVMStmtIn llvmStmt

-- | Return the input permissions for a 'TypedLLVMStmt'
typedLLVMStmtIn :: TypedLLVMStmt w ret ps_in ps_out -> DistPerms ps_in
typedLLVMStmtIn (ConstructLLVMWord _) = DistPermsNil
typedLLVMStmtIn (AssertLLVMWord (TypedReg x) e) =
  distPerms1 x (ValPerm_Eq $ PExpr_LLVMWord e)
typedLLVMStmtIn (AssertLLVMPtr (TypedReg x)) =
  distPerms1 x (ValPerm_Conj1 Perm_IsLLVMPtr)
typedLLVMStmtIn (DestructLLVMWord (TypedReg x) e) =
  distPerms1 x (ValPerm_Eq $ PExpr_LLVMWord e)
typedLLVMStmtIn (OffsetLLVMValue _ _) =
  DistPermsNil
typedLLVMStmtIn (TypedLLVMLoad (TypedReg x) fp ps ps_l) =
  permAssert
  (lifetimeCurrentPermsLifetime ps_l == llvmFieldLifetime fp)
  "typedLLVMStmtIn: TypedLLVMLoad: mismatch for field lifetime" $
  permAssert (bvEq (llvmFieldOffset fp) (bvInt 0))
  "typedLLVMStmtIn: TypedLLVMLoad: mismatch for field offset" $
  appendDistPerms
  (DistPermsCons ps x (ValPerm_Conj1 $ Perm_LLVMField fp))
  (lifetimeCurrentPermsPerms ps_l)
typedLLVMStmtIn (TypedLLVMStore (TypedReg x) fp _ ps cur_ps) =
  permAssert (llvmFieldRW fp == PExpr_Write &&
              bvEq (llvmFieldOffset fp) (bvInt 0) &&
              llvmFieldLifetime fp == lifetimeCurrentPermsLifetime cur_ps)
  "typedLLVMStmtIn: TypedLLVMStore: mismatch for field permission" $
  appendDistPerms
  (DistPermsCons ps x (ValPerm_Conj1 $ Perm_LLVMField fp))
  (lifetimeCurrentPermsPerms cur_ps)
typedLLVMStmtIn (TypedLLVMAlloca (TypedReg f) fperms _) =
  distPerms1 f (ValPerm_Conj [Perm_LLVMFrame fperms])
typedLLVMStmtIn TypedLLVMCreateFrame = DistPermsNil
typedLLVMStmtIn (TypedLLVMDeleteFrame (TypedReg f) fperms perms) =
  case llvmFrameDeletionPerms fperms of
    Some perms'
      | Just Refl <- testEquality perms perms' ->
        DistPermsCons perms f (ValPerm_Conj1 $ Perm_LLVMFrame fperms)
    _ -> error "typedLLVMStmtIn: incorrect perms in rule"

-- | Return the output permissions for a 'TypedStmt'
typedStmtOut :: TypedStmt ext rets ps_in ps_out -> MapRList Name rets ->
                DistPerms ps_out
typedStmtOut (TypedSetReg _ (TypedExpr _ (Just e))) (_ :>: ret) =
  distPerms1 ret (ValPerm_Eq e)
typedStmtOut (TypedSetReg _ (TypedExpr _ Nothing)) (_ :>: ret) =
  distPerms1 ret ValPerm_True
typedStmtOut (TypedCall _ fun_perm ghosts args l ps) (_ :>: ret) =
  DistPermsCons
  (funPermDistOuts fun_perm (typedRegsToVars args :>: ret) l ghosts)
  l (ValPerm_Conj1 $ Perm_LOwned ps)
typedStmtOut BeginLifetime (_ :>: l) =
  distPerms1 l $ ValPerm_Conj [Perm_LOwned PExpr_PermListNil]
typedStmtOut (EndLifetime l perms _ _) _ = perms
typedStmtOut (TypedAssert _ _) _ = DistPermsNil
typedStmtOut (TypedLLVMStmt llvmStmt) (_ :>: ret) =
  typedLLVMStmtOut llvmStmt ret

-- | Return the output permissions for a 'TypedStmt'
typedLLVMStmtOut :: TypedLLVMStmt w ret ps_in ps_out -> Name ret ->
                    DistPerms ps_out
typedLLVMStmtOut (ConstructLLVMWord (TypedReg x)) ret =
  distPerms1 ret (ValPerm_Eq $ PExpr_LLVMWord $ PExpr_Var x)
typedLLVMStmtOut (AssertLLVMWord (TypedReg x) _) ret =
  distPerms1 ret (ValPerm_Eq $ PExpr_Nat 0)
typedLLVMStmtOut (AssertLLVMPtr _) _ = DistPermsNil
typedLLVMStmtOut (DestructLLVMWord (TypedReg x) e) ret =
  distPerms1 ret (ValPerm_Eq e)
typedLLVMStmtOut (OffsetLLVMValue (TypedReg x) (TypedReg off)) ret =
  distPerms1 ret (ValPerm_Eq $ PExpr_LLVMOffset x $ PExpr_Var off)
typedLLVMStmtOut (TypedLLVMLoad (TypedReg x) fp ps ps_l) ret =
  if lifetimeCurrentPermsLifetime ps_l == llvmFieldLifetime fp then
    appendDistPerms
    (DistPermsCons
     (DistPermsCons ps
      x (ValPerm_Conj1 $ Perm_LLVMField $
         fp { llvmFieldContents = ValPerm_Eq (PExpr_Var ret) }))
     ret (llvmFieldContents fp))
    (lifetimeCurrentPermsPerms ps_l)
  else
    error "typedLLVMStmtOut: TypedLLVMLoad: mismatch for field lifetime"
typedLLVMStmtOut (TypedLLVMStore (TypedReg x) fp e ps cur_ps) _ =
  permAssert (llvmFieldRW fp == PExpr_Write &&
              bvEq (llvmFieldOffset fp) (bvInt 0) &&
              llvmFieldLifetime fp == lifetimeCurrentPermsLifetime cur_ps)
  "typedLLVMStmtOut: TypedLLVMStore: mismatch for field permission" $
  appendDistPerms
  (DistPermsCons ps x (ValPerm_Conj1 $ Perm_LLVMField $
                       fp { llvmFieldContents = ValPerm_Eq e }))
  (lifetimeCurrentPermsPerms cur_ps)
typedLLVMStmtOut (TypedLLVMAlloca
                  (TypedReg f) (fperms :: LLVMFramePerm w) len) ret =
  distPerms2 f (ValPerm_Conj [Perm_LLVMFrame ((PExpr_Var ret, len):fperms)])
  ret (llvmFieldsPermOfSize Proxy len)
typedLLVMStmtOut TypedLLVMCreateFrame ret =
  distPerms1 ret $ ValPerm_Conj [Perm_LLVMFrame []]
typedLLVMStmtOut (TypedLLVMDeleteFrame _ _ _) _ = DistPermsNil


-- | Check that the permission stack of the given permission set matches the
-- input permissions of the given statement, and replace them with the output
-- permissions of the statement
applyTypedStmt :: TypedStmt ext rets ps_in ps_out -> MapRList Name rets ->
                  PermSet ps_in -> PermSet ps_out
applyTypedStmt stmt rets =
  modifyDistPerms $ \perms ->
  if perms == typedStmtIn stmt then
    typedStmtOut stmt rets
  else
    error "applyTypedStmt: unexpected input permissions!"


----------------------------------------------------------------------
-- * Typed Sequences of Crucible Statements
----------------------------------------------------------------------

-- | Typed return argument
data TypedRet ret ps =
  TypedRet (TypeRepr ret) (TypedReg ret) (Binding ret (DistPerms ps))


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
                   TypedStmt ext rets ps_in ps_next ->
                   Mb rets (TypedStmtSeq ext blocks ret ps_next) ->
                   TypedStmtSeq ext blocks ret ps_in

  -- | Typed version of 'TermStmt', which terminates the current block
  TypedTermStmt :: ProgramLoc ->
                   TypedTermStmt blocks ret ps_in ->
                   TypedStmtSeq ext blocks ret ps_in


$(mkNuMatching [t| forall w tp ps_out ps_in.
                TypedLLVMStmt w tp ps_out ps_in |])
$(mkNuMatching [t| forall ext rets ps_in ps_out. NuMatchingExtC ext =>
                TypedStmt ext rets ps_in ps_out |])
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
    !(TypedEntryID blocks args ghosts) -> !(CruCtx args) -> !(TypeRepr ret) ->
    !(MbDistPerms (ghosts :++: args)) ->
    -- FIXME: I think ret_ps here should = inits...?
    !(Mb (ghosts :++: args :> ret) (DistPerms ret_ps)) ->
    !(Mb (ghosts :++: args) (TypedStmtSeq ext blocks ret (ghosts :++: args))) ->
    TypedEntry ext blocks ret args

typedEntryIndex :: TypedEntry ext blocks ret args -> Int
typedEntryIndex (TypedEntry entryID _ _ _ _ _) = entryIndex entryID

-- | A typed Crucible block is a list of typed entrypoints to that block
newtype TypedBlock ext blocks ret args
  = TypedBlock [TypedEntry ext blocks ret args]

-- | A map assigning a 'TypedBlock' to each 'BlockID'
type TypedBlockMap ext blocks ret =
  MapRList (TypedBlock ext blocks ret) blocks

instance Show (TypedEntry ext blocks ret args) where
  show (TypedEntry entryID _ _ _ _ _) =
    "<entry " ++ show (entryIDIndices entryID) ++ ">"

instance Show (TypedBlock ext blocks ret args) where
  show (TypedBlock entries) = show entries

instance Show (TypedBlockMap ext blocks ret) where
  show blkMap =
    show $ mapRListToList $ mapMapRList (Constant . show) blkMap

-- | A typed Crucible CFG
data TypedCFG
     (ext :: Type)
     (blocks :: RList (RList CrucibleType))
     (ghosts :: RList CrucibleType)
     (inits :: RList CrucibleType)
     (ret :: CrucibleType)
  = TypedCFG { tpcfgHandle :: !(TypedFnHandle ghosts inits ret)
             , tpcfgFunPerm :: !(FunPerm ghosts inits ret)
             , tpcfgBlockMap :: !(TypedBlockMap ext blocks ret)
             , tpcfgEntryBlockID ::
                 !(TypedEntryID blocks inits (ghosts :> LifetimeType))
             }


tpcfgInputPerms :: TypedCFG ext blocks ghosts inits ret ->
                   Mb (ghosts :> LifetimeType) (MbValuePerms inits)
tpcfgInputPerms = funPermIns . tpcfgFunPerm

tpcfgOutputPerms :: TypedCFG ext blocks ghosts inits ret ->
                    Mb (ghosts :> LifetimeType) (MbValuePerms (inits :> ret))
tpcfgOutputPerms = funPermOuts . tpcfgFunPerm


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
    stVarTypes :: NameMap TypeRepr,
    stPPInfo   :: PPInfo
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
    entryInfoPermsOut :: Mb (ghosts :++: args :> ret) (DistPerms ret_ps)
  } -> BlockEntryInfo blocks ret args

-- | Extract the 'BlockID' from entrypoint info
entryInfoBlockID :: BlockEntryInfo blocks ret args -> Member blocks args
entryInfoBlockID (BlockEntryInfo entryID _ _ _) = entryBlockID entryID

-- | Extract the entry id from entrypoint info
entryInfoIndex :: BlockEntryInfo blocks ret args -> Int
entryInfoIndex (BlockEntryInfo entryID _ _ _) = entryIndex entryID

-- | Extract the block id, entry id pair from a 'BlockEntryInfo"
entryInfoIndices :: BlockEntryInfo blocks ret args -> (Int, Int)
entryInfoIndices (BlockEntryInfo entryID _ _ _) = entryIDIndices entryID

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
                     Mb (ghosts :++: args :> ret) (DistPerms ret_ps) ->
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

blockInfoMapIxs :: BlockInfoMap ext blocks ret -> [(Int,Int)]
blockInfoMapIxs =
  concat . mapRListToList . mapMapRList
  (Constant . map entryInfoIndices . blockInfoEntries)


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
                        Mb (ghosts :++: args :> ret) (DistPerms ret_ps) ->
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
    stRetType :: TypeRepr ret,
    stBlockTrans :: Assignment (BlockIDTrans blocks) cblocks,
    stBlockInfo :: BlockInfoMap ext blocks ret,
    stPermEnv :: PermEnv
  }

{-
$(mkNuMatching [t| forall ext cblocks blocks ret.
                TopPermCheckState ext cblocks blocks ret |])

instance Closable (TopPermCheckState ext cblocks blocks ret) where
  toClosed (TopPermCheckState {..}) =
    $(mkClosed [| TopPermCheckState |])
    `clApply` (toClosed stRetType)
    `clApplyCl` stBlockTrans
    `clApplyCl` stBlockInfo
    `clApplyCl` stFunTypeEnv

instance BindState (TopPermCheckState ext cblocks blocks ret) where
  bindState [nuP| TopPermCheckState retType bt i env |] =
    TopPermCheckState (mbLift retType) (mbLift bt) (mbLift i) (mbLift env)
-}

-- | Build an empty 'TopPermCheckState' from a Crucible 'BlockMap'
emptyTopPermCheckState ::
  TypeRepr ret -> BlockMap ext cblocks ret -> Closed PermEnv ->
  Closed (TopPermCheckState ext cblocks (CtxCtxToRList cblocks) ret)
emptyTopPermCheckState ret blkMap cl_env =
  $(mkClosed [| \ret' blkMap' env' ->
               TopPermCheckState
              { stRetType = ret'
              , stBlockTrans = buildBlockIDMap blkMap'
              , stBlockInfo = emptyBlockInfoMap blkMap'
              , stPermEnv = env' } |])
  `clApply` toClosed ret `clApply` closeAssign toClosed blkMap `clApply` cl_env


-- | Look up a Crucible block id in a top-level perm-checking state
stLookupBlockID :: BlockID cblocks args ->
                   TopPermCheckState ext cblocks blocks ret ->
                   Member blocks (CtxToRList args)
stLookupBlockID (BlockID ix) st =
  unBlockIDTrans $ stBlockTrans st Ctx.! ix

-- | The top-level monad for permission-checking CFGs
type TopPermCheckM ext cblocks blocks ret =
  State (Closed (TopPermCheckState ext cblocks blocks ret))

modifyBlockInfo :: Closed (BlockInfoMap ext blocks ret ->
                           BlockInfoMap ext blocks ret) ->
                   TopPermCheckM ext cblocks blocks ret ()
modifyBlockInfo f =
  modify (\cl_st ->
           $(mkClosed [| \f st -> st { stBlockInfo = f (stBlockInfo st) } |])
           `clApply` f `clApply` cl_st)

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
        stVarTypes = NameMap.empty,
        stPPInfo   = emptyPPInfo } in
  runGenContM (runGenStateT m st) (\((), _) -> return ())


-- | Get the current top-level state
top_get :: PermCheckM ext cblocks blocks ret args r ps r ps
           (Closed (TopPermCheckState ext cblocks blocks ret))
top_get = gcaptureCC $ \k -> get >>= k

lookupBlockInfo :: Member blocks args ->
                   PermCheckM ext cblocks blocks ret args_in r ps r ps
                   (BlockInfo ext blocks ret args)
lookupBlockInfo memb =
  top_get >>>= \top_st ->
  greturn (mapRListLookup memb $ stBlockInfo $ unClosed top_st)

insNewBlockEntry :: Member blocks args -> CruCtx args -> CruCtx ghosts ->
                    Closed (MbDistPerms (ghosts :++: args)) ->
                    Closed (Mb (ghosts :++: args :> ret) (DistPerms ret_ps)) ->
                    TopPermCheckM ext cblocks blocks ret
                    (TypedEntryID blocks args ghosts)
insNewBlockEntry memb arg_tps ghost_tps perms_in perms_ret =
  do cl_st <- get
     let cl_blkMap_entryID =
           $(mkClosed [| blockInfoMapAddEntry |])
           `clApply` toClosed memb `clApply` toClosed arg_tps
           `clApply` toClosed ghost_tps
           `clApply` perms_in `clApply` perms_ret `clApply`
           ($(mkClosed [| stBlockInfo |]) `clApply` cl_st)
     put ($(mkClosed [| \st x -> st { stBlockInfo = fst x } |])
          `clApply` cl_st `clApply` cl_blkMap_entryID)
     return $ snd $ unClosed cl_blkMap_entryID

-- | Look up the current primary permission associated with a variable
getVarPerm :: ExprVar a ->
              PermCheckM ext cblocks blocks ret args r ps r ps (ValuePerm a)
getVarPerm x = view (varPerm x) <$> stCurPerms <$> gget

-- | Set the current primary permission associated with a variable
setVarPerm :: ExprVar a -> ValuePerm a ->
              PermCheckM ext cblocks blocks ret args r ps r ps ()
setVarPerm x p = gmodify $ modifySTCurPerms $ set (varPerm x) p

-- | Look up the current primary permission associated with a register
getRegPerm :: TypedReg a ->
              PermCheckM ext cblocks blocks ret args r ps r ps (ValuePerm a)
getRegPerm (TypedReg x) = getVarPerm x

-- | Eliminate any disjunctions, existentials, or recursive permissions for a
-- register and then return the resulting "simple" permission, leaving it on the
-- top of the stack
getPushSimpleRegPerm :: TypedReg a ->
                        StmtPermCheckM ext cblocks blocks ret args
                        (ps :> a) ps (ValuePerm a)
getPushSimpleRegPerm r =
  getRegPerm r >>>= \p_init ->
  embedImplM TypedImplStmt emptyCruCtx
  (implPushM (typedRegVar r) p_init >>>
   elimOrsExistsRecsM (typedRegVar r)) >>>= \(_, p_ret) ->
  greturn p_ret

-- | Eliminate any disjunctions, existentials, or recursive permissions for a
-- register and then return the resulting "simple" permission
getSimpleRegPerm :: TypedReg a ->
                    StmtPermCheckM ext cblocks blocks ret args ps ps (ValuePerm a)
getSimpleRegPerm r =
  getRegPerm r >>>= \p_init ->
  embedImplM TypedImplStmt emptyCruCtx
  (implPushM (typedRegVar r) p_init >>>
   elimOrsExistsRecsM (typedRegVar r) >>>= \p ->
    implPopM (typedRegVar r) p >>> greturn p) >>>= \(_, p_ret) ->
  greturn p_ret


-- | Eliminate any disjunctions, existentials, recursive permissions, or
-- equality permissions for an LLVM register until we either get a conjunctive
-- permission for it or we get that it is equal to a bitvector word. In either
-- case, leave the resulting permission on the top of the stack and return its
-- contents as the return value.
getAtomicOrWordLLVMPerms ::
  (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
  StmtPermCheckM ext cblocks blocks ret args
  (ps :> LLVMPointerType w)
  ps
  (Either (PermExpr (BVType w)) [AtomicPerm (LLVMPointerType w)])
getAtomicOrWordLLVMPerms r =
  let x = typedRegVar r in
  getPushSimpleRegPerm r >>>= \p ->
  case p of
    ValPerm_Conj ps ->
      greturn $ Right ps
    ValPerm_Eq (PExpr_Var y) ->
      embedImplM TypedImplStmt emptyCruCtx
      (introEqCopyM x (PExpr_Var y) >>> recombinePerm x p) >>>
      getAtomicOrWordLLVMPerms (TypedReg y) >>>= \eith ->
      case eith of
        Left e ->
          embedImplM TypedImplStmt emptyCruCtx
          (introCastM x y $ ValPerm_Eq $ PExpr_LLVMWord e) >>>
          greturn (Left e)
        Right ps ->
          embedImplM TypedImplStmt emptyCruCtx (introCastM x y $
                                                ValPerm_Conj ps) >>>
          greturn (Right ps)
    ValPerm_Eq e@(PExpr_LLVMOffset y off) ->
      embedImplM TypedImplStmt emptyCruCtx
      (introEqCopyM x e >>> recombinePerm x p) >>>
      getAtomicOrWordLLVMPerms (TypedReg y) >>>= \eith ->
      case eith of
        Left e ->
          embedImplM TypedImplStmt emptyCruCtx (offsetLLVMWordM y e off x) >>>
          greturn (Left $ bvAdd e off)
        Right ps ->
          embedImplM TypedImplStmt emptyCruCtx (castLLVMPtrM y ps off x) >>>
          greturn (Right $ map (offsetLLVMAtomicPerm $ bvNegate off) ps)
    ValPerm_Eq e@(PExpr_LLVMWord e_word) ->
      embedImplM TypedImplStmt emptyCruCtx (introEqCopyM x e >>>
                                            recombinePerm x p) >>>
      greturn (Left e_word)


-- | Like 'getAtomicOrWordLLVMPerms', but fail if an equality permission to a
-- bitvector word is found
getAtomicLLVMPerms :: (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
                      StmtPermCheckM ext cblocks blocks ret args
                      (ps :> LLVMPointerType w)
                      ps
                      [AtomicPerm (LLVMPointerType w)]
getAtomicLLVMPerms r =
  getAtomicOrWordLLVMPerms r >>>= \eith ->
  case eith of
    Right ps -> greturn ps
    Left e ->
      stmtFailM (\i ->
                  sep [string "getAtomicLLVMPerms:",
                       string "Needed atomic permissions for" <+> permPretty i r,
                       string "but found" <+>
                       permPretty i (ValPerm_Eq $ PExpr_LLVMWord e)])


-- | Look up the function permission associated with a typed register
getRegFunPerm :: TypedReg (FunctionHandleType cargs fret) ->
                 StmtPermCheckM ext cblocks blocks ret args ps ps
                 (SomeFunPerm (CtxToRList cargs) fret)
getRegFunPerm freg =
  (stPermEnv <$> unClosed <$> top_get) >>>= \env ->
  getSimpleRegPerm freg >>>= \p_freg ->
  case p_freg of
    ValPerm_Eq (PExpr_Fun f)
      | Just (some_fun_perm, _) <- lookupFunPerm env f ->
          greturn some_fun_perm
    ValPerm_Conj [Perm_Fun fun_perm] -> greturn (SomeFunPerm fun_perm)
    _ -> stmtFailM (\i ->
                     string "No function permission for" <+> permPretty i freg)

-- | Find all the variables of LLVM frame pointer type in a sequence
-- FIXME: move to Permissions.hs
findLLVMFrameVars :: NatRepr w -> CruCtx as -> MapRList Name as ->
                     [ExprVar (LLVMFrameType w)]
findLLVMFrameVars _ CruCtxNil _ = []
findLLVMFrameVars w (CruCtxCons tps (LLVMFrameRepr w')) (ns :>: n) =
  case testEquality w w' of
    Just Refl -> n : findLLVMFrameVars w tps ns
    Nothing -> error "findLLVMFrameVars: found LLVM frame pointer of wrong type"
findLLVMFrameVars w (CruCtxCons tps _) (ns :>: _) = findLLVMFrameVars w tps ns


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
              PermCheckM ext cblocks blocks ret args r ps r ps (TypeRepr a)
getVarType x =
  (NameMap.lookup x <$> stVarTypes <$> gget) >>>= \maybe_tp ->
  case maybe_tp of
    Just tp -> greturn tp
    Nothing ->
      stmtTraceM (\i -> string "getVarType: could not find type for variable:"
                        <+> permPretty i x) >>>
      error "getVarType"

-- | Look up the types of multiple free variables
getVarTypes :: MapRList Name tps ->
               PermCheckM ext cblocks blocks ret args r ps r ps (CruCtx tps)
getVarTypes MNil = greturn CruCtxNil
getVarTypes (xs :>: x) = CruCtxCons <$> getVarTypes xs <*> getVarType x

-- | Remember the type of a free variable, and ensure that it has a permission
setVarType :: ExprVar a -> TypeRepr a ->
              PermCheckM ext cblocks blocks ret args r ps r ps ()
setVarType x tp =
  gmodify $ \st ->
  st { stCurPerms = initVarPerm x (stCurPerms st),
       stVarTypes = NameMap.insert x tp (stVarTypes st),
       stPPInfo = ppInfoAddExprName "x" x (stPPInfo st) }

-- | Remember the types of a sequence of free variables
setVarTypes :: MapRList Name tps -> CruCtx tps ->
               PermCheckM ext cblocks blocks ret args r ps r ps ()
setVarTypes _ CruCtxNil = greturn ()
setVarTypes (xs :>: x) (CruCtxCons tps tp) =
  setVarTypes xs tps >>> setVarType x tp

-- | Emit debugging output using the current 'PPInfo'
stmtTraceM :: (PPInfo -> Doc) ->
              PermCheckM ext cblocks blocks ret args r ps r ps ()
stmtTraceM f =
  (f <$> stPPInfo <$> get) >>>= \doc -> tracePretty doc (greturn ())

-- | Failure in the statement permission-checking monad
stmtFailM :: (PPInfo -> Doc) -> PermCheckM ext cblocks blocks ret args r1 ps1
             (TypedStmtSeq ext blocks ret ps2) ps2 a
stmtFailM msg =
  stmtTraceM (\i -> string "Type-checking failure:" <+> msg i) >>>
  gabortM (return $ TypedImplStmt $
           PermImpl_Step Impl1_Fail MbPermImpls_Nil)

-- | Smart constructor for applying a function on 'PermImpl's
applyImplFun :: (PermImpl r ps -> r ps) -> PermImpl r ps -> r ps
applyImplFun _ (PermImpl_Done r) = r
applyImplFun f impl = f impl

-- | FIXME HERE: Make 'ImplM' quantify over any underlying monad, so that we do
-- not have to use 'traversePermImpl' after we run an 'ImplM'
data WithImplState vars a ps ps' =
  WithImplState a (ImplState vars ps) (ps' :~: ps)

-- | Embed an implication computation inside a permission-checking computation
embedImplM :: (forall ps. PermImpl r ps -> r ps) -> CruCtx vars ->
              ImplM vars (TopPermCheckState ext cblocks blocks ret)
              r ps_out ps_in a ->
              PermCheckM ext cblocks blocks ret args
              (r ps_out) ps_out (r ps_in) ps_in (PermSubst vars, a)
embedImplM f_impl vars m =
  gmapRet (f_impl <$>) >>>
  (stCurPerms <$> gget) >>>= \perms_in ->
  (stPermEnv <$> unClosed <$> top_get) >>>= \env ->
  (stPPInfo <$> gget) >>>= \ppInfo ->
  (stVarTypes <$> gget) >>>= \varTypes ->
  (gcaptureCC $ \k ->
    runImplM vars perms_in env ppInfo varTypes k m) >>>= \(a, implSt) ->
  gmodify ((\st -> st { stPPInfo = implSt ^. implStatePPInfo,
                        stVarTypes = implSt ^. implStateNameTypes })
           . setSTCurPerms (implSt ^. implStatePerms)) >>>
  greturn (completePSubst vars (implSt ^. implStatePSubst), a)

-- | Special case of 'embedImplM' for a statement type-checking context where
-- @vars@ is empty
stmtEmbedImplM ::
  ImplM RNil (TopPermCheckState ext cblocks blocks ret)
  (TypedStmtSeq ext blocks ret) ps_out ps_in a
  ->
  StmtPermCheckM ext cblocks blocks ret args ps_out ps_in a
stmtEmbedImplM m =
  embedImplM TypedImplStmt emptyCruCtx m >>>= \(_,a) -> greturn a


-- | Recombine any outstanding distinguished permissions back into the main
-- permission set, in the context of type-checking statements
stmtRecombinePerms :: StmtPermCheckM ext cblocks blocks ret args RNil ps_in ()
stmtRecombinePerms =
  gget >>>= \st ->
  let dist_perms = view distPerms (stCurPerms st) in
  embedImplM TypedImplStmt emptyCruCtx (recombinePerms dist_perms) >>>= \_ ->
  greturn ()

stmtProvePerms' :: PermCheckExtC ext =>
                   CruCtx vars -> ExDistPerms vars ps ->
                   StmtPermCheckM ext cblocks blocks ret args
                   ps RNil (PermSubst vars)
stmtProvePerms' vars ps =
  embedImplM TypedImplStmt vars (proveVarsImpl ps) >>>= \(s,_) ->
  greturn s

-- | Prove permissions in the context of type-checking statements
stmtProvePerms :: (PermCheckExtC ext, KnownRepr CruCtx vars) =>
                  ExDistPerms vars ps ->
                  StmtPermCheckM ext cblocks blocks ret args
                  ps RNil (PermSubst vars)
stmtProvePerms ps = stmtProvePerms' knownRepr ps

-- | Prove a single permission in the context of type-checking statements
stmtProvePerm :: (PermCheckExtC ext, KnownRepr CruCtx vars) =>
                 TypedReg a -> Mb vars (ValuePerm a) ->
                 StmtPermCheckM ext cblocks blocks ret args
                 (ps :> a) ps (PermSubst vars)
stmtProvePerm (TypedReg x) mb_p =
  embedImplM TypedImplStmt knownRepr (proveVarImpl x mb_p) >>>= \(s,_) ->
  greturn s

-- | Try to prove that a register equals a constant integer using equality
-- permissions in the context
resolveConstant :: TypedReg tp ->
                   StmtPermCheckM ext cblocks blocks ret args ps ps
                   (Maybe Integer)
resolveConstant = helper . PExpr_Var . typedRegVar where
  helper :: PermExpr a ->
            StmtPermCheckM ext cblocks blocks ret args ps ps (Maybe Integer)
  helper (PExpr_Var x) =
    getVarPerm x >>>= \p ->
    case p of
      ValPerm_Eq e -> helper e
      _ -> greturn Nothing
  helper (PExpr_Nat i) = greturn (Just i)
  helper (PExpr_BV factors off) =
    foldM (\maybe_res (BVFactor i x) ->
            helper (PExpr_Var x) >>= \maybe_x_val ->
            case (maybe_res, maybe_x_val) of
              (Just res, Just x_val) -> return (Just (res + x_val * i))
              _ -> return Nothing)
    (Just off) factors
  helper (PExpr_LLVMWord e) = helper e
  helper (PExpr_LLVMOffset x e) =
    do maybe_x_val <- helper (PExpr_Var x)
       maybe_e_val <- helper e
       case (maybe_x_val, maybe_e_val) of
         (Just x_val, Just e_val) -> return (Just (x_val + e_val))
         _ -> return Nothing
  helper _ = return Nothing


-- FIXME HERE: documentation!
convertRegType :: ExtRepr ext -> ProgramLoc ->
                  TypedReg tp1 -> TypeRepr tp1 -> TypeRepr tp2 ->
                  StmtPermCheckM ext cblocks blocks ret args RNil RNil
                  (TypedReg tp2)
convertRegType _ _ reg tp1 tp2
  | Just Refl <- testEquality tp1 tp2 = greturn reg
convertRegType _ loc reg (BVRepr w1) tp2@(BVRepr w2)
  | Left LeqProof <- decideLeq (knownNat :: NatRepr 1) w2
  , NatCaseGT LeqProof <- testNatCases w1 w2 =
    withKnownNat w2 $
    emitStmt knownRepr loc (TypedSetReg tp2 $
                            TypedExpr (BVTrunc w2 w1 $ RegNoVal reg)
                            Nothing) >>>= \(_ :>: x) ->
    stmtRecombinePerms >>>
    greturn (TypedReg x)
convertRegType _ loc reg (BVRepr w1) tp2@(BVRepr w2)
  | Left LeqProof <- decideLeq (knownNat :: NatRepr 1) w1
  , Left LeqProof <- decideLeq (knownNat :: NatRepr 1) w2
  , NatCaseLT LeqProof <- testNatCases w1 w2 =
    withKnownNat w2 $
    emitStmt knownRepr loc (TypedSetReg tp2 $
                            TypedExpr (BVSext w2 w1 $ RegNoVal reg)
                            Nothing) >>>= \(_ :>: x) ->
    stmtRecombinePerms >>>
    greturn (TypedReg x)
convertRegType ExtRepr_LLVM loc reg (LLVMPointerRepr w1) (BVRepr w2)
  | Just Refl <- testEquality w1 w2 =
    withKnownNat w1 $
    stmtProvePerm reg llvmExEqWord >>>= \subst ->
    let e = substLookup subst Member_Base in
    emitLLVMStmt knownRepr loc (DestructLLVMWord reg e) >>>= \x ->
    stmtRecombinePerms >>>
    greturn (TypedReg x)
convertRegType ext loc reg (LLVMPointerRepr w1) (BVRepr w2) =
  convertRegType ext loc reg (LLVMPointerRepr w1) (BVRepr w1) >>>= \reg' ->
  convertRegType ext loc reg' (BVRepr w1) (BVRepr w2)
convertRegType ExtRepr_LLVM loc reg (BVRepr w2) (LLVMPointerRepr w1)
  | Just Refl <- testEquality w1 w2 =
    withKnownNat w1 $
    emitLLVMStmt knownRepr loc (ConstructLLVMWord reg) >>>= \x ->
    stmtRecombinePerms >>> greturn (TypedReg x)
convertRegType ext loc reg (BVRepr w1) (LLVMPointerRepr w2) =
  convertRegType ext loc reg (BVRepr w1) (BVRepr w2) >>>= \reg' ->
  convertRegType ext loc reg' (BVRepr w2) (LLVMPointerRepr w2)
convertRegType ext loc reg (LLVMPointerRepr w1) (LLVMPointerRepr w2) =
  convertRegType ext loc reg (LLVMPointerRepr w1) (BVRepr w1) >>>= \reg1 ->
  convertRegType ext loc reg1 (BVRepr w1) (BVRepr w2) >>>= \reg2 ->
  convertRegType ext loc reg2 (BVRepr w2) (LLVMPointerRepr w2)
convertRegType _ _ x tp1 tp2 =
  stmtFailM (\i -> string "Could not cast" <+> permPretty i x
                   <+> string "from" <+> string (show tp1)
                   <+> string "to" <+> string (show tp2))

-- | Emit a statement in the current statement sequence, where the supplied
-- function says how that statement modifies the current permissions, given the
-- freshly-bound names for the return values. Return those freshly-bound names
-- for the return values.
emitStmt :: TypeCtx rets => CruCtx rets -> ProgramLoc ->
            TypedStmt ext rets ps_in ps_out ->
            StmtPermCheckM ext cblocks blocks ret args ps_out ps_in
            (MapRList Name rets)
emitStmt tps loc stmt =
  gopenBinding
  ((TypedConsStmt loc stmt <$>) . strongMbM)
  (nuMulti typeCtxProxies $ \vars -> ()) >>>= \(ns, ()) ->
  setVarTypes ns tps >>>
  gmodify (modifySTCurPerms $ applyTypedStmt stmt ns) >>>
  greturn ns


-- | Call emitStmt with a 'TypedLLVMStmt'
emitLLVMStmt :: TypeRepr tp -> ProgramLoc ->
                TypedLLVMStmt (ArchWidth arch) tp ps_in ps_out ->
                StmtPermCheckM (LLVM arch) cblocks blocks ret args ps_out ps_in
                (Name tp)
emitLLVMStmt tp loc stmt =
  emitStmt (singletonCruCtx tp) loc (TypedLLVMStmt stmt) >>>= \(_ :>: n) ->
  greturn n

-- | A program location for code which was generated by the type-checker
checkerProgramLoc :: ProgramLoc
checkerProgramLoc =
  mkProgramLoc (functionNameFromText "None")
  (OtherPos "(Generated by permission type-checker)")

-- | Create a new lifetime @l@
beginLifetime :: StmtPermCheckM ext cblocks blocks ret args
                 RNil RNil (ExprVar LifetimeType)
beginLifetime =
  emitStmt knownRepr checkerProgramLoc BeginLifetime >>>= \(_ :>: n) ->
  stmtRecombinePerms >>>
  greturn n

-- | End a lifetime
endLifetime :: PermCheckExtC ext => ExprVar LifetimeType ->
               StmtPermCheckM ext cblocks blocks ret args RNil RNil ()
endLifetime l =
  stmtTraceM (\i -> string "Ending lifetime" <+> permPretty i l) >>>
  getVarPerm l >>>= \l_perm ->
  case l_perm of
    ValPerm_Conj [Perm_LOwned ps_list]
      | Some ps <- permListToDistPerms ps_list ->
        stmtProvePerms (distPermsToExDistPerms $
                        minLtEndPerms (PExpr_Var l) ps) >>>= \_ ->
        stmtProvePerm (TypedReg l) (emptyMb l_perm) >>>= \_ ->
        embedImplM TypedImplStmt CruCtxNil (buildLifetimeEndPerms
                                            l) >>>= \(_, some_end_perms) ->
        case some_end_perms of
          Some end_perms ->
            stmtTraceM (\i -> string "Dropping permissions:" <+>
                              permPretty i (lifetimeEndPermsToDistPerms
                                            end_perms)) >>>
            embedImplM TypedImplStmt CruCtxNil
            (implPushLifetimeEndPerms end_perms) >>>= \_ ->
            emitStmt knownRepr checkerProgramLoc
            (EndLifetime l ps ps_list (lifetimeEndPermsToDistPerms
                                       end_perms)) >>>= \_ ->
            stmtRecombinePerms
    _ -> stmtFailM (\i ->
                     string "endLifetime: no lowned permission for"
                     <+> permPretty i l)


----------------------------------------------------------------------
-- * Permission Checking for Expressions and Statements
----------------------------------------------------------------------

-- | Get a dynamic representation of an architecture's width
archWidth :: KnownNat (ArchWidth arch) => f arch -> NatRepr (ArchWidth arch)
archWidth _ = knownNat

-- | Type-check a Crucible register by looking it up in the translated context
tcReg :: CtxTrans ctx -> Reg ctx tp -> TypedReg tp
tcReg ctx (Reg ix) = ctx ! ix

-- | Type-check a Crucible register and also look up its value, if known
tcRegWithVal :: CtxTrans ctx -> Reg ctx tp ->
                StmtPermCheckM ext cblocks blocks ret args' ps ps
                (RegWithVal tp)
tcRegWithVal ctx r_untyped =
  let r = tcReg ctx r_untyped in
  getSimpleRegPerm r >>>= \p ->
  case p of
    ValPerm_Eq e -> greturn (RegWithVal r e)
    _ -> greturn (RegNoVal r)

-- | Type-check a sequence of Crucible registers
tcRegs :: CtxTrans ctx -> Assignment (Reg ctx) tps -> TypedRegs (CtxToRList tps)
tcRegs ctx (viewAssign -> AssignEmpty) = TypedRegsNil
tcRegs ctx (viewAssign -> AssignExtend regs reg) =
  TypedRegsCons (tcRegs ctx regs) (tcReg ctx reg)


-- | Type-check a Crucibe block id into a 'Member' proof
tcBlockID :: BlockID cblocks args ->
             StmtPermCheckM ext cblocks blocks ret args' ps ps
             (Member blocks (CtxToRList args))
tcBlockID blkID = stLookupBlockID blkID <$> unClosed <$> top_get

-- | Type-check a Crucible expression to test if it has a statically known
-- 'PermExpr' value that we can use as an @eq(e)@ permission on the output of
-- the expression
tcExpr :: PermCheckExtC ext => App ext RegWithVal tp ->
          StmtPermCheckM ext cblocks blocks ret args ps ps
          (Maybe (PermExpr tp))
tcExpr (ExtensionApp e_ext :: App ext RegWithVal tp)
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = error "tcExpr: unexpected LLVM expression"

tcExpr (NatLit i) = greturn $ Just $ PExpr_Nat $ toInteger i

tcExpr (BVLit w i) = withKnownNat w $ greturn $ Just $ bvInt i

tcExpr (BVAdd w (RegWithVal _ e1) (RegWithVal _ e2)) =
  withKnownNat w $ greturn $ Just $ bvAdd e1 e2

tcExpr _ = greturn Nothing -- FIXME HERE NOW: at least handle bv operations


-- | Typecheck a statement and emit it in the current statement sequence,
-- starting and ending with an empty stack of distinguished permissions
tcEmitStmt :: PermCheckExtC ext => CtxTrans ctx -> ProgramLoc ->
              Stmt ext ctx ctx' ->
              StmtPermCheckM ext cblocks blocks ret args RNil RNil
              (CtxTrans ctx')
tcEmitStmt ctx loc stmt =
  stmtTraceM (const (string "Type-checking statement:" <+>
                     ppStmt (size ctx) stmt)) >>>
  tcEmitStmt' ctx loc stmt

tcEmitStmt' :: PermCheckExtC ext => CtxTrans ctx -> ProgramLoc ->
               Stmt ext ctx ctx' ->
               StmtPermCheckM ext cblocks blocks ret args RNil RNil
               (CtxTrans ctx')
tcEmitStmt' ctx loc (SetReg tp (App (ExtensionApp e_ext
                                     :: App ext (Reg ctx) tp)))
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = tcEmitLLVMSetExpr Proxy ctx loc e_ext
tcEmitStmt' ctx loc (SetReg tp (App e)) =
  traverseFC (tcRegWithVal ctx) e >>>= \e_with_vals ->
  tcExpr e_with_vals >>>= \maybe_val ->
  let typed_e = TypedExpr e_with_vals maybe_val in
  emitStmt (singletonCruCtx tp) loc (TypedSetReg tp typed_e) >>>= \(_ :>: x) ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx x)

tcEmitStmt' ctx loc (ExtendAssign stmt_ext :: Stmt ext ctx ctx')
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = tcEmitLLVMStmt Proxy ctx loc stmt_ext

tcEmitStmt' ctx loc (CallHandle ret freg_untyped args_ctx args_untyped) =
  let freg = tcReg ctx freg_untyped
      args = tcRegs ctx args_untyped in
  getRegFunPerm freg >>>= \some_fun_perm ->
  case some_fun_perm of
    SomeFunPerm fun_perm ->
      beginLifetime >>>= \l ->
      (stmtProvePerms' (funPermGhosts fun_perm)
       (funPermExDistIns fun_perm (typedRegsToVars args) l)) >>>= \ghosts ->
      (getVarPerm l >>>= \l_perm ->
        case l_perm of
          ValPerm_Conj [Perm_LOwned ps] -> greturn ps
          _ -> error "tcEmitStmt: CallHandle: unexpected perm on lifetime"
      ) >>>= \ps ->
      stmtProvePerm (TypedReg l) (emptyMb $
                                  ValPerm_Conj1 $ Perm_LOwned ps) >>>= \_ ->
      stmtProvePerm freg (emptyMb $ ValPerm_Conj1 $ Perm_Fun fun_perm) >>>= \_ ->
      (emitStmt (singletonCruCtx ret) loc
       (TypedCall freg fun_perm (exprsOfSubst ghosts) args l ps)
      ) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      endLifetime l >>>
      greturn (addCtxName ctx ret)

tcEmitStmt' ctx loc (Assert reg msg) =
  emitStmt CruCtxNil loc (TypedAssert (tcReg ctx reg) (tcReg ctx msg)) >>>= \_ ->
  greturn ctx

tcEmitStmt' _ _ _ = error "tcEmitStmt: unsupported statement"


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
      emitLLVMStmt knownRepr loc (ConstructLLVMWord toff_reg) >>>= \x ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx x)
    _ -> stmtFailM (\i -> "LLVM_PointerExpr: Non-zero pointer block: "
                          <> permPretty i tblk_reg)

-- Type-check the LLVM value destructor that gets the block value, by either
-- proving a permission eq(llvmword e) and returning block 0 or proving
-- permission is_llvmptr and returning the constant value 1.
--
-- NOTE: our SAW translation does not include any computational content for
-- pointer blocks and offsets, so we cannot represent the actual runtime value
-- of the pointer block of a pointer. We can only know if it is zero or not by
-- using permissions, and we map all non-zero values to 1. This implicitly
-- assumes that the behavior of the program we are verifying is not altered in a
-- meaningful way by mapping the return value of 'LLVM_PointerBlock' to 1 when
-- it is applied to pointers, which is the case for all programs currently
-- generated by Crucible from LLVM.
tcEmitLLVMSetExpr arch ctx loc (LLVM_PointerBlock w ptr_reg) =
  let tptr_reg = tcReg ctx ptr_reg
      x = typedRegVar tptr_reg in
  withKnownNat w $
  getAtomicOrWordLLVMPerms tptr_reg >>>= \eith ->
  case eith of
    Left e ->
      emitLLVMStmt knownRepr loc (AssertLLVMWord tptr_reg e) >>>= \ret ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    Right ps ->
      stmtRecombinePerms >>>
      stmtProvePerm tptr_reg (emptyMb $ ValPerm_Conj1 Perm_IsLLVMPtr) >>>
      emitLLVMStmt knownRepr loc (AssertLLVMPtr tptr_reg) >>>
      emitStmt knownRepr loc (TypedSetReg knownRepr $
                              TypedExpr (NatLit 1)
                              (Just $ PExpr_Nat 1)) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)

-- Type-check the LLVM value destructor that gets the offset value, by either
-- proving a permission eq(llvmword e) and returning block e or proving
-- permission is_llvmptr and returning the constant bitvector value 0.
--
-- NOTE: Just as with 'LLVM_PointerBlock', because our SAW translation does not
-- include any computational content for pointer blocks and offsets, we cannot
-- represent the actual runtime value of the offset of a pointer. We thus return
-- 0 as a dummy value. This implicitly assumes that the behavior of the program
-- we are verifying is not altered in a meaningful way by mapping the return
-- value of 'LLVM_PointerOffset' to 0 when it is applied to pointers, which is
-- the case for all programs currently generated by Crucible from LLVM.
tcEmitLLVMSetExpr arch ctx loc (LLVM_PointerOffset w ptr_reg) =
  let tptr_reg = tcReg ctx ptr_reg
      x = typedRegVar tptr_reg in
  withKnownNat w $
  getAtomicOrWordLLVMPerms tptr_reg >>>= \eith ->
  case eith of
    Left e ->
      emitLLVMStmt knownRepr loc (DestructLLVMWord
                                  tptr_reg e) >>>= \ret ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    Right ps ->
      stmtRecombinePerms >>>
      stmtProvePerm tptr_reg (emptyMb $ ValPerm_Conj1 Perm_IsLLVMPtr) >>>
      emitLLVMStmt knownRepr loc (AssertLLVMPtr tptr_reg) >>>
      emitStmt knownRepr loc (TypedSetReg knownRepr $
                              TypedExpr (BVLit w 0)
                              (Just $ bvInt 1)) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)


-- FIXME HERE: move withLifetimeCurrentPerms somewhere better...

-- | Perform a statement type-checking conversation inside a context where the
-- supplied lifetime has been proved to be current using the supplied
-- 'LifetimeCurrentPerms'
withLifetimeCurrentPerms ::
  PermExpr LifetimeType ->
  (forall ps_l. LifetimeCurrentPerms ps_l ->
   StmtPermCheckM ext cblocks blocks ret args (ps_out :++: ps_l)
   (ps_in :++: ps_l) a) ->
  StmtPermCheckM ext cblocks blocks ret args ps_out ps_in a
withLifetimeCurrentPerms l m =
  -- Get the proof steps needed to prove that the lifetime l is current
  stmtEmbedImplM (getLifetimeCurrentPerms l) >>>= \some_cur_perms ->
  case some_cur_perms of
    Some cur_perms ->
      -- Prove that the required permissions
      stmtEmbedImplM (proveLifetimeCurrent cur_perms) >>>
      -- Perform the computation
      m cur_perms >>>= \a ->
      -- Recombine the proof that the lifetime is current
      stmtEmbedImplM (recombineLifetimeCurrentPerms cur_perms) >>>
      -- Finally, return the result
      greturn a


-- | Emit a 'TypedLLVMLoad' instruction, assuming the given LLVM field
-- permission is on the top of the stack. Prove the required lifetime
-- permissions as part of this process, and pop the resulting lifetime
-- permission off the stack before returning. Return the resulting return
-- register.
emitTypedLLVMLoad ::
  (1 <= w, KnownNat w, w ~ ArchWidth arch) =>
  Proxy arch -> ProgramLoc ->
  TypedReg (LLVMPointerType w) -> LLVMFieldPerm w -> DistPerms ps ->
  StmtPermCheckM (LLVM arch) cblocks blocks ret args
  (ps :> LLVMPointerType w :> LLVMPointerType w)
  (ps :> LLVMPointerType w)
  (Name (LLVMPointerType (ArchWidth arch)))
emitTypedLLVMLoad _ loc treg fp ps =
  withLifetimeCurrentPerms (llvmFieldLifetime fp) $ \cur_perms ->
  emitLLVMStmt knownRepr loc (TypedLLVMLoad treg fp ps cur_perms)


-- | Emit a 'TypedLLVMStore' instruction, assuming the given LLVM field
-- permission is on the top of the stack. Prove the required lifetime
-- permissions as part of this process, and pop the resulting lifetime
-- permission off the stack before returning. Return the resulting return
-- register of unit type.
emitTypedLLVMStore ::
  (1 <= w, KnownNat w, w ~ ArchWidth arch) =>
  Proxy arch -> ProgramLoc ->
  TypedReg (LLVMPointerType (ArchWidth arch)) ->
  LLVMFieldPerm (ArchWidth arch) ->
  PermExpr (LLVMPointerType (ArchWidth arch)) -> DistPerms ps ->
  StmtPermCheckM (LLVM arch) cblocks blocks ret args
  (ps :> LLVMPointerType w)
  (ps :> LLVMPointerType w)
  (Name UnitType)
emitTypedLLVMStore _ loc treg_ptr fp e ps =
  withLifetimeCurrentPerms (llvmFieldLifetime fp) $ \cur_perms ->
  emitLLVMStmt knownRepr loc (TypedLLVMStore treg_ptr fp e ps cur_perms)


-- | Typecheck a statement and emit it in the current statement sequence,
-- starting and ending with an empty stack of distinguished permissions
tcEmitLLVMStmt ::
  (1 <= w, KnownNat w, w ~ ArchWidth arch) => Proxy arch ->
  CtxTrans ctx -> ProgramLoc -> LLVMStmt w (Reg ctx) tp ->
  StmtPermCheckM (LLVM arch) cblocks blocks ret args RNil RNil
  (CtxTrans (ctx ::> tp))

-- Type-check a load of an LLVM pointer
tcEmitLLVMStmt arch ctx loc (LLVM_Load _ reg tp _ _) =
  let treg = tcReg ctx reg
      x = typedRegVar treg in
  -- First, look for an LLVM array or field permission for offset 0
  getAtomicLLVMPerms treg >>>= \ps ->
  stmtEmbedImplM
  (foldMapWithDefault implCatchM
   (implFailMsgM "LLVM_Load: could not find permission for offset 0")
   greturn
   (findMaybeIndices (llvmPermContainsOffset $ bvInt 0) ps)) >>>= \(i,_) ->
  case ps !! i of
    Perm_LLVMField fp ->
      -- If we found a field perm for offset 0, first extract it out of all the
      -- other perms for x and pop all the other perms off of the stack
      stmtEmbedImplM (implExtractConjM x ps i >>>
                      recombinePerm x (ValPerm_Conj (deleteNth i ps))) >>>
      -- Next, emit the typed LLVM load instruction
      emitTypedLLVMLoad arch loc treg fp DistPermsNil >>>= \z ->
      -- Recombine the resulting permissions and return the new ctx
      stmtRecombinePerms >>>
      -- Finally, convert the return value to the requested type and return the
      -- result
      convertRegType knownRepr loc (TypedReg z) knownRepr tp >>>= \ret ->
      greturn (addCtxName ctx $ typedRegVar ret)

    Perm_LLVMArray ap
      | Just ix <- matchLLVMArrayField ap (bvInt 0) ->
        -- Extract the array perm we want out of the other perms on the stack
        -- and pop all the other perms off of the stack, then borrow the field
        -- corresopnding to offset 0
        stmtEmbedImplM (implExtractConjM x ps i >>>
                        recombinePerm x (ValPerm_Conj (deleteNth i ps)) >>>
                        implLLVMArrayIndexBorrow x ap ix) >>>= \(ap',fp) ->
        -- Emit the typed LLVM load instruction, noting that the array
        -- permission is on the stack below the borrowed field permission
        emitTypedLLVMLoad arch loc treg fp (distPerms1 x $ ValPerm_Conj1 $
                                            Perm_LLVMArray ap') >>>= \z ->
        -- If the resulting perms on z are copyable, copy them and return the
        -- borrow back to the array, otherwise leave things like they are
        let z_p = llvmFieldContents fp in
        (if permIsCopyable z_p then
           stmtEmbedImplM (implCopyM z z_p >>>
                           recombinePermExpl z ValPerm_True z_p >>>
                           introLLVMFieldContentsM x z >>>
                           implLLVMArrayIndexReturn x ap' ix) >>>
           stmtRecombinePerms
         else
           stmtRecombinePerms) >>>
        -- Finally, convert the return value to the requested type and return
        -- the result
        convertRegType knownRepr loc (TypedReg z) knownRepr tp >>>= \ret ->
        greturn (addCtxName ctx $ typedRegVar ret)

    _ ->
      error ("tcEmitLLVMStmt: LLVM_Load: "
             ++ "unexpected permission matched by llvmPermContainsOffset")


-- Type-check a store of an LLVM pointer
tcEmitLLVMStmt arch ctx loc (LLVM_Store _ (ptr :: Reg ctx (LLVMPointerType w)) tp _ _ val) =
  let tptr :: TypedReg (LLVMPointerType w) = tcReg ctx ptr
      tval = tcReg ctx val
      tp_ptr = LLVMPointerRepr (knownRepr :: NatRepr w) in
  convertRegType knownRepr loc tval tp tp_ptr >>>= \tval_ptr ->
  stmtProvePerm tptr (llvmWriteTrueExLPerm $ bvInt 0) >>>= \subst ->
  let l = substLookup subst Member_Base in
  let fp = llvmFieldWriteTrueL (bvInt 0) l in
  emitTypedLLVMStore arch loc tptr fp
  (PExpr_Var $ typedRegVar tval_ptr) DistPermsNil >>>= \z ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx z)


{- FIXME HERE: old approach that performed the case split on the current perms
  getAtomicLLVMPerms tptr >>>= \ps ->
  stmtEmbedImplM
  (foldMapWithDefault implCatchM
   (implFailMsgM "LLVM_Store: could not find permission for offset 0")
   greturn
   (findMaybeIndices (llvmPermContainsOffset $ bvInt 0) ps)) >>>= \(i,_) ->
  case ps !! i of
    Perm_LLVMField fp
      | PExpr_Write <- llvmFieldRW fp ->
        -- If we found a field perm for offset 0, first extract it out of all
        -- the other perms for x and pop all the other perms off of the stack
        stmtEmbedImplM (implExtractConjM x ps i >>>
                        recombinePerm x (ValPerm_Conj (deleteNth i ps))) >>>
        -- Next, emit the typed LLVM store instruction
        emitTypedLLVMStore arch loc tptr fp tval_ptr DistPermsNil >>>= \z ->
        -- Finally, return the expanded context
        stmtRecombinePerms >>>
        greturn (addCtxName ctx z)

    Perm_LLVMArray ap
      | Just ix <- matchLLVMArrayField ap (bvInt 0) ->
        -- Extract the array perm we want out of the other perms on the stack
        -- and pop all the other perms off of the stack, then borrow the field
        -- corresopnding to offset 0
        stmtEmbedImplM (implExtractConjM x ps i >>>
                        recombinePerm x (ValPerm_Conj (deleteNth i ps)) >>>
                        implLLVMArrayIndexBorrow x ap ix) >>>= \(ap',fp) ->
        -- Emit the typed LLVM store instruction, noting that the array
        -- permission is on the stack below the borrowed field permission
        emitTypedLLVMStore arch loc tptr fp tval_ptr
        (distPerms1 x $ ValPerm_Conj1 $ Perm_LLVMArray ap') >>>= \z ->
        -- If the permissions in the array field are copyable, then copy them
        -- from the register value being stored and return the borrow; otherwise
        -- leave the borrow intact
        let field_p = llvmFieldContents fp in
        (if permIsCopyable field_p then
           stmtEmbedImplM
           (proveVarImpl (typedRegVar tval_ptr) (emptyMb field_p) >>>
            introLLVMFieldContentsM x (typedRegVar tval_ptr) >>>
            implLLVMArrayIndexReturn x ap' ix) >>>
           stmtRecombinePerms
         else
           stmtRecombinePerms) >>>
        -- Finally, return the expanded context
        greturn (addCtxName ctx z)

    _ ->
      error ("tcEmitLLVMStmt: LLVM_Store: "
             ++ "unexpected permission matched by llvmPermContainsOffset")
-}


-- Type-check an empty mem-clear instruction as a no-op
tcEmitLLVMStmt _ ctx loc (LLVM_MemClear _ _ 0) =
  emitStmt knownRepr loc (TypedSetReg knownRepr $
                          TypedExpr EmptyApp
                          (Just PExpr_Unit)) >>>= \(_ :>: z) ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx z)

-- It is currently an error to clear a number of bytes that is not a multiple of
-- the machine word size, so throw an error
tcEmitLLVMStmt arch ctx loc (LLVM_MemClear _ ptr bytes)
  | bytesToInteger bytes `mod` intValue (archWidth arch) /= 0 =
    stmtFailM (\_ -> string "LLVM_MemClear: size not a multiple of arch width")

-- Type-check a non-empty mem-clear instruction by writing a 0 to the last word
-- and then recursively clearing all but the last word
tcEmitLLVMStmt arch ctx loc (LLVM_MemClear mem ptr bytes) =
  let tptr = tcReg ctx ptr
      off = bytesToInteger bytes - intValue (archWidth arch) in
  stmtProvePerm tptr (llvmWriteTrueExLPerm $ bvInt off) >>>= \subst ->
  let l = substLookup subst Member_Base in
  let fp = llvmFieldWriteTrueL (bvInt off) l in
  emitTypedLLVMStore arch loc tptr fp (PExpr_LLVMWord $
                                       bvInt 0) DistPermsNil >>>
  stmtRecombinePerms >>>
  tcEmitLLVMStmt arch ctx loc (LLVM_MemClear mem ptr $
                               bytes - fromIntegral (intValue (archWidth arch)))

-- Type-check an alloca instruction
tcEmitLLVMStmt arch ctx loc (LLVM_Alloca w _ sz_reg _ _) =
  let sz_treg = tcReg ctx sz_reg in
  getFramePtr >>>= \maybe_fp ->
  maybe (greturn ValPerm_True) getRegPerm maybe_fp >>>= \fp_perm ->
  resolveConstant sz_treg >>>= \maybe_sz ->
  case (maybe_fp, fp_perm, maybe_sz) of
    (Just fp, ValPerm_Conj [Perm_LLVMFrame fperms], Just sz) ->
      stmtProvePerm fp (emptyMb fp_perm) >>>= \_ ->
      emitLLVMStmt knownRepr loc (TypedLLVMAlloca fp fperms sz) >>>= \y ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx y)
    (_, _, Nothing) ->
      stmtFailM (\i -> string "LLVM_Alloca: non-constant size for"
                       <+> permPretty i sz_treg)
    (Just fp, p, _) ->
      stmtFailM (\i -> string "LLVM_Alloca: expected LLVM frame perm for "
                       <+> permPretty i fp <> ", found perm"
                       <+> permPretty i p)
    (Nothing, _, _) ->
      stmtFailM (const $ string "LLVM_Alloca: no frame pointer set")

-- Type-check a push frame instruction
tcEmitLLVMStmt arch ctx loc (LLVM_PushFrame _) =
  emitLLVMStmt knownRepr loc TypedLLVMCreateFrame >>>= \fp ->
  setFramePtr (TypedReg fp) >>>
  stmtRecombinePerms >>>
  emitStmt knownRepr loc (TypedSetReg knownRepr
                          (TypedExpr EmptyApp Nothing)) >>>= \(_ :>: y) ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx y)

-- Type-check a pop frame instruction
tcEmitLLVMStmt arch ctx loc (LLVM_PopFrame _) =
  getFramePtr >>>= \maybe_fp ->
  maybe (greturn ValPerm_True) getRegPerm maybe_fp >>>= \fp_perm ->
  case (maybe_fp, fp_perm) of
    (Just fp, ValPerm_Conj [Perm_LLVMFrame fperms])
      | Some del_perms <- llvmFrameDeletionPerms fperms ->
        stmtProvePerms (distPermsToExDistPerms del_perms) >>>= \_ ->
        stmtProvePerm fp (emptyMb fp_perm) >>>= \_ ->
        emitLLVMStmt knownRepr loc (TypedLLVMDeleteFrame
                                    fp fperms del_perms) >>>= \y ->
        gmodify (\st -> st { stExtState = PermCheckExtState_LLVM Nothing }) >>>
        greturn (addCtxName ctx y)
    _ -> stmtFailM (const $ string "LLVM_PopFrame: no frame perms")

-- Type-check a pointer offset instruction by emitting OffsetLLVMValue
tcEmitLLVMStmt arch ctx loc (LLVM_PtrAddOffset w _ ptr off) =
  let tptr = tcReg ctx ptr
      toff = tcReg ctx off in
  emitLLVMStmt knownRepr loc (OffsetLLVMValue tptr toff) >>>= \ret ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx ret)

tcEmitLLVMStmt _arch _ctx _loc _stmt =
  error "tcEmitLLVMStmt: unimplemented statement"

-- FIXME HERE NOW: need to handle PtrEq, PtrLe, PtrAddOffset, and PtrSubtract


----------------------------------------------------------------------
-- * Permission Checking for Jump Targets and Termination Statements
----------------------------------------------------------------------

mkEqVarPerms :: MapRList Name ctx -> MapRList Name ctx -> DistPerms ctx
mkEqVarPerms MNil _ = DistPermsNil
mkEqVarPerms (xs :>: x) (ys :>: y) =
  DistPermsCons (mkEqVarPerms xs ys) x (ValPerm_Eq $ PExpr_Var y)

-- | Take a set of permissions on some ghost variables as well as a set of
-- assignments @arg1=ghost1, ...@ of those ghost variables to the "real"
-- arguments of a block and add the permissions @arg1:eq(ghost1), ...@ to the
-- input permissions
buildInputPermsH :: Mb ghosts (DistPerms ghosts) ->
                    Mb ghosts (MapRList Name args) ->
                    MbDistPerms (ghosts :++: args)
buildInputPermsH mb_perms mb_args =
  mbCombine $ mbMap2 (\perms args ->
                       nuMulti args $ \arg_vars ->
                       appendDistPerms perms (mkEqVarPerms arg_vars args))
  mb_perms mb_args

buildInputPerms :: MapRList Name (ghosts :: RList CrucibleType) ->
                   DistPerms ghosts -> MapRList Name args ->
                   Closed (MbDistPerms (ghosts :++: args))
buildInputPerms xs perms_in args_in =
  $(mkClosed [| buildInputPermsH |])
  `clApply` maybe (error "buildInputPerms") id (abstractVars xs perms_in)
  `clApply` maybe (error "buildInputPerms") id (abstractVars xs args_in)

abstractPermsRet :: MapRList Name (ghosts :: RList CrucibleType) ->
                    MapRList f args ->
                    Binding (ret :: CrucibleType) (DistPerms ret_ps) ->
                    Closed (Mb (ghosts :++: args :> ret) (DistPerms ret_ps))
abstractPermsRet xs args ret_perms =
  $(mkClosed [| \args ->  mbCombine . mbCombine . fmap (nuMulti args . const) |])
  `clApply` closedProxies args
  `clApply` maybe (error "abstractPermsRet") id (abstractVars xs ret_perms)

-- | Type-check a Crucible jump target
tcJumpTarget :: CtxTrans ctx -> JumpTarget cblocks ctx ->
                StmtPermCheckM ext cblocks blocks ret args RNil RNil
                (PermImpl (TypedJumpTarget blocks) RNil)
tcJumpTarget ctx (JumpTarget blkID arg_tps args) =
  (stPermEnv <$> unClosed <$> top_get) >>>= \env ->
  (stPPInfo <$> get) >>>= \ppInfo ->
  (stVarTypes <$> gget) >>>= \varTypes ->
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
      (Some ghost_perms, Some (RetPerms ret_perms)) ->
        -- Get the types of all variables we hold permissions on, and then use
        -- these to make a new entrypoint into the given block, whose ghost
        -- arguments are all those that we hold permissions on
        getVarTypes (distPermsVars ghost_perms) >>>= \ghost_tps ->

        -- Translate each "real" argument x into an eq(x) permission, and then
        -- form the append of (ghosts :++: real_args) for the types and the
        -- permissions. These are all used to build the TypedJumpTarget.
        let args_t = tcRegs ctx args
            args_vars = typedRegsToVars args_t
            arg_eq_perms = mkEqVarPerms args_vars args_vars
            perms_in = appendDistPerms ghost_perms arg_eq_perms in

        -- Insert a new block entrypoint that has all the permissions we
        -- constructed above as input permissions
        liftPermCheckM
        (insNewBlockEntry memb (mkCruCtx arg_tps) ghost_tps
         (buildInputPerms (distPermsVars ghost_perms) ghost_perms args_vars)
         (abstractPermsRet (distPermsVars ghost_perms)
          args_vars ret_perms)) >>>= \entryID ->

        -- Build the typed jump target for this jump target
        let target_t = TypedJumpTarget entryID (mkCruCtx arg_tps) perms_in in

        -- Finally, build the PermImpl that proves all the required permissions
        -- from the current permission set. This proof just copies the existing
        -- permissions into the current distinguished perms, and then proves
        -- that each "real" argument register equals itself.
        liftPermCheckM $
        runImplM CruCtxNil (stCurPerms st) env ppInfo varTypes
        (const $ return target_t)
        (implPushMultiM ghost_perms >>>
         proveVarsImplAppend (distPermsToExDistPerms $
                              mkEqVarPerms args_vars args_vars))


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
  (unClosed <$> top_get) >>>= \top_st ->
  let env = stPermEnv top_st
      ppInfo = stPPInfo st
      varTypes = stVarTypes st in
  case stRetPerms st of
    Some (RetPerms mb_ret_perms) ->
      let ret_perms =
            varSubst (singletonVarSubst $ typedRegVar treg) mb_ret_perms in
      liftPermCheckM
      (TypedReturn <$>
       runImplM CruCtxNil (stCurPerms st) env ppInfo varTypes
       (const $ return $ TypedRet (stRetType top_st) treg mb_ret_perms)
       (proveVarsImpl $ distPermsToExDistPerms ret_perms))
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
  tcEmitStmt ctx loc stmt >>>= \ctx' -> tcEmitStmtSeq ctx' stmts
tcEmitStmtSeq ctx (TermStmt loc tstmt) =
  tcTermStmt ctx tstmt >>>= \typed_tstmt ->
  gmapRet (>> return (TypedTermStmt loc typed_tstmt))

llvmReprWidth :: ExtRepr (LLVM arch) -> NatRepr (ArchWidth arch)
llvmReprWidth ExtRepr_LLVM = knownRepr

setInputExtState :: ExtRepr ext -> CruCtx as -> MapRList Name as ->
                    PermCheckM ext cblocks blocks ret args r ps r ps ()
setInputExtState ExtRepr_Unit _ _ = greturn ()
setInputExtState repr@ExtRepr_LLVM tps ns
  | [n] <- findLLVMFrameVars (llvmReprWidth repr) tps ns
  = setFramePtr $ TypedReg n
setInputExtState ExtRepr_LLVM _ _ =
  -- FIXME: make sure there are not more than one frame var and/or a frame var
  -- of the wrong type
  greturn ()

-- | Type-check a single block entrypoint
tcBlockEntry :: PermCheckExtC ext => Block ext cblocks ret args ->
                BlockEntryInfo blocks ret (CtxToRList args) ->
                TopPermCheckM ext cblocks blocks ret
                (TypedEntry ext blocks ret (CtxToRList args))
tcBlockEntry blk (BlockEntryInfo {..}) =
  (stRetType <$> unClosed <$> get) >>= \retType ->
  fmap (TypedEntry entryInfoID entryInfoArgs retType
        entryInfoPermsIn entryInfoPermsOut) $
  strongMbM $
  flip nuMultiWithElim
  (MNil :>: entryInfoPermsIn :>:
   mbSeparate (MNil :>: Proxy) entryInfoPermsOut) $ \ns (_ :>: perms
                                                         :>: ret_perms) ->
  runPermCheckM (distPermSet $ runIdentity perms)
  (RetPerms $ runIdentity ret_perms) $
  let ctx =
        mkCtxTrans (blockInputs blk) $ snd $
        splitMapRList (entryGhosts entryInfoID)
        (cruCtxProxies $ entryInfoArgs) ns in
  setVarTypes ns (appendCruCtx (entryGhosts entryInfoID) entryInfoArgs) >>>
  stmtTraceM (\i ->
               string "Input types:"
               <> align (pretty $
                         appendCruCtx (entryGhosts entryInfoID) entryInfoArgs)
               PP.<$>
               string "Input perms:"
               <> align (permPretty i $ runIdentity perms)) >>>
  setInputExtState knownRepr (entryGhosts entryInfoID)
  (fst $ splitMapRList (entryGhosts entryInfoID) (cruCtxProxies
                                                  entryInfoArgs) ns) >>>
  stmtRecombinePerms >>>
  tcEmitStmtSeq ctx (blk ^. blockStmts)

-- | Type-check a Crucible block
tcBlock :: PermCheckExtC ext => Member blocks (CtxToRList args) ->
           Block ext cblocks ret args ->
           TopPermCheckM ext cblocks blocks ret
           (TypedBlock ext blocks ret (CtxToRList args))
tcBlock memb blk =
  do entries <- blockInfoEntries <$> mapRListLookup memb <$>
       stBlockInfo <$> unClosed <$> get
     TypedBlock <$> mapM (tcBlockEntry blk) entries

-- | Type-check a Crucible block and put its translation into the 'BlockInfo'
-- for that block
tcEmitBlock :: PermCheckExtC ext => Block ext cblocks ret args ->
               TopPermCheckM ext cblocks blocks ret ()
tcEmitBlock blk =
  do !cl_memb <- toClosed <$> stLookupBlockID (blockID blk) <$> unClosed <$> get
     !cl_block_t <- closedM ( $(mkClosed [| tcBlock |])
                              `clApply` cl_memb `clApply` toClosed blk)
     modifyBlockInfo ($(mkClosed [| blockInfoMapSetBlock |] )
                      `clApply` cl_memb `clApply` cl_block_t)

funPermToBlockInputs :: FunPerm ghosts args ret ->
                        MbDistPerms (ghosts :> LifetimeType :++: args)
funPermToBlockInputs fun_perm =
  mbValuePermsToDistPerms $
  fmap (appendValuePerms (ValPerms_Cons (trueValuePerms $ funPermGhosts fun_perm) $
                          ValPerm_Conj1 $ Perm_LOwned $ PExpr_PermListNil)) $
  mbCombine $ funPermIns fun_perm

funPermToBlockOutputs :: FunPerm ghosts args ret ->
                         Mb ((ghosts :> LifetimeType) :++: args :> ret)
                         (DistPerms (args :> ret :> LifetimeType))
funPermToBlockOutputs (fun_perm :: FunPerm ghosts args ret) =
  mbCombine @_ @_ @(args :> ret) @(ghosts :> LifetimeType) $
  nuMultiWithElim1 (\(_ :>: l) mb_perms ->
                     fmap (\perms ->
                            DistPermsCons perms l $
                            ValPerm_Conj1 $ Perm_LOwned $ PExpr_PermListNil) $
                     mbValuePermsToDistPerms mb_perms) $
  funPermOuts fun_perm


-- | Type-check a Crucible CFG
tcCFG :: PermCheckExtC ext => Closed PermEnv ->
         Closed (FunPerm ghosts (CtxToRList inits) ret) ->
         CFG ext blocks inits ret ->
         TypedCFG ext (CtxCtxToRList blocks) ghosts (CtxToRList inits) ret
tcCFG env [clP| fun_perm@(FunPerm cl_ghosts _ _ perms_in perms_out) |] cfg =
  let ghosts = unClosed cl_ghosts in
  flip evalState (emptyTopPermCheckState (handleReturnType $ cfgHandle cfg)
                  (cfgBlockMap cfg) env) $
  do init_memb <- stLookupBlockID (cfgEntryBlockID cfg) <$> unClosed <$> get
     init_entry <-
       insNewBlockEntry init_memb (mkCruCtx $ handleArgTypes $ cfgHandle cfg)
       (CruCtxCons ghosts knownRepr)
       ($(mkClosed [| funPermToBlockInputs |]) `clApply` fun_perm)
       ($(mkClosed [| funPermToBlockOutputs |]) `clApply` fun_perm)
     !(init_st) <- get
     mapM_ (visit cfg) (trace "visiting CFG..." $ cfgWeakTopologicalOrdering cfg)
     !final_st <- get
     trace "visiting complete!" $ return $ TypedCFG
       { tpcfgHandle = TypedFnHandle ghosts (cfgHandle cfg)
       , tpcfgFunPerm = unClosed fun_perm
       , tpcfgBlockMap =
           mapMapRList
           (maybe (error "tcCFG: unvisited block!") id . blockInfoBlock)
           (stBlockInfo $ unClosed final_st)
       , tpcfgEntryBlockID = init_entry }
  where
    visit :: PermCheckExtC ext => CFG ext cblocks inits ret ->
             WTOComponent (Some (BlockID cblocks)) ->
             TopPermCheckM ext cblocks blocks ret ()
    visit cfg (Vertex (Some blkID)) =
      do blkIx <- memberLength <$> stLookupBlockID blkID <$> unClosed <$> get
         () <- trace ("Visiting block: " ++ show blkIx) $ return ()
         !ret <- tcEmitBlock (getBlock blkID (cfgBlockMap cfg))
         !s <- get
         trace ("Visiting block " ++ show blkIx ++ " complete") $ return ret
    visit cfg (SCC (Some blkID) comps) =
      tcEmitBlock (getBlock blkID (cfgBlockMap cfg)) >>
      mapM_ (visit cfg) comps
