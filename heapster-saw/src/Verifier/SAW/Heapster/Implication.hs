{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE BangPatterns #-}

module Verifier.SAW.Heapster.Implication where

import Data.Maybe
import Data.List
import Data.Functor.Product
import Data.Functor.Compose
import Data.Reflection
import qualified Data.BitVector.Sized as BV
import GHC.TypeLits
import Control.Lens hiding ((:>), ix)
import Control.Applicative
import Control.Monad.State.Strict hiding (ap)

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits.MonadBind
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap
import Data.Binding.Hobbits.NameSet (NameSet)
import qualified Data.Binding.Hobbits.NameSet as NameSet

import Prettyprinter as PP

import Data.Parameterized.BoolRepr

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core
import Lang.Crucible.FunctionHandle
import Verifier.SAW.Term.Functor (Ident)

import Data.Binding.Hobbits
import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.GenMonad

import GHC.Stack
import Debug.Trace


----------------------------------------------------------------------
-- * Equality Proofs
----------------------------------------------------------------------

-- | An equality permission @x:eq(e)@ read as an an equality @x=e@ or @e=x@,
-- where the 'Bool' flag is 'True' for the former and 'False' for the latter
data EqPerm a = EqPerm (ExprVar a) (PermExpr a) Bool

-- | Get the LHS of the equation represented by an 'EqPerm'
eqPermLHS :: EqPerm a -> PermExpr a
eqPermLHS (EqPerm x _ True) = PExpr_Var x
eqPermLHS (EqPerm _ e False) = e

-- | Get the RHS of the equation represented by an 'EqPerm'
eqPermRHS :: EqPerm a -> PermExpr a
eqPermRHS (EqPerm _ e True) = e
eqPermRHS (EqPerm x _ False) = PExpr_Var x

-- | Get the variable out of an 'EqPerm'
eqPermVar :: EqPerm a -> ExprVar a
eqPermVar (EqPerm x _ _) = x

-- | Get the permission @eq(e)@ out of an 'EqPerm'
eqPermPerm :: EqPerm a -> ValuePerm a
eqPermPerm (EqPerm _ e _) = ValPerm_Eq e

-- | Get the variable and permission out of an 'EqPerm'
eqPermVarAndPerm :: EqPerm a -> VarAndPerm a
eqPermVarAndPerm (EqPerm x e _) = VarAndPerm x (ValPerm_Eq e)

-- | Apply symmetry to an 'EqPerm', changing an @e1=e2@ proof to @e2=e1@
eqPermSym :: EqPerm a -> EqPerm a
eqPermSym (EqPerm x e flag) = EqPerm x e (not flag)

-- | A single step of an equality proof on some type @a@ is a sequence of @N@
-- 'EqPerms', each of which specifies a LHS and a RHS expression (one of which
-- is a variable), along with a function @f@ from these @N@ expressions to an
-- @a@. This represents a proof that @f es_lhs = f es_rhs@, where @es_lhs@ and
-- @es_rhs@ are the LHS and RHS expressions, respectively, of the 'EqPerm's.
data EqProofStep ps a = EqProofStep (RAssign EqPerm ps) (PermExprs ps -> a)

-- | Get the left-hand side of an 'EqProofStep'
eqProofStepLHS :: EqProofStep ps a -> a
eqProofStepLHS (EqProofStep eq_perms f) = f (RL.map eqPermLHS eq_perms)

-- | Get the right-hand side of an 'EqProofStep'
eqProofStepRHS :: EqProofStep ps a -> a
eqProofStepRHS (EqProofStep eq_perms f) = f (RL.map eqPermRHS eq_perms)

-- | Get the equality permissions required by an 'EqProofStep'
eqProofStepPerms :: EqProofStep ps a -> DistPerms ps
eqProofStepPerms (EqProofStep eq_perms _) = RL.map eqPermVarAndPerm eq_perms

instance Functor (EqProofStep ps) where
  fmap f (EqProofStep eq_perms g) = EqProofStep eq_perms (f . g)

-- | Build a reflexive 'EqProofStep' that any object equals itself. The
-- resulting proof uses no 'EqPerm's. This function along with
-- 'eqProofStepLiftA2' forms a parameterized 'Applicative', where the @ps@
-- argument changes when we combine proofs but otherwise satisfies the
-- 'Applicative' laws.
eqProofStepRefl :: a -> EqProofStep RNil a
eqProofStepRefl a = EqProofStep MNil (const a)

-- | Apply symmetry to a 'EqProofStep', changing an @e1=e2@ proof to @e2=e1@
eqProofStepSym :: EqProofStep ps a -> EqProofStep ps a
eqProofStepSym (EqProofStep eq_perms f) =
  EqProofStep (RL.map eqPermSym eq_perms) f

-- | Combine two 'EqProofStep's using a function, similar to the 'liftA2' method
-- of 'Applicative'. The result uses the 'EqPerm's of both proofs. This function
-- along with 'eqProofStepRefl' forms a parameterized 'Applicative', where the
-- @ps@ argument changes when we combine proofs but otherwise satisfies the
-- 'Applicative' laws.
eqProofStepLiftA2 :: (a -> b -> c) -> EqProofStep ps1 a -> EqProofStep ps2 b ->
                     EqProofStep (ps1 :++: ps2) c
eqProofStepLiftA2 f (EqProofStep eq_perms1 g1) (EqProofStep eq_perms2 g2) =
  EqProofStep (RL.append eq_perms1 eq_perms2) $ \es ->
  let (es1, es2) = RL.split eq_perms1 eq_perms2 es in
  f (g1 es1) (g2 es2)


-- | A proof that two objects are equal, using 0 or more 'EqProofStep' steps
data EqProof ps a where
  EqProofRefl :: a -> EqProof RNil a
  EqProofCons :: EqProof ps1 a -> EqProofStep ps2 a ->
                 EqProof (ps1 :++: ps2) a

-- NOTE: this can be done but requires a lot of type-level equality proofs
{-
-- | Construct an 'EqProof' by transitivity, checking that the RHS of the first
-- proof equals the LHS of the second
eqProofTrans :: Eq a => EqProof ps1 a -> EqProof ps2 a ->
                EqProof (ps1 :++: ps2) a
eqProofTrans eqp (EqProofRefl a) | eqProofRHS eqp == a = eqp
-- FIXME: need to prove RNil :++: ps2 :~: ps2
--eqProofTrans EqProofRefl eqp = eqp
eqProofTrans eqp1 eqp2
  | eqProofRHS eqp1 == eqProofLHS eqp2
  = EqProofTrans eqp1 eqp2
eqProofTrans _ _ = error "eqProofTrans"
-}

-- | Get the LHS of an 'EqProof'
eqProofLHS :: EqProof ps a -> a
eqProofLHS (EqProofRefl a) = a
eqProofLHS (EqProofCons eqp1 _) = eqProofLHS eqp1

-- | Get the RHS of an 'EqProof'
eqProofRHS :: EqProof ps a -> a
eqProofRHS (EqProofRefl a) = a
eqProofRHS (EqProofCons _ eq_step) = eqProofStepRHS eq_step

-- | Get the permissions needed by an 'EqProof'
eqProofPerms :: EqProof ps a -> DistPerms ps
eqProofPerms (EqProofRefl _) = DistPermsNil
eqProofPerms (EqProofCons eqp eq_step) =
  appendDistPerms (eqProofPerms eqp) (eqProofStepPerms eq_step)

instance Functor (EqProof ps) where
  fmap f (EqProofRefl a) = EqProofRefl $ f a
  fmap f (EqProofCons eqp eq_step) =
    EqProofCons (fmap f eqp) (fmap f eq_step)

-- | An equality proof using some unknown set of permissions
data SomeEqProof a where
  SomeEqProofRefl :: a -> SomeEqProof a
  SomeEqProofCons :: SomeEqProof a -> EqProofStep ps a -> SomeEqProof a

-- | Get the LHS of a 'SomeEqProof'
someEqProofLHS :: SomeEqProof a -> a
someEqProofLHS (SomeEqProofRefl a) = a
someEqProofLHS (SomeEqProofCons some_eqp _) = someEqProofLHS some_eqp

-- | Get the RHS of a 'SomeEqProof'
someEqProofRHS :: SomeEqProof a -> a
someEqProofRHS (SomeEqProofRefl a) = a
someEqProofRHS (SomeEqProofCons _ eq_step) = eqProofStepRHS eq_step

-- | Construct a 'SomeEqProof' for @x=e@ or @e=x@ using an @x:eq(e)@ permission,
-- where the 'Bool' flag is 'True' for @x=e@ and 'False' for @e=x@ like 'EqPerm'
someEqProofPerm :: ExprVar a -> PermExpr a -> Bool -> SomeEqProof (PermExpr a)
someEqProofPerm x e flag =
  let eq_step = EqProofStep (MNil :>: EqPerm x e flag) (\(_ :>: e') -> e') in
  SomeEqProofCons (SomeEqProofRefl $ eqProofStepLHS eq_step) eq_step

-- | Apply symmetry to a 'SomeEqProof', changing an @e1=e2@ proof to @e2=e1@
someEqProofSym :: SomeEqProof a -> SomeEqProof a
someEqProofSym eqp_top =
  helper eqp_top (SomeEqProofRefl $ someEqProofRHS eqp_top) where
  -- helper implements someEqProofSym using an accumulator
  helper :: SomeEqProof a -> SomeEqProof a -> SomeEqProof a
  helper (SomeEqProofRefl _) accum = accum
  helper (SomeEqProofCons eqp step) accum =
    helper eqp (SomeEqProofCons accum (eqProofStepSym step))

-- | Construct a 'SomeEqProof' by transitivity
someEqProofTrans :: Eq a => SomeEqProof a -> SomeEqProof a -> SomeEqProof a
someEqProofTrans some_eqp1 some_eqp2
  | someEqProofRHS some_eqp1 == someEqProofLHS some_eqp2 =
    someEqProofTrans' some_eqp1 some_eqp2
someEqProofTrans _ _ = error "someEqProofTrans"

-- | Unchecked version of 'someEqProofTrans'
someEqProofTrans' :: SomeEqProof a -> SomeEqProof a -> SomeEqProof a
someEqProofTrans' some_eqp (SomeEqProofRefl _) = some_eqp
someEqProofTrans' some_eqp1 (SomeEqProofCons some_eqp2 eq_step) =
  SomeEqProofCons (someEqProofTrans' some_eqp1 some_eqp2) eq_step

instance Functor SomeEqProof where
  fmap f (SomeEqProofRefl a) = SomeEqProofRefl $ f a
  fmap f (SomeEqProofCons some_eqp eq_step) =
    SomeEqProofCons (fmap f some_eqp) (fmap f eq_step)

-- NOTE: this is possible, but it requires a lot of type-level equality proofs
{-
-- | A version of 'liftA2' for 'EqProof', which, like 'eqProofStepLiftA2', forms
-- a parameterized 'Applicative'
eqProofLiftA2 :: (a -> b -> c) -> EqProof ps1 a -> EqProof ps2 b ->
                 EqProof (ps1 :++: ps2) c
eqProofLiftA2 f (EqProofRefl a) eqp
  -- NOTE: this is to prove RNil :++: ps2 ~ ps2
  | Refl <- prependRNilEq (eqProofPerms eqp) = fmap (f a) eqp
eqProofLiftA2 f eqp (EqProofRefl b) = fmap (flip f b) eqp
eqProofLiftA2 f (EqProof1 eq_step1) (EqProof1 eq_step2) =
  EqProof1 (eqProofStepLiftA2 f eq_step1 eq_step2)
-}

instance Applicative SomeEqProof where
  pure = SomeEqProofRefl
  liftA2 f (SomeEqProofRefl a) some_eqp = fmap (f a) some_eqp
  liftA2 f some_eqp (SomeEqProofRefl b) = fmap (flip f b) some_eqp
  liftA2 f (SomeEqProofCons eqp1 step1) (SomeEqProofCons eqp2 step2) =
    SomeEqProofCons (liftA2 f eqp1 eqp2) (eqProofStepLiftA2 f step1 step2)

-- | An 'EqProofStep' with an existentially quantified list of permissions
data SomeEqProofStep a = forall ps. SomeEqProofStep (EqProofStep ps a)

-- | Build an 'EqProofStep' by finding each free variable @x@ in an object that
-- has some equality permission @x:eq(e)@ in the supplied variable permission
-- map and substituting @e@ for @x@
eqProofStepFromSubst :: (AbstractVars a, FreeVars a,
                         Substable PermSubst a Identity) => NameMap ValuePerm ->
                        a -> SomeEqProofStep a
eqProofStepFromSubst var_ps a
  | AbsObj vars cl_mb_a <- abstractFreeVars a
  , eq_perms <- RL.map (\var -> case NameMap.lookup var var_ps of
                           Just (ValPerm_Eq e) -> EqPerm var e True
                           _ -> EqPerm var (PExpr_Var var) True) vars =
    SomeEqProofStep $
    EqProofStep eq_perms (\es -> subst (substOfExprs es) (unClosed cl_mb_a))

-- | Build a 'SomeEqProof' by finding each free variable @x@ in an object that
-- has some equality permission @x:eq(e)@ in the supplied variable permission
-- map and substituting @e@ for @x@
someEqProofFromSubst :: (AbstractVars a, FreeVars a,
                         Substable PermSubst a Identity) => NameMap ValuePerm ->
                        a -> SomeEqProof a
someEqProofFromSubst var_ps a
  | SomeEqProofStep eq_step <- eqProofStepFromSubst var_ps a =
    SomeEqProofCons (SomeEqProofRefl a) eq_step

-- | A 'SomeEqProof' that has been converted to an 'EqProof' with explicit perms
data UnSomeEqProof a = forall ps. UnSomeEqProof (EqProof ps a)

-- | Convert a 'SomeEqProof' to an 'EqProof'
unSomeEqProof :: SomeEqProof a -> UnSomeEqProof a
unSomeEqProof (SomeEqProofRefl a) = UnSomeEqProof $ EqProofRefl a
unSomeEqProof (SomeEqProofCons some_eqp eq_step)
  | UnSomeEqProof eqp <- unSomeEqProof some_eqp =
    UnSomeEqProof $ EqProofCons eqp eq_step


----------------------------------------------------------------------
-- * Permission Implications
----------------------------------------------------------------------

-- | A simple implication is an implication that does not introduce any
-- variables or act on the 'varPermMap' part of a permission set. (Compare to
-- the more general 'PermImpl'.) It has the form
--
-- > P1 * ... * Pn -o P1' * ... * Pm'
--
-- where the types of @P1@ through @Pn@ are given by the first type argument
-- @ps_in@ and those of @P1'@ through @Pm'@ are given by the second, @ps_out@.
data SimplImpl ps_in ps_out where
  -- | Drop a permission, i.e., forget about it:
  --
  -- > x:p -o .
  SImpl_Drop :: ExprVar a -> ValuePerm a -> SimplImpl (RNil :> a) RNil

  -- | Copy any copyable permission:
  --
  -- > x:p -o x:p * x:p
  SImpl_Copy :: ExprVar a -> ValuePerm a ->
                SimplImpl (RNil :> a) (RNil :> a :> a)

  -- | Swap the top two permissions on the stack:
  --
  -- > x:p1 * y:p2 -o y:p2 * x:p1
  SImpl_Swap :: ExprVar a -> ValuePerm a -> ExprVar b -> ValuePerm b ->
                SimplImpl (RNil :> a :> b) (RNil :> b :> a)

  -- | Move permission @p@ that is on the stack below two lists @ps1@ and @ps2@
  -- towards the top of the stack by moving it between @ps1@ and @ps2@. That is,
  -- change the stack
  --
  -- > x:p, ps1, ps2 -o ps1, x:p, ps2
  SImpl_MoveUp :: DistPerms ps1 -> ExprVar a -> ValuePerm a -> DistPerms ps2 ->
                  SimplImpl (RNil :> a :++: ps1 :++: ps2) (ps1 :> a :++: ps2)

  -- | Move permission @p@ that is on the stack between two lists @ps1@ and
  -- @ps2@ towards the bottom of the stack by moving it below both @ps1@ and
  -- @ps2@. This inverts 'SImpl_MoveUp'. That is, change the stack
  --
  -- > ps1, x:p, ps2 -o x:p, ps1, ps2
  SImpl_MoveDown :: DistPerms ps1 -> ExprVar a -> ValuePerm a -> DistPerms ps2 ->
                    SimplImpl (ps1 :> a :++: ps2) (RNil :> a :++: ps1 :++: ps2)

  -- | @SImpl_IntroOrL x p1 p2@ applies left disjunction introduction:
  --
  -- > x:p1 -o x:(p1 \/ p2)
  SImpl_IntroOrL :: ExprVar a -> ValuePerm a -> ValuePerm a ->
                    SimplImpl (RNil :> a) (RNil :> a)

  -- | @SImpl_IntroOrR x p1 p2 pf@ applies right disjunction introduction:
  --
  -- > x:p2 -o x:(p1 \/ p2)
  SImpl_IntroOrR :: ExprVar a -> ValuePerm a -> ValuePerm a ->
                    SimplImpl (RNil :> a) (RNil :> a)

  -- | @SImpl_IntroExists x e p@ applies existential introduction:
  --
  -- > x:[e/z]p -o x:(exists z.p)
  SImpl_IntroExists :: KnownRepr TypeRepr tp => ExprVar a -> PermExpr tp ->
                       Binding tp (ValuePerm a) ->
                       SimplImpl (RNil :> a) (RNil :> a)

  -- | Cast a proof of @y:p@ to one of @x:p@ using @x:eq(y)@:
  --
  -- > x:eq(y) * y:p -o x:p
  SImpl_Cast :: ExprVar a -> ExprVar a -> ValuePerm a ->
                SimplImpl (RNil :> a :> a) (RNil :> a)

  -- | Cast a proof of @x:p@ to one of @x:p'@ using a proof that @p=p'@ along
  -- with the equality permissions needed by that proof:
  --
  -- > x1:eq(e1), ..., xn:eq(en), x:p -o x:p'
  SImpl_CastPerm :: ExprVar a -> EqProof ps (ValuePerm a) ->
                    SimplImpl (RNil :> a :++: ps) (RNil :> a)

  -- | Introduce a proof that @x:eq(x)@:
  --
  -- > . -o x:eq(x)
  SImpl_IntroEqRefl :: ExprVar a -> SimplImpl RNil (RNil :> a)

  -- | Invert an @x:eq(y)@ permission into a @y:eq(x)@ permission:
  --
  -- > x:eq(y) -o y:eq(x)
  SImpl_InvertEq :: ExprVar a -> ExprVar a -> SimplImpl (RNil :> a) (RNil :> a)

  -- | Prove @x:eq(y)@ by proving equality permissions for both @x@ and @y@ to
  -- the same expression, thereby implementing a form of transitivity of
  -- equality where the second equality is inversted:
  --
  -- > x:eq(e) * y:eq(e) -o x:eq(y)
  SImpl_InvTransEq :: ExprVar a -> ExprVar a -> PermExpr a ->
                      SimplImpl (RNil :> a :> a) (RNil :> a)

  -- FIXME HERE: remove this in favor of SImpl_Copy

  -- | Copy an equality proof on the top of the stack:
  --
  -- > x:eq(e) -o x:eq(e) * x:eq(e)
  SImpl_CopyEq :: ExprVar a -> PermExpr a ->
                  SimplImpl (RNil :> a) (RNil :> a :> a)

  -- | Cast an @eq(llvmword(y))@ proof to an @eq(llvmword(e))@ proof using a
  -- proof of @y:eq(e)@:
  --
  -- > x:eq(llvmword(y)) * y:eq(e) -o x:eq(llvmword(e))
  SImpl_LLVMWordEq :: (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
                      ExprVar (BVType w) -> PermExpr (BVType w) ->
                      SimplImpl (RNil :> LLVMPointerType w :> BVType w)
                      (RNil :> LLVMPointerType w)

  -- | Introduce an empty conjunction on @x@, i.e.:
  --
  -- > . -o x:true
  SImpl_IntroConj :: ExprVar a -> SimplImpl RNil (RNil :> a)

  -- | Extract the @i@th atomic permission out of a conjunct, putting it below
  -- that conjunct on the stack:
  --
  -- > x:(p0 * ... * p(n-1)) -o x:pi * x:(p0 * ... p(i-1) * p(i+1) ... * p(n-1))
  SImpl_ExtractConj :: ExprVar a -> [AtomicPerm a] -> Int ->
                       SimplImpl (RNil :> a) (RNil :> a :> a)

  -- | Copy the @i@th atomic permission out of a conjunct, assuming it is
  -- copyable, putting it below that conjunct on the stack:
  --
  -- > x:(p0 * ... * p (n-1)) -o x:pi * x:(p0 * ... * p(n-1))
  SImpl_CopyConj :: ExprVar a -> [AtomicPerm a] -> Int ->
                    SimplImpl (RNil :> a) (RNil :> a :> a)

  -- | Insert an atomic permission below the top of the stack at the @i@th
  -- position in the conjunct on the top of the stack, where @i@ must be between
  -- @0@ and @n@ (the number of conjuncts), inclusive:
  --
  -- > x:p * x:(p0 * ... * p(n-1))
  -- >   -o x:(p0 * ... * p(i-1) * p * pi * ... * p(n-1))
  SImpl_InsertConj :: ExprVar a -> AtomicPerm a -> [AtomicPerm a] -> Int ->
                      SimplImpl (RNil :> a :> a) (RNil :> a)

  -- | Combine the top two conjunctive permissions on the stack:
  --
  -- > x:(p1 * ... * pi) * x:(pi+1 * ... * pn) -o x:(p1 * ... * pn)
  SImpl_AppendConjs :: ExprVar a -> [AtomicPerm a] -> [AtomicPerm a] ->
                       SimplImpl (RNil :> a :> a) (RNil :> a)

  -- | Split the conjunctive permissions on the top of the stack in two:
  --
  -- > x:(p1 * ... * pn) -o x:(p1 * ... * pi) * x:(pi+1 * ... * pn)
  SImpl_SplitConjs :: ExprVar a -> [AtomicPerm a] -> Int ->
                      SimplImpl (RNil :> a) (RNil :> a :> a)

  -- | Prove a struct permission of @true@ permissions on any struct:
  --
  -- > -o x:struct(true, ..., true)
  SImpl_IntroStructTrue ::
    ExprVar (StructType ctx) -> RAssign Proxy (CtxToRList ctx) ->
    SimplImpl RNil (RNil :> StructType ctx)

  -- | Prove a struct permission of equality permissions from an equality
  -- permission to a struct:
  --
  -- > x:eq(struct(e1, ..., en)) -o x:struct(eq(e1), ..., eq(en))
  SImpl_StructEqToPerm ::
    ExprVar (StructType ctx) -> PermExprs (CtxToRList ctx) ->
    SimplImpl (RNil :> StructType ctx) (RNil :> StructType ctx)

  -- | Prove an equality permission to a struct from a struct permission of
  -- equality permissions:
  --
  -- > x:struct(eq(e1), ..., eq(en)) -o x:eq(struct(e1, ..., en))
  SImpl_StructPermToEq ::
    ExprVar (StructType ctx) -> PermExprs (CtxToRList ctx) ->
    SimplImpl (RNil :> StructType ctx) (RNil :> StructType ctx)

  -- | Prove a permission @p@ on a struct field that is known to equal some
  -- variable @y@ using a proof of @y:p@:
  --
  -- > x:struct(ps, eq(y), ps'), y:p -o x:struct(ps,p,ps')
  SImpl_IntroStructField ::
    ExprVar (StructType ctx) -> RAssign ValuePerm (CtxToRList ctx) ->
    Member (CtxToRList ctx) a -> ValuePerm a ->
    SimplImpl (RNil :> StructType ctx :> a) (RNil :> StructType ctx)

  -- | Prove a function permission for a statically-known function (assuming
  -- that the given entry is in the current function environment):
  --
  -- > x:eq(handle) -o x:fun_perm
  SImpl_ConstFunPerm ::
    args ~ CtxToRList cargs =>
    ExprVar (FunctionHandleType cargs ret) ->
    FnHandle cargs ret -> FunPerm ghosts (CtxToRList cargs) ret -> Ident ->
    SimplImpl (RNil :> FunctionHandleType cargs ret)
    (RNil :> FunctionHandleType cargs ret)

  -- | Cast a proof of @x:eq(word(e1))@ to one of @x:eq(word(e2))@ using an
  -- equality permission @e1=e2@ on top of the stack:
  --
  -- > x:eq(word(e1)) * x:prop(e1=e2) -o x:eq(word(e2))
  SImpl_CastLLVMWord ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
    PermExpr (BVType w) -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)

  -- | Invert an @x:eq(y+off)@ proof into a @y:eq(x-off)@ proof:
  --
  -- > x:eq(y+off) -o y:eq(x-off)
  SImpl_InvertLLVMOffsetEq ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
    ExprVar (LLVMPointerType w) ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Cast a proof of @y:eq(word(e))@ to one of @x:eq(word(e+off))@ using an
  -- equality permission @x:eq(y+off)@ on top of the stack:
  --
  -- > x:eq(y+off) * y:eq(word(e)) -o x:eq(word(e+off))
  SImpl_OffsetLLVMWord ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
    PermExpr (BVType w) -> ExprVar (LLVMPointerType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)

  -- | Cast a permission @y:p@ of LLVM type on the top of the stack to @x:(p -
  -- off)@ using a proof of @x:eq(y+off)@ just below it on the stack:
  --
  -- > x:eq(y+off) * y:p -o x:(p - off)
  --
  -- FIXME: change this to work for arbitrary types with 'offsetPerm'
  SImpl_CastLLVMPtr ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> ValuePerm (LLVMPointerType w) ->
    PermExpr (BVType w) -> ExprVar (LLVMPointerType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)

  -- | Cast a proof of @x:free(e1)@ to one of @x:free(e2)@ using an equality
  -- permission @e1=e2@ on top of the stack:
  --
  -- > x:free(e1) * x:prop(e1=e2) -o x:free(e2)
  SImpl_CastLLVMFree ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
    PermExpr (BVType w) -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)

  -- | Cast the offset of a field permission from @off@ to @off'@ using an
  -- equality permission @off=off'@ on the top of the stack:
  --
  -- > x:ptr((rw,off) |-> p) * x:prop(off=off') -o x:ptr((rw,off') |-> p)
  SImpl_CastLLVMFieldOffset ::
    (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w sz -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)

  -- | Combine proofs of @x:ptr((rw,off) |-> eq(y))@ and @y:p@ on the top of the
  -- permission stack into a proof of @x:ptr((rw,off) |-> p)@, where the
  -- supplied 'LLVMFieldPerm' gives the required output permission:
  --
  -- > x:ptr((rw,off) |-> eq(y)) * y:p -o x:ptr((rw,off) |-> p)
  SImpl_IntroLLVMFieldContents ::
    (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
    ExprVar (LLVMPointerType w) -> ExprVar (LLVMPointerType sz) ->
    LLVMFieldPerm w sz ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType sz)
    (RNil :> LLVMPointerType w)

  -- | Demote an LLVM field permission to read:
  --
  -- > x:[ls]ptr((W,off) |-> p) -o [ls]x:ptr((R,off) |-> p)
  SImpl_DemoteLLVMFieldRW ::
    (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w sz ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Copy an array permission out of a larger array permission, assuming that
  -- all fields of the array are copyable, using a proof that the copied array
  -- permission is contained in the larger one as per 'llvmArrayContainsArray',
  -- i.e., that the range of the smaller array is contained in the larger one
  -- and that all borrows in the larger one are either preserved in the smaller
  -- or are disjoint from it:
  --
  -- > x:ar1=array(off1,<len1,*stride,fps,bs1)
  -- > * x:prop('llvmArrayContainsArray' ar1 ar2)
  -- >   -o x:ar2=array(off2,<len2,*stride,fps,bs2)
  -- >      * x:ar1=array(off1,<len1,*stride,fps,bs1)
  SImpl_LLVMArrayCopy ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w :> LLVMPointerType w)

  -- | Borrow an array permission from a larger array permission, using a proof
  -- that the borrowed array permission is contained in the larger one as per
  -- 'llvmArrayContainsArray', i.e., that the range of the smaller array is
  -- contained in the larger one and that all borrows in the larger one are
  -- either preserved in the smaller or are disjoint from it:
  --
  -- > x:ar1=array(off1,<len1,*stride,fps,bs1++bs2)
  -- > * x:prop('llvmArrayContainsArray' ar1 ar2)
  -- >   -o x:ar2=array(off2,<len2,*stride,fps, bs2+(off1-off2))
  -- >      * x:array(off1,<len1,*stride,fps,[off2,len2):bs1)
  SImpl_LLVMArrayBorrow ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w :> LLVMPointerType w)

  -- | Return a borrowed range of an array permission, undoing a borrow:
  --
  -- > x:array(off2,<len2,*stride,fps,bs2)
  -- > * x:array(off1,<len1,*stride,fps,[off2,len2):bs1)
  -- >   -o x:array(off,<len,*stride,fps,bs1++(bs2+(off2-off1)))
  SImpl_LLVMArrayReturn ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)

  -- | Append two array permissions, assuming one ends where the other begins
  -- and that they have the same stride and fields:
  --
  -- > x:array(off1, <len1, *stride, fps, bs1)
  -- > * x:array(off2=off1+len*stride*word_size, <len2, *stride, fps, bs2)
  -- >   -o x:array(off1,<len1+len2,*stride,fps,bs1++bs2)
  SImpl_LLVMArrayAppend ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)

  -- | Rearrange the order of the borrows in an array permission:
  --
  -- > x:array(off,<len,*stride,fps,bs)
  -- > -o x:array(off,<len,*stride,fps,permute(bs))
  SImpl_LLVMArrayRearrange ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Convert an array to a field of the same size with @true@ contents:
  --
  -- > x:array(off,<(sz/stride/8),*stride,fps,[]) -o x:[l]ptr((rw,off) |-> true)
  --
  -- where all @fps@ must have the same @rw@ and @l@
  SImpl_LLVMArrayToField ::
    (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> NatRepr sz ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Prove an empty array with length 0:
  --
  -- > -o x:array(off,<0,*stride,fps,[])
  SImpl_LLVMArrayEmpty ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    SimplImpl RNil (RNil :> LLVMPointerType w)

  -- | Prove an array of static length from from field permissions for a single
  -- cell, leaving borrows for all the other cells:
  --
  -- > x:fps+(cell*w*stride)
  -- > -o x:array(off,<N,*stride,fps, all field borrows other than for cell)
  SImpl_LLVMArrayOneCell ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Copy out the @j@th field permission of the @i@th element of an array
  -- permission, assuming that the @j@th field permission is copyable, where @j@
  -- is a static 'Int' and @i@ is an expression. Requires a proposition
  -- permission on the top of the stack stating that @i@ is in the range of the
  -- array and that the specified field permission does not overlap with any of
  -- the existing borrows:
  --
  -- > x:array(off,<len,*stride,fps,bs)
  -- > * x:(prop(i \in [off,len)) * disjoint(bs,i*stride+offset(fp_j)))
  -- >   -o x:(fp_j + off + i*stride) * x:array(off,<len,*stride,fps,bs)
  SImpl_LLVMArrayIndexCopy ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayIndex w ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w :> LLVMPointerType w)

  -- | Borrow the @j@th field permission of the @i@th element of an array
  -- permission, where @j@ is a static 'Int' and @i@ is an expression. Requires
  -- a proposition permission on the top of the stack stating that @i@ is in the
  -- range of the array and that the specified field permission does not overlap
  -- with any of the existing borrows, and adds a borrow of the given field:
  --
  -- > x:array(off,<len,*stride,fps,bs)
  -- > * x:(prop(i \in [off,len)) * disjoint(bs,i*stride+offset(fp_j)))
  -- >   -o x:(fp_j + off + i*stride)
  -- >      * x:array(off,<len,*stride,fps,(i*stride+offset(fp_j)):bs)
  SImpl_LLVMArrayIndexBorrow ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayIndex w ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w :> LLVMPointerType w)

  -- | Return the @j@th field permission of the @i@th element of an array
  -- permission, where @j@ is a static 'Int' and @i@ is an expression, undoing a
  -- borrow:
  --
  -- > x:(fp_j + offset + i*stride)
  -- > * x:array(off,<len,*stride,fps,(i*stride+offset(fp_j)):bs)
  -- >   -o x:array(off,<len,*stride,fps,bs)
  SImpl_LLVMArrayIndexReturn ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayIndex w ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)

  -- | Apply an implication to the @i@th field of an array permission:
  --
  -- > y:fpi -o y:fpi'
  -- > ------------------------------------------------
  -- > x:array(off,<len,*stride,(fp1, ..., fpn),bs) -o
  -- >   x:array(off,<len,*stride,
  -- >           (fp1, ..., fp(i-1), fpi', fp(i+1), ..., fpn),bs)
  SImpl_LLVMArrayContents ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> Int -> LLVMArrayField w ->
    LocalPermImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w) ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Prove that @x@ is a pointer from a field permission:
  --
  -- > x:ptr((rw,off) |-> p) -o x:is_llvmptr * x:ptr((rw,off) |-> p)
  SImpl_LLVMFieldIsPtr ::
    (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w sz ->
    SimplImpl (RNil :> LLVMPointerType w)
    (RNil :> LLVMPointerType w :> LLVMPointerType w)

  -- | Prove that @x@ is a pointer from a field permission:
  --
  -- > x:array(...) -o x:is_llvmptr * x:array(...)
  SImpl_LLVMArrayIsPtr ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    SimplImpl (RNil :> LLVMPointerType w)
    (RNil :> LLVMPointerType w :> LLVMPointerType w)

  -- | Prove that @x@ is a pointer from a memblock permission:
  --
  -- > x:[l]memblock(...) -o x:is_llvmptr * x:[l]memblock(...)
  SImpl_LLVMBlockIsPtr ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w)
    (RNil :> LLVMPointerType w :> LLVMPointerType w)

  -- | Save a permission for later by splitting it into part that is in the
  -- current lifetime and part that is saved in the lifetime for later:
  --
  -- > x:F<l,rws> * l:[l2]lcurrent * l2:lowned (ps_in -o ps_out)
  -- >   -o x:F<l2,rws> * l2:lowned (x:F<l2,Rs>, ps_in -o x:F<l,rws>, ps_out)
  --
  -- Note that this rule also supports @l=always@, in which case the second
  -- permission is just @l2:true@ (as a hack, because it has the same type)
  SImpl_SplitLifetime ::
    KnownRepr TypeRepr a => ExprVar a -> LifetimeFunctor args a ->
    PermExprs args -> PermExpr LifetimeType -> ExprVar LifetimeType ->
    LOwnedPerms ps_in -> LOwnedPerms ps_out ->
    SimplImpl (RNil :> a :> LifetimeType :> LifetimeType)
    (RNil :> a :> LifetimeType)

  -- | Subsume a smaller lifetime @l2@ inside a bigger lifetime @l1@, by putting
  -- the @lowned@ permission for @l1@ inside that of @l2@:
  --
  -- > l1:lowned (ps_in1 -o ps_out1) * l2:lowned (ps_in2 -o ps_out2)
  -- >   -o l1:[l2]lcurrent
  -- >      * l2:lowned (ps_in2 -o l1:lowned (ps_in1 -o ps_out1),ps_out2)
  SImpl_SubsumeLifetime :: ExprVar LifetimeType ->
                           LOwnedPerms ps_in1 -> LOwnedPerms ps_out1 ->
                           ExprVar LifetimeType ->
                           LOwnedPerms ps_in2 -> LOwnedPerms ps_out2 ->
                           SimplImpl (RNil :> LifetimeType :> LifetimeType)
                           (RNil :> LifetimeType :> LifetimeType)

  -- | Weaken a lifetime in a permission from some @l@ to some @l2@ that is
  -- contained in @l@, i.e., such that @l@ is current during @l2@, assuming that
  -- @F@ isa valid lifetime functor:
  --
  -- > F<l> * 'lcurrentPerm' l l2 -o F<l2>
  SImpl_WeakenLifetime :: KnownRepr TypeRepr a => ExprVar a ->
                          LifetimeFunctor args a -> PermExprs args ->
                          PermExpr LifetimeType -> ExprVar LifetimeType ->
                          SimplImpl (RNil :> a :> LifetimeType) (RNil :> a)

  -- | Map the input and output permissions of a lifetime ownership permission
  -- using local implications:
  --
  -- > Ps1 * Ps_in' -o Ps_in                          Ps2 * Ps_out -o Ps_out'
  -- > ----------------------------------------------------------------------
  -- > Ps1 * Ps2 * l:lowned (Ps_in -o Ps_out) -o l:lowned (Ps_in' -o Ps_out')
  SImpl_MapLifetime ::
    ExprVar LifetimeType -> LOwnedPerms ps_in -> LOwnedPerms ps_out ->
    LOwnedPerms ps_in' -> LOwnedPerms ps_out' ->
    DistPerms ps1 -> DistPerms ps2 ->
    LocalPermImpl (ps1 :++: ps_in') ps_in ->
    LocalPermImpl (ps2 :++: ps_out) ps_out' ->
    SimplImpl (ps1 :++: ps2 :> LifetimeType) (RNil :> LifetimeType)

  -- | End a lifetime, taking in its @lowned@ permission and all the permissions
  -- required by the @lowned@ permission to end it, and returning all
  -- permissions given back by the @lowned@ lifetime:
  --
  -- > ps_in * l:lowned (ps_in -o ps_out) -o ps_out
  SImpl_EndLifetime :: ExprVar LifetimeType ->
                       LOwnedPerms ps_in -> LOwnedPerms ps_out ->
                       SimplImpl (ps_in :> LifetimeType) ps_out

  -- | Reflexivity for @lcurrent@ proofs:
  --
  -- > . -o l:lcurrent(l)
  SImpl_LCurrentRefl :: ExprVar LifetimeType ->
                        SimplImpl RNil (RNil :> LifetimeType)

  -- | Transitively combine @lcurrent@ proofs:
  --
  -- > l1:lcurrent(l2) * l2:lcurrent(l3) -o l1:lcurrent(l3)
  SImpl_LCurrentTrans :: ExprVar LifetimeType -> ExprVar LifetimeType ->
                         PermExpr LifetimeType ->
                         SimplImpl (RNil :> LifetimeType :> LifetimeType)
                         (RNil :> LifetimeType)

  -- | Demote the modality of an LLVM block permission to read:
  --
  -- > x:[l]memblock(rw,off,len,sh) -o x:[l]memblock(R,off,len,sh)
  SImpl_DemoteLLVMBlockRW ::
    (1 <= w, KnownNat w) =>
    ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Prove an empty memblock permission of length 0:
  --
  -- > -o x:memblock(rw,l,off,0,emptysh)
  SImpl_IntroLLVMBlockEmpty ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    SimplImpl RNil (RNil :> LLVMPointerType w)

  -- | Coerce an memblock permission to an empty memblock permission:
  --
  -- > x:memblock(rw,l,off,len,sh) -o x:memblock(rw,l,off,len,emptysh)
  SImpl_CoerceLLVMBlockEmpty ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Eliminate any @memblock@ permission to an array of bytes:
  --
  -- > x:memblock(rw,l,off,len,emptysh)
  -- >   -o x:array(off,<len,*1,[[l](rw,0,8) |-> true])
  SImpl_ElimLLVMBlockToBytes ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Convert a memblock permission of shape @sh@ to one of shape @sh;emptysh@:
  --
  -- > x:memblock(rw,l,off,len,sh) -o x:memblock(rw,l,off,len,sh;emptysh)
  SImpl_IntroLLVMBlockSeqEmpty ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Convert a memblock permission of shape @sh;emptysh@ to one of shape @sh@:
  --
  -- > x:memblock(rw,l,off,len,sh;emptysh) -o x:memblock(rw,l,off,len,sh)
  SImpl_ElimLLVMBlockSeqEmpty ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Fold the body of a named shape in a @memblock@ permission:
  --
  -- > x:memblock(rw,l,off,len,'unfoldNamedShape' nmsh args)
  -- >   -o x:memblock(rw,l,off,len,nmsh<args>)
  SImpl_IntroLLVMBlockNamed ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    NamedShape 'True args w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Unfold the body of a named shape in a @memblock@ permission:
  --
  -- > x:memblock(rw,l,off,len,nmsh<args>)
  -- >   -o x:memblock(rw,l,off,len,'unfoldNamedShape' nmsh args)
  SImpl_ElimLLVMBlockNamed ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    NamedShape 'True args w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Prove an llvmblock permission of shape @sh@ from one of equality shape
  -- @eqsh(y)@ and a shape permission on @y@:
  --
  -- > x:memblock(rw,l,off,len,eqsh(y)), y:shape(sh)
  -- >   -o x:memblock(rw,l,off,len,sh)
  SImpl_IntroLLVMBlockFromEq ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
    LLVMBlockPerm w -> ExprVar (LLVMBlockType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMBlockType w)
    (RNil :> LLVMPointerType w)

  -- | Prove an llvmblock permission of pointer shape from a pointer:
  --
  -- > x:[l]ptr((rw,off,w) |-> [l2]memblock(rw2,off,'llvmShapeLength'(sh),sh))
  -- >   -o x:[l]memblock(rw,off,w/8,[l2]ptrsh(rw2,sh))
  SImpl_IntroLLVMBlockPtr ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
    Maybe (PermExpr RWModalityType) -> Maybe (PermExpr LifetimeType) ->
    LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Eliminate an llvmblock permission of pointer shape:
  --
  -- > x:[l]memblock(rw,off,w/8,[l2]ptrsh(rw2,sh))
  -- >   -o x:[l]ptr((rw,off,w) |->
  -- >                 [l2]memblock(rw2,off,'llvmShapeLength'(sh),sh))
  SImpl_ElimLLVMBlockPtr ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
    Maybe (PermExpr RWModalityType) -> Maybe (PermExpr LifetimeType) ->
    LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Prove a block of field shape from the corresponding field permission:
  --
  -- > x:[l]ptr((rw,off,sz) |-> p) -o x:memblock(rw,l,off,len+sz,ptrsh(sz,p))
  SImpl_IntroLLVMBlockField ::
    (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w sz ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Eliminate a block of field shape to the corresponding field permission
  -- plus an empty memblock for the remaining @len@, which is the extra arg:
  --
  -- > x:[l]memblock(rw,off,len,fieldsh(sz,p))
  -- >   -o x:[l]ptr((rw,off,sz) |-> p) * [l]memblock(rw,off+sz,len-sz,emptysh)
  SImpl_ElimLLVMBlockField ::
    (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w sz -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Prove a block of array shape from the corresponding array permission:
  --
  -- > x:array(...) -o x:memblock(...)
  SImpl_IntroLLVMBlockArray ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Eliminate a block of array shape to the corresponding array permission:
  --
  -- > x:memblock(...) -o x:array(...)
  SImpl_ElimLLVMBlockArray ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Prove a block of shape @sh1;sh2@ from blocks of shape @sh1@ and @sh2@,
  -- where the supplied 'LLVMBlockPerm' gives @sh1@ and the supplied additional
  -- arguments give @len2@ and @sh2@:
  --
  -- > x:memblock(rw,l,off,len1,sh1) * memblock(rw,l,off+len1,len2,sh2)
  -- >   -o x:memblock(rw,l,off,len1+len2,sh1;sh2)
  SImpl_IntroLLVMBlockSeq ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
    LLVMBlockPerm w -> PermExpr (BVType w) -> PermExpr (LLVMShapeType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)

  -- | Eliminate a block of shape @sh1;sh2@ to blocks of shape @sh1@ and @sh2@,
  -- as long as we can compute the length of @sh1@, where the supplied
  -- 'LLVMBlockPerm' gives @sh1@ and the additional argument gives @sh2@:
  --
  -- > x:memblock(rw,l,off,len,sh1;sh2)
  -- >   -o x:memblock(rw,l,off,len(sh1),sh1)
  -- >      * memblock(rw,l,off+len(sh1),len-len(sh1),sh2)
  SImpl_ElimLLVMBlockSeq ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
    LLVMBlockPerm w -> PermExpr (LLVMShapeType w) ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Prove a block of shape @sh1 orsh sh2@ from a disjunction, where the
  -- supplied 'LLVMBlockPerm' gives @sh1@ and the additional argument is @sh2@:
  --
  -- > x:memblock(rw,l,off,len,sh1) or memblock(rw,l,off,len,sh2)
  -- >   -o x:memblock(rw,l,off,len,sh1 orsh sh2)
  SImpl_IntroLLVMBlockOr ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
    LLVMBlockPerm w -> PermExpr (LLVMShapeType w) ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Eliminate a block of shape @sh1 orsh sh2@ to a disjunction, where the
  -- supplied 'LLVMBlockPerm' gives @sh1@ and the additional argument is @sh2@::
  --
  -- > x:memblock(rw,l,off,len,sh1 orsh sh2)
  -- >   -o x:memblock(rw,l,off,len,sh1) or memblock(rw,l,off,len,sh2)
  SImpl_ElimLLVMBlockOr ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
    LLVMBlockPerm w -> PermExpr (LLVMShapeType w) ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Prove a block of shape @exsh z:A.sh@ from an existential:
  --
  -- > x:exists z:A.memblock(rw,l,off,len,sh)
  -- >   -o x:memblock(rw,l,off,len,exsh z:A.sh)
  SImpl_IntroLLVMBlockEx ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Eliminate a block of shape @exsh z:A.sh@ from to existential:
  --
  -- > x:memblock(rw,l,off,len,exsh z:A.sh)
  -- >   -o x:exists z:A.memblock(rw,l,off,len,sh)
  SImpl_ElimLLVMBlockEx ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)

  -- | Fold a named permission (other than an opaque permission):
  --
  -- > x:(unfold P args) -o x:P<args>
  SImpl_FoldNamed :: NameSortCanFold ns ~ 'True =>
                     ExprVar a -> NamedPerm ns args a -> PermExprs args ->
                     PermOffset a -> SimplImpl (RNil :> a) (RNil :> a)

  -- | Unfold a named permission (other than an opaque permission):
  --
  -- > x:P<args> -o x:(unfold P args)
  SImpl_UnfoldNamed :: NameSortCanFold ns ~ 'True =>
                       ExprVar a -> NamedPerm ns args a -> PermExprs args ->
                       PermOffset a -> SimplImpl (RNil :> a) (RNil :> a)

  -- | Map a named permission that is conjoinable to a conjunction:
  --
  -- > x:P<args> -o x:ValPerm_Conj [P<args>]
  SImpl_NamedToConj :: NameSortIsConj ns ~ 'True => ExprVar a ->
                       NamedPermName ns args a -> PermExprs args ->
                       PermOffset a ->
                       SimplImpl (RNil :> a) (RNil :> a)

  -- | Map a conjuctive named permission to a named permission:
  --
  -- > x:ValPerm_Conj [P<args>] -o x:P<args>
  SImpl_NamedFromConj :: NameSortIsConj ns ~ 'True => ExprVar a ->
                         NamedPermName ns args a -> PermExprs args ->
                         PermOffset a -> SimplImpl (RNil :> a) (RNil :> a)


{- FIXME HERE: Write the rule for proving one recursive perm implies another

  -- | Apply an implication to the body of a least fixed-point permission:
  --
  -- > y:p1 -o y:p2
  -- > ----------------------
  -- > x:mu X.p1 -o x:mu X.p2
  SImpl_Mu ::
    ExprVar a -> Binding (ValuePerm a) (ValuePerm a) ->
    Binding (ValuePerm a) (ValuePerm a) ->
    Binding (ValuePerm a) (PermImpl ((:~:) (RNil :> a)) (RNil :> a)) ->
    SimplImpl (RNil :> a) (RNil :> a)
-}

  -- | Weaken an @always@ lifetime argument of a named permission:
  --
  -- > x:P<args1,always,args2> -o x:P<args1,l,args2>
  SImpl_NamedArgAlways :: ExprVar a -> NamedPermName ns args a ->
                          PermExprs args -> PermOffset a ->
                          Member args LifetimeType -> PermExpr LifetimeType ->
                          SimplImpl (RNil :> a) (RNil :> a)

  -- | Weaken a lifetime argument @l1@ of a named permission:
  --
  -- > x:P<args1,l1,args2> * l1:[l2]lcurrent -o x:P<args1,l2,args2>
  SImpl_NamedArgCurrent :: ExprVar a -> NamedPermName ns args a ->
                           PermExprs args -> PermOffset a ->
                           Member args LifetimeType -> PermExpr LifetimeType ->
                           SimplImpl (RNil :> a :> LifetimeType) (RNil :> a)

  -- | Weaken a 'Write' modality argument to any other modality:
  --
  -- > x:P<args1,W,args2> -o x:P<args1,rw,args2>
  SImpl_NamedArgWrite :: ExprVar a -> NamedPermName ns args a ->
                         PermExprs args -> PermOffset a ->
                         Member args RWModalityType ->
                         PermExpr RWModalityType ->
                         SimplImpl (RNil :> a) (RNil :> a)

  -- | Weaken any modality argument to a 'Read' modality:
  --
  -- > x:P<args1,rw,args2> -o x:P<args1,R,args2>
  SImpl_NamedArgRead :: ExprVar a -> NamedPermName ns args a ->
                        PermExprs args -> PermOffset a ->
                        Member args RWModalityType ->
                        SimplImpl (RNil :> a) (RNil :> a)

  -- | Implements transitivity of reachability permissions:
  --
  -- > x:P<args,y>, y:P<args,e> -o x:P<args,e>
  SImpl_ReachabilityTrans ::
    ExprVar a -> RecPerm b 'True (args :> a) a ->
    PermExprs args -> PermOffset a -> ExprVar a -> PermExpr a ->
    SimplImpl (RNil :> a :> a) (RNil :> a)


-- | A single step of permission implication. These can have multiple,
-- disjunctive conclusions, each of which can bind some number of variables, and
-- can also move permissions between the primary permissions for each variable
-- and the permission stack. The general form is:
--
-- > x1::Px1 * ... * xl::Pl * P1 * ... * Pn
-- >   -o (zs1 . x1::Px1_1 * ... * xl::Pxl_1 * P1_1 * ... * P1_k1) \/
-- >      ... \/ (zsm . x1::Px1_m * ... * xl::Pxl_m * Pm_1 * ... * Pm_km)
--
-- where @zsi@ is a list of permission variables bound in the permissions @Pi_j@
-- and @xi::Pxi@ denotes the primary permission for variable @xi@. In the
-- comments below, we often omit the primary variable permissions when they do
-- not change. The types of @P1@ through @Pn@ are given by the first type
-- argument @ps_in@ of this type, while those of the @zsi@ and the @Pi_j@
-- permissions are given by the @ps_outs@ argument. The latter is an 'RList' of
-- the form
--
-- > RNil :> (bs1, ps1) :> ... :> (bsm, psm)
--
-- where each @bsi@ is itself an 'RList' of the types of the bound variables in
-- @zsi@ and @psi@ is an 'RList' of the types of @Pi_1@ through @Pi_km@.
data PermImpl1 ps_in ps_outs where
  -- | Failure of a permission implication, along with a string explanation of
  -- the failure, which is a proof of 0 disjuncts:
  --
  -- > ps -o .
  Impl1_Fail :: String -> PermImpl1 ps RNil

  -- | Catch any failure in the first branch by calling the second, passing the
  -- same input permissions to both branches:
  --
  -- > ps -o ps \/ ps
  Impl1_Catch :: PermImpl1 ps (RNil :> '(RNil, ps) :> '(RNil, ps))

  -- | Push the primary permission for variable @x@ onto the stack:
  --
  -- > x::P * ps -o x::true * ps * x:P
  Impl1_Push :: ExprVar a -> ValuePerm a ->
                PermImpl1 ps (RNil :> '(RNil, ps :> a))

  -- | Pop the a permission for variable @x@ back to the primary permission for
  -- @x@, assuming the latter is the trivial permission @true@:
  --
  -- > x::true * ps * x:P -o x::P * ps
  Impl1_Pop :: ExprVar a -> ValuePerm a ->
               PermImpl1 (ps :> a) (RNil :> '(RNil, ps))

  -- | Eliminate a disjunction on the top of the stack:
  --
  -- > ps * x:(p1 \/ p2) -o (ps * x:p1) \/ (ps * x:p2)
  Impl1_ElimOr :: ExprVar a -> ValuePerm a -> ValuePerm a ->
                  PermImpl1 (ps :> a)
                  (RNil :> '(RNil, ps :> a) :> '(RNil, ps :> a))

  -- | Eliminate an existential on the top of the stack:
  --
  -- > ps * x:(exists z.p) -o z. ps * x:p
  Impl1_ElimExists :: KnownRepr TypeRepr tp => ExprVar a ->
                      Binding tp (ValuePerm a) ->
                      PermImpl1 (ps :> a) (RNil :> '(RNil :> tp, ps :> a))

  -- | Apply a 'SimplImpl'
  Impl1_Simpl :: SimplImpl ps_in ps_out -> Proxy ps ->
                 PermImpl1 (ps :++: ps_in) (RNil :> '(RNil, ps :++: ps_out))

  -- | Let-bind a fresh variable @x@ to expression @e@, leaving an equality
  -- permission on top of the stack:
  --
  -- > ps -o x. ps * x:eq(e)
  Impl1_LetBind :: TypeRepr tp -> PermExpr tp ->
                   PermImpl1 ps (RNil :> '(RNil :> tp, ps :> tp))

  -- | Project out a field of a struct @x@ by binding a fresh variable @y@ for
  -- its contents, and assign the permissions for that field to @y@, replacing
  -- them with a proof that the field equals @y@:
  --
  -- > x:struct(ps,p,ps') -o y. x:struct(ps, eq(y), ps'), y:p
  Impl1_ElimStructField ::
    ExprVar (StructType ctx) -> RAssign ValuePerm (CtxToRList ctx) ->
    TypeRepr a -> Member (CtxToRList ctx) a ->
    PermImpl1 (ps :> StructType ctx) (RNil :> '(RNil :> a,
                                                ps :> StructType ctx :> a))

  -- | Eliminate the contents of an LLVM field permission, binding a new
  -- variable to hold those permissions and changing the contents of the field
  -- permission to an equals permision for that variable:
  --
  -- > x:ptr((rw,off) -> p) -o y. x:ptr((rw,off) -> eq(y)) * y:p
  Impl1_ElimLLVMFieldContents ::
    (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w sz ->
    PermImpl1 (ps :> LLVMPointerType w)
    (RNil :> '(RNil :> LLVMPointerType sz,
               ps :> LLVMPointerType w :> LLVMPointerType sz))

  -- | Eliminate an llvmblock permission of shape @sh@ to one of equality shape
  -- @eqsh(y)@ and a shape permission on @y@ for a fresh variable @y@:
  --
  -- > x:memblock(rw,l,off,len,sh)
  -- >   -o y. x:memblock(rw,l,off,len,eqsh(y)),
  -- >         y:shape('modalizeShape'(rw,l,sh))
  Impl1_ElimLLVMBlockToEq ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
    PermImpl1 (ps :> LLVMPointerType w)
    (RNil :> '(RNil :> LLVMBlockType w,
               ps :> LLVMPointerType w :> LLVMBlockType w))

  -- | Begin a new lifetime:
  --
  -- > . -o ret:lowned(empty -o empty)
  Impl1_BeginLifetime ::
    PermImpl1 ps (RNil :> '(RNil :> LifetimeType, ps :> LifetimeType))

  -- | Try to prove a bitvector proposition, or fail (as in the 'Impl1_Fail'
  -- rule) if this is not possible, where the 'String' is a pretty-printing of
  -- the proposition (for ease of translation):
  --
  -- > . -o prop(p)
  Impl1_TryProveBVProp ::
    (1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) -> BVProp w ->
    String -> PermImpl1 ps (RNil :> '(RNil, ps :> LLVMPointerType w))


-- | A @'PermImpl' r ps@ is a proof tree of the judgment
--
-- > Gamma | Pl * P |- (Gamma1 | Pl1 * P1) \/ ... \/ (Gamman | Pln * Pn)
--
-- that contains an element of type @r@ at each leaf of the proof tree. Each
-- disjunct on the right of the judgment corresponds to a different leaf in the
-- tree, while each @Gammai@ denotes the variables that are bound on the path
-- from the root to that leaf. The @ps@ argument captures the form of the
-- "distinguished" left-hand side permissions @Pl@.
--
-- FIXME: explain that @Pl@ is like a stack, and that intro rules apply to the
-- top of the stack
--
-- FIXME: it would be nice to have PermImpl r ps_out ps_in, where ps_out is
-- guaranteed to be the stack shape at any Impl_Done, but this would make our
-- generalized monad below more complicated...
data PermImpl r ps where
  PermImpl_Done :: !(r ps) -> PermImpl r ps
  PermImpl_Step :: !(PermImpl1 ps_in ps_outs) ->
                   !(MbPermImpls r ps_outs) ->
                   PermImpl r ps_in

-- | Helper type for 'PermImpl', that defines a collection of permission
-- implications, one for each element of the @bs_pss@ type argument. Each of
-- these elements are of the form @(bs,ps)@, where @ps@ determines the input
-- permissions for that implication tree and @bs@ specifies an existential
-- contexts of bound variables for that implication tree.
data MbPermImpls r bs_pss where
  MbPermImpls_Nil :: MbPermImpls r RNil
  MbPermImpls_Cons :: CruCtx bs ->
                      !(MbPermImpls r bs_pss) ->
                      !(Mb bs (PermImpl r ps)) ->
                      MbPermImpls r (bs_pss :> '(bs,ps))

-- | A local implication, from an input to an output permission set
newtype LocalPermImpl ps_in ps_out =
  LocalPermImpl (PermImpl (LocalImplRet ps_out) ps_in)

-- | The "success" condition of a 'LocalPermImpl', which essentially is just a
-- type equality stating that the output permissions are as expected
newtype LocalImplRet ps ps' = LocalImplRet (ps :~: ps')

-- | The identity implication
idLocalPermImpl :: LocalPermImpl ps ps
idLocalPermImpl = LocalPermImpl $ PermImpl_Done $ LocalImplRet Refl

-- type IsLLVMPointerTypeList w ps = RAssign ((:~:) (LLVMPointerType w)) ps

$(mkNuMatching [t| forall a. EqPerm a |])
$(mkNuMatching [t| forall ps a. NuMatching a => EqProofStep ps a |])
$(mkNuMatching [t| forall ps a. NuMatching a => EqProof ps a |])
$(mkNuMatching [t| forall ps_in ps_out. SimplImpl ps_in ps_out |])
$(mkNuMatching [t| forall ps_in ps_outs. PermImpl1 ps_in ps_outs |])
$(mkNuMatching [t| forall r bs_pss. NuMatchingAny1 r => MbPermImpls r bs_pss |])
$(mkNuMatching [t| forall r ps. NuMatchingAny1 r => PermImpl r ps |])
$(mkNuMatching [t| forall ps_in ps_out. LocalPermImpl ps_in ps_out |])
$(mkNuMatching [t| forall ps ps'. LocalImplRet ps ps' |])

instance NuMatchingAny1 EqPerm where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 (LocalImplRet ps) where
  nuMatchingAny1Proof = nuMatchingProof


-- | Compile-time flag for whether to prune failure branches in 'implCatchM'
pruneFailingBranches :: Bool
pruneFailingBranches = False


-- | Apply the 'PermImpl_Step' constructor to a 'PermImpl1' rule and its
-- sub-proofs, performing the following simplifications (some of which are
-- performed by the helper function 'permImplCatch'), where @unary impl@
-- represents any unary rule applied to the implication @impl@:
--
-- > unary (fail msg) --> fail msg
-- > unary (catch impl (fail msg)) --> catch (unary impl) (fail msg)
-- > catch (fail msg1) (fail msg2) --> fail (msg1 ++ msg2)
-- > catch (catch impl1 impl2) impl3 --> catch impl1 (catch impl2 impl3)
-- > elim_or (fail msg1) (fail msg2) --> fail (msg1 ++ msg2)
permImplStep :: NuMatchingAny1 r => PermImpl1 ps_in ps_outs ->
                MbPermImpls r ps_outs -> PermImpl r ps_in

-- No need to simplify a fail
permImplStep impl1@(Impl1_Fail _) mb_impls = PermImpl_Step impl1 mb_impls

-- Catch --> call the permImplCatch function
permImplStep Impl1_Catch ((MbPermImpls_Cons _
                           (MbPermImpls_Cons _ _ mb_pimpl1) mb_pimpl2)) =
  permImplCatch (elimEmptyMb mb_pimpl1) (elimEmptyMb mb_pimpl2)

-- Unary rules applied to failure --> failures
--
-- NOTE: we write the cases all out explicitly in case we add a new Impl1 rule
-- that does not work this way, since not simplifying is better than
-- oversimplifying
permImplStep impl1@(Impl1_Push _ _) mb_impls =
  permImplStepUnary impl1 mb_impls
permImplStep impl1@(Impl1_Pop _ _) mb_impls =
  permImplStepUnary impl1 mb_impls
permImplStep impl1@(Impl1_ElimExists _ _) mb_impls =
  permImplStepUnary impl1 mb_impls
permImplStep impl1@(Impl1_Simpl _ _) mb_impls =
  permImplStepUnary impl1 mb_impls
permImplStep impl1@(Impl1_LetBind _ _) mb_impls =
  permImplStepUnary impl1 mb_impls
permImplStep impl1@(Impl1_ElimStructField _ _ _ _) mb_impls =
  permImplStepUnary impl1 mb_impls
permImplStep impl1@(Impl1_ElimLLVMFieldContents _ _) mb_impls =
  permImplStepUnary impl1 mb_impls
permImplStep impl1@(Impl1_BeginLifetime) mb_impls =
  permImplStepUnary impl1 mb_impls
permImplStep impl1@(Impl1_TryProveBVProp _ _ _) mb_impls =
  permImplStepUnary impl1 mb_impls

-- An or elimination fails if both branches fail
permImplStep (Impl1_ElimOr _ _ _) (MbPermImpls_Cons _
                                   (MbPermImpls_Cons _ MbPermImpls_Nil
                                    (matchMbImplFail -> Just msg1))
                                   (matchMbImplFail -> Just msg2)) =
  PermImpl_Step (Impl1_Fail
                 (msg1 ++ "\n\n--------------------\n\n" ++ msg2))
  MbPermImpls_Nil

-- Default case: just apply PermImpl_Step
permImplStep impl1 mb_impls = PermImpl_Step impl1 mb_impls


-- | Helper for 'permImplStep': apply the 'PermImpl_Step' constructor to a unary
-- 'PermImpl1' rule and an implication that follows it, performing the necessary
-- simplifications
permImplStepUnary :: NuMatchingAny1 r =>
                     PermImpl1 ps_in (RNil :> '(bs, ps_out)) ->
                     MbPermImpls r (RNil :> '(bs, ps_out)) -> PermImpl r ps_in

-- If the continuation implication is a failure, percolate it up
permImplStepUnary _ (MbPermImpls_Cons _ _ (matchMbImplFail -> Just msg)) =
  PermImpl_Step (Impl1_Fail msg) MbPermImpls_Nil

-- If the continuation implication is a catch with a failure on the right-hand
-- side, percolate up the catch
{- FIXME: this exposes some weird performance bug!
permImplStepUnary impl1 (MbPermImpls_Cons MbPermImpls_Nil
                         (matchMbImplCatchFail -> Just (mb_impl, msg))) =
    PermImpl_Step Impl1_Catch
    (MbPermImpls_Cons
     (MbPermImpls_Cons MbPermImpls_Nil $
      emptyMb $ PermImpl_Step impl1 $
      MbPermImpls_Cons MbPermImpls_Nil mb_impl)
     (emptyMb $ PermImpl_Step (Impl1_Fail msg) MbPermImpls_Nil))
-}

-- Default case: just apply PermImpl_Step
permImplStepUnary impl1 mb_impls = PermImpl_Step impl1 mb_impls


-- | Pattern-match an implication inside a binding to see if it is just a
-- failure, and if so, return the failure message, all without requiring a
-- 'NuMatchingAny1' constraint on the @r@ variable
matchMbImplFail :: NuMatchingAny1 r => Mb ctx (PermImpl r ps) -> Maybe String
matchMbImplFail mb_impl = case mbMatch mb_impl of
  [nuMP| PermImpl_Step (Impl1_Fail msg) _ |] -> Just $ mbLift msg
  _ -> Nothing

-- | Pattern-matchin an implication inside a binding to see if it is a catch
-- whose right-hand side is just a failure, all without requiring a
-- 'NuMatchingAny1' constraint on the @r@ variable
matchMbImplCatchFail :: NuMatchingAny1 r =>
                        Mb (ctx :: RList CrucibleType) (PermImpl r ps) ->
                        Maybe (Mb ctx (PermImpl r ps), String)
matchMbImplCatchFail mb_impl = case mbMatch mb_impl of
  [nuMP| PermImpl_Step Impl1_Catch
                      (MbPermImpls_Cons _ (MbPermImpls_Cons _ _ mb_impl1)
                      mb_impl2) |]
    | Just msg <- matchMbImplFail (mbCombine RL.typeCtxProxies mb_impl2) ->
      Just (mbCombine RL.typeCtxProxies mb_impl1, msg)
  _ -> Nothing

-- | Produce a branching proof tree that performs the first implication and, if
-- that one fails, falls back on the second. If 'pruneFailingBranches' is set,
-- failing branches are pruned; otherwise, catches are reorganized so that they
-- are right-nested, and any failures are combined.
permImplCatch :: PermImpl r ps -> PermImpl r ps -> PermImpl r ps
permImplCatch (PermImpl_Step (Impl1_Fail _) _) pimpl
  | pruneFailingBranches = pimpl
permImplCatch pimpl (PermImpl_Step (Impl1_Fail _) _)
  | pruneFailingBranches = pimpl
permImplCatch (PermImpl_Step (Impl1_Fail str1) _) (PermImpl_Step
                                                   (Impl1_Fail str2) mb_impls) =
  PermImpl_Step (Impl1_Fail (str1 ++ "\n\n--------------------\n\n" ++ str2)) mb_impls
permImplCatch pimpl1@(PermImpl_Step (Impl1_Fail _) _) pimpl2 =
  permImplCatch pimpl2 pimpl1
permImplCatch (PermImpl_Step Impl1_Catch
               (MbPermImpls_Cons _
                (MbPermImpls_Cons _ _ mb_pimpl_1a) mb_pimpl_1b)) pimpl2 =
  permImplCatch (elimEmptyMb mb_pimpl_1a) $
  permImplCatch (elimEmptyMb mb_pimpl_1b) pimpl2
permImplCatch pimpl1 pimpl2 =
  PermImpl_Step Impl1_Catch $
  MbPermImpls_Cons knownRepr (MbPermImpls_Cons knownRepr MbPermImpls_Nil $ emptyMb pimpl1) $
  emptyMb pimpl2


-- | Test if a 'PermImpl' "succeeds", meaning there is at least one non-failing
-- branch. If it does succeed, return a heuristic number for how "well" it
-- succeeds; e.g., rate a 'PermImpl' higher if all disjunctive branches succeed,
-- that is, if both children of every 'Impl1_ElimOr' succeed. Return 0 if the
-- 'PermImpl' does not succeed at all.
permImplSucceeds :: PermImpl r ps -> Int
permImplSucceeds (PermImpl_Done _) = 2
permImplSucceeds (PermImpl_Step (Impl1_Fail _) _) = 0
permImplSucceeds (PermImpl_Step Impl1_Catch
                  (MbPermImpls_Cons _ (MbPermImpls_Cons _ _ mb_impl1) mb_impl2)) =
  max (mbLift $ fmap permImplSucceeds mb_impl1)
  (mbLift $ fmap permImplSucceeds mb_impl2)
permImplSucceeds (PermImpl_Step (Impl1_Push _ _) (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl
permImplSucceeds (PermImpl_Step (Impl1_Pop _ _) (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl
permImplSucceeds (PermImpl_Step (Impl1_ElimOr _ _ _)
                  (MbPermImpls_Cons _ (MbPermImpls_Cons _ _ mb_impl1) mb_impl2)) =
  max (mbLift (fmap permImplSucceeds mb_impl1))
  (mbLift (fmap permImplSucceeds mb_impl2))
permImplSucceeds (PermImpl_Step (Impl1_ElimExists _ _)
                  (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl
permImplSucceeds (PermImpl_Step (Impl1_Simpl _ _)
                  (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl
permImplSucceeds (PermImpl_Step (Impl1_LetBind _ _)
                  (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl
permImplSucceeds (PermImpl_Step (Impl1_ElimStructField _ _ _ _)
                  (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl
permImplSucceeds (PermImpl_Step (Impl1_ElimLLVMFieldContents _ _)
                  (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl
permImplSucceeds (PermImpl_Step (Impl1_ElimLLVMBlockToEq _ _)
                  (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl
permImplSucceeds (PermImpl_Step Impl1_BeginLifetime
                  (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl
permImplSucceeds (PermImpl_Step (Impl1_TryProveBVProp _ _ _)
                  (MbPermImpls_Cons _ _ mb_impl)) =
  mbLift $ fmap permImplSucceeds mb_impl

-- | Test if a 'PermImpl' fails, meaning 'permImplSucceeds' returns 0
permImplFails :: PermImpl r ps -> Bool
permImplFails = (== 0) . permImplSucceeds


-- FIXME: no longer needed...?
-- traversePermImpl :: forall m ps r1 r2.
--                     MonadStrongBind m => (forall ps'. r1 ps' -> m (r2 ps')) ->
--                     PermImpl r1 ps -> m (PermImpl r2 ps)
-- traversePermImpl f (PermImpl_Done r) = PermImpl_Done <$> f r
-- traversePermImpl f (PermImpl_Step impl1 mb_perm_impls) =
--   PermImpl_Step impl1 <$> helper mb_perm_impls
--   where
--     helper :: MbPermImpls r1 bs_pss -> m (MbPermImpls r2 bs_pss)
--     helper MbPermImpls_Nil = return MbPermImpls_Nil
--     helper (MbPermImpls_Cons _ mb_impls mb_impl) =
--       do mb_impls' <- helper mb_impls
--          mb_impl' <- strongMbM (fmap (traversePermImpl f) mb_impl)
--          return (MbPermImpls_Cons _ mb_impls' mb_impl')

-- | Assert a condition and print an error message if it fails
--
-- FIXME: put this somewhere more meaningful...
permAssert :: Bool -> String -> a -> a
permAssert True _ a = a
permAssert False str _ = error str

-- | Compute the input permissions of a 'SimplImpl' implication
simplImplIn :: SimplImpl ps_in ps_out -> DistPerms ps_in
simplImplIn (SImpl_Drop x p) = distPerms1 x p
simplImplIn (SImpl_Copy x p) =
  permAssert (permIsCopyable p)
  "simplImplIn: SImpl_Copy: permission is not copyable!" $
  distPerms1 x p
simplImplIn (SImpl_Swap x p1 y p2) = distPerms2 x p1 y p2
simplImplIn (SImpl_MoveUp ps1 x p ps2) =
  appendDistPerms (distPerms1 x p) $ appendDistPerms ps1 ps2
simplImplIn (SImpl_MoveDown ps1 x p ps2) =
  appendDistPerms (DistPermsCons ps1 x p) ps2
simplImplIn (SImpl_IntroOrL x p1 _) = distPerms1 x p1
simplImplIn (SImpl_IntroOrR x _ p2) = distPerms1 x p2
simplImplIn (SImpl_IntroExists x e p) =
  distPerms1 x (subst (singletonSubst e) p)
simplImplIn (SImpl_Cast x y p) = distPerms2 x (ValPerm_Eq $ PExpr_Var y) y p
simplImplIn (SImpl_CastPerm x eqp) =
  appendDistPerms (distPerms1 x (eqProofLHS eqp)) (eqProofPerms eqp)
simplImplIn (SImpl_IntroEqRefl _) = DistPermsNil
simplImplIn (SImpl_InvertEq x y) = distPerms1 x (ValPerm_Eq $ PExpr_Var y)
simplImplIn (SImpl_InvTransEq x y e) =
  distPerms2 x (ValPerm_Eq e) y (ValPerm_Eq e)
simplImplIn (SImpl_CopyEq x e) = distPerms1 x (ValPerm_Eq e)
simplImplIn (SImpl_LLVMWordEq x y e) =
  distPerms2 x (ValPerm_Eq (PExpr_LLVMWord (PExpr_Var y))) y (ValPerm_Eq e)
simplImplIn (SImpl_IntroConj _) = DistPermsNil
simplImplIn (SImpl_ExtractConj x ps _) = distPerms1 x (ValPerm_Conj ps)
simplImplIn (SImpl_CopyConj x ps _) = distPerms1 x (ValPerm_Conj ps)
simplImplIn (SImpl_InsertConj x p ps _) =
  distPerms2 x (ValPerm_Conj [p]) x (ValPerm_Conj ps)
simplImplIn (SImpl_AppendConjs x ps1 ps2) =
  distPerms2 x (ValPerm_Conj ps1) x (ValPerm_Conj ps2)
simplImplIn (SImpl_SplitConjs x ps _) =
  distPerms1 x (ValPerm_Conj ps)
simplImplIn (SImpl_IntroStructTrue _ _) = DistPermsNil
simplImplIn (SImpl_StructEqToPerm x exprs) =
  distPerms1 x (ValPerm_Eq $ PExpr_Struct exprs)
simplImplIn (SImpl_StructPermToEq x exprs) =
  distPerms1 x (ValPerm_Conj1 $ Perm_Struct $
                RL.map ValPerm_Eq $ exprsToRAssign exprs)
simplImplIn (SImpl_IntroStructField x ps memb p) =
  case RL.get memb ps of
    ValPerm_Eq (PExpr_Var y) ->
      distPerms2 x (ValPerm_Conj1 $ Perm_Struct ps) y p
    _ -> error "simplImplIn: SImpl_IntroStructField: field does not have an equality permission to a variable"
simplImplIn (SImpl_ConstFunPerm x h _ _) =
  distPerms1 x (ValPerm_Eq $ PExpr_Fun h)
simplImplIn (SImpl_CastLLVMWord x e1 e2) =
  distPerms2 x (ValPerm_Eq $ PExpr_LLVMWord e1)
  x (ValPerm_Conj [Perm_BVProp $ BVProp_Eq e1 e2])
simplImplIn (SImpl_InvertLLVMOffsetEq x off y) =
  distPerms1 x $ ValPerm_Eq $ PExpr_LLVMOffset y off
simplImplIn (SImpl_OffsetLLVMWord y e off x) =
  distPerms2 x (ValPerm_Eq $ PExpr_LLVMOffset y off)
  y (ValPerm_Eq (PExpr_LLVMWord e))
simplImplIn (SImpl_CastLLVMPtr y p off x) =
  distPerms2 x (ValPerm_Eq $ PExpr_LLVMOffset y off) y p
simplImplIn (SImpl_CastLLVMFree x e1 e2) =
  distPerms2 x (ValPerm_Conj [Perm_LLVMFree e1])
  x (ValPerm_Conj [Perm_BVProp $ BVProp_Eq e1 e2])
simplImplIn (SImpl_CastLLVMFieldOffset x fld off') =
  distPerms2 x (ValPerm_Conj [Perm_LLVMField fld])
  x (ValPerm_Conj [Perm_BVProp $ BVProp_Eq (llvmFieldOffset fld) off'])
simplImplIn (SImpl_IntroLLVMFieldContents x y fld) =
  distPerms2 x (ValPerm_Conj [Perm_LLVMField $
                              fld { llvmFieldContents =
                                    ValPerm_Eq (PExpr_Var y)}])
  y (llvmFieldContents fld)
simplImplIn (SImpl_DemoteLLVMFieldRW x fld) =
  distPerms1 x (ValPerm_Conj [Perm_LLVMField fld])
simplImplIn (SImpl_LLVMArrayCopy x ap sub_ap) =
  if isJust (llvmArrayIsOffsetArray ap sub_ap) &&
     atomicPermIsCopyable (Perm_LLVMArray ap) then
    distPerms2 x (ValPerm_Conj [Perm_LLVMArray ap])
    x (ValPerm_Conj $ map Perm_BVProp $ llvmArrayContainsArray ap sub_ap)
  else
    error "simplImplIn: SImpl_LLVMArrayCopy: array permission not copyable or not a sub-array"
simplImplIn (SImpl_LLVMArrayBorrow x ap sub_ap) =
  if isJust (llvmArrayIsOffsetArray ap sub_ap) then
    distPerms2 x (ValPerm_Conj [Perm_LLVMArray ap])
    x (ValPerm_Conj $ map Perm_BVProp $ llvmArrayContainsArray ap sub_ap)
  else
    error "simplImplIn: SImpl_LLVMArrayBorrow: array permission not a sub-array"
simplImplIn (SImpl_LLVMArrayReturn x ap ret_ap) =
  if isJust (llvmArrayIsOffsetArray ap ret_ap) &&
     elem (llvmSubArrayBorrow ap ret_ap) (llvmArrayBorrows ap) then
    distPerms2 x (ValPerm_Conj [Perm_LLVMArray ret_ap])
    x (ValPerm_Conj [Perm_LLVMArray ap])
  else
    error "simplImplIn: SImpl_LLVMArrayReturn: array not being borrowed or not a sub-array"

simplImplIn (SImpl_LLVMArrayAppend x ap1 ap2) =
  case llvmArrayIsOffsetArray ap1 ap2 of
    Just len1
      | bvEq len1 (llvmArrayLen ap1)
      , llvmArrayFields ap1 == llvmArrayFields ap2 ->
        distPerms2 x (ValPerm_Conj1 $ Perm_LLVMArray ap1)
        x (ValPerm_Conj1 $ Perm_LLVMArray ap2)
    _ -> error "simplImplIn: SImpl_LLVMArrayAppend: arrays cannot be appended"

simplImplIn (SImpl_LLVMArrayRearrange x ap1 ap2) =
  if bvEq (llvmArrayOffset ap1) (llvmArrayOffset ap2) &&
     bvEq (llvmArrayLen ap1) (llvmArrayLen ap2) &&
     llvmArrayStride ap1 == llvmArrayStride ap2 &&
     llvmArrayFields ap1 == llvmArrayFields ap2 &&
     all (flip elem (llvmArrayBorrows ap2)) (llvmArrayBorrows ap1) &&
     all (flip elem (llvmArrayBorrows ap1)) (llvmArrayBorrows ap2) then
    distPerms1 x (ValPerm_Conj1 $ Perm_LLVMArray ap1)
  else
    error "simplImplIn: SImpl_LLVMArrayRearrange: arrays not equivalent"

simplImplIn (SImpl_LLVMArrayToField x ap _) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMArray ap)

simplImplIn (SImpl_LLVMArrayEmpty _ ap) =
  if bvEq (llvmArrayLen ap) (bvInt 0) && llvmArrayBorrows ap == [] then
    DistPermsNil
  else
    error "simplImplIn: SImpl_LLVMArrayEmpty: malformed empty array permission"

simplImplIn (SImpl_LLVMArrayOneCell x ap) =
  case llvmArrayAsFields ap of
    Just (flds, []) ->
      distPerms1 x (ValPerm_Conj $ map llvmArrayFieldToAtomicPerm flds)
    _ -> error "simplImplIn: SImpl_LLVMArrayOneCell: unexpected form of array permission"

simplImplIn (SImpl_LLVMArrayIndexCopy x ap ix) =
  if llvmArrayIndexFieldNum ix < length (llvmArrayFields ap) &&
     atomicPermIsCopyable (llvmArrayFieldToAtomicPerm $
                           llvmArrayFieldWithOffset ap ix) then
    distPerms2 x (ValPerm_Conj [Perm_LLVMArray ap])
    x (ValPerm_Conj $ map Perm_BVProp $ llvmArrayIndexInArray ap ix)
  else
    if llvmArrayIndexFieldNum ix >= length (llvmArrayFields ap) then
      error "simplImplIn: SImpl_LLVMArrayIndexCopy: index out of range"
    else
      error "simplImplIn: SImpl_LLVMArrayIndexCopy: field is not copyable"

simplImplIn (SImpl_LLVMArrayIndexBorrow x ap ix) =
  distPerms2 x (ValPerm_Conj [Perm_LLVMArray ap])
  x (ValPerm_Conj $ map Perm_BVProp $ llvmArrayIndexInArray ap ix)

simplImplIn (SImpl_LLVMArrayIndexReturn x ap ix) =
  if elem (FieldBorrow ix) (llvmArrayBorrows ap) then
    distPerms2 x (ValPerm_Conj1 $ llvmArrayFieldToAtomicPerm $
                  llvmArrayFieldWithOffset ap ix)
    x (ValPerm_Conj [Perm_LLVMArray ap])
  else
    error "simplImplIn: SImpl_LLVMArrayIndexReturn: index not being borrowed"

simplImplIn (SImpl_LLVMArrayContents x ap _ _ _) =
  distPerms1 x (ValPerm_Conj [Perm_LLVMArray ap])
simplImplIn (SImpl_LLVMFieldIsPtr x fp) =
  distPerms1 x (ValPerm_Conj [Perm_LLVMField fp])
simplImplIn (SImpl_LLVMArrayIsPtr x ap) =
  distPerms1 x (ValPerm_Conj [Perm_LLVMArray ap])
simplImplIn (SImpl_LLVMBlockIsPtr x bp) =
  distPerms1 x (ValPerm_Conj [Perm_LLVMBlock bp])
simplImplIn (SImpl_SplitLifetime x f args l l2 ps_in ps_out) =
  -- If l=always then the second permission is l2:true
  let (l',l'_p) = lcurrentPerm l l2 in
  distPerms3 x (ltFuncApply f args l) l' l'_p l2 (ValPerm_LOwned ps_in ps_out)
simplImplIn (SImpl_SubsumeLifetime l1 ps_in1 ps_out1 l2 ps_in2 ps_out2) =
  distPerms2 l1 (ValPerm_LOwned ps_in1 ps_out1)
  l2 (ValPerm_LOwned ps_in2 ps_out2)
simplImplIn (SImpl_WeakenLifetime x f args l l2) =
  let (l',l'_p) = lcurrentPerm l l2 in
  distPerms2 x (ltFuncApply f args l) l' l'_p
simplImplIn (SImpl_MapLifetime l ps_in ps_out _ _ ps1 ps2 _ _) =
  RL.append ps1 $ DistPermsCons ps2 l $ ValPerm_LOwned ps_in ps_out
simplImplIn (SImpl_EndLifetime l ps_in ps_out) =
  case lownedPermsToDistPerms ps_in of
    Just perms_in ->
      DistPermsCons perms_in l $ ValPerm_LOwned ps_in ps_out
    Nothing ->
      error "simplImplIn: SImpl_EndLifetime: non-variables in input permissions"
simplImplIn (SImpl_LCurrentRefl _) = DistPermsNil
simplImplIn (SImpl_LCurrentTrans l1 l2 l3) =
  distPerms2 l1 (ValPerm_LCurrent $ PExpr_Var l2) l2 (ValPerm_LCurrent l3)
simplImplIn (SImpl_IntroLLVMBlockEmpty _ _) = DistPermsNil
simplImplIn (SImpl_DemoteLLVMBlockRW x bp) =
  distPerms1 x $ ValPerm_LLVMBlock bp
simplImplIn (SImpl_CoerceLLVMBlockEmpty x bp) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock bp)
simplImplIn (SImpl_ElimLLVMBlockToBytes x bp) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock bp)
simplImplIn (SImpl_IntroLLVMBlockSeqEmpty x bp) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock bp)
simplImplIn (SImpl_ElimLLVMBlockSeqEmpty x bp) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                bp { llvmBlockShape =
                       PExpr_SeqShape (llvmBlockShape bp) PExpr_EmptyShape })
simplImplIn (SImpl_IntroLLVMBlockNamed x bp nmsh) =
  case llvmBlockShape bp of
    PExpr_NamedShape rw l nmsh' args
      | Just (Refl,Refl) <- namedShapeEq nmsh nmsh'
      , Just sh' <- unfoldModalizeNamedShape rw l nmsh args ->
        distPerms1 x (ValPerm_LLVMBlock $ bp { llvmBlockShape = sh' })
    _ -> error "simplImplIn: SImpl_IntroLLVMBlockNamed: unexpected block shape"
simplImplIn (SImpl_ElimLLVMBlockNamed x bp _) =
  distPerms1 x $ ValPerm_LLVMBlock bp
simplImplIn (SImpl_IntroLLVMBlockFromEq x bp y) =
  distPerms2 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                bp { llvmBlockShape = PExpr_EqShape $ PExpr_Var y })
  y (ValPerm_Conj1 $ Perm_LLVMBlockShape $ llvmBlockShape bp)
simplImplIn (SImpl_IntroLLVMBlockPtr x maybe_rw2 maybe_l2 bp) =
  if llvmShapeLength (llvmBlockShape bp) == Just (llvmBlockLen bp) then
    distPerms1 x (llvmBlockPtrPerm $
                  llvmBlockAdjustModalities maybe_rw2 maybe_l2 bp)
  else
    error "simplImplIn: SImpl_IntroLLVMBlockPtr: incorrect length"
simplImplIn (SImpl_ElimLLVMBlockPtr x maybe_rw2 maybe_l2 bp) =
  if llvmShapeLength (llvmBlockShape bp) == Just (llvmBlockLen bp) then
    distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                  bp { llvmBlockLen = bvInt (machineWordBytes bp),
                       llvmBlockShape =
                         PExpr_PtrShape maybe_rw2 maybe_l2 (llvmBlockShape bp) })
  else
    error "simplImplIn: SImpl_ElimLLVMBlockPtr: incorrect length"
simplImplIn (SImpl_IntroLLVMBlockField x fp) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMField fp)
simplImplIn (SImpl_ElimLLVMBlockField x fp len) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                (llvmFieldPermToBlock fp) { llvmBlockLen = len })
simplImplIn (SImpl_IntroLLVMBlockArray x ap) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMArray ap)
simplImplIn (SImpl_ElimLLVMBlockArray x ap) =
  case llvmAtomicPermToBlock (Perm_LLVMArray ap) of
    Just bp -> distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock bp)
    Nothing ->
      error "simplImplIn: SImpl_ElimLLVMBlockArray: malformed array permission"
simplImplIn (SImpl_IntroLLVMBlockSeq x bp1 len2 sh2) =
  distPerms2
  x (ValPerm_Conj1 $ Perm_LLVMBlock bp1)
  x (ValPerm_Conj1 $ Perm_LLVMBlock $
     bp1 { llvmBlockOffset = bvAdd (llvmBlockOffset bp1) (llvmBlockLen bp1),
           llvmBlockLen = len2, llvmBlockShape = sh2 })
simplImplIn (SImpl_ElimLLVMBlockSeq x bp sh2) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                bp { llvmBlockShape = PExpr_SeqShape (llvmBlockShape bp) sh2 })
simplImplIn (SImpl_IntroLLVMBlockOr x bp1 sh2) =
  distPerms1 x (ValPerm_Or
                (ValPerm_Conj1 $ Perm_LLVMBlock bp1)
                (ValPerm_Conj1 $ Perm_LLVMBlock $ bp1 { llvmBlockShape = sh2 }))
simplImplIn (SImpl_ElimLLVMBlockOr x bp1 sh2) =
  let sh1 = llvmBlockShape bp1 in
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                bp1 { llvmBlockShape = PExpr_OrShape sh1 sh2 })
simplImplIn (SImpl_IntroLLVMBlockEx x bp) =
  case llvmBlockShape bp of
    PExpr_ExShape mb_sh ->
      distPerms1 x (ValPerm_Exists $
                    flip fmap mb_sh $ \sh ->
                     ValPerm_LLVMBlock (bp { llvmBlockShape = sh }))
    _ ->
      error "simplImplIn: SImpl_IntroLLVMBlockEx: non-existential shape"
simplImplIn (SImpl_ElimLLVMBlockEx x bp) =
  distPerms1 x (ValPerm_LLVMBlock bp)
simplImplIn (SImpl_FoldNamed x np args off) =
  distPerms1 x (unfoldPerm np args off)
simplImplIn (SImpl_UnfoldNamed x np args off) =
  distPerms1 x (ValPerm_Named (namedPermName np) args off)
simplImplIn (SImpl_NamedToConj x npn args off) =
  distPerms1 x (ValPerm_Named npn args off)
simplImplIn (SImpl_NamedFromConj x npn args off) =
  distPerms1 x (ValPerm_Conj1 $ Perm_NamedConj npn args off)
-- simplImplIn (SImpl_Mu x p1 _ _) = distPerms1 x (ValPerm_Mu p1)
simplImplIn (SImpl_NamedArgAlways x npn args off memb _) =
  case nthPermExpr args memb of
    PExpr_Always -> distPerms1 x (ValPerm_Named npn args off)
    _ -> error "simplImplIn: SImplNamedArgAlways: non-always argument!"
simplImplIn (SImpl_NamedArgCurrent x npn args off memb l2) =
  case nthPermExpr args memb of
    PExpr_Var l1 ->
      distPerms2 x (ValPerm_Named npn args off) l1 (ValPerm_LCurrent l2)
    _ -> error "simplImplIn: SImplNamedArgCurrent: non-variable argument!"
simplImplIn (SImpl_NamedArgWrite x npn args off memb _) =
  case nthPermExpr args memb of
    PExpr_RWModality Write ->
      distPerms1 x (ValPerm_Named npn args off)
    _ -> error "simplImplIn: SImplNamedArgWrite: non-Write argument!"
simplImplIn (SImpl_NamedArgRead x npn args off _) =
  distPerms1 x (ValPerm_Named npn args off)
simplImplIn (SImpl_ReachabilityTrans x rp args off y e) =
  let npn = recPermName rp in
  distPerms2 x (ValPerm_Named npn (PExprs_Cons args (PExpr_Var y)) off)
  y (ValPerm_Named npn (PExprs_Cons args e) off)


-- | Compute the output permissions of a 'SimplImpl' implication
simplImplOut :: SimplImpl ps_in ps_out -> DistPerms ps_out
simplImplOut (SImpl_Drop _ _) = DistPermsNil
simplImplOut (SImpl_Copy x p) =
  if permIsCopyable p then distPerms2 x p x p else
    error "simplImplOut: SImpl_Copy: permission is not copyable!"
simplImplOut (SImpl_Swap x p1 y p2) = distPerms2 y p2 x p1
simplImplOut (SImpl_MoveUp ps1 x p ps2) =
  appendDistPerms (DistPermsCons ps1 x p) ps2
simplImplOut (SImpl_MoveDown ps1 x p ps2) =
  appendDistPerms (distPerms1 x p) $ appendDistPerms ps1 ps2
simplImplOut (SImpl_IntroOrL x p1 p2) = distPerms1 x (ValPerm_Or p1 p2)
simplImplOut (SImpl_IntroOrR x p1 p2) = distPerms1 x (ValPerm_Or p1 p2)
simplImplOut (SImpl_IntroExists x _ p) = distPerms1 x (ValPerm_Exists p)
simplImplOut (SImpl_Cast x _ p) = distPerms1 x p
simplImplOut (SImpl_CastPerm x eqp) = distPerms1 x (eqProofRHS eqp)
simplImplOut (SImpl_IntroEqRefl x) = distPerms1 x (ValPerm_Eq $ PExpr_Var x)
simplImplOut (SImpl_InvertEq x y) = distPerms1 y (ValPerm_Eq $ PExpr_Var x)
simplImplOut (SImpl_InvTransEq x y _) = distPerms1 x (ValPerm_Eq $ PExpr_Var y)
simplImplOut (SImpl_CopyEq x e) = distPerms2 x (ValPerm_Eq e) x (ValPerm_Eq e)
simplImplOut (SImpl_LLVMWordEq x _ e) =
  distPerms1 x (ValPerm_Eq (PExpr_LLVMWord e))
simplImplOut (SImpl_IntroConj x) = distPerms1 x ValPerm_True
simplImplOut (SImpl_ExtractConj x ps i) =
  if i < length ps then
    distPerms2 x (ValPerm_Conj [ps !! i])
    x (ValPerm_Conj (take i ps ++ drop (i+1) ps))
  else
    error "simplImplOut: SImpl_ExtractConj: index out of bounds"
simplImplOut (SImpl_CopyConj x ps i) =
  if i < length ps && atomicPermIsCopyable (ps !! i) then
    distPerms2 x (ValPerm_Conj [ps !! i]) x (ValPerm_Conj ps)
  else
    if i >= length ps then
      error "simplImplOut: SImpl_CopyConj: index out of bounds"
    else
      error "simplImplOut: SImpl_CopyConj: permission not copyable"
simplImplOut (SImpl_InsertConj x p ps i) =
  distPerms1 x (ValPerm_Conj (take i ps ++ p : drop i ps))
simplImplOut (SImpl_AppendConjs x ps1 ps2) =
  distPerms1 x (ValPerm_Conj (ps1 ++ ps2))
simplImplOut (SImpl_SplitConjs x ps i) =
  distPerms2 x (ValPerm_Conj (take i ps)) x (ValPerm_Conj (drop i ps))
simplImplOut (SImpl_IntroStructTrue x fs) =
  distPerms1 x (ValPerm_Conj1 $ Perm_Struct $ trueValuePerms fs)
simplImplOut (SImpl_StructEqToPerm x exprs) =
  distPerms1 x (ValPerm_Conj1 $ Perm_Struct $
                RL.map ValPerm_Eq $ exprsToRAssign exprs)
simplImplOut (SImpl_StructPermToEq x exprs) =
  distPerms1 x (ValPerm_Eq $ PExpr_Struct exprs)
simplImplOut (SImpl_IntroStructField x ps memb p) =
  distPerms1 x (ValPerm_Conj1 $ Perm_Struct $ RL.set memb p ps)
simplImplOut (SImpl_ConstFunPerm x _ fun_perm _) =
  distPerms1 x (ValPerm_Conj1 $ Perm_Fun fun_perm)
simplImplOut (SImpl_CastLLVMWord x _ e2) =
  distPerms1 x (ValPerm_Eq $ PExpr_LLVMWord e2)
simplImplOut (SImpl_InvertLLVMOffsetEq x off y) =
  distPerms1 y $ ValPerm_Eq $ PExpr_LLVMOffset x $ bvNegate off
simplImplOut (SImpl_OffsetLLVMWord _ e off x) =
  distPerms1 x (ValPerm_Eq $ PExpr_LLVMWord $ bvAdd e off)
simplImplOut (SImpl_CastLLVMPtr _ p off x) =
  distPerms1 x (offsetLLVMPerm (bvNegate off) p)
simplImplOut (SImpl_CastLLVMFree x _ e2) =
  distPerms1 x (ValPerm_Conj [Perm_LLVMFree e2])
simplImplOut (SImpl_CastLLVMFieldOffset x fld off') =
  distPerms1 x (ValPerm_Conj [Perm_LLVMField $ fld { llvmFieldOffset = off' }])
simplImplOut (SImpl_IntroLLVMFieldContents x _ fld) =
  distPerms1 x (ValPerm_Conj [Perm_LLVMField fld])
simplImplOut (SImpl_DemoteLLVMFieldRW x fld) =
  distPerms1 x (ValPerm_Conj [Perm_LLVMField $
                              fld { llvmFieldRW = PExpr_Read }])
simplImplOut (SImpl_LLVMArrayCopy x ap sub_ap) =
  if isJust (llvmArrayIsOffsetArray ap sub_ap) &&
     atomicPermIsCopyable (Perm_LLVMArray ap) then
    distPerms2 x (ValPerm_Conj [Perm_LLVMArray sub_ap])
    x (ValPerm_Conj [Perm_LLVMArray ap])
  else
    error "simplImplOut: SImpl_LLVMArrayCopy: array permission not copyable or not a sub-array"

simplImplOut (SImpl_LLVMArrayBorrow x ap sub_ap) =
  case llvmArrayIsOffsetArray ap sub_ap of
    Just _ ->
      distPerms2 x (ValPerm_Conj [Perm_LLVMArray sub_ap])
      x (ValPerm_Conj
         [Perm_LLVMArray $
          llvmArrayAddBorrow (llvmSubArrayBorrow ap sub_ap) $
          llvmArrayRemArrayBorrows ap sub_ap])
    Nothing ->
      error "simplImplOut: SImpl_LLVMArrayBorrow: array permission not a sub-array"

simplImplOut (SImpl_LLVMArrayReturn x ap ret_ap) =
  if isJust (llvmArrayIsOffsetArray ap ret_ap) &&
     elem (llvmSubArrayBorrow ap ret_ap) (llvmArrayBorrows ap) then
    distPerms1 x
    (ValPerm_Conj [Perm_LLVMArray $
                   llvmArrayRemBorrow (llvmSubArrayBorrow ap ret_ap) $
                   llvmArrayAddArrayBorrows ap ret_ap])
  else
    error "simplImplOut: SImpl_LLVMArrayReturn: array not being borrowed or not a sub-array"

simplImplOut (SImpl_LLVMArrayAppend x ap1 ap2) =
  case llvmArrayIsOffsetArray ap1 ap2 of
    Just len1
      | bvEq len1 (llvmArrayLen ap1)
      , llvmArrayFields ap1 == llvmArrayFields ap2
      , ap1' <- ap1 { llvmArrayLen =
                        bvAdd (llvmArrayLen ap1) (llvmArrayLen ap2) } ->
        distPerms1 x $ ValPerm_Conj1 $ Perm_LLVMArray $
        llvmArrayAddArrayBorrows ap1' ap2
    _ -> error "simplImplOut: SImpl_LLVMArrayAppend: arrays cannot be appended"

simplImplOut (SImpl_LLVMArrayRearrange x ap1 ap2) =
  if bvEq (llvmArrayOffset ap1) (llvmArrayOffset ap2) &&
     bvEq (llvmArrayLen ap1) (llvmArrayLen ap2) &&
     llvmArrayStride ap1 == llvmArrayStride ap2 &&
     llvmArrayFields ap1 == llvmArrayFields ap2 &&
     all (flip elem (llvmArrayBorrows ap2)) (llvmArrayBorrows ap1) &&
     all (flip elem (llvmArrayBorrows ap1)) (llvmArrayBorrows ap2) then
    distPerms1 x (ValPerm_Conj1 $ Perm_LLVMArray ap2)
  else
    error "simplImplOut: SImpl_LLVMArrayRearrange: arrays not equivalent"

simplImplOut (SImpl_LLVMArrayToField x ap sz) =
  case llvmArrayToField sz ap of
    Just fp -> distPerms1 x (ValPerm_Conj1 $ Perm_LLVMField fp)
    Nothing ->
      error "simplImplOut: SImpl_LLVMArrayToField: malformed array permission"

simplImplOut (SImpl_LLVMArrayEmpty x ap) =
  if bvEq (llvmArrayLen ap) (bvInt 0) && llvmArrayBorrows ap == [] then
    distPerms1 x (ValPerm_Conj1 $ Perm_LLVMArray ap)
  else
    error "simplImplOut: SImpl_LLVMArrayEmpty: malformed empty array permission"

simplImplOut (SImpl_LLVMArrayOneCell x ap) =
  case llvmArrayAsFields ap of
    Just (_, []) ->
      distPerms1 x (ValPerm_Conj1 $ Perm_LLVMArray ap)
    _ -> error "simplImplOut: SImpl_LLVMArrayOneCell: unexpected form of array permission"

simplImplOut (SImpl_LLVMArrayIndexCopy x ap ix) =
  if llvmArrayIndexFieldNum ix < length (llvmArrayFields ap) &&
     atomicPermIsCopyable (llvmArrayFieldToAtomicPerm $
                           llvmArrayFieldWithOffset ap ix) then
    distPerms2 x (ValPerm_Conj1 $ llvmArrayFieldToAtomicPerm $
                  llvmArrayFieldWithOffset ap ix)
    x (ValPerm_Conj [Perm_LLVMArray ap])
  else
    if llvmArrayIndexFieldNum ix >= length (llvmArrayFields ap) then
      error "simplImplOut: SImpl_LLVMArrayIndexCopy: index out of range"
    else
      error "simplImplOut: SImpl_LLVMArrayIndexCopy: field is not copyable"

simplImplOut (SImpl_LLVMArrayIndexBorrow x ap ix) =
  distPerms2 x (ValPerm_Conj1 $ llvmArrayFieldToAtomicPerm $
                llvmArrayFieldWithOffset ap ix)
  x (ValPerm_Conj [Perm_LLVMArray $
                   llvmArrayAddBorrow (FieldBorrow ix) ap])

simplImplOut (SImpl_LLVMArrayIndexReturn x ap ix) =
  if elem (FieldBorrow ix) (llvmArrayBorrows ap) then
    distPerms1 x
    (ValPerm_Conj [Perm_LLVMArray $ llvmArrayRemBorrow (FieldBorrow ix) ap])
  else
    error "simplImplOut: SImpl_LLVMArrayIndexReturn: index not being borrowed"

simplImplOut (SImpl_LLVMArrayContents x ap i fp _) =
  distPerms1 x (ValPerm_Conj [Perm_LLVMArray $
                              ap { llvmArrayFields =
                                     take i (llvmArrayFields ap) ++
                                     fp : drop (i+1) (llvmArrayFields ap)}])

simplImplOut (SImpl_LLVMFieldIsPtr x fp) =
  distPerms2 x (ValPerm_Conj1 Perm_IsLLVMPtr)
  x (ValPerm_Conj [Perm_LLVMField fp])
simplImplOut (SImpl_LLVMArrayIsPtr x ap) =
  distPerms2 x (ValPerm_Conj1 Perm_IsLLVMPtr)
  x (ValPerm_Conj [Perm_LLVMArray ap])
simplImplOut (SImpl_LLVMBlockIsPtr x bp) =
  distPerms2 x (ValPerm_Conj1 Perm_IsLLVMPtr)
  x (ValPerm_Conj [Perm_LLVMBlock bp])
simplImplOut (SImpl_SplitLifetime x f args l l2 ps_in ps_out) =
  distPerms2 x (ltFuncApply f args $ PExpr_Var l2)
  l2 (ValPerm_LOwned
      (ps_in :>: ltFuncMinApplyLOP x f (PExpr_Var l2))
      (ps_out :>: ltFuncApplyLOP x f args l))
simplImplOut (SImpl_SubsumeLifetime l1 ps_in1 _ps_out1 l2 ps_in2 ps_out2) =
  distPerms2 l1 (ValPerm_LCurrent $ PExpr_Var l2)
  l2 (ValPerm_LOwned ps_in2
      (ps_out2 :>: LOwnedPermLifetime (PExpr_Var l1) ps_in1 ps_out2))
simplImplOut (SImpl_WeakenLifetime x f args _ l2) =
  distPerms1 x (ltFuncApply f args $ PExpr_Var l2)
simplImplOut (SImpl_MapLifetime l _ _ ps_in' ps_out' _ _ _ _) =
  distPerms1 l $ ValPerm_LOwned ps_in' ps_out'
simplImplOut (SImpl_EndLifetime _ _ ps_out) =
  case lownedPermsToDistPerms ps_out of
    Just perms_out -> perms_out
    _ -> error "simplImplOut: SImpl_EndLifetime: non-variable in output permissions"
simplImplOut (SImpl_LCurrentRefl l) =
  distPerms1 l (ValPerm_LCurrent $ PExpr_Var l)
simplImplOut (SImpl_LCurrentTrans l1 _ l3) =
  distPerms1 l1 (ValPerm_LCurrent l3)
simplImplOut (SImpl_DemoteLLVMBlockRW x bp) =
  distPerms1 x $ ValPerm_LLVMBlock (bp { llvmBlockRW = PExpr_Read })
simplImplOut (SImpl_IntroLLVMBlockEmpty x bp) =
  case llvmBlockShape bp of
    PExpr_EmptyShape -> distPerms1 x $ ValPerm_Conj1 $ Perm_LLVMBlock bp
    _ -> error "simplImplOut: SImpl_IntroLLVMBlockEmpty: malformed permission"
simplImplOut (SImpl_CoerceLLVMBlockEmpty x bp) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                bp { llvmBlockShape = PExpr_EmptyShape })
simplImplOut (SImpl_ElimLLVMBlockToBytes x (LLVMBlockPerm {..})) =
  distPerms1 x (llvmByteArrayPerm llvmBlockOffset llvmBlockLen
                llvmBlockRW llvmBlockLifetime)
simplImplOut (SImpl_IntroLLVMBlockSeqEmpty x bp) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                bp { llvmBlockShape =
                       PExpr_SeqShape (llvmBlockShape bp) PExpr_EmptyShape })
simplImplOut (SImpl_ElimLLVMBlockSeqEmpty x bp) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock bp)
simplImplOut (SImpl_IntroLLVMBlockNamed x bp _) =
  distPerms1 x $ ValPerm_LLVMBlock bp
simplImplOut (SImpl_ElimLLVMBlockNamed x bp nmsh) =
  case llvmBlockShape bp of
    PExpr_NamedShape rw l nmsh' args
      | Just (Refl,Refl) <- namedShapeEq nmsh nmsh'
      , Just sh' <- unfoldModalizeNamedShape rw l nmsh args ->
        distPerms1 x (ValPerm_LLVMBlock $ bp { llvmBlockShape = sh' })
    _ -> error "simplImplOut: SImpl_ElimLLVMBlockNamed: unexpected block shape"
simplImplOut (SImpl_IntroLLVMBlockFromEq x bp _) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock bp)
simplImplOut (SImpl_IntroLLVMBlockPtr x maybe_rw2 maybe_l2 bp) =
  if llvmShapeLength (llvmBlockShape bp) == Just (llvmBlockLen bp) then
    distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                  bp { llvmBlockLen = bvInt (machineWordBytes bp),
                       llvmBlockShape =
                         PExpr_PtrShape maybe_rw2 maybe_l2 (llvmBlockShape bp) })
  else
    error "simplImplOut: SImpl_IntroLLVMBlockPtr: incorrect length"
simplImplOut (SImpl_ElimLLVMBlockPtr x maybe_rw2 maybe_l2 bp) =
  if llvmShapeLength (llvmBlockShape bp) == Just (llvmBlockLen bp) then
    distPerms1 x (llvmBlockPtrPerm $
                  llvmBlockAdjustModalities maybe_rw2 maybe_l2 bp)
  else
    error "simplImplOut: SImpl_ElimLLVMBlockPtr: incorrect length"
simplImplOut (SImpl_IntroLLVMBlockField x fp) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $ llvmFieldPermToBlock fp)
simplImplOut (SImpl_ElimLLVMBlockField x fp len) =
  let bp_fp = llvmFieldPermToBlock fp
      sz = llvmFieldLen fp in
  distPerms1 x (ValPerm_Conj
                [Perm_LLVMField fp,
                 Perm_LLVMBlock $
                 bp_fp { llvmBlockOffset = bvAdd (llvmFieldOffset fp) sz,
                         llvmBlockLen = bvSub len sz,
                         llvmBlockShape = PExpr_EmptyShape }])
simplImplOut (SImpl_IntroLLVMBlockArray x ap) =
  case llvmAtomicPermToBlock (Perm_LLVMArray ap) of
    Just bp -> distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock bp)
    Nothing ->
      error "simplImplOut: SImpl_IntroLLVMBlockArray: malformed array permission"
simplImplOut (SImpl_ElimLLVMBlockArray x ap) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMArray ap)
simplImplOut (SImpl_IntroLLVMBlockSeq x bp1 len2 sh2) =
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                bp1 { llvmBlockLen = bvAdd (llvmBlockLen bp1) len2,
                      llvmBlockShape = PExpr_SeqShape (llvmBlockShape bp1) sh2 })
simplImplOut (SImpl_ElimLLVMBlockSeq x bp sh2) =
  case llvmShapeLength (llvmBlockShape bp) of
    Just len1 ->
      distPerms1
      x (ValPerm_Conj
         [Perm_LLVMBlock (bp { llvmBlockLen = len1 }),
          Perm_LLVMBlock $
          bp { llvmBlockOffset = bvAdd (llvmBlockOffset bp) len1,
               llvmBlockLen = bvSub (llvmBlockLen bp) len1,
               llvmBlockShape = sh2 }])
    Nothing ->
      error "simplImplOut: SImpl_ElimLLVMBlockSeq"
simplImplOut (SImpl_IntroLLVMBlockOr x bp1 sh2) =
  let sh1 = llvmBlockShape bp1 in
  distPerms1 x (ValPerm_Conj1 $ Perm_LLVMBlock $
                bp1 { llvmBlockShape = PExpr_OrShape sh1 sh2 })
simplImplOut (SImpl_ElimLLVMBlockOr x bp1 sh2) =
  distPerms1 x (ValPerm_Or
                (ValPerm_Conj1 $ Perm_LLVMBlock bp1)
                (ValPerm_Conj1 $ Perm_LLVMBlock $ bp1 { llvmBlockShape = sh2 }))
simplImplOut (SImpl_IntroLLVMBlockEx x bp) =
  distPerms1 x (ValPerm_LLVMBlock bp)
simplImplOut (SImpl_ElimLLVMBlockEx x bp) =
  case llvmBlockShape bp of
    PExpr_ExShape mb_sh ->
      distPerms1 x (ValPerm_Exists $
                    flip fmap mb_sh $ \sh ->
                     ValPerm_LLVMBlock (bp { llvmBlockShape = sh }))
    _ ->
      error "simplImplOut: SImpl_ElimLLVMBlockEx: non-existential shape"
simplImplOut (SImpl_FoldNamed x np args off) =
  distPerms1 x (ValPerm_Named (namedPermName np) args off)
simplImplOut (SImpl_UnfoldNamed x np args off) =
  distPerms1 x (unfoldPerm np args off)
simplImplOut (SImpl_NamedToConj x npn args off) =
  distPerms1 x (ValPerm_Conj1 $ Perm_NamedConj npn args off)
simplImplOut (SImpl_NamedFromConj x npn args off) =
  distPerms1 x (ValPerm_Named npn args off)
-- simplImplOut (SImpl_Mu x _ p2 _) = distPerms1 x (ValPerm_Mu p2)
simplImplOut (SImpl_NamedArgAlways x npn args off memb l) =
  distPerms1 x (ValPerm_Named npn (setNthPermExpr args memb l) off)
simplImplOut (SImpl_NamedArgCurrent x npn args off memb l2) =
  distPerms1 x (ValPerm_Named npn (setNthPermExpr args memb l2) off)
simplImplOut (SImpl_NamedArgWrite x npn args off memb rw) =
  distPerms1 x (ValPerm_Named npn (setNthPermExpr args memb rw) off)
simplImplOut (SImpl_NamedArgRead x npn args off memb) =
  distPerms1 x (ValPerm_Named npn
                (setNthPermExpr args memb (PExpr_RWModality Read))
                off)
simplImplOut (SImpl_ReachabilityTrans x rp args off _ e) =
  distPerms1 x (ValPerm_Named (recPermName rp) (PExprs_Cons args e) off)


-- | Apply a 'SimplImpl' implication to the permissions on the top of a
-- permission set stack, checking that they equal the 'simplImplIn' of the
-- 'SimplImpl' and then replacing them with its 'simplImplOut'
applySimplImpl :: HasCallStack => PPInfo -> Proxy ps ->
                  SimplImpl ps_in ps_out -> PermSet (ps :++: ps_in) ->
                  PermSet (ps :++: ps_out)
applySimplImpl pp_info prx simpl =
  modifyDistPerms $ \all_ps ->
  let (ps, ps_in) =
        splitDistPerms prx (distPermsToProxies $ simplImplIn simpl) all_ps in
  if ps_in == simplImplIn simpl then
    appendDistPerms ps (simplImplOut simpl)
  else
    error $ renderDoc $
    vsep [pretty "applySimplImpl: incorrect input permissions",
          pretty "expected: " <> permPretty pp_info (simplImplIn simpl),
          pretty "actual: " <> permPretty pp_info ps_in]

-- | A sequence of permission sets inside name-bindings
data MbPermSets bs_pss where
  MbPermSets_Nil :: MbPermSets RNil
  MbPermSets_Cons :: MbPermSets bs_pss -> CruCtx bs -> Mb bs (PermSet ps) ->
                     MbPermSets (bs_pss :> '(bs,ps))

-- | Helper for building a one-element 'MbPermSets' sequence
mbPermSets1 :: KnownRepr CruCtx bs =>
               Mb bs (PermSet ps) -> MbPermSets (RNil :> '(bs,ps))
mbPermSets1 = MbPermSets_Cons MbPermSets_Nil knownRepr

-- | Helper for building a two-element 'MbPermSets' sequence
mbPermSets2 :: (KnownRepr CruCtx bs1, KnownRepr CruCtx bs2) =>
               Mb bs1 (PermSet ps1) -> Mb bs2 (PermSet ps2) ->
               MbPermSets (RNil :> '(bs1,ps1) :> '(bs2,ps2))
mbPermSets2 ps1 ps2 =
  MbPermSets_Cons (MbPermSets_Cons MbPermSets_Nil knownRepr ps1) knownRepr ps2

-- | Apply a single permission implication step to a permission set
applyImpl1 :: HasCallStack => PPInfo -> PermImpl1 ps_in ps_outs ->
              PermSet ps_in -> MbPermSets ps_outs
applyImpl1 _ (Impl1_Fail _) _ = MbPermSets_Nil
applyImpl1 _ Impl1_Catch ps = mbPermSets2 (emptyMb ps) (emptyMb ps)
applyImpl1 pp_info (Impl1_Push x p) ps =
  if ps ^. varPerm x == p then
    mbPermSets1 $ emptyMb $ pushPerm x p $ set (varPerm x) ValPerm_True ps
  else
    error $ renderDoc (pretty "applyImpl1: Impl1_Push" <+>
                       permPretty pp_info x <+> colon <> softline <>
                       pretty "expected:" <+> permPretty pp_info p <> softline <>
                       pretty "found:" <+>
                       permPretty pp_info (ps ^. varPerm x))
applyImpl1 pp_info (Impl1_Pop x p) ps =
  if ps ^. topDistPerm x == p && ps ^. varPerm x == ValPerm_True then
    mbPermSets1 $ emptyMb $ fst $ popPerm x $ set (varPerm x) p ps
  else
    if ps ^. varPerm x == ValPerm_True then
      error $ renderDoc $
      vsep [pretty "applyImpl1: Impl1_Pop: unexpected permissions on top of the stack",
            pretty "expected: " <> permPretty pp_info p,
            pretty "actual: " <> permPretty pp_info (ps ^. topDistPerm x)]
    else
      error $ renderDoc $
      vsep [pretty "applyImpl1: Impl1_Pop: non-empty permissions for variable"
            <+> permPretty pp_info x <> pretty ":",
            permPretty pp_info (ps ^. varPerm x)]
applyImpl1 _ (Impl1_ElimOr x p1 p2) ps =
  if ps ^. topDistPerm x == ValPerm_Or p1 p2 then
    mbPermSets2 (emptyMb $ set (topDistPerm x) p1 ps)
    (emptyMb $ set (topDistPerm x) p2 ps)
  else
    error "applyImpl1: Impl1_ElimOr: unexpected permission"
applyImpl1 _ (Impl1_ElimExists x p_body) ps =
  if ps ^. topDistPerm x == ValPerm_Exists p_body then
    mbPermSets1 (fmap (\p -> set (topDistPerm x) p ps) p_body)
  else
    error "applyImpl1: Impl1_ElimExists: unexpected permission"
applyImpl1 pp_info (Impl1_Simpl simpl prx) ps =
  mbPermSets1 $ emptyMb $ applySimplImpl pp_info prx simpl ps
applyImpl1 _ (Impl1_LetBind tp e) ps =
  MbPermSets_Cons MbPermSets_Nil (CruCtxCons CruCtxNil tp) $
  nu $ \x -> pushPerm x (ValPerm_Eq e) ps
applyImpl1 _ (Impl1_ElimStructField x ps' tp memb) ps =
  if ps ^. topDistPerm x == ValPerm_Conj [Perm_Struct ps'] then
    (MbPermSets_Cons MbPermSets_Nil (singletonCruCtx tp) $ nu $ \y ->
      pushPerm y (RL.get memb ps') $
      set (topDistPerm x) (ValPerm_Conj1 $ Perm_Struct $
                           RL.set memb (ValPerm_Eq $ PExpr_Var y) ps')
      ps)
  else
    error "applyImpl1: Impl1_ElimStructField: unexpected permission"
applyImpl1 _ (Impl1_ElimLLVMFieldContents x fp) ps =
  if ps ^. topDistPerm x == ValPerm_Conj [Perm_LLVMField fp] then
    (mbPermSets1 $ nu $ \y ->
      pushPerm y (llvmFieldContents fp) $
      set (topDistPerm x) (ValPerm_Conj [Perm_LLVMField $
                                         fp { llvmFieldContents =
                                              ValPerm_Eq (PExpr_Var y) }])
      ps)
  else
    error "applyImpl1: Impl1_ElimLLVMFieldContents: unexpected permission"
applyImpl1 _ (Impl1_ElimLLVMBlockToEq x bp) ps =
  if ps ^. topDistPerm x == ValPerm_Conj1 (Perm_LLVMBlock bp) then
    (mbPermSets1 $ nu $ \y ->
      pushPerm y (ValPerm_Conj1 $ Perm_LLVMBlockShape $
                  modalizeBlockShape bp) $
      set (topDistPerm x) (ValPerm_Conj1 $ Perm_LLVMBlock $
                           bp { llvmBlockShape = PExpr_EqShape $ PExpr_Var y })
      ps)
  else
    error "applyImpl1: SImpl_ElimLLVMBlockToEq: unexpected permission"
applyImpl1 _ Impl1_BeginLifetime ps =
  mbPermSets1 $ nu $ \l -> pushPerm l (ValPerm_LOwned MNil MNil) ps
applyImpl1 _ (Impl1_TryProveBVProp x prop _) ps =
  mbPermSets1 $ emptyMb $
  pushPerm x (ValPerm_Conj [Perm_BVProp prop]) ps


instance SubstVar PermVarSubst m => Substable PermVarSubst (EqPerm a) m where
  genSubst s (mbMatch -> [nuMP| EqPerm x e b |]) =
    EqPerm <$> genSubst s x <*> genSubst s e <*> return (mbLift b)

instance SubstVar PermVarSubst m => Substable1 PermVarSubst EqPerm m where
  genSubst1 = genSubst

-- NOTE: PermVarSubst is always associated with the Identity monad because of
-- the functional dependency of SubstVar; this is necessary to substitute inside
-- the function used in EqProofStep
instance (NuMatching a, Substable PermVarSubst a Identity) =>
         Substable PermVarSubst (EqProofStep ps a) Identity where
  genSubst s (mbMatch -> [nuMP| EqProofStep eq_perms f |]) =
    Identity $ EqProofStep (runIdentity $ genSubst s eq_perms) $ \es ->
    runIdentity $ genSubst s $ fmap ($ es) f

instance (NuMatching a, Substable PermVarSubst a Identity) =>
         Substable PermVarSubst (EqProof ps a) Identity where
  genSubst s eqp = case mbMatch eqp of
    [nuMP| EqProofRefl a |] ->
      EqProofRefl <$> genSubst s a
    [nuMP| EqProofCons eqp' eq_step |] ->
      EqProofCons <$> genSubst s eqp' <*> genSubst s eq_step

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (SimplImpl ps_in ps_out) m where
  genSubst s mb_impl = case mbMatch mb_impl of
    [nuMP| SImpl_Drop x p |] ->
      SImpl_Drop <$> genSubst s x <*> genSubst s p
    [nuMP| SImpl_Copy x p |] ->
      SImpl_Copy <$> genSubst s x <*> genSubst s p
    [nuMP| SImpl_Swap x p1 y p2 |] ->
      SImpl_Swap <$> genSubst s x <*> genSubst s p1 <*> genSubst s y <*> genSubst s p2
    [nuMP| SImpl_MoveUp ps1 x p ps2 |] ->
      SImpl_MoveUp <$> genSubst s ps1 <*> genSubst s x <*>
                       genSubst s p <*> genSubst s ps2
    [nuMP| SImpl_MoveDown ps1 x p ps2 |] ->
      SImpl_MoveDown <$> genSubst s ps1 <*> genSubst s x <*>
                         genSubst s p <*> genSubst s ps2
    [nuMP| SImpl_IntroOrL x p1 p2 |] ->
      SImpl_IntroOrL <$> genSubst s x <*> genSubst s p1 <*> genSubst s p2
    [nuMP| SImpl_IntroOrR x p1 p2 |] ->
      SImpl_IntroOrR <$> genSubst s x <*> genSubst s p1 <*> genSubst s p2
    [nuMP| SImpl_IntroExists x e p |] ->
      SImpl_IntroExists <$> genSubst s x <*> genSubst s e <*> genSubst s p
    [nuMP| SImpl_Cast x y p |] ->
      SImpl_Cast <$> genSubst s x <*> genSubst s y <*> genSubst s p
    [nuMP| SImpl_CastPerm x eqp |] ->
      SImpl_CastPerm <$> genSubst s x <*> return (runIdentity $ genSubst s eqp)
    [nuMP| SImpl_IntroEqRefl x |] ->
      SImpl_IntroEqRefl <$> genSubst s x
    [nuMP| SImpl_InvertEq x y |] ->
      SImpl_InvertEq <$> genSubst s x <*> genSubst s y
    [nuMP| SImpl_InvTransEq x y e |] ->
      SImpl_InvTransEq <$> genSubst s x <*> genSubst s y <*> genSubst s e
    [nuMP| SImpl_CopyEq x e |] ->
      SImpl_CopyEq <$> genSubst s x <*> genSubst s e
    [nuMP| SImpl_LLVMWordEq x y e |] ->
      SImpl_LLVMWordEq <$> genSubst s x <*> genSubst s y <*> genSubst s e
    [nuMP| SImpl_IntroConj x |] ->
      SImpl_IntroConj <$> genSubst s x
    [nuMP| SImpl_ExtractConj x ps i |] ->
      SImpl_ExtractConj <$> genSubst s x <*> genSubst s ps <*> return (mbLift i)
    [nuMP| SImpl_CopyConj x ps i |] ->
      SImpl_CopyConj <$> genSubst s x <*> genSubst s ps <*> return (mbLift i)
    [nuMP| SImpl_InsertConj x p ps i |] ->
      SImpl_InsertConj <$> genSubst s x <*> genSubst s p <*>
                           genSubst s ps <*> return (mbLift i)
    [nuMP| SImpl_AppendConjs x ps1 ps2 |] ->
      SImpl_AppendConjs <$> genSubst s x <*> genSubst s ps1 <*> genSubst s ps2
    [nuMP| SImpl_SplitConjs x ps i |] ->
      SImpl_SplitConjs <$> genSubst s x <*> genSubst s ps <*> return (mbLift i)
    [nuMP| SImpl_IntroStructTrue x fs |] ->
      SImpl_IntroStructTrue <$> genSubst s x <*> return (mbLift fs)
    [nuMP| SImpl_StructEqToPerm x exprs |] ->
      SImpl_StructEqToPerm <$> genSubst s x <*> genSubst s exprs
    [nuMP| SImpl_StructPermToEq x exprs |] ->
      SImpl_StructPermToEq <$> genSubst s x <*> genSubst s exprs
    [nuMP| SImpl_IntroStructField x ps memb p |] ->
      SImpl_IntroStructField <$> genSubst s x <*> genSubst s ps
                             <*> genSubst s memb <*> genSubst s p
    [nuMP| SImpl_ConstFunPerm x h fun_perm ident |] ->
      SImpl_ConstFunPerm <$> genSubst s x <*> return (mbLift h) <*>
                             genSubst s fun_perm <*> return (mbLift ident)
    [nuMP| SImpl_CastLLVMWord x e1 e2 |] ->
      SImpl_CastLLVMWord <$> genSubst s x <*> genSubst s e1 <*> genSubst s e2
    [nuMP| SImpl_InvertLLVMOffsetEq x off y |] ->
      SImpl_InvertLLVMOffsetEq <$> genSubst s x <*> genSubst s off <*> genSubst s y
    [nuMP| SImpl_OffsetLLVMWord y e off x |] ->
      SImpl_OffsetLLVMWord <$> genSubst s y <*> genSubst s e <*>
                               genSubst s off <*> genSubst s x
    [nuMP| SImpl_CastLLVMPtr y p off x |] ->
      SImpl_CastLLVMPtr <$> genSubst s y <*> genSubst s p <*>
                            genSubst s off <*> genSubst s x
    [nuMP| SImpl_CastLLVMFree x e1 e2 |] ->
      SImpl_CastLLVMFree <$> genSubst s x <*> genSubst s e1 <*> genSubst s e2
    [nuMP| SImpl_CastLLVMFieldOffset x fld off' |] ->
      SImpl_CastLLVMFieldOffset <$> genSubst s x <*> genSubst s fld <*>
                                    genSubst s off'
    [nuMP| SImpl_IntroLLVMFieldContents x y fld |] ->
      SImpl_IntroLLVMFieldContents <$> genSubst s x <*> genSubst s y <*>
                                       genSubst s fld
    [nuMP| SImpl_DemoteLLVMFieldRW x fld |] ->
      SImpl_DemoteLLVMFieldRW <$> genSubst s x <*> genSubst s fld
    [nuMP| SImpl_LLVMArrayCopy x ap rng |] ->
      SImpl_LLVMArrayCopy <$> genSubst s x <*> genSubst s ap <*> genSubst s rng
    [nuMP| SImpl_LLVMArrayBorrow x ap rng |] ->
      SImpl_LLVMArrayBorrow <$> genSubst s x <*> genSubst s ap <*> genSubst s rng
    [nuMP| SImpl_LLVMArrayReturn x ap rng |] ->
      SImpl_LLVMArrayReturn <$> genSubst s x <*> genSubst s ap <*> genSubst s rng
    [nuMP| SImpl_LLVMArrayAppend x ap1 ap2 |] ->
      SImpl_LLVMArrayAppend <$> genSubst s x <*> genSubst s ap1 <*> genSubst s ap2
    [nuMP| SImpl_LLVMArrayRearrange x ap1 ap2 |] ->
      SImpl_LLVMArrayRearrange <$> genSubst s x <*> genSubst s ap1 <*> genSubst s ap2
    [nuMP| SImpl_LLVMArrayToField x ap sz |] ->
      SImpl_LLVMArrayToField <$> genSubst s x <*> genSubst s ap
                             <*> return (mbLift sz)
    [nuMP| SImpl_LLVMArrayEmpty x ap |] ->
      SImpl_LLVMArrayEmpty <$> genSubst s x <*> genSubst s ap
    [nuMP| SImpl_LLVMArrayOneCell x ap |] ->
      SImpl_LLVMArrayOneCell <$> genSubst s x <*> genSubst s ap
    [nuMP| SImpl_LLVMArrayIndexCopy x ap ix |] ->
      SImpl_LLVMArrayIndexCopy <$> genSubst s x <*> genSubst s ap <*> genSubst s ix
    [nuMP| SImpl_LLVMArrayIndexBorrow x ap ix |] ->
      SImpl_LLVMArrayIndexBorrow <$> genSubst s x <*> genSubst s ap <*>
                                     genSubst s ix
    [nuMP| SImpl_LLVMArrayIndexReturn x ap ix |] ->
      SImpl_LLVMArrayIndexReturn <$> genSubst s x <*> genSubst s ap <*>
                                     genSubst s ix
    [nuMP| SImpl_LLVMArrayContents x ap i fp impl |] ->
      SImpl_LLVMArrayContents <$> genSubst s x <*> genSubst s ap <*>
                                  return (mbLift i) <*> genSubst s fp <*>
                                  genSubst s impl
    [nuMP| SImpl_LLVMFieldIsPtr x fp |] ->
      SImpl_LLVMFieldIsPtr <$> genSubst s x <*> genSubst s fp
    [nuMP| SImpl_LLVMArrayIsPtr x ap |] ->
      SImpl_LLVMArrayIsPtr <$> genSubst s x <*> genSubst s ap
    [nuMP| SImpl_LLVMBlockIsPtr x bp |] ->
      SImpl_LLVMBlockIsPtr <$> genSubst s x <*> genSubst s bp
    [nuMP| SImpl_SplitLifetime x f args l l2 ps_in ps_out |] ->
      SImpl_SplitLifetime <$> genSubst s x <*> genSubst s f <*> genSubst s args
                          <*> genSubst s l <*> genSubst s l2
                          <*> genSubst s ps_in <*> genSubst s ps_out
    [nuMP| SImpl_SubsumeLifetime l1 ps_in1 ps_out1 l2 ps_in2 ps_out2 |] ->
      SImpl_SubsumeLifetime <$> genSubst s l1 <*> genSubst s ps_in1
                            <*> genSubst s ps_out1 <*> genSubst s l2
                            <*> genSubst s ps_in2 <*> genSubst s ps_out2
    [nuMP| SImpl_WeakenLifetime x f args l l2 |] ->
      SImpl_WeakenLifetime <$> genSubst s x <*> genSubst s f <*> genSubst s args
                           <*> genSubst s l <*> genSubst s l2
    [nuMP| SImpl_MapLifetime l ps_in ps_out ps_in' ps_out'
                            ps1 ps2 impl1 impl2 |] ->
      SImpl_MapLifetime <$> genSubst s l <*> genSubst s ps_in
                        <*> genSubst s ps_out <*> genSubst s ps_in'
                        <*> genSubst s ps_out' <*> genSubst s ps1
                        <*> genSubst s ps2 <*> genSubst s impl1
                        <*> genSubst s impl2
    [nuMP| SImpl_EndLifetime l ps_in ps_out |] ->
      SImpl_EndLifetime <$> genSubst s l <*> genSubst s ps_in
                        <*> genSubst s ps_out
    [nuMP| SImpl_LCurrentRefl l |] ->
      SImpl_LCurrentRefl <$> genSubst s l
    [nuMP| SImpl_LCurrentTrans l1 l2 l3 |] ->
      SImpl_LCurrentTrans <$> genSubst s l1 <*> genSubst s l2 <*> genSubst s l3
    [nuMP| SImpl_DemoteLLVMBlockRW x bp |] ->
      SImpl_DemoteLLVMBlockRW <$> genSubst s x <*> genSubst s bp
    [nuMP| SImpl_IntroLLVMBlockEmpty x bp |] ->
      SImpl_IntroLLVMBlockEmpty <$> genSubst s x <*> genSubst s bp
    [nuMP| SImpl_CoerceLLVMBlockEmpty x bp |] ->
      SImpl_CoerceLLVMBlockEmpty <$> genSubst s x <*> genSubst s bp
    [nuMP| SImpl_ElimLLVMBlockToBytes x bp |] ->
      SImpl_ElimLLVMBlockToBytes <$> genSubst s x <*> genSubst s bp
    [nuMP| SImpl_IntroLLVMBlockSeqEmpty x bp |] ->
      SImpl_IntroLLVMBlockSeqEmpty <$> genSubst s x <*> genSubst s bp
    [nuMP| SImpl_ElimLLVMBlockSeqEmpty x bp |] ->
      SImpl_ElimLLVMBlockSeqEmpty <$> genSubst s x <*> genSubst s bp
    [nuMP| SImpl_IntroLLVMBlockNamed x bp nmsh |] ->
      SImpl_IntroLLVMBlockNamed <$> genSubst s x <*> genSubst s bp
                                <*> genSubst s nmsh
    [nuMP| SImpl_ElimLLVMBlockNamed x bp nmsh |] ->
      SImpl_ElimLLVMBlockNamed <$> genSubst s x <*> genSubst s bp
                               <*> genSubst s nmsh
    [nuMP| SImpl_IntroLLVMBlockFromEq x bp y |] ->
      SImpl_IntroLLVMBlockFromEq <$> genSubst s x <*> genSubst s bp
                                 <*> genSubst s y
    [nuMP| SImpl_IntroLLVMBlockPtr x maybe_rw maybe_l bp |] ->
      SImpl_IntroLLVMBlockPtr <$> genSubst s x <*> genSubst s maybe_rw
                              <*> genSubst s maybe_l <*> genSubst s bp
    [nuMP| SImpl_ElimLLVMBlockPtr x maybe_rw maybe_l bp |] ->
      SImpl_ElimLLVMBlockPtr <$> genSubst s x <*> genSubst s maybe_rw
                             <*> genSubst s maybe_l <*> genSubst s bp
    [nuMP| SImpl_IntroLLVMBlockField x fp |] ->
      SImpl_IntroLLVMBlockField <$> genSubst s x <*> genSubst s fp
    [nuMP| SImpl_ElimLLVMBlockField x fp len |] ->
      SImpl_ElimLLVMBlockField <$> genSubst s x <*> genSubst s fp
                               <*> genSubst s len
    [nuMP| SImpl_IntroLLVMBlockArray x fp |] ->
      SImpl_IntroLLVMBlockArray <$> genSubst s x <*> genSubst s fp
    [nuMP| SImpl_ElimLLVMBlockArray x fp |] ->
      SImpl_ElimLLVMBlockArray <$> genSubst s x <*> genSubst s fp
    [nuMP| SImpl_IntroLLVMBlockSeq x bp1 len2 sh2 |] ->
      SImpl_IntroLLVMBlockSeq <$> genSubst s x <*> genSubst s bp1
                              <*> genSubst s len2 <*> genSubst s sh2
    [nuMP| SImpl_ElimLLVMBlockSeq x bp1 sh2 |] ->
      SImpl_ElimLLVMBlockSeq <$> genSubst s x <*> genSubst s bp1
                             <*> genSubst s sh2
    [nuMP| SImpl_IntroLLVMBlockOr x bp1 sh2 |] ->
      SImpl_IntroLLVMBlockOr <$> genSubst s x <*> genSubst s bp1
                             <*> genSubst s sh2
    [nuMP| SImpl_ElimLLVMBlockOr x bp1 sh2 |] ->
      SImpl_ElimLLVMBlockOr <$> genSubst s x <*> genSubst s bp1 <*> genSubst s sh2
    [nuMP| SImpl_IntroLLVMBlockEx x bp |] ->
      SImpl_IntroLLVMBlockEx <$> genSubst s x <*> genSubst s bp
    [nuMP| SImpl_ElimLLVMBlockEx x bp |] ->
      SImpl_ElimLLVMBlockEx <$> genSubst s x <*> genSubst s bp
    [nuMP| SImpl_FoldNamed x np args off |] ->
      SImpl_FoldNamed <$> genSubst s x <*> genSubst s np <*> genSubst s args
                      <*> genSubst s off
    [nuMP| SImpl_UnfoldNamed x np args off |] ->
      SImpl_UnfoldNamed <$> genSubst s x <*> genSubst s np <*> genSubst s args
                        <*> genSubst s off
    [nuMP| SImpl_NamedToConj x npn args off |] ->
      SImpl_NamedToConj <$> genSubst s x <*> genSubst s npn <*> genSubst s args
                        <*> genSubst s off
    [nuMP| SImpl_NamedFromConj x npn args off |] ->
      SImpl_NamedFromConj <$> genSubst s x <*> genSubst s npn <*> genSubst s args
                          <*> genSubst s off
    [nuMP| SImpl_NamedArgAlways x npn args off memb l |] ->
      SImpl_NamedArgAlways <$> genSubst s x <*> genSubst s npn <*>
                               genSubst s args <*> genSubst s off <*>
                               genSubst s memb <*> genSubst s l
    [nuMP| SImpl_NamedArgCurrent x npn args off memb l2 |] ->
      SImpl_NamedArgCurrent <$> genSubst s x <*> genSubst s npn <*>
                                genSubst s args <*> genSubst s off <*>
                                genSubst s memb <*> genSubst s l2
    [nuMP| SImpl_NamedArgWrite x npn args off memb rw |] ->
      SImpl_NamedArgWrite <$> genSubst s x <*> genSubst s npn <*>
                              genSubst s args <*> genSubst s off <*>
                              genSubst s memb <*> genSubst s rw
    [nuMP| SImpl_NamedArgRead x npn args off memb |] ->
      SImpl_NamedArgRead <$> genSubst s x <*> genSubst s npn <*>
                             genSubst s args <*> genSubst s off <*>
                             genSubst s memb
    [nuMP| SImpl_ReachabilityTrans x rp args off y e |] ->
      SImpl_ReachabilityTrans <$> genSubst s x <*> genSubst s rp <*>
                                  genSubst s args <*> genSubst s off <*>
                                  genSubst s y <*> genSubst s e

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (PermImpl1 ps_in ps_out) m where
  genSubst s mb_impl = case mbMatch mb_impl of
    [nuMP| Impl1_Fail str |] -> return (Impl1_Fail $ mbLift str)
    [nuMP| Impl1_Catch |] -> return Impl1_Catch
    [nuMP| Impl1_Push x p |] ->
      Impl1_Push <$> genSubst s x <*> genSubst s p
    [nuMP| Impl1_Pop x p |] ->
      Impl1_Pop <$> genSubst s x <*> genSubst s p
    [nuMP| Impl1_ElimOr x p1 p2 |] ->
      Impl1_ElimOr <$> genSubst s x <*> genSubst s p1 <*> genSubst s p2
    [nuMP| Impl1_ElimExists x p_body |] ->
      Impl1_ElimExists <$> genSubst s x <*> genSubst s p_body
    [nuMP| Impl1_Simpl simpl prx |] ->
      Impl1_Simpl <$> genSubst s simpl <*> return (mbLift prx)
    [nuMP| Impl1_LetBind tp e |] ->
      Impl1_LetBind (mbLift tp) <$> genSubst s e
    [nuMP| Impl1_ElimStructField x ps tp memb |] ->
      Impl1_ElimStructField <$> genSubst s x <*> genSubst s ps
                            <*> return (mbLift tp) <*> genSubst s memb
    [nuMP| Impl1_ElimLLVMFieldContents x fp |] ->
      Impl1_ElimLLVMFieldContents <$> genSubst s x <*> genSubst s fp
    [nuMP| Impl1_ElimLLVMBlockToEq x bp |] ->
      Impl1_ElimLLVMBlockToEq <$> genSubst s x <*> genSubst s bp
    [nuMP| Impl1_BeginLifetime |] -> return Impl1_BeginLifetime
    [nuMP| Impl1_TryProveBVProp x prop prop_str |] ->
      Impl1_TryProveBVProp <$> genSubst s x <*> genSubst s prop <*>
                               return (mbLift prop_str)

-- FIXME: shouldn't need the SubstVar PermVarSubst m assumption...
instance (NuMatchingAny1 r, SubstVar PermVarSubst m,
          Substable1 PermVarSubst r m) =>
         Substable PermVarSubst (PermImpl r ps) m where
  genSubst s mb_impl = case mbMatch mb_impl of
    [nuMP| PermImpl_Done r |] -> PermImpl_Done <$> genSubst1 s r
    [nuMP| PermImpl_Step impl1 mb_impls |] ->
      PermImpl_Step <$> genSubst s impl1 <*> genSubst s mb_impls

-- FIXME: shouldn't need the SubstVar PermVarSubst m assumption...
instance (NuMatchingAny1 r, SubstVar PermVarSubst m,
          Substable1 PermVarSubst r m) =>
         Substable PermVarSubst (MbPermImpls r bs_pss) m where
  genSubst s mb_impls = case mbMatch mb_impls of
    [nuMP| MbPermImpls_Nil |] -> return MbPermImpls_Nil
    [nuMP| MbPermImpls_Cons mpx mb_impl mb_impls' |] ->
      let px = mbLift mpx in
      MbPermImpls_Cons px <$> genSubst s mb_impl <*> genSubstMb (cruCtxProxies px) s mb_impls'

-- FIXME: shouldn't need the SubstVar PermVarSubst m assumption...
instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (LocalPermImpl ps_in ps_out) m where
  genSubst s (mbMatch -> [nuMP| LocalPermImpl impl |]) =
    LocalPermImpl <$> genSubst s impl

instance SubstVar s m => Substable s (LocalImplRet ps ps') m where
  genSubst _ (mbMatch -> [nuMP| LocalImplRet Refl |]) = return $ LocalImplRet Refl

instance SubstVar s m => Substable1 s (LocalImplRet ps) m where
  genSubst1 _ (mbMatch -> [nuMP| LocalImplRet Refl |]) = return $ LocalImplRet Refl


----------------------------------------------------------------------
-- * Permission Implication Monad
----------------------------------------------------------------------

-- FIXME: instead of having a separate PPInfo and name type map, we should maybe
-- combine all the local context into one type...?

data RecurseFlag = RecLeft | RecRight | RecNone
  deriving (Eq, Show, Read)

data ImplState vars ps =
  ImplState { _implStatePerms :: PermSet ps,
              _implStateVars :: CruCtx vars,
              _implStatePSubst :: PartialSubst vars,
              _implStatePVarSubst :: RAssign (Compose Maybe ExprVar) vars,
              -- FIXME HERE: remove implStateLifetimes
              _implStateLifetimes :: [ExprVar LifetimeType],
              -- ^ Stack of active lifetimes, where the first element is the
              -- current lifetime (we should have an @lowned@ permission for it)
              -- and each lifetime contains (i.e., has an @lcurrent@ permission
              -- for) the next lifetime in the stack
              _implStateRecRecurseFlag :: RecurseFlag,
              -- ^ Whether we are recursing under a recursive permission, either
              -- on the left hand or the right hand side
              _implStatePermEnv :: PermEnv,
              -- ^ The current permission environment
              _implStatePPInfo :: PPInfo,
              -- ^ Pretty-printing for all variables in scope
              _implStateNameTypes :: NameMap TypeRepr,
              -- ^ Types of all the variables in scope
              _implStateFailPrefix :: String,
              -- ^ A prefix string to prepend to any failure messages
              _implStateDoTrace :: Bool
              -- ^ Whether tracing is turned on or not
            }
makeLenses ''ImplState

mkImplState :: CruCtx vars -> PermSet ps -> PermEnv ->
               PPInfo -> String -> Bool -> NameMap TypeRepr ->
               ImplState vars ps
mkImplState vars perms env info fail_prefix do_trace nameTypes =
  ImplState {
  _implStateVars = vars,
  _implStatePerms = perms,
  _implStatePSubst = emptyPSubst vars,
  _implStatePVarSubst = RL.map (const $ Compose Nothing) (cruCtxProxies vars),
  _implStateLifetimes = [],
  _implStateRecRecurseFlag = RecNone,
  _implStatePermEnv = env,
  _implStatePPInfo = info,
  _implStateNameTypes = nameTypes,
  _implStateFailPrefix = fail_prefix,
  _implStateDoTrace = do_trace
  }

extImplState :: KnownRepr TypeRepr tp => ImplState vars ps ->
                ImplState (vars :> tp) ps
extImplState s =
  s { _implStateVars = extCruCtx (_implStateVars s),
      _implStatePSubst = extPSubst (_implStatePSubst s),
      _implStatePVarSubst = (_implStatePVarSubst s) :>: Compose Nothing }

unextImplState :: ImplState (vars :> a) ps -> ImplState vars ps
unextImplState s =
  s { _implStateVars = unextCruCtx (_implStateVars s),
      _implStatePSubst = unextPSubst (_implStatePSubst s),
      _implStatePVarSubst = RL.tail (_implStatePVarSubst s) }

-- | The implication monad is a state-continuation monad that uses 'ImplState'
type ImplM vars s r ps_out ps_in =
  GenStateContT
    (ImplState vars ps_out) (PermImpl r ps_out)
    (ImplState vars ps_in ) (PermImpl r ps_in )
    (State (Closed s))

-- | Run an 'ImplM' computation by passing it a @vars@ context, a starting
-- permission set, top-level state, and a continuation to consume the output
runImplM ::
  CruCtx vars ->
  PermSet ps_in ->
  PermEnv                   {- ^ permission environment   -} ->
  PPInfo                    {- ^ pretty-printer settings  -} ->
  String                    {- ^ fail prefix              -} ->
  Bool                      {- ^ do trace                 -} ->
  NameMap TypeRepr          {- ^ name types               -} ->
  ImplM vars s r ps_out ps_in a ->
  ((a, ImplState vars ps_out) -> State (Closed s) (r ps_out)) ->
  State (Closed s) (PermImpl r ps_in)
runImplM vars perms env ppInfo fail_prefix do_trace nameTypes m k =
  runGenStateContT
    m
    (mkImplState vars perms env ppInfo fail_prefix do_trace nameTypes)
    (\s a -> PermImpl_Done <$> k (a, s))

-- | Run an 'ImplM' computation that returns a 'PermImpl', by inserting that
-- 'PermImpl' inside of the larger 'PermImpl' that is built up by the 'ImplM'
-- computation.
runImplImplM :: CruCtx vars -> PermSet ps_in -> PermEnv -> PPInfo ->
                String -> Bool -> NameMap TypeRepr ->
                ImplM vars s r ps_out ps_in (PermImpl r ps_out) ->
                State (Closed s) (PermImpl r ps_in)
runImplImplM vars perms env ppInfo fail_prefix do_trace nameTypes m =
  runGenStateContT
    m
    (mkImplState vars perms env ppInfo fail_prefix do_trace nameTypes)
    (\_ -> pure)

-- | Embed a sub-computation in a name-binding inside another 'ImplM'
-- computation, throwing away any state from that sub-computation and returning
-- a 'PermImpl' inside a name-binding
embedImplM :: DistPerms ps_in ->
              ImplM RNil s r' ps_out ps_in (r' ps_out) ->
              ImplM vars s r ps ps (PermImpl r' ps_in)
embedImplM ps_in m =
  get >>= \s ->
  lift $
  runImplM CruCtxNil (distPermSet ps_in)
  (view implStatePermEnv s) (view implStatePPInfo s)
  (view implStateFailPrefix s) (view implStateDoTrace s)
  (view implStateNameTypes s) m (pure . fst)

-- | Embed a sub-computation in a name-binding inside another 'ImplM'
-- computation, throwing away any state from that sub-computation and returning
-- a 'PermImpl' inside a name-binding
embedMbImplM :: Mb ctx (PermSet ps_in) ->
                Mb ctx (ImplM RNil s r' ps_out ps_in (r' ps_out)) ->
                ImplM vars s r ps ps (Mb ctx (PermImpl r' ps_in))
embedMbImplM mb_ps_in mb_m =
  do s <- get
     lift $ strongMbM $ mbMap2
       (\ps_in m ->
        runImplM
         CruCtxNil ps_in
         (view implStatePermEnv    s) (view implStatePPInfo  s)
         (view implStateFailPrefix s) (view implStateDoTrace s)
         (view implStateNameTypes  s) m (pure . fst))
       mb_ps_in mb_m

-- | Run an 'ImplM' computation in a locally-scoped way, where all effects
-- are restricted to the local computation. This is essentially a form of the
-- @reset@ operation of delimited continuations.
--
-- FIXME: figure out a more general @reset@ combinator...
localImplM ::
  ImplM vars s r ps_out ps_in (PermImpl r ps_out) ->
  ImplM vars s r ps_in ps_in (PermImpl r ps_in)
localImplM m =
  do st <- get
     lift (runGenStateContT m st (\_ -> pure))

-- | Look up the type of an existential variable
getExVarType :: Member vars tp -> ImplM vars s r ps ps (TypeRepr tp)
getExVarType memb =
  do varTypes <- use implStateVars
     pure (cruCtxLookup varTypes memb)

-- | Look up the current partial substitution
getPSubst :: ImplM vars s r ps ps (PartialSubst vars)
getPSubst = use implStatePSubst

-- | Add a multi-binding for the current existential variables around a value
-- (that does not use those variables)
mbVarsM :: a -> ImplM vars s r ps ps (Mb vars a)
mbVarsM a =
  do px <- uses implStateVars cruCtxProxies
     pure (mbPure px a)

-- | Apply the current partial substitution to an expression, failing if the
-- partial substitution is not complete enough. The supplied 'String' is the
-- calling function, used for error reporting in the failure.
partialSubstForceM :: (NuMatchingAny1 r, PermPretty a,
                       Substable PartialSubst a Maybe) =>
                      Mb vars a -> String -> ImplM vars s r ps ps a
partialSubstForceM mb_e caller =
  do psubst <- getPSubst
     case partialSubst psubst mb_e of
       Just e -> pure e
       Nothing ->
         implTraceM (\i -> sep [pretty ("Incomplete susbtitution in " ++ caller
                                        ++ " for:"),
                                permPretty i mb_e]) >>= implFailM

-- | Modify the current partial substitution
modifyPSubst :: (PartialSubst vars -> PartialSubst vars) ->
                ImplM vars s r ps ps ()
modifyPSubst f = implStatePSubst %= f

-- | Set the value for an existential variable in the current substitution,
-- raising an error if it is already set
setVarM :: Member vars a -> PermExpr a -> ImplM vars s r ps ps ()
setVarM memb e =
  do vars <- uses implStateVars cruCtxProxies
     _ <- implTraceM (\i -> pretty "Setting" <+>
                       permPretty i (nuMulti vars $ \ns -> RL.get memb ns) <+>
                       pretty "=" <+> permPretty i e)
     modifyPSubst (psubstSet memb e)

-- | Get a free variable that is provably equal to the value of an existential
-- variable, let-binding a fresh variable if the evar is instantiated with a
-- non-variable expression. It is an error if the evar has no instantiation in
-- the current partial substitution.
getVarVarM :: NuMatchingAny1 r => Member vars a ->
              ImplM vars s r ps ps (ExprVar a)
getVarVarM memb =
  getPSubst >>>= \psubst ->
  use implStatePVarSubst >>>= \pvsubst ->
  case (RL.get memb pvsubst, psubstLookup psubst memb) of
    (Compose (Just n), _) -> pure n
    (_, Just e) ->
      getExVarType memb >>>= \tp ->
      implLetBindVar tp e >>>= \n ->
      implStatePVarSubst %= RL.set memb (Compose (Just n)) >>>
      pure n
    _ -> error "getVarVarM"

-- | Run an implication computation with one more existential variable,
-- returning the optional expression it was bound to in the current partial
-- substitution when it is done
withExtVarsM :: KnownRepr TypeRepr tp =>
                ImplM (vars :> tp) s r ps1 ps2 a ->
                ImplM vars s r ps1 ps2 (a, PermExpr tp)
withExtVarsM m =
  gmodify extImplState   >>>
  m                      >>>= \a ->
  getPSubst              >>>= \psubst ->
  gmodify unextImplState >>>
  pure (a, case psubstLookup psubst Member_Base of
             Just e -> e
             Nothing -> zeroOfType knownRepr)

-- | Perform either the first, second, or both computations with an 'implCatchM'
-- between, depending on the recursion flag
implRecFlagCaseM :: NuMatchingAny1 r => ImplM vars s r ps_out ps_in a ->
                    ImplM vars s r ps_out ps_in a ->
                    ImplM vars s r ps_out ps_in a
implRecFlagCaseM m1 m2 =
  use implStateRecRecurseFlag >>>= \case
    RecLeft  -> m1
    RecRight -> m2
    RecNone  -> implCatchM m1 m2

-- | Set the recursive permission recursion flag to indicate recursion on the
-- right, or fail if we are already recursing on the left
implSetRecRecurseRightM :: NuMatchingAny1 r => ImplM vars s r ps ps ()
implSetRecRecurseRightM =
  use implStateRecRecurseFlag >>= \case
    RecLeft -> implFailMsgM "Tried to unfold a mu on the right after unfolding on the left"
    _ -> implStateRecRecurseFlag .= RecRight

-- | Set the recursive recursion flag to indicate recursion on the left, or fail
-- if we are already recursing on the right
implSetRecRecurseLeftM :: NuMatchingAny1 r => ImplM vars s r ps ps ()
implSetRecRecurseLeftM =
  use implStateRecRecurseFlag >>= \case
    RecRight ->
      implFailMsgM "Tried to unfold a mu on the left after unfolding on the right"
    _ -> implStateRecRecurseFlag .= RecLeft

-- | Look up the 'NamedPerm' structure for a named permssion
implLookupNamedPerm :: NamedPermName ns args a ->
                       ImplM vars s r ps ps (NamedPerm ns args a)
implLookupNamedPerm npn =
  (view implStatePermEnv <$> get) >>>= \env ->
  case lookupNamedPerm env npn of
    Just np -> pure np
    Nothing -> error ("Named permission " ++ namedPermNameName npn
                      ++ " not defined!")

-- | Get the current 'PermSet'
getPerms :: ImplM vars s r ps ps (PermSet ps)
getPerms = use implStatePerms

-- | Look up the current permission for a given variable
getPerm :: ExprVar a -> ImplM vars s r ps ps (ValuePerm a)
getPerm x = use (implStatePerms . varPerm x)

-- | Get the pointer permissions for a variable @x@, assuming @x@ has LLVM
-- pointer permissions
getLLVMPtrPerms :: ExprVar (LLVMPointerType w) ->
                   ImplM vars s r ps ps [LLVMPtrPerm w]
getLLVMPtrPerms x = use (implStatePerms . varPerm x . llvmPtrPerms)

-- | Get the distinguished permission stack
getDistPerms :: ImplM vars s r ps ps (DistPerms ps)
getDistPerms = use (implStatePerms . distPerms)

-- | Get the top permission in the stack
getTopDistPerm :: ExprVar a -> ImplM vars s r (ps :> a) (ps :> a) (ValuePerm a)
getTopDistPerm x = use (implStatePerms . topDistPerm x)

-- | Set the current 'PermSet'
setPerms :: PermSet ps -> ImplM vars s r ps ps ()
setPerms perms = implStatePerms .= perms

-- | Set the current permission for a given variable
setPerm :: ExprVar a -> ValuePerm a -> ImplM vars s r ps ps ()
setPerm x p = implStatePerms . varPerm x .= p

-- | Get the current lifetime
getCurLifetime :: ImplM vars s r ps ps (ExprVar LifetimeType)
getCurLifetime =
  do ls <- use implStateLifetimes
     case ls of
       l:_ -> pure l
       [] -> error "getCurLifetime: no current lifetime!"

-- | Push a lifetime onto the lifetimes stack
pushLifetime :: ExprVar LifetimeType -> ImplM vars s r ps ps ()
pushLifetime l = implStateLifetimes %= (l:)

-- | Pop a lifetime off of the lifetimes stack
popLifetime :: ImplM vars s r ps ps (ExprVar LifetimeType)
popLifetime =
  do l <- getCurLifetime
     implStateLifetimes %= tail
     pure l

-- | Push (as in 'implPushM') the permission for the current lifetime
implPushCurLifetimePermM :: NuMatchingAny1 r => ExprVar LifetimeType ->
                            ImplM vars s r (ps :> LifetimeType) ps ()
implPushCurLifetimePermM l =
  getCurLifetime >>>= \l' ->
  (if l == l' then pure () else
     error "implPushLifetimePermM: wrong value for the current lifetime!") >>>
  getPerm l >>>= \p ->
  case p of
    ValPerm_Conj [Perm_LOwned _ _] -> implPushM l p
    _ -> error "implPushLifetimePermM: no LOwned permission for the current lifetime!"

-- | Pop (as in 'implPopM') the permission for the current lifetime
implPopCurLifetimePermM :: NuMatchingAny1 r => ExprVar LifetimeType ->
                           ImplM vars s r ps (ps :> LifetimeType) ()
implPopCurLifetimePermM l =
  getCurLifetime >>>= \l' ->
  (if l == l' then pure () else
     error "implPopLifetimePermM: wrong value for the current lifetime!") >>>
  getTopDistPerm l >>>= \p ->
  case p of
    ValPerm_Conj [Perm_LOwned _ _] -> implPopM l p
    _ -> error "implPopLifetimePermM: no LOwned permission for the current lifetime!"

{- FIXME: this should no longer be needed!
-- | Map the final return value and the current permissions
gmapRetAndPerms :: (PermSet ps2 -> PermSet ps1) ->
                   (PermImpl r ps1 -> PermImpl r ps2) ->
                   ImplM vars s r ps1 ps2 ()
gmapRetAndPerms f_perms f_impl =
  gmapRetAndState (over implStatePerms f_perms) f_impl
-}


-- | Look up the type of a free variable
implGetVarType :: Name a -> ImplM vars s r ps ps (TypeRepr a)
implGetVarType n =
  do varTypes <- use implStateNameTypes
     case NameMap.lookup n varTypes of
       Just tp -> pure tp
       Nothing ->
         implTraceM (\i -> pretty "Could not find type for variable:" <+>
                           permPretty i n) >>>
         error "implGetVarType"

-- | Look up the types of a list of free variables
implGetVarTypes :: RAssign Name a -> ImplM vars s r ps ps (CruCtx a)
implGetVarTypes MNil = pure CruCtxNil
implGetVarTypes (xs :>: x) =
  CruCtxCons <$> implGetVarTypes xs <*> implGetVarType x

-- | Find the first variable of a specific type
implFindVarOfType :: TypeRepr a -> ImplM vars s r ps ps (Maybe (Name a))
implFindVarOfType tp =
  do varTypes <- use implStateNameTypes
     pure (foldr (\(NameAndElem n tp') rest ->
                     case testEquality tp tp' of
                       Just Refl -> return n
                       Nothing -> rest) Nothing
             (NameMap.assocs varTypes))

-- | Remember the types associated with a list of 'Name's, and also ensure those
-- names have permissions
implSetNameTypes :: RAssign Name ctx -> CruCtx ctx -> ImplM vars s r ps ps ()
implSetNameTypes MNil _ = pure ()
implSetNameTypes (ns :>: n) (CruCtxCons tps tp) =
  do implStateNameTypes %= NameMap.insert n tp
     implStatePerms     %= initVarPerm n
     implSetNameTypes ns tps


----------------------------------------------------------------------
-- * The Permission Implication Rules as Monadic Operations
----------------------------------------------------------------------

type family Fst (p :: (k1,k2)) :: k1 where Fst '(x,_) = x
type family Snd (p :: (k1,k2)) :: k2 where Snd '(_,y) = y

-- | An 'ImplM' continuation for a permission implication rule
newtype Impl1Cont vars s r ps_r a bs_ps =
  Impl1Cont (RAssign Name (Fst bs_ps) -> ImplM vars s r ps_r (Snd bs_ps) a)

-- | Apply a permission implication rule, with the given continuations in the
-- possible disjunctive branches of the result
implApplyImpl1 :: HasCallStack => NuMatchingAny1 r => PermImpl1 ps_in ps_outs ->
                  RAssign (Impl1Cont vars s r ps_r a) ps_outs ->
                  ImplM vars s r ps_r ps_in a
implApplyImpl1 impl1 mb_ms =
  use implStatePerms >>>= \perms ->
  use implStatePPInfo >>>= \pp_info ->
  gmapRet (PermImpl_Step impl1 <$>) >>>
  helper (applyImpl1 pp_info impl1 perms) mb_ms
  where
    helper :: MbPermSets ps_outs ->
              RAssign (Impl1Cont vars s r ps_r a) ps_outs ->
              GenStateContT
                (ImplState vars ps_r)  (PermImpl r ps_r)
                (ImplState vars ps_in) (MbPermImpls r ps_outs)
                (State (Closed s)) a
    helper MbPermSets_Nil _ = gabortM (return MbPermImpls_Nil)
    helper (MbPermSets_Cons mbperms ctx mbperm) (args :>: Impl1Cont f) =
      gparallel (\m1 m2 -> MbPermImpls_Cons ctx <$> m1 <*> m2)
      (helper mbperms args)
      (gopenBinding strongMbM mbperm >>>= \(ns, perms') ->
        gmodify (set implStatePerms perms' .
                 over implStatePPInfo (ppInfoAddExprNames "z" ns)) >>>
        implSetNameTypes ns ctx >>>
        f ns)

-- | Emit debugging output using the current 'PPInfo' if the 'implStateDoTrace'
-- flag is set
implTraceM :: (PPInfo -> PP.Doc ann) -> ImplM vars s r ps ps String
implTraceM f =
  do do_trace <- use implStateDoTrace
     doc <- uses implStatePPInfo f
     let str = renderDoc doc
     fn do_trace str (pure str)
  where
    fn True  = trace
    fn False = const id

-- | Run an 'ImplM' computation with 'implStateDoTrace' temporarily disabled
implWithoutTracingM :: ImplM vars s r ps_out ps_in a ->
                       ImplM vars s r ps_out ps_in a
implWithoutTracingM m =
  use implStateDoTrace >>>= \saved ->
  (implStateDoTrace .= False) >>>
  m >>>= \a ->
  (implStateDoTrace .= saved) >>
  pure a

-- | Terminate the current proof branch with a failure
implFailM :: NuMatchingAny1 r => String -> ImplM vars s r ps_any ps a
implFailM str =
  use implStateFailPrefix >>>= \prefix ->
  implTraceM (const $ pretty (prefix ++ "Implication failed")) >>>
  implApplyImpl1 (Impl1_Fail (prefix ++ str)) MNil

-- | Call 'implFailM' and also output a debugging message
implFailMsgM :: NuMatchingAny1 r => String -> ImplM vars s r ps_any ps a
implFailMsgM msg =
  implTraceM (const $ pretty msg) >>>= implFailM

-- | Pretty print an implication @x:p -o (vars).p'@
ppImpl :: PPInfo -> ExprVar tp -> ValuePerm tp ->
          Mb (vars :: RList CrucibleType) (ValuePerm tp) -> PP.Doc ann
ppImpl i x p mb_p =
  sep [PP.group (permPretty i x <> PP.colon <> PP.align (permPretty i p)),
       PP.pretty "-o",
       PP.group (PP.align (permPretty i mb_p))]

-- | Terminate the current proof branch with a failure proving @x:p -o mb_p@
implFailVarM :: NuMatchingAny1 r => String -> ExprVar tp -> ValuePerm tp ->
                Mb vars (ValuePerm tp) -> ImplM vars s r ps_any ps a
implFailVarM f x p mb_p =
  implTraceM (\i ->
               sep [pretty f <> colon <+> pretty "Could not prove",
                    ppImpl i x p mb_p]) >>>=
  implFailM

-- | Produce a branching proof tree that performs the first implication and, if
-- that one fails, falls back on the second. If 'pruneFailingBranches' is set,
-- failing branches are pruned.
implCatchM :: NuMatchingAny1 r =>
              ImplM vars s r ps1 ps2 a -> ImplM vars s r ps1 ps2 a ->
              ImplM vars s r ps1 ps2 a
implCatchM m1 m2 =
  implApplyImpl1 Impl1_Catch (MNil :>: Impl1Cont (const m1)
                              :>: Impl1Cont (const m2))

-- | "Push" all of the permissions in the permission set for a variable, which
-- should be equal to the supplied permission, after deleting those permissions
-- from the input permission set. This is like a simple "proof" of @x:p@.
implPushM :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
             ImplM vars s r (ps :> a) ps ()
implPushM x p =
  implApplyImpl1 (Impl1_Push x p) (MNil :>: Impl1Cont (const $ pure ()))

-- | Call 'implPushM' for multiple @x:p@ permissions
implPushMultiM :: NuMatchingAny1 r => DistPerms ps -> ImplM vars s r ps RNil ()
implPushMultiM DistPermsNil = pure ()
implPushMultiM (DistPermsCons ps x p) =
  implPushMultiM ps >>> implPushM x p

-- | For each permission @x:p@ in a list of permissions, either prove @x:eq(x)@
-- by reflexivity if @p=eq(x)@ or push @x:p@ if @x@ has permissions @p@
implPushOrReflMultiM :: NuMatchingAny1 r => DistPerms ps ->
                        ImplM vars s r ps RNil ()
implPushOrReflMultiM DistPermsNil = pure ()
implPushOrReflMultiM (DistPermsCons ps x (ValPerm_Eq (PExpr_Var x')))
  | x == x' = implPushOrReflMultiM ps >>> introEqReflM x
implPushOrReflMultiM (DistPermsCons ps x p) =
  implPushOrReflMultiM ps >>> implPushM x p

-- | Pop a permission from the top of the stack back to the primary permission
-- for a variable, assuming that the primary permission for that variable is
-- empty, i.e., is the @true@ permission
implPopM :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
            ImplM vars s r ps (ps :> a) ()
implPopM x p =
  implApplyImpl1 (Impl1_Pop x p) (MNil :>: Impl1Cont (const $ pure ()))

-- | Eliminate a disjunctive permission @x:(p1 \/ p2)@, building proof trees
-- that proceed with both @x:p1@ and @x:p2@
implElimOrM :: NuMatchingAny1 r => ExprVar a -> ValuePerm a -> ValuePerm a ->
               ImplM vars s r (ps :> a) (ps :> a) ()
implElimOrM x p1 p2 =
  implTraceM (\pp_info -> pretty "Eliminating or:" <+>
                          permPretty pp_info (ValPerm_Or p1 p2)) >>>
  implApplyImpl1 (Impl1_ElimOr x p1 p2)
  (MNil :>: Impl1Cont (const $ pure ()) :>: Impl1Cont (const $ pure ()))

-- | Eliminate an existential permission @x:(exists (y:tp).p)@ in the current
-- permission set
implElimExistsM :: (NuMatchingAny1 r, KnownRepr TypeRepr tp) =>
                   ExprVar a -> Binding tp (ValuePerm a) ->
                   ImplM vars s r (ps :> a) (ps :> a) ()
implElimExistsM x p =
  implApplyImpl1 (Impl1_ElimExists x p)
  (MNil :>: Impl1Cont (const $ pure ()))

-- | Apply a simple implication rule to the top permissions on the stack
implSimplM :: HasCallStack => NuMatchingAny1 r => Proxy ps ->
              SimplImpl ps_in ps_out ->
              ImplM vars s r (ps :++: ps_out) (ps :++: ps_in) ()
implSimplM prx simpl =
  implApplyImpl1 (Impl1_Simpl simpl prx)
  (MNil :>: Impl1Cont (const $ pure ()))

-- | Bind a new variable @x@ that is set to the supplied expression @e@ and has
-- permissions @eq(e)@, returning @x@
implLetBindVar :: NuMatchingAny1 r => TypeRepr tp -> PermExpr tp ->
                  ImplM vars s r ps ps (Name tp)
-- NOTE: we explicitly do *not* want to re-use an existing variable, for the
-- case where we need distinct bound variables, i.e., for proveVarsImplVarEVars
--
-- implLetBindVar _ (PExpr_Var x) = greturn x
implLetBindVar tp e =
  implApplyImpl1 (Impl1_LetBind tp e)
  (MNil :>: Impl1Cont (\(_ :>: n) -> pure n)) >>>= \n ->
  implPopM n (ValPerm_Eq e) >>>
  pure n

-- | Bind a sequence of variables with 'implLetBindVar'
implLetBindVars :: NuMatchingAny1 r => CruCtx tps -> PermExprs tps ->
                   ImplM vars s r ps ps (RAssign ExprVar tps)
implLetBindVars CruCtxNil MNil = pure MNil
implLetBindVars (CruCtxCons tps tp) (es :>: e) =
  (:>:) <$> implLetBindVars tps es <*> implLetBindVar tp e

-- | Project out a field of a struct @x@ by binding a fresh variable @y@ for its
-- contents, and assign the permissions for that field to @y@, replacing them
-- with a proof that the field equals @y@, popping the permissions for @y@ and
-- returning the variable @y@. If the given struct field already has permissions
-- @eq(y)@ for some @y@, just return that @y@.
implElimStructField ::
  NuMatchingAny1 r => ExprVar (StructType ctx) ->
  RAssign ValuePerm (CtxToRList ctx) -> Member (CtxToRList ctx) a ->
  ImplM vars s r (ps :> StructType ctx) (ps :> StructType ctx) (ExprVar a)
implElimStructField _ ps memb
  | ValPerm_Eq (PExpr_Var y) <- RL.get memb ps = pure y
implElimStructField x ps memb =
  implGetVarType x >>>= \(StructRepr tps) ->
  let tp = RL.get memb (assignToRList tps) in
  implApplyImpl1 (Impl1_ElimStructField x ps tp memb)
  (MNil :>: Impl1Cont (\(_ :>: n) -> pure n)) >>>= \y ->
  implPopM y (RL.get memb ps) >>>
  pure y

-- | Apply 'implElimStructField' to a sequence of fields in a struct permission,
-- to get out a sequence of variables for the corrsponding fields of that struct
implElimStructFields ::
  NuMatchingAny1 r => ExprVar (StructType ctx) ->
  RAssign ValuePerm (CtxToRList ctx) -> RAssign (Member (CtxToRList ctx)) fs ->
  ImplM vars s r (ps :> StructType ctx) (ps :> StructType ctx) (RAssign ExprVar fs)
implElimStructFields _ _ MNil = pure MNil
implElimStructFields x ps (membs :>: memb) =
  implElimStructField x ps memb >>>= \y ->
  implElimStructFields x (RL.set memb (ValPerm_Eq $
                                       PExpr_Var y) ps) membs >>>= \ys ->
  pure (ys :>: y)

-- | Apply 'implElimStructField' to all fields in a struct permission, to get
-- out a sequence of variables for the fields of that struct
implElimStructAllFields ::
  NuMatchingAny1 r => ExprVar (StructType ctx) ->
  RAssign ValuePerm (CtxToRList ctx) ->
  ImplM vars s r (ps :> StructType ctx) (ps :> StructType ctx)
  (RAssign Name (CtxToRList ctx))
implElimStructAllFields x ps = implElimStructFields x ps (RL.members ps)

-- | Prove a struct permission @struct(p1,...,pn)@ from a struct permission
-- (described by the second argument) where some subset of the field permissions
-- are equality permissions to variables along with proofs that the variables
-- have the required permissions
implIntroStructFields ::
  NuMatchingAny1 r => ExprVar (StructType ctx) ->
  RAssign ValuePerm (CtxToRList ctx) -> RAssign (Member (CtxToRList ctx)) fs ->
  ImplM vars s r (ps :> StructType ctx) (ps :++: fs :> StructType ctx) ()
implIntroStructFields _ _ MNil = pure ()
implIntroStructFields x ps (membs :>: memb)
  | ValPerm_Eq (PExpr_Var y) <- RL.get memb ps =
    (distPermsHeadPerm <$> distPermsSnoc <$> getDistPerms) >>>= \y_p ->
    implSwapM y y_p x (ValPerm_Conj1 $ Perm_Struct ps) >>>
    implSimplM Proxy (SImpl_IntroStructField x ps memb y_p) >>>
    implIntroStructFields x (RL.set memb y_p ps) membs
implIntroStructFields _ _ _ =
  error "implIntroStructFields: malformed input permission"

-- | Prove a struct permission @struct(p1,...,pn)@ from a struct permission
-- @struct(eq(y1),...,eq(yn))@ on top of the stack of equality permissions to
-- variables along with proofs below it on the stack that each variable @yi@ has
-- the corresponding permission @pi@
implIntroStructAllFields ::
  NuMatchingAny1 r => ExprVar (StructType ctx) ->
  ImplM vars s r (ps :> StructType ctx) (ps :++: CtxToRList ctx
                                         :> StructType ctx) ()
implIntroStructAllFields x =
  getTopDistPerm x >>>= \(ValPerm_Conj1 (Perm_Struct ps)) ->
  implIntroStructFields x ps (RL.members ps)

-- | Eliminate a permission @x:ptr((rw,off) |-> p)@ into permissions
-- @x:ptr((rw,off) |-> eq(y))@ and @y:p@ for a fresh variable @y@, returning the
-- fresh variable @y@ and popping the @y@ permissions off the stack. If @p@
-- already has the form @eq(y)@, then just return @y@.
implElimLLVMFieldContentsM ::
  (NuMatchingAny1 r, 1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
  ExprVar (LLVMPointerType w) -> LLVMFieldPerm w sz ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w)
  (ExprVar (LLVMPointerType sz))
implElimLLVMFieldContentsM _ fp
  | ValPerm_Eq (PExpr_Var y) <- llvmFieldContents fp
  = pure y
implElimLLVMFieldContentsM x fp =
  implApplyImpl1 (Impl1_ElimLLVMFieldContents x fp)
  (MNil :>: Impl1Cont (\(_ :>: n) -> pure n)) >>>= \y ->
  implPopM y (llvmFieldContents fp) >>>
  pure y

-- | Prove a reachability permission @x:P<args,e>@ from a proof of @x:eq(e)@ on
-- the top of the stack
implReachabilityReflM ::
  NuMatchingAny1 r =>
  ExprVar a -> NamedPermName (RecursiveSort b 'True) args a ->
  PermExprs args -> PermOffset a ->
  ImplM vars s r (ps :> a) (ps :> a) ()
implReachabilityReflM x npn all_args off
  | NameReachConstr <- namedPermNameReachConstr npn
  , PExprs_Cons args e <- all_args =
    implLookupNamedPerm npn >>>= \np ->
    case unfoldPerm np (PExprs_Cons args e) off of
      ValPerm_Or p1 p2
        | p1 == ValPerm_Eq e ->
          introOrLM x p1 p2 >>>
          implFoldNamedM x npn (PExprs_Cons args e) off
      _ -> error "implReachabilityReflM: unexpected form of unfolded permission"

-- | Prove a reachability permission @x:P<args,e>@ from proofs of
-- @x:P<args,y>@ and @y:P<args,e>@ on the top of the stack
implReachabilityTransM ::
  NuMatchingAny1 r =>
  ExprVar a -> NamedPermName (RecursiveSort b 'True) args a ->
  PermExprs args -> PermOffset a -> ExprVar a ->
  ImplM vars s r (ps :> a) (ps :> a :> a) ()
implReachabilityTransM x npn all_args off y
  | NameReachConstr <- namedPermNameReachConstr npn
  , PExprs_Cons args e <- all_args =
    implLookupNamedPerm npn >>>= \(NamedPerm_Rec rp) ->
    implSimplM Proxy (SImpl_ReachabilityTrans x rp args off y e)

-- | Eliminate a @memblock@ permission with arbitrary shape @sh@, which cannot
-- have any free variables outside of pointer shapes, to have equality shape
-- @eqsh(y)@ for a variable @y@, assuming that permission is on the top of the
-- stack, and return the variable @y@. If @sh@ is already of this form, just
-- return the variable without doing any elimination.
implElimLLVMBlockToEq ::
  (NuMatchingAny1 r, 1 <= w, KnownNat w) => ExprVar (LLVMPointerType w) ->
  LLVMBlockPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w)
  (ExprVar (LLVMBlockType w))
implElimLLVMBlockToEq _ (LLVMBlockPerm
                         { llvmBlockShape = PExpr_EqShape (PExpr_Var y)}) =
  pure y
implElimLLVMBlockToEq x bp =
  implApplyImpl1 (Impl1_ElimLLVMBlockToEq x bp)
  (MNil :>: Impl1Cont (\(_ :>: n) -> pure n)) >>>= \y ->
  implPopM y (ValPerm_Conj1 $ Perm_LLVMBlockShape $ modalizeBlockShape bp) >>>
  pure y

-- | Try to prove a proposition about bitvectors dynamically, failing as in
-- 'implFailM' if the proposition does not hold
implTryProveBVProp :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                      ExprVar (LLVMPointerType w) -> BVProp w ->
                      ImplM vars s r (ps :> LLVMPointerType w) ps ()
implTryProveBVProp x p =
  use implStatePPInfo >>>= \i ->
  let str = renderDoc (permPretty i p) in
  implApplyImpl1 (Impl1_TryProveBVProp x p str)
  (MNil :>: Impl1Cont (const $ pure ()))

-- | Try to prove a sequence of propositions using 'implTryProveBVProp'
implTryProveBVProps :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                       ExprVar (LLVMPointerType w) -> [BVProp w] ->
                       ImplM vars s r (ps :> LLVMPointerType w) ps ()
implTryProveBVProps x [] = introConjM x
implTryProveBVProps x (prop:props) =
  implTryProveBVProp x prop >>>
  implTryProveBVProps x props >>>
  implInsertConjM x (Perm_BVProp prop) (map Perm_BVProp props) 0

-- | Drop a permission from the top of the stack
implDropM :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
             ImplM vars s r ps (ps :> a) ()
implDropM x p = implSimplM Proxy (SImpl_Drop x p)

-- | Copy a permission on the top of the stack, assuming it is copyable
implCopyM :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
             ImplM vars s r (ps :> a :> a) (ps :> a) ()
implCopyM x p = implSimplM Proxy (SImpl_Copy x p)

-- | Swap the top two permissions on the top of the stack
implSwapM :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
             ExprVar b -> ValuePerm b ->
             ImplM vars s r (ps :> b :> a) (ps :> a :> b) ()
implSwapM x p1 y p2 = implSimplM Proxy (SImpl_Swap x p1 y p2)

-- | Move permission @p@ that is on the stack below two lists @ps1@ and @ps2@
-- towards the top of the stack by moving it between @ps1@ and @ps2@. That is,
-- change the stack
--
-- > perms, p, p1_1, ..., p1_n, p2_1, ..., p2_m
--
-- to
--
-- > perms, p1_1, ..., p1_n, p, p2_1, ..., p2_m
implMoveUpM ::
  NuMatchingAny1 r =>
  prx ps -> RAssign f ps1 -> ExprVar a -> RAssign f ps2 ->
  ImplM vars s r (ps :++: ps1 :> a :++: ps2) (ps :> a :++: ps1 :++: ps2) ()
implMoveUpM (ps :: prx ps) ps1 (x :: ExprVar a) ps2 =
  -- FIXME: this is gross! Find a better way to do all this!
  getDistPerms >>>= \perms ->
  let (perms0x, perms12) =
        splitDistPerms (Proxy :: Proxy (ps :> a)) (RL.append ps1 ps2) perms
      (perms1, perms2) = splitDistPerms ps1 ps2 perms12 in
  case (perms0x, RL.appendRNilConsEq ps x (RL.append ps1 ps2)) of
    (DistPermsCons _perms0 x' p, Refl)
      | Just Refl <- testEquality x x' ->
        implSimplM (Proxy :: Proxy ps) (SImpl_MoveUp perms1 x p perms2)
    (DistPermsCons _ _x' _, _) -> error "implMoveUpM: unexpected variable"

-- | Move permission @p@ that is on the stack between two lists @ps1@ and @ps2@
-- towards the bottom of the stack by moving it below both @ps1@ and @ps2@. That
-- is, change the stack
--
-- > perms, p1_1, ..., p1_n, p, p2_1, ..., p2_m
--
-- to
--
-- > perms, p, p1_1, ..., p1_n, p2_1, ..., p2_m
implMoveDownM ::
  NuMatchingAny1 r =>
  prx ps -> RAssign f (ps1 :> a) -> ExprVar a -> RAssign f ps2 ->
  ImplM vars s r (ps :> a :++: ps1 :++: ps2) (ps :++: ps1 :> a :++: ps2) ()
implMoveDownM (ps :: prx ps) ps1x (x :: ExprVar a) ps2 =
  -- FIXME: this is gross! Find a better way to do all this!
  getDistPerms >>>= \perms ->
  let (_, perms1x2) = splitDistPerms ps (RL.append ps1x ps2) perms
      (perms1x, perms2) = splitDistPerms ps1x ps2 perms1x2 in
  case (perms1x, RL.appendRNilConsEq ps (RL.head ps1x) (RL.append
                                                        (RL.tail ps1x) ps2)) of
    (DistPermsCons perms1 x' p, Refl)
      | Just Refl <- testEquality x x' ->
        implSimplM (Proxy :: Proxy ps) (SImpl_MoveDown perms1 x p perms2)
    _ -> error "implMoveDownM: unexpected variable"

-- | Eliminate disjunctives and existentials on the top of the stack and return
-- the resulting permission
elimOrsExistsM :: NuMatchingAny1 r => ExprVar a ->
                  ImplM vars s r (ps :> a) (ps :> a) (ValuePerm a)
elimOrsExistsM x =
  getTopDistPerm x >>= \case
    ValPerm_Or p1 p2 -> implElimOrM x p1 p2 >>> elimOrsExistsM x
    ValPerm_Exists mb_p ->
      implElimExistsM x mb_p >>> elimOrsExistsM x
    p -> pure p

-- | Eliminate disjunctives, existentials, recusive permissions, and
-- defined permissions on the top of the stack
elimOrsExistsNamesM :: NuMatchingAny1 r => ExprVar a ->
                       ImplM vars s r (ps :> a) (ps :> a) (ValuePerm a)
elimOrsExistsNamesM x =
  getTopDistPerm x >>= \case
    ValPerm_Or p1 p2 -> implElimOrM x p1 p2 >>> elimOrsExistsNamesM x
    ValPerm_Exists mb_p ->
      implElimExistsM x mb_p >>> elimOrsExistsNamesM x
    ValPerm_Named npn args off
      | TrueRepr <- nameCanFoldRepr npn ->
        implUnfoldNamedM x npn args off >>> elimOrsExistsNamesM x
    ValPerm_Named npn args off
      | TrueRepr <- nameIsConjRepr npn ->
        implNamedToConjM x npn args off >>> getTopDistPerm x
    p -> pure p

-- | Eliminate any disjunctions, existentials, recursive permissions, or defined
-- permissions for a variable and then return the resulting "simple" permission
getSimpleVarPerm :: NuMatchingAny1 r => ExprVar a ->
                    ImplM vars s r ps ps (ValuePerm a)
getSimpleVarPerm x =
  getPerm x >>= \p_init ->
  implPushM x p_init >>>
  elimOrsExistsNamesM x >>>= \p ->
  implPopM x p >>> pure p

-- | Eliminate any disjunctions, existentials, recursive permissions, or defined
-- permissions for a variable to try to get an equality permission
-- @eq(e)@. Return @e@ if this is successful.
getVarEqPerm :: NuMatchingAny1 r => ExprVar a ->
                ImplM vars s r ps ps (Maybe (PermExpr a))
getVarEqPerm x =
  getPerm x >>= \p_init ->
  implPushM x p_init >>>
  elimOrsExistsNamesM x >>>=
  \case
    p@(ValPerm_Eq e) -> implPopM x p >>> pure (Just e)
    ValPerm_Conj [Perm_Struct ps] ->
      implElimStructAllFields x ps >>>= \ys ->
      implSimplM Proxy (SImpl_StructPermToEq x $ namesToExprs ys) >>>
      implPopM x (ValPerm_Eq $ PExpr_Struct $ namesToExprs ys) >>>
      pure (Just $ PExpr_Struct $ namesToExprs ys)
    p -> implPopM x p >>> pure Nothing

-- | Eliminate any disjunctions, existentials, recursive permissions, or defined
-- permissions for any variables in the supplied expression and substitute any
-- equality permissions for those variables. Also eta-expand any struct
-- variables to a struct of variables using 'implElimStructAllFields'.
getEqualsExpr :: NuMatchingAny1 r => PermExpr a ->
                 ImplM vars s r ps ps (PermExpr a)
getEqualsExpr e@(PExpr_Var x) =
  getVarEqPerm x >>= \case Just e' -> getEqualsExpr e'
                           Nothing -> pure e
getEqualsExpr (PExpr_BV factors off) =
  foldr bvAdd (PExpr_BV [] off) <$>
  mapM (\(BVFactor (BV.BV i) x) ->
         bvMult i <$> getEqualsExpr (PExpr_Var x)) factors
getEqualsExpr (PExpr_LLVMWord e) =
  PExpr_LLVMWord <$> getEqualsExpr e
getEqualsExpr (PExpr_LLVMOffset x off) =
  addLLVMOffset <$> getEqualsExpr (PExpr_Var x) <*> getEqualsExpr off
getEqualsExpr e = pure e


-- | Introduce a proof of @x:eq(x)@ onto the top of the stack
introEqReflM :: NuMatchingAny1 r => ExprVar a -> ImplM vars s r (ps :> a) ps ()
introEqReflM x = implSimplM Proxy (SImpl_IntroEqRefl x)

-- | Invert a proof of @x:eq(y)@ on the top of the stack to one of @y:eq(x)@
invertEqM :: NuMatchingAny1 r => ExprVar a -> ExprVar a ->
             ImplM vars s r (ps :> a) (ps :> a) ()
invertEqM x y = implSimplM Proxy (SImpl_InvertEq x y)

-- | Prove @x:eq(y)@ by proving equality permissions for both @x@ and @y@ to the
-- same expression, thereby implementing a form of transitivity of equality
-- where the second equality is inversted:
invTransEqM :: NuMatchingAny1 r => ExprVar a -> ExprVar a -> PermExpr a ->
               ImplM vars s r (ps :> a) (ps :> a :> a) ()
invTransEqM x y e = implSimplM Proxy (SImpl_InvTransEq x y e)

-- | Copy an @x:eq(e)@ permission on the top of the stack
introEqCopyM :: NuMatchingAny1 r => ExprVar a -> PermExpr a ->
                ImplM vars s r (ps :> a :> a) (ps :> a) ()
introEqCopyM x e = implSimplM Proxy (SImpl_CopyEq x e)

-- | Cast an @eq(llvmword(y))@ proof to an @eq(llvmword(e))@ proof using a
-- proof of @y:eq(e)@
llvmWordEqM :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
               ExprVar (LLVMPointerType w) ->
               ExprVar (BVType w) -> PermExpr (BVType w) ->
               ImplM vars s r (ps :> LLVMPointerType w)
               (ps :> LLVMPointerType w :> BVType w) ()
llvmWordEqM x y e = implSimplM Proxy (SImpl_LLVMWordEq x y e)

-- | Cast a @y:p@ perm on the top of the stack to an @x:p@ perm using an
-- @x:eq(y)@ just below it on the stack
introCastM :: NuMatchingAny1 r => ExprVar a -> ExprVar a -> ValuePerm a ->
              ImplM vars s r (ps :> a) (ps :> a :> a) ()
introCastM x y p = implSimplM Proxy (SImpl_Cast x y p)

-- | Prove a sequence of equality permissions @x1:eq(e1),...,xn:eq(en)@, where
-- each is proved either by reflexivity, if it is of the form @x:eq(x)@, or by
-- copying an equality permission already held by the variable in quesiton, if
-- it is not. It is an error if any of the supplied perms are not equality
-- perms, or if any @xi@ does not have permission @eq(ei)@ in the current
-- permission set for @ei@ not equal to @xi@.
implProveEqPerms :: NuMatchingAny1 r => DistPerms ps' ->
                    ImplM vars s r (ps :++: (RNil :> a :++: ps')) (ps :> a) ()
implProveEqPerms DistPermsNil = pure ()
implProveEqPerms (DistPermsCons ps' x (ValPerm_Eq (PExpr_Var y)))
  | x == y
  = implProveEqPerms ps' >>> introEqReflM x
implProveEqPerms (DistPermsCons ps' x p@(ValPerm_Eq _)) =
  implProveEqPerms ps' >>>
  implPushM x p >>> implCopyM x p >>> implPopM x p
implProveEqPerms _ = error "implProveEqPerms: non-equality permission"

-- | Cast a proof of @x:p@ to one of @x:p'@ using a proof that @p=p'@
implCastPermM :: NuMatchingAny1 r => ExprVar a -> SomeEqProof (ValuePerm a) ->
                 ImplM vars s r (ps :> a) (ps :> a) ()
implCastPermM x some_eqp
  | UnSomeEqProof eqp <- unSomeEqProof some_eqp =
    implProveEqPerms (eqProofPerms eqp) >>>
    implSimplM Proxy (SImpl_CastPerm x eqp)

-- | Cast a permission somewhere in the stack using an equality proof
implCastStackElemM :: NuMatchingAny1 r => Member ps a ->
                      SomeEqProof (ValuePerm a) -> ImplM vars s r ps ps ()
implCastStackElemM memb some_eqp =
  getDistPerms >>>= \all_perms ->
  case RL.memberSplitAt all_perms memb of
    RL.SplitAtMemberRet ps0 px@(VarAndPerm x _) ps1 ->
      implMoveUpM ps0 ps1 x MNil >>>
      implCastPermM x some_eqp >>>
      implMoveDownM ps0 (ps1 :>: px) x MNil

-- | Cast all of the permissions on the stack using 'implCastPermM'
implCastStackM :: NuMatchingAny1 r => SomeEqProof (ValuePerms ps) ->
                  ImplM vars s r ps ps ()
implCastStackM some_eqp =
  getDistPerms >>>= \perms ->
  RL.foldr (\memb m ->
             implCastStackElemM memb (fmap (RL.get memb) some_eqp) >>> m)
  (pure ())
  (RL.members perms)

-- | Introduce a proof of @x:true@ onto the top of the stack, which is the same
-- as an empty conjunction
introConjM :: NuMatchingAny1 r => ExprVar a -> ImplM vars s r (ps :> a) ps ()
introConjM x = implSimplM Proxy (SImpl_IntroConj x)

-- | Extract the @i@th atomic permission from the conjunct on the top of the
-- stack and put it just below the top of the stack
implExtractConjM :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] -> Int ->
                    ImplM vars s r (ps :> a :> a) (ps :> a) ()
implExtractConjM x ps i = implSimplM Proxy (SImpl_ExtractConj x ps i)

-- | Extract the @i@th atomic permission from the conjunct on the top of the
-- stack and push it to the top of the stack; i.e., call 'implExtractConjM' and
-- then swap the top two stack elements
implExtractSwapConjM :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] -> Int ->
                        ImplM vars s r (ps :> a :> a) (ps :> a) ()
implExtractSwapConjM x ps i =
  implExtractConjM x ps i >>>
  implSwapM x (ValPerm_Conj1 $ ps!!i) x (ValPerm_Conj $ deleteNth i ps)

-- | Combine the top two conjunctive permissions on the stack
implAppendConjsM :: NuMatchingAny1 r => ExprVar a ->
                    [AtomicPerm a] -> [AtomicPerm a] ->
                    ImplM vars s r (ps :> a) (ps :> a :> a) ()
implAppendConjsM x ps1 ps2 = implSimplM Proxy (SImpl_AppendConjs x ps1 ps2)

-- | Split the conjuctive permissions on the top of the stack into the first @i@
-- and the remaining conjuncts after those
implSplitConjsM :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] -> Int ->
                   ImplM vars s r (ps :> a :> a) (ps :> a) ()
implSplitConjsM x ps i = implSimplM Proxy (SImpl_SplitConjs x ps i)

-- | Split the conjuctive permissions on the top of the stack into the first @i@
-- and the remaining conjuncts after those, and then swap them
implSplitSwapConjsM :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] -> Int ->
                       ImplM vars s r (ps :> a :> a) (ps :> a) ()
implSplitSwapConjsM x ps i =
  implSplitConjsM x ps i >>>
  implSwapM x (ValPerm_Conj $ take i ps) x (ValPerm_Conj $ drop i ps)

-- | Copy the @i@th atomic permission in the conjunct on the top of the stack,
-- assuming that conjunction contains the given atomic permissions and that the
-- given conjunct is copyable, and put the copied atomic permission just below
-- the top of the stack
implCopyConjM :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] -> Int ->
                 ImplM vars s r (ps :> a :> a) (ps :> a) ()
implCopyConjM x ps i = implSimplM Proxy (SImpl_CopyConj x ps i)

-- | Copy the @i@th atomic permission in the conjunct on the top of the stack
-- and push it to the top of the stack; i.e., call 'implCopyConjM' and then swap
-- the top two stack elements
implCopySwapConjM :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] -> Int ->
                     ImplM vars s r (ps :> a :> a) (ps :> a) ()
implCopySwapConjM x ps i =
  implCopyConjM x ps i >>>
  implSwapM x (ValPerm_Conj1 $ ps!!i) x (ValPerm_Conj ps)

-- | Either extract or copy the @i@th atomic permission in the conjunct on the
-- top of the stack, popping the remaining permissions
implGetPopConjM :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] -> Int ->
                   ImplM vars s r (ps :> a) (ps :> a) ()
implGetPopConjM x ps i =
  if atomicPermIsCopyable (ps!!i) then
    implCopyConjM x ps i >>>
    implPopM x (ValPerm_Conj ps)
  else
    implExtractConjM x ps i >>>
    implPopM x (ValPerm_Conj $ deleteNth i ps)

-- | If the top element of the stack is copyable, then copy it and pop it, and
-- otherwise just leave it alone on top of the stack
implMaybeCopyPopM :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
                     ImplM vars s r (ps :> a) (ps :> a) ()
implMaybeCopyPopM x p | permIsCopyable p = implCopyM x p >>> implPopM x p
implMaybeCopyPopM _ _ = pure ()

-- | Insert an atomic permission below the top of the stack at the @i@th
-- position in the conjunct on the top of the stack, where @i@ must be between
implInsertConjM :: NuMatchingAny1 r => ExprVar a ->
                   AtomicPerm a -> [AtomicPerm a] -> Int ->
                   ImplM vars s r (ps :> a) (ps :> a :> a) ()
implInsertConjM x p ps i = implSimplM Proxy (SImpl_InsertConj x p ps i)

-- | Insert an atomic permission on the top of the stack into the @i@th position
-- in the conjunct below it on the of the stack; that is, swap the top two
-- permissions and call 'implInsertConjM'
implSwapInsertConjM :: NuMatchingAny1 r => ExprVar a ->
                       AtomicPerm a -> [AtomicPerm a] -> Int ->
                       ImplM vars s r (ps :> a) (ps :> a :> a) ()
implSwapInsertConjM x p ps i =
  implSwapM x (ValPerm_Conj ps) x (ValPerm_Conj1 p) >>>
  implInsertConjM x p ps i

-- | Apply the left or-introduction rule to the top of the permission stack,
-- changing it from @x:p1@ to @x:(p1 \/ p2)@
introOrLM :: NuMatchingAny1 r => ExprVar a -> ValuePerm a -> ValuePerm a ->
             ImplM vars s r (ps :> a) (ps :> a) ()
introOrLM x p1 p2 = implSimplM Proxy (SImpl_IntroOrL x p1 p2)

-- | Apply the right or-introduction rule to the top of the permission stack,
-- changing it from @x:p2@ to @x:(p1 \/ p2)@
introOrRM :: NuMatchingAny1 r => ExprVar a -> ValuePerm a -> ValuePerm a ->
             ImplM vars s r (ps :> a) (ps :> a) ()
introOrRM x p1 p2 = implSimplM Proxy (SImpl_IntroOrR x p1 p2)

-- | Apply existential introduction to the top of the permission stack, changing
-- it from @[e/x]p@ to @exists (x:tp).p@
--
-- FIXME: is there some way we could "type-check" this, to ensure that the
-- permission on the top of the stack really equals @[e/x]p@?
introExistsM :: (KnownRepr TypeRepr tp, NuMatchingAny1 r) =>
                ExprVar a -> PermExpr tp -> Binding tp (ValuePerm a) ->
                ImplM vars s r (ps :> a) (ps :> a) ()
introExistsM x e p_body = implSimplM Proxy (SImpl_IntroExists x e p_body)

-- | Cast a proof of @x:eq(LLVMWord(e1))@ to @x:eq(LLVMWord(e2))@ on the top of
-- the stack
castLLVMWordEqM ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> PermExpr (BVType w) -> PermExpr (BVType w) ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()
castLLVMWordEqM x e1 e2 =
  implTryProveBVProp x (BVProp_Eq e1 e2) >>>
  implSimplM Proxy (SImpl_CastLLVMWord x e1 e2)

-- | Cast a @y:p@ on the top of the stack to @x:(p - off)@ using a
-- proof of @x:eq(y+off)@ just below it on the stack
castLLVMPtrM :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                ExprVar (LLVMPointerType w) ->
                ValuePerm (LLVMPointerType w) -> PermExpr (BVType w) ->
                ExprVar (LLVMPointerType w) ->
                ImplM vars s r (ps :> LLVMPointerType w)
                (ps :> LLVMPointerType w :> LLVMPointerType w) ()
castLLVMPtrM y p off x = implSimplM Proxy (SImpl_CastLLVMPtr y p off x)

-- | Cast a @y:eq(word(e))@ on the top of the stack to @x:eq(word(e+off))@ using
-- a proof of @x:eq(y+off)@ just below it on the stack
offsetLLVMWordM :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                   ExprVar (LLVMPointerType w) ->
                   PermExpr (BVType w) -> PermExpr (BVType w) ->
                   ExprVar (LLVMPointerType w) ->
                   ImplM vars s r (ps :> LLVMPointerType w)
                   (ps :> LLVMPointerType w :> LLVMPointerType w) ()
offsetLLVMWordM y e off x = implSimplM Proxy (SImpl_OffsetLLVMWord y e off x)

-- | Cast a proof of @x:free(e1)@ on the top of the stack to one of @x:free(e2)@
-- by first proving that @e1=e2@
castLLVMFreeM :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                 ExprVar (LLVMPointerType w) ->
                 PermExpr (BVType w) -> PermExpr (BVType w) ->
                 ImplM vars s r (ps :> LLVMPointerType w)
                 (ps :> LLVMPointerType w) ()
castLLVMFreeM x e1 e2 =
  implTryProveBVProp x (BVProp_Eq e1 e2) >>>
  implSimplM Proxy (SImpl_CastLLVMFree x e1 e2)

-- | Fold a named permission (other than an opaque permission)
implFoldNamedM :: (NameSortCanFold ns ~ 'True, NuMatchingAny1 r) => ExprVar a ->
                  NamedPermName ns args a -> PermExprs args -> PermOffset a ->
                  ImplM vars s r (ps :> a) (ps :> a) ()
implFoldNamedM x npn args off =
  do np <- implLookupNamedPerm npn
     implSimplM Proxy (SImpl_FoldNamed x np args off)

-- | Unfold a named permission (other than an opaque permission), returning the
-- unfolding
implUnfoldNamedM :: (NameSortCanFold ns ~ 'True, NuMatchingAny1 r) =>
                    ExprVar a -> NamedPermName ns args a ->
                    PermExprs args -> PermOffset a ->
                    ImplM vars s r (ps :> a) (ps :> a) (ValuePerm a)
implUnfoldNamedM x npn args off =
  do np <- implLookupNamedPerm npn
     implSimplM Proxy (SImpl_UnfoldNamed x np args off)
     pure (unfoldPerm np args off)

-- | Map a named permission that is conjoinable to a conjunction
implNamedToConjM :: (NameSortIsConj ns ~ 'True, NuMatchingAny1 r) =>
                    ExprVar a -> NamedPermName ns args a ->
                    PermExprs args -> PermOffset a ->
                    ImplM vars s r (ps :> a) (ps :> a) ()
implNamedToConjM x npn args off =
  implSimplM Proxy (SImpl_NamedToConj x npn args off)

-- | Map a conjuctive named permission to a named permission
implNamedFromConjM :: (NameSortIsConj ns ~ 'True, NuMatchingAny1 r) =>
                      ExprVar a -> NamedPermName ns args a -> PermExprs args ->
                      PermOffset a -> ImplM vars s r (ps :> a) (ps :> a) ()
implNamedFromConjM x npn args off =
  implSimplM Proxy (SImpl_NamedFromConj x npn args off)

-- | Begin a fresh lifetime, returning the lifetime that was created and popping
-- its @lowned@ permission off of the stack
implBeginLifetimeM :: NuMatchingAny1 r =>
                      ImplM vars s r ps ps (ExprVar LifetimeType)
implBeginLifetimeM =
  implApplyImpl1 Impl1_BeginLifetime
    (MNil :>: Impl1Cont (\(_ :>: n) -> pure n)) >>>= \l ->
  implPopM l (ValPerm_LOwned MNil MNil) >>>
  pure l

-- | End a lifetime, assuming the top of the stack is of the form
--
-- > ps, ps_in, l:lowned(ps_in -o ps_out)
--
-- Pop all the returned permissions @ps_out@, leaving just @ps@ on the stack.
implEndLifetimeM :: NuMatchingAny1 r => Proxy ps -> ExprVar LifetimeType ->
                    LOwnedPerms ps_in -> LOwnedPerms ps_out ->
                    ImplM vars s r ps (ps :++: ps_in :> LifetimeType) ()
implEndLifetimeM ps l ps_in ps_out@(lownedPermsToDistPerms -> Just dps_out) =
  implSimplM ps (SImpl_EndLifetime l ps_in ps_out) >>>
  recombinePermsPartial ps dps_out
implEndLifetimeM _ _ _ _ = implFailM "implEndLifetimeM: lownedPermsToDistPerms"


-- | Save a permission for later by splitting it into part that is in the
-- current lifetime and part that is saved in the lifetime for later. Assume
-- permissions
--
-- > x:F<l> * l:[l2]lcurrent * l2:lowned ps
--
-- are on the top of the stack, and return @x:F<l2>@ on top of the stack,
-- popping the new @lowned@ permission on @l2@
implSplitLifetimeM :: (KnownRepr TypeRepr a, NuMatchingAny1 r) =>
                      ExprVar a -> LifetimeFunctor args a ->
                      PermExprs args -> PermExpr LifetimeType ->
                      ExprVar LifetimeType ->
                      LOwnedPerms ps_in -> LOwnedPerms ps_out ->
                      ImplM vars s r (ps :> a)
                      (ps :> a :> LifetimeType :> LifetimeType) ()
implSplitLifetimeM x f args l l2 ps_in ps_out =
  implTraceM (\i ->
               sep [pretty "Splitting lifetime to" <+> permPretty i l2 <> colon,
                    permPretty i (ltFuncMinApply f l)]) >>>
  implSimplM Proxy (SImpl_SplitLifetime x f args l l2 ps_in ps_out) >>>
  getTopDistPerm l2 >>>= implPopM l2

-- | Find all lifetimes that we currently own which could, if ended, help prove
-- the specified permissions, and return them with their @lowned@ permissions
lifetimesThatCouldProve :: NuMatchingAny1 r => Mb vars (DistPerms ps') ->
                           ImplM vars s r ps ps [(ExprVar LifetimeType,
                                                  AtomicPerm LifetimeType)]
lifetimesThatCouldProve mb_ps =
  do Some all_perms <- uses implStatePerms permSetAllVarPerms
     pure (RL.foldr
             (\case
                 VarAndPerm l (ValPerm_LOwned ps_in ps_out)
                   | mbLift $ fmap (lownedPermsCouldProve ps_out) mb_ps ->
                     ((l, Perm_LOwned ps_in ps_out) :)
                 _ -> id)
             []
             all_perms)

-- | Combine proofs of @x:ptr(pps,(off,spl) |-> eq(y))@ and @y:p@ on the top of
-- the permission stack into a proof of @x:ptr(pps,(off,spl |-> p))@
introLLVMFieldContentsM ::
  (1 <= w, KnownNat w, 1 <= sz, KnownNat sz, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> ExprVar (LLVMPointerType sz) ->
  LLVMFieldPerm w sz ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w :>
                                            LLVMPointerType sz) ()
introLLVMFieldContentsM x y fp =
  implSimplM Proxy (SImpl_IntroLLVMFieldContents x y fp)

-- | Borrow a field from an LLVM array permission on the top of the stack, after
-- proving (with 'implTryProveBVProps') that the index is in the array exclusive
-- of any outstanding borrows (see 'llvmArrayIndexInArray'). Return the
-- resulting array permission with the borrow and the borrowed field permission,
-- leaving the arry permission on top of the stack and the field permission just
-- below it on the stack.
implLLVMArrayIndexBorrow ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayIndex w ->
  ImplM vars s r (ps :> LLVMPointerType w :> LLVMPointerType w)
  (ps :> LLVMPointerType w) (LLVMArrayPerm w, LLVMArrayField w)
implLLVMArrayIndexBorrow x ap ix =
  implTryProveBVProps x (llvmArrayIndexInArray ap ix) >>>
  implSimplM Proxy (SImpl_LLVMArrayIndexBorrow x ap ix) >>>
  pure (llvmArrayAddBorrow (FieldBorrow ix) ap,
           llvmArrayFieldWithOffset ap ix)

-- | Copy a field from an LLVM array permission on the top of the stack, after
-- proving (with 'implTryProveBVProps') that the index is in the array exclusive
-- of any outstanding borrows (see 'llvmArrayIndexInArray')
implLLVMArrayIndexCopy ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayIndex w ->
  ImplM vars s r (ps :> LLVMPointerType w
                  :> LLVMPointerType w) (ps :> LLVMPointerType w) ()
implLLVMArrayIndexCopy x ap ix =
  implTryProveBVProps x (llvmArrayIndexInArray ap ix) >>>
  implSimplM Proxy (SImpl_LLVMArrayIndexCopy x ap ix)

-- | Return a field permission that has been borrowed from an array permission,
-- where the array permission is on the top of the stack and the field
-- permission borrowed from it is just below it
implLLVMArrayIndexReturn ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayIndex w ->
  ImplM vars s r (ps :> LLVMPointerType w)
  (ps :> LLVMPointerType w :> LLVMPointerType w) ()
implLLVMArrayIndexReturn x ap ix =
  implSimplM Proxy (SImpl_LLVMArrayIndexReturn x ap ix)

-- | Borrow a sub-array from an array as per 'SImpl_LLVMArrayBorrow', leaving
-- the remainder of the larger array on the top of the stack and the borrowed
-- sub-array just beneath it
implLLVMArrayBorrow ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w :> LLVMPointerType w)
  (ps :> LLVMPointerType w) ()
implLLVMArrayBorrow x ap sub_ap =
  implTryProveBVProps x (llvmArrayContainsArray ap sub_ap) >>>
  implSimplM Proxy (SImpl_LLVMArrayBorrow x ap sub_ap)

-- | Copy a sub-array from an array as per 'SImpl_LLVMArrayCopy'
implLLVMArrayCopy ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w :> LLVMPointerType w)
  (ps :> LLVMPointerType w) ()
implLLVMArrayCopy x ap sub_ap =
  implTryProveBVProps x (llvmArrayContainsArray ap sub_ap) >>>
  implSimplM Proxy (SImpl_LLVMArrayCopy x ap sub_ap)

-- | Return a borrowed sub-array to an array as per 'SImpl_LLVMArrayReturn',
-- where the borrowed array permission is just below the top of the stack and
-- the array it was borrowed from is on top of the stack.  Return the new array
-- permission after the return that is now on the top of the stack.
implLLVMArrayReturn ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w)
  (ps :> LLVMPointerType w :> LLVMPointerType w)
  (LLVMArrayPerm w)
implLLVMArrayReturn x ap ret_ap =
  implSimplM Proxy (SImpl_LLVMArrayReturn x ap ret_ap) >>>
  pure (llvmArrayRemBorrow (llvmSubArrayBorrow ap ret_ap) $
           llvmArrayAddArrayBorrows ap ret_ap)

-- | Add a borrow to an LLVM array permission, failing if that is not possible
-- because the borrow is not in range of the array. The permission that is
-- borrowed is left on top of the stack and returned as a return value.
implLLVMArrayBorrowBorrow ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayBorrow w ->
  ImplM vars s r (ps :> LLVMPointerType w :> LLVMPointerType w)
  (ps :> LLVMPointerType w) (ValuePerm (LLVMPointerType w))
implLLVMArrayBorrowBorrow x ap (FieldBorrow ix) =
  implLLVMArrayIndexBorrow x ap ix >>>= \(ap',field) ->
  let fld_p = ValPerm_Conj1 $ llvmArrayFieldToAtomicPerm field in
  implSwapM x fld_p x (ValPerm_LLVMArray ap') >>>
  pure fld_p
implLLVMArrayBorrowBorrow x ap b@(RangeBorrow _) =
  let p = permForLLVMArrayBorrow ap b
      ValPerm_Conj1 (Perm_LLVMArray sub_ap) = p
      ap' = llvmArrayAddBorrow b ap in
  implLLVMArrayBorrow x ap' sub_ap >>>
  implSwapM x p x (ValPerm_Conj1 $ Perm_LLVMArray ap') >>>
  pure p

-- | Return a borrow to an LLVM array permission, assuming the array is at the
-- top of the stack and the borrowed permission, which should be that returned
-- by 'permForLLVMArrayBorrow', is just below it
implLLVMArrayReturnBorrow ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayBorrow w ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w
                                            :> LLVMPointerType w) ()
implLLVMArrayReturnBorrow x ap (FieldBorrow ix) =
  implLLVMArrayIndexReturn x ap ix
implLLVMArrayReturnBorrow x ap b@(RangeBorrow _) =
  let ValPerm_Conj1 (Perm_LLVMArray ap_ret) = permForLLVMArrayBorrow ap b in
  implLLVMArrayReturn x ap ap_ret >>>
  pure ()


-- | Append to array permissions, assuming one ends where the other begins and
-- that they have the same stride and fields
implLLVMArrayAppend ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w
                                            :> LLVMPointerType w) ()
implLLVMArrayAppend x ap1 ap2 =
  implSimplM Proxy (SImpl_LLVMArrayAppend x ap1 ap2)


-- | Rearrange the order of the borrows in an array permission
implLLVMArrayRearrange ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> LLVMArrayPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()
implLLVMArrayRearrange x ap_in ap_out =
  implSimplM Proxy (SImpl_LLVMArrayRearrange x ap_in ap_out)

-- | Prove an empty array with length 0
implLLVMArrayEmpty ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w) ps ()
implLLVMArrayEmpty x ap = implSimplM Proxy (SImpl_LLVMArrayEmpty x ap)

-- | Prove an array that can be expressed as the conjunction of @N@ fields from
-- those @N@ fields, assuming a proof of those fields is on the top of the stack
implLLVMArrayOneCell :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                        ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
                        ImplM vars s r (ps :> LLVMPointerType w)
                        (ps :> LLVMPointerType w) ()
implLLVMArrayOneCell x ap =
  implSimplM Proxy (SImpl_LLVMArrayOneCell x ap)


-- | Prove the @memblock@ permission returned by @'llvmAtomicPermToBlock' p@
-- from a proof of @p@ on top of the stack, assuming it returned one
implIntroLLVMBlock :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                      ExprVar (LLVMPointerType w) ->
                      AtomicPerm (LLVMPointerType w) ->
                      ImplM vars s r (ps :> LLVMPointerType w)
                      (ps :> LLVMPointerType w) ()
implIntroLLVMBlock x (Perm_LLVMField fp) =
  implSimplM Proxy (SImpl_IntroLLVMBlockField x fp)
implIntroLLVMBlock x p@(Perm_LLVMArray ap)
  | isJust (llvmAtomicPermToBlock p) =
    implSimplM Proxy (SImpl_IntroLLVMBlockArray x ap)
implIntroLLVMBlock _ (Perm_LLVMBlock _bp) = pure ()
implIntroLLVMBlock _ _ = error "implIntroLLVMBlock: malformed permission"

-- | Prove a @memblock@ permission with a foldable named shape from its
-- unfolding, assuming that unfolding is on the top of the stack
implIntroLLVMBlockNamed :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                           ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
                           ImplM vars s r (ps :> LLVMPointerType w)
                           (ps :> LLVMPointerType w) ()
implIntroLLVMBlockNamed x bp
  | PExpr_NamedShape _ _ nmsh _ <- llvmBlockShape bp
  , TrueRepr <- namedShapeCanUnfoldRepr nmsh =
    implSimplM Proxy (SImpl_IntroLLVMBlockNamed x bp nmsh)
implIntroLLVMBlockNamed _ _ =
  error "implIntroLLVMBlockNamed: malformed permission"

-- | Eliminate a @memblock@ permission on the top of the stack, if possible,
-- otherwise fail
implElimLLVMBlock :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                     ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
                     ImplM vars s r (ps :> LLVMPointerType w)
                     (ps :> LLVMPointerType w) ()
implElimLLVMBlock x bp@(LLVMBlockPerm { llvmBlockShape = PExpr_EmptyShape }) =
  implSimplM Proxy (SImpl_ElimLLVMBlockToBytes x bp)
implElimLLVMBlock x bp
  | Just sh_len <- llvmShapeLength $ llvmBlockShape bp
  , bvLt sh_len $ llvmBlockLen bp =
    -- If the "natural" length of the shape of a memblock permission is smaller
    -- than its actual length, sequence with the empty shape and then eliminate
    implSimplM Proxy (SImpl_IntroLLVMBlockSeqEmpty x bp) >>>
    implSimplM Proxy (SImpl_ElimLLVMBlockSeq x bp PExpr_EmptyShape)
implElimLLVMBlock x bp@(LLVMBlockPerm { llvmBlockShape =
                                          PExpr_NamedShape rw l nmsh args })
  | TrueRepr <- namedShapeCanUnfoldRepr nmsh
  , Just sh' <- unfoldModalizeNamedShape rw l nmsh args =
    (if namedShapeIsRecursive nmsh
     then implSetRecRecurseLeftM else pure ()) >>>
    implSimplM Proxy (SImpl_ElimLLVMBlockNamed x bp nmsh) >>>
    implElimLLVMBlock x (bp { llvmBlockShape = sh' })
implElimLLVMBlock x bp@(LLVMBlockPerm { llvmBlockShape =
                                          PExpr_EqShape (PExpr_Var y) }) =
  -- For shape eqsh(y), prove y:block(sh) for some sh, apply
  -- SImpl_IntroLLVMBlockFromEq, and then recursively eliminate the resulting
  -- memblock permission
  mbVarsM () >>>= \mb_unit ->
  withExtVarsM (proveVarImplInt y $ mbCombine RL.typeCtxProxies $ flip fmap mb_unit $ const $
                nu $ \sh -> ValPerm_Conj1 $
                            Perm_LLVMBlockShape $ PExpr_Var sh) >>>= \(_, sh) ->
  let bp' = bp { llvmBlockShape = sh } in
  implSimplM Proxy (SImpl_IntroLLVMBlockFromEq x bp' y) >>>
  implElimLLVMBlock x bp'
implElimLLVMBlock x bp@(LLVMBlockPerm { llvmBlockShape =
                                          PExpr_PtrShape maybe_rw maybe_l sh })
  | Just len <- llvmShapeLength sh =
    let bp' = bp { llvmBlockLen = len, llvmBlockShape = sh } in
    implSimplM Proxy (SImpl_ElimLLVMBlockPtr x maybe_rw maybe_l bp')
    -- NOTE: no need to recurse in this case, because we have a normal pointer
    -- permission on x (even though its contents are a memblock permission)
implElimLLVMBlock x (LLVMBlockPerm { llvmBlockShape =
                                     PExpr_FieldShape (LLVMFieldShape p)
                                   , ..}) =
  implSimplM Proxy (SImpl_ElimLLVMBlockField x
                    (LLVMFieldPerm { llvmFieldRW = llvmBlockRW,
                                     llvmFieldLifetime = llvmBlockLifetime,
                                     llvmFieldOffset = llvmBlockOffset,
                                     llvmFieldContents = p })
                    llvmBlockLen)
implElimLLVMBlock x bp@(LLVMBlockPerm { llvmBlockShape =
                                          PExpr_ArrayShape _ _ _ }) =
  implSimplM Proxy (SImpl_ElimLLVMBlockArray x $ llvmArrayBlockToArrayPerm bp)
implElimLLVMBlock x bp@(LLVMBlockPerm { llvmBlockShape =
                                          PExpr_SeqShape sh1 sh2 })
  | isJust $ llvmShapeLength sh1 =
    implSimplM Proxy (SImpl_ElimLLVMBlockSeq
                      x (bp { llvmBlockShape = sh1 }) sh2)
implElimLLVMBlock x bp@(LLVMBlockPerm { llvmBlockShape =
                                        PExpr_OrShape sh1 sh2 }) =
  implSimplM Proxy (SImpl_ElimLLVMBlockOr x (bp { llvmBlockShape = sh1 }) sh2)
implElimLLVMBlock x bp@(LLVMBlockPerm { llvmBlockShape =
                                        PExpr_ExShape _mb_sh }) =
  implSimplM Proxy (SImpl_ElimLLVMBlockEx x bp)
implElimLLVMBlock _ bp =
  implTraceM (\i -> pretty "Could not eliminate permission" <+>
                    permPretty i (Perm_LLVMBlock bp)) >>>=
  implFailM

-- | Eliminate a @memblock@ permission on the top of the stack and recombine it,
-- if this is possible; otherwise fail
implElimPopLLVMBlock :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
                        ExprVar (LLVMPointerType w) -> LLVMBlockPerm w ->
                        ImplM vars s r ps (ps :> LLVMPointerType w) ()
implElimPopLLVMBlock x bp =
  implElimLLVMBlock x bp >>> getTopDistPerm x >>>= \p' -> recombinePerm x p'


----------------------------------------------------------------------
-- * Support for Proving Lifetimes Are Current
----------------------------------------------------------------------

-- | Build a 'LifetimeCurrentPerms' to prove that a lifetime @l@ is current in
-- the current permission set, failing if this is not possible
getLifetimeCurrentPerms :: NuMatchingAny1 r => PermExpr LifetimeType ->
                           ImplM vars s r ps ps (Some LifetimeCurrentPerms)
getLifetimeCurrentPerms PExpr_Always = pure $ Some AlwaysCurrentPerms
getLifetimeCurrentPerms (PExpr_Var l) =
  getPerm l >>= \case
    ValPerm_LOwned ps_in ps_out ->
      pure $ Some $ LOwnedCurrentPerms l ps_in ps_out
    ValPerm_LCurrent l' ->
      getLifetimeCurrentPerms l' >>= \some_cur_perms ->
      case some_cur_perms of
        Some cur_perms -> pure $ Some $ CurrentTransPerms cur_perms l
    _ ->
      implTraceM (\i -> pretty "Could not prove lifetime is current:" <+>
                        permPretty i l) >>=
      implFailM

-- | Prove the permissions represented by a 'LifetimeCurrentPerms'
proveLifetimeCurrent :: NuMatchingAny1 r => LifetimeCurrentPerms ps_l ->
                        ImplM vars s r (ps :++: ps_l) ps ()
proveLifetimeCurrent AlwaysCurrentPerms = pure ()
proveLifetimeCurrent (LOwnedCurrentPerms l ps_in ps_out) =
  implPushM l (ValPerm_LOwned ps_in ps_out)
proveLifetimeCurrent (CurrentTransPerms cur_perms l) =
  proveLifetimeCurrent cur_perms >>>
  let l' = lifetimeCurrentPermsLifetime cur_perms
      p_l_cur = ValPerm_LCurrent l' in
  implPushM l p_l_cur >>>
  implCopyM l p_l_cur >>>
  implPopM l p_l_cur


----------------------------------------------------------------------
-- * Recombining Permissions
----------------------------------------------------------------------

-- | Simplify an equality permission @x:eq(e)@ that we assume is on the top of
-- the stack by substituting any equality permissions on variables in @e@,
-- returning the resulting expression
simplEqPerm :: NuMatchingAny1 r => ExprVar a -> PermExpr a ->
               ImplM vars s r (as :> a) (as :> a) (PermExpr a)
simplEqPerm x e@(PExpr_Var y) =
  getPerm y >>= \case
  p@(ValPerm_Eq e') ->
    implPushM y p >>> implCopyM y p >>> implPopM y p >>>
    introCastM x y p >>> pure e'
  _ -> pure e
simplEqPerm x e@(PExpr_LLVMOffset y off) =
  getPerm y >>= \case
  p@(ValPerm_Eq e') ->
    implPushM y p >>> implCopyM y p >>> implPopM y p >>>
    castLLVMPtrM y p off x >>> pure (addLLVMOffset e' off)
  _ -> pure e
simplEqPerm _ e = pure e

-- | Recombine the permission @x:p@ on top of the stack back into the existing
-- permission for @x@
recombinePerm :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
                 ImplM vars s r as (as :> a) ()
recombinePerm x p = getPerm x >>>= \x_p -> recombinePermExpl x x_p p

-- | Recombine the permission @x:p@ on top of the stack back into the existing
-- permission @x_p@ for @x@, where @x_p@ is given explicitly as the first
-- permission argument and @p@ is the second
recombinePermExpl :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
                     ValuePerm a -> ImplM vars s r as (as :> a) ()
recombinePermExpl x x_p p =
  {-
  use implStatePPInfo >>>= \info ->
  tracePretty (string "recombinePerm" <+> permPretty info x
               </> permPretty info x_p </> string "<-"
               </> permPretty info p) $ -}
  recombinePerm' x x_p p

recombinePerm' :: NuMatchingAny1 r => ExprVar a -> ValuePerm a -> ValuePerm a ->
                  ImplM vars s r as (as :> a) ()
recombinePerm' x _ p@ValPerm_True = implDropM x p
recombinePerm' x ValPerm_True (ValPerm_Eq e) =
  simplEqPerm x e >>>= \e' ->  implPopM x (ValPerm_Eq e')
recombinePerm' x ValPerm_True p = implPopM x p
recombinePerm' x (ValPerm_Eq (PExpr_Var y)) _
  | y == x = error "recombinePerm: variable x has permission eq(x)!"
recombinePerm' x (ValPerm_Eq e1) p@(ValPerm_Eq e2)
  | e1 == e2 = implDropM x p
recombinePerm' x x_p@(ValPerm_Eq (PExpr_Var y)) p =
  implPushM x x_p >>> introEqCopyM x (PExpr_Var y) >>> implPopM x x_p >>>
  invertEqM x y >>> implSwapM x p y (ValPerm_Eq (PExpr_Var x)) >>>
  introCastM y x p >>> getPerm y >>>= \y_p -> recombinePermExpl y y_p p
recombinePerm' x x_p@(ValPerm_Eq (PExpr_LLVMOffset y off)) (ValPerm_Conj ps) =
  implPushM x x_p >>> introEqCopyM x (PExpr_LLVMOffset y off) >>>
  implPopM x x_p >>> implSimplM Proxy (SImpl_InvertLLVMOffsetEq x off y) >>>
  implSwapM x (ValPerm_Conj ps) y (ValPerm_Eq
                                   (PExpr_LLVMOffset x (bvNegate off))) >>>
  castLLVMPtrM x (ValPerm_Conj ps) (bvNegate off) y >>>
  getPerm y >>>= \y_p ->
  recombinePermExpl y y_p (ValPerm_Conj $ mapMaybe (offsetLLVMAtomicPerm off) ps)
recombinePerm' x p p'@(ValPerm_Eq _) =
  -- NOTE: we could handle this by swapping the stack with the variable perm and
  -- calling recombinePerm again, but this could potentially create permission
  -- equality cycles with, e.g., x:eq(y) * y:eq(x). Plus, we don't expect any
  -- functions or typed instructions to return equality permissions unless it is
  -- for a new, fresh variable, in which case the above cases will handle it
  implTraceM (\i ->
               pretty "recombinePerm: unexpected equality permission being recombined" <> softline <>
               permPretty i x <+> colon <+> permPretty i p <+>
               pretty "<-" <+> permPretty i p') >>>
  error "recombinePerm: unexpected equality permission being recombined"
recombinePerm' x x_p (ValPerm_Or _ _) =
  elimOrsExistsM x >>>= \p' -> recombinePermExpl x x_p p'
recombinePerm' x x_p (ValPerm_Exists _) =
  elimOrsExistsM x >>>= \p' -> recombinePermExpl x x_p p'
recombinePerm' x x_p@(ValPerm_Or _ _) p =
  implPushM x x_p >>> elimOrsExistsM x >>>= \x_p' ->
  implPopM x x_p' >>> recombinePermExpl x x_p' p
recombinePerm' x x_p@(ValPerm_Exists _) p =
  implPushM x x_p >>> elimOrsExistsM x >>>= \x_p' ->
  implPopM x x_p' >>> recombinePermExpl x x_p' p
recombinePerm' x (ValPerm_Conj x_ps) (ValPerm_Conj (p:ps)) =
  implExtractConjM x (p:ps) 0 >>>
  implSwapM x (ValPerm_Conj1 p) x (ValPerm_Conj ps) >>>
  recombinePermConj x x_ps p >>>= \x_ps' ->
  recombinePermExpl x (ValPerm_Conj x_ps') (ValPerm_Conj ps)
recombinePerm' x x_p (ValPerm_Named npn args off)
  | TrueRepr <- nameIsConjRepr npn =
    implNamedToConjM x npn args off >>>
    recombinePermExpl x x_p (ValPerm_Conj1 $ Perm_NamedConj npn args off)
recombinePerm' x _ p = implDropM x p

-- | Recombine a single conjuct @x:p@ on top of the stack back into the existing
-- conjuctive permission @x_p1 * ... * x_pn@ for @x@, returning the resulting
-- permission conjucts for @x@
recombinePermConj :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] ->
                     AtomicPerm a -> ImplM vars s r as (as :> a) [AtomicPerm a]

-- If p is a field read permission that is already in x_ps, drop it
recombinePermConj x x_ps p@(Perm_LLVMField fp)
  | Just (Perm_LLVMField fp') <-
      find (\case Perm_LLVMField fp' ->
                    bvEq (llvmFieldOffset fp') (llvmFieldOffset fp)
                  _ -> False) x_ps
  , PExpr_Read <- llvmFieldRW fp
  , PExpr_Read <- llvmFieldRW fp' =
    implDropM x (ValPerm_Conj1 p) >>>
    pure x_ps

-- If p is an is_llvmptr permission and x_ps already contains one, drop it
recombinePermConj x x_ps p@Perm_IsLLVMPtr
  | elem Perm_IsLLVMPtr x_ps =
    implDropM x (ValPerm_Conj1 p) >>>
    pure x_ps

-- If p is a field that was borrowed from an array, return it; i.e., if we are
-- returning x:ptr((rw,off+i*stride+j) |-> p) and x has a permission of the form
-- x:array(off,<len,*stride,fps,(i*stride+j):bs) where the jth element of fps
-- equals ptr((rw,j) |-> p), then remove (i*stride+j) from bs
recombinePermConj x x_ps (Perm_LLVMField fp)
  | (ap,i,ix):_ <-
      flip mapMaybe (zip x_ps [0::Int ..]) $
      \case (Perm_LLVMArray ap, i)
              | Just ix <- matchLLVMArrayField ap (llvmFieldOffset fp)
              , elem (FieldBorrow ix) (llvmArrayBorrows ap) ->
                Just (ap,i,ix)
            _ -> Nothing
  , LLVMArrayField fp == llvmArrayFieldWithOffset ap ix =
    implPushM x (ValPerm_Conj x_ps) >>> implExtractConjM x x_ps i >>>
    let x_ps' = deleteNth i x_ps in
    implPopM x (ValPerm_Conj x_ps') >>>
    implLLVMArrayIndexReturn x ap ix >>>
    recombinePermConj x x_ps' (Perm_LLVMArray $
                               llvmArrayRemBorrow (FieldBorrow ix) ap)

-- If p is an array that was borrowed from some other array, return it
recombinePermConj x x_ps (Perm_LLVMArray ap)
  | (ap_bigger,i):_ <-
      flip mapMaybe (zip x_ps [0::Int ..])
      (\case (Perm_LLVMArray ap', i)
               | isJust (llvmArrayIsOffsetArray ap' ap) &&
                 elem (llvmSubArrayBorrow ap' ap) (llvmArrayBorrows ap') &&
                 llvmArrayStride ap' == llvmArrayStride ap &&
                 llvmArrayFields ap' == llvmArrayFields ap ->
                 return (ap', i)
             _ -> Nothing) =
    implPushM x (ValPerm_Conj x_ps) >>> implExtractConjM x x_ps i >>>
    let x_ps' = deleteNth i x_ps in
    implPopM x (ValPerm_Conj x_ps') >>>
    implLLVMArrayReturn x ap_bigger ap >>>= \ap_bigger' ->
    recombinePermConj x x_ps' (Perm_LLVMArray ap_bigger')

-- Default case: insert p at the end of the x_ps
recombinePermConj x x_ps p =
  implPushM x (ValPerm_Conj x_ps) >>>
  implInsertConjM x p x_ps (length x_ps) >>>
  implPopM x (ValPerm_Conj (x_ps ++ [p])) >>>
  pure (x_ps ++ [p])


-- | Recombine the permissions on the stack back into the permission set
recombinePerms :: NuMatchingAny1 r => DistPerms ps -> ImplM vars s r RNil ps ()
recombinePerms DistPermsNil = pure ()
recombinePerms (DistPermsCons ps' x p) =
  recombinePerm x p >>> recombinePerms ps'

-- | Recombine some of the permissions on the stack back into the permission set
recombinePermsPartial :: NuMatchingAny1 r => f ps -> DistPerms ps' ->
                         ImplM vars s r ps (ps :++: ps') ()
recombinePermsPartial _ DistPermsNil = pure ()
recombinePermsPartial ps (DistPermsCons ps' x p) =
  recombinePerm x p >>> recombinePermsPartial ps ps'

-- | Recombine the permissions for a 'LifetimeCurrentPerms' list
recombineLifetimeCurrentPerms :: NuMatchingAny1 r =>
                                 LifetimeCurrentPerms ps_l ->
                                 ImplM vars s r ps (ps :++: ps_l) ()
recombineLifetimeCurrentPerms AlwaysCurrentPerms = pure ()
recombineLifetimeCurrentPerms (LOwnedCurrentPerms l ps_in ps_out) =
  recombinePermExpl l ValPerm_True (ValPerm_LOwned ps_in ps_out)
recombineLifetimeCurrentPerms (CurrentTransPerms cur_perms l) =
  implDropM l (ValPerm_LCurrent $ lifetimeCurrentPermsLifetime cur_perms) >>>
  recombineLifetimeCurrentPerms cur_perms


----------------------------------------------------------------------
-- * Proving Equalities
----------------------------------------------------------------------

-- | Fail when trying to prove an equality
proveEqFail :: (NuMatchingAny1 r, PermPretty (f a)) => f a -> Mb vars (f a) ->
               ImplM vars s r ps ps any
proveEqFail e mb_e =
  implTraceM (\i ->
               sep [pretty "proveEq" <> colon <+> pretty "Could not prove",
                    sep [permPretty i e <+>
                         pretty "=" <+> permPretty i mb_e]]) >>>=
  implFailM

-- | Typeclass for the generic function that tries to extend the current partial
-- substitution to unify an expression with an expression pattern and returns a
-- proof of the equality on success
class ProveEq a where
  proveEq :: NuMatchingAny1 r => a -> Mb vars a ->
             ImplM vars s r ps ps (SomeEqProof a)

instance (Eq a, Eq b, ProveEq a, ProveEq b, Substable PermSubst a Identity,
          Substable PermSubst b Identity) => ProveEq (a,b) where
  proveEq (a,b) mb_ab =
    do eqp1 <- proveEq a (fmap fst mb_ab)
       eqp2 <- proveEq b (fmap snd mb_ab)
       pure ((,) <$> eqp1 <*> eqp2)

instance (Eq a, Eq b, Eq c, ProveEq a, ProveEq b, ProveEq c,
          Substable PermSubst a Identity,
          Substable PermSubst b Identity,
          Substable PermSubst c Identity) => ProveEq (a,b,c) where
  proveEq (a,b,c) mb_abc =
    do eqp1 <- proveEq a (fmap (\(x,_,_) -> x) mb_abc)
       eqp2 <- proveEq b (fmap (\(_,y,_) -> y) mb_abc)
       eqp3 <- proveEq c (fmap (\(_,_,z) -> z) mb_abc)
       pure ((,,) <$> eqp1 <*> eqp2 <*> eqp3)

instance ProveEq (PermExpr a) where
  proveEq e mb_e =
    do psubst <- getPSubst
       proveEqH psubst e mb_e

instance ProveEq (LLVMFramePerm w) where
  proveEq [] [nuP| [] |] = pure $ SomeEqProofRefl []
  proveEq ((e,i):fperms) [nuP| ((mb_e,mb_i)):mb_fperms |]
    | mbLift mb_i == i =
      do eqp1 <- proveEq e mb_e
         eqp2 <- proveEq fperms mb_fperms
         pure (liftA2 (\x y -> (x,i):y) eqp1 eqp2)
  proveEq perms mb = proveEqFail perms mb

instance ProveEq (LLVMBlockPerm w) where
  proveEq bp mb_bp =
    do eqp_rw  <- proveEq (llvmBlockRW       bp) (fmap llvmBlockRW       mb_bp)
       eqp_l   <- proveEq (llvmBlockLifetime bp) (fmap llvmBlockLifetime mb_bp)
       eqp_off <- proveEq (llvmBlockOffset   bp) (fmap llvmBlockOffset   mb_bp)
       eqp_len <- proveEq (llvmBlockLen      bp) (fmap llvmBlockLen      mb_bp)
       eqp_sh  <- proveEq (llvmBlockShape    bp) (fmap llvmBlockShape    mb_bp)
       pure (LLVMBlockPerm <$>
              eqp_rw <*> eqp_l <*> eqp_off <*> eqp_len <*> eqp_sh)


-- | Substitute any equality permissions for the variables in an expression,
-- returning a proof that the input expression equals the output. Unlike
-- 'getEqualsExpr', this does not eliminate any permissions, because it is used
-- by 'proveEq' to instantiate existential variables, and we do not want to have
-- to eliminate perms just to set @z=e@.
--
-- FIXME: maybe 'getEqualsExpr' should also not eliminate permissions?
substEqsWithProof :: (AbstractVars a, FreeVars a,
                      Substable PermSubst a Identity, NuMatchingAny1 r) =>
                     a -> ImplM vars s r ps ps (SomeEqProof a)
substEqsWithProof a =
  do var_ps <- use (implStatePerms . varPermMap)
     pure (someEqProofFromSubst var_ps a)


-- | The main work horse for 'proveEq' on expressions
proveEqH :: NuMatchingAny1 r => PartialSubst vars -> PermExpr a ->
            Mb vars (PermExpr a) ->
            ImplM vars s r ps ps (SomeEqProof (PermExpr a))
proveEqH psubst e mb_e = case (e, mbMatch mb_e) of

  -- If the RHS is an unset variable z, simplify e using any available equality
  -- proofs to some e' and set z=e'
  (_, [nuMP| PExpr_Var z |])
    | Left memb <- mbNameBoundP z
    , Nothing <- psubstLookup psubst memb ->
      substEqsWithProof e >>= \eqp ->
      setVarM memb (someEqProofRHS eqp) >>> pure eqp

  -- If the RHS is a set variable, substitute for it and recurse
  (_, [nuMP| PExpr_Var z |])
    | Left memb <- mbNameBoundP z
    , Just e' <- psubstLookup psubst memb ->
      proveEqH psubst e (fmap (const e') z)

  -- If the RHS = LHS, do a proof by reflexivity
  _ | Just e' <- partialSubst psubst mb_e
    , e == e' -> pure (SomeEqProofRefl e)

  -- To prove x=y, try to see if either side has an eq permission, if necessary by
  -- eliminating compound permissions, and proceed by transitivity if possible
  (PExpr_Var x, [nuMP| PExpr_Var mb_y |])
    | Right y <- mbNameBoundP mb_y ->
      getPerm x >>= \x_p ->
      getPerm y >>= \y_p ->
      case (x_p, y_p) of
        (ValPerm_Eq e', _) ->
          -- If we have x:eq(e'), prove e' = y and apply transitivity
          proveEq e' mb_e >>= \some_eqp ->
          pure $ someEqProofTrans (someEqProofPerm x e' True) some_eqp
        (_, ValPerm_Eq e') ->
          -- If we have y:eq(e'), prove x = e' and apply transitivity
          proveEq e (fmap (const e') mb_e) >>= \some_eqp ->
          pure $ someEqProofTrans some_eqp (someEqProofPerm y e' False)
        (_, _) ->
          -- If we have no equality perms, eliminate perms on x and y to see if we
          -- can get one; if so, recurse, and otherwise, raise an error
          getVarEqPerm x >>= \case
          Just _ -> proveEqH psubst e mb_e
          Nothing -> getVarEqPerm y >>= \case
            Just _ -> proveEqH psubst e mb_e
            Nothing -> proveEqFail e mb_e

  -- To prove x=e, try to see if x:eq(e') and proceed by transitivity
  (PExpr_Var x, _) ->
    getVarEqPerm x >>= \case
    Just e' ->
      proveEq e' mb_e >>= \eqp2 ->
      pure (someEqProofTrans (someEqProofPerm x e' True) eqp2)
    Nothing -> proveEqFail e mb_e

  -- To prove e=x, try to see if x:eq(e') and proceed by transitivity
  (_, [nuMP| PExpr_Var z |])
    | Right x <- mbNameBoundP z ->
      getVarEqPerm x >>= \case
        Just e' ->
          proveEq e (fmap (const e') mb_e) >>= \eqp ->
          pure (someEqProofTrans eqp (someEqProofPerm x e' False))
        Nothing -> proveEqFail e mb_e

  -- FIXME: if proving word(e1)=word(e2) for ground e2, we could add an assertion
  -- that e1=e2 using a BVProp_Eq

  -- Prove word(e1) = word(e2) by proving e1=e2
  (PExpr_LLVMWord e', [nuMP| PExpr_LLVMWord mb_e' |]) ->
    fmap PExpr_LLVMWord <$> proveEqH psubst e' mb_e'

  -- Prove e = N*z + M where e - M is a multiple of N by setting z = (e-M)/N
  (_, [nuMP| PExpr_BV [BVFactor (BV.BV mb_n) z] (BV.BV mb_m) |])
    | Left memb <- mbNameBoundP z
    , Nothing <- psubstLookup psubst memb
    , bvIsZero (bvMod (bvSub e (bvInt $ mbLift mb_m)) (mbLift mb_n)) ->
      setVarM memb (bvDiv (bvSub e (bvInt $ mbLift mb_m)) (mbLift mb_n)) >>>
      pure (SomeEqProofRefl e)

  -- FIXME: add cases to prove struct(es1)=struct(es2)

  -- Otherwise give up!
  _ -> proveEqFail e mb_e


-- | Build a proof on the top of the stack that @x:eq(e)@. Assume that all @x@
-- permissions are on the top of the stack and given by argument @p@, and pop
-- them back to the primary permission for @x@ at the end of the proof.
proveVarEq :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
              Mb vars (PermExpr a) -> ImplM vars s r (ps :> a) (ps :> a) ()
proveVarEq x p mb_e =
  implPopM x p >>> proveEq (PExpr_Var x) mb_e >>>= \some_eqp ->
  introEqReflM x >>> implCastPermM x (fmap ValPerm_Eq some_eqp)

-- | Prove that @e1=e2@ using 'proveEq' and then cast permission @x:(f e1)@,
-- which is on top of the stack, to @x:(f e2)@
proveEqCast :: (ProveEq a, NuMatchingAny1 r) => ExprVar b ->
               (a -> ValuePerm b) -> a -> Mb vars a ->
               ImplM vars s r (ps :> b) (ps :> b) ()
proveEqCast x f e mb_e =
  do some_eqp <- proveEq e mb_e
     implCastPermM x (fmap f some_eqp)


----------------------------------------------------------------------
-- * Lifetime Proofs
----------------------------------------------------------------------

-- | Take a variable @x@, a lifetime functor @F@, a lifetime @l@, and a desired
-- lifetime-in-bindings @mb_l@, assuming the permission @x:F<l>@ is on the top
-- of the stack. Try to coerce the permission to @x:F<mb_l>@, possibly by
-- instantiating existential variables in @mb_l@ and/or splitting lifetimes.
proveVarLifetimeFunctor ::
  (KnownRepr TypeRepr a, NuMatchingAny1 r) =>
  ExprVar a -> LifetimeFunctor args a -> PermExprs args ->
  PermExpr LifetimeType -> Mb vars (PermExpr LifetimeType) ->
  ImplM vars s r (ps :> a) (ps :> a) ()
proveVarLifetimeFunctor x f args l mb_l =
  do psubst <- getPSubst
     proveVarLifetimeFunctor' x f args l mb_l psubst

-- | The main workhorse for 'proveVarLifetimeFunctor'
proveVarLifetimeFunctor' ::
  (KnownRepr TypeRepr a, NuMatchingAny1 r) =>
  ExprVar a -> LifetimeFunctor args a -> PermExprs args ->
  PermExpr LifetimeType -> Mb vars (PermExpr LifetimeType) ->
  PartialSubst vars ->
  ImplM vars s r (ps :> a) (ps :> a) ()
proveVarLifetimeFunctor' x f args l mb_l psubst = case mbMatch mb_l of

  -- If mb_l is an unset evar, set mb_l = l and return
  [nuMP| PExpr_Var mb_z |]
    | Left memb <- mbNameBoundP mb_z
    , Nothing <- psubstLookup psubst memb ->
      setVarM memb l

  -- If mb_l is a set evar, substitute for it and recurse
  [nuMP| PExpr_Var mb_z |]
    | Left memb <- mbNameBoundP mb_z
    , Just l2 <- psubstLookup psubst memb ->
      proveVarLifetimeFunctor' x f args l (fmap (const l2) mb_z) psubst

  -- If mb_l==l, we are done
  _ | mbLift $ fmap (== l) mb_l ->
      pure ()

  -- If mb_l is a free variable l2 /= l, we need to split or weaken the lifetime
  [nuMP| PExpr_Var mb_z |]
    | Right l2 <- mbNameBoundP mb_z ->
      getPerm l2 >>= \case

        -- If we have l2:lowned ps, prove l:[l2]lcurrent * l2:lowned ps and then
        -- split the lifetime
        ValPerm_LOwned ps_in ps_out ->
          let (l',l'_p) = lcurrentPerm l l2 in
          proveVarImplInt l' (fmap (const l'_p) mb_z) >>>
          implPushM l2 (ValPerm_LOwned ps_in ps_out) >>>
          implSplitLifetimeM x f args l l2 ps_in ps_out

        -- Otherwise, prove l:[l2]lcurrent and weaken the lifetime
        _ ->
          let (l',l'_p) = lcurrentPerm l l2 in
          proveVarImplInt l' (fmap (const l'_p) mb_z) >>>
          implSimplM Proxy (SImpl_WeakenLifetime x f args l l2)

  -- Otherwise, fail; this should only include the case where the RHS is always
  -- but the LHS is not, which we cannot do anything with
  _ ->
    implFailVarM "proveVarLifetimeFunctor" x (ltFuncApply f args l)
    (fmap (ltFuncApply f args) mb_l)


----------------------------------------------------------------------
-- * Solving for Permission List Implications
----------------------------------------------------------------------

-- | A sequence of permissions in bindings that need to be proved
type NeededPerms vars = Some (RAssign (Compose (Mb vars) VarAndPerm))

-- | Convert a 'NeededPerms' list to an 'ExDistPerms'
neededPermsToExDistPerms :: RAssign prx vars ->
                            RAssign (Compose (Mb vars) VarAndPerm) ps ->
                            Mb vars (DistPerms ps)
neededPermsToExDistPerms vars MNil = nuMulti (RL.map (\_-> Proxy) vars) (const MNil)
neededPermsToExDistPerms vars (ps :>: Compose mb_vap) =
  mbMap2 (:>:) (neededPermsToExDistPerms vars ps) mb_vap

-- | A single needed permission
neededPerms1 :: Mb vars (ExprVar a) -> Mb vars (ValuePerm a) -> NeededPerms vars
neededPerms1 mb_x mb_p = Some (MNil :>: Compose (mbMap2 VarAndPerm mb_x mb_p))

-- | If the second argument is an unset lifetime variable, set it to the first,
-- otherwise do nothing
tryUnifyLifetimes :: PermExpr LifetimeType -> Mb vars (PermExpr LifetimeType) ->
                     ImplM vars s r ps ps ()
tryUnifyLifetimes l mb_l = case mbMatch mb_l of
  [nuMP| PExpr_Var mb_l' |]
    | Left memb <- mbNameBoundP mb_l' ->
      do psubst <- getPSubst
         case psubstLookup psubst memb of
           Nothing -> setVarM memb l
           _ -> pure ()
  _ -> pure ()

-- | Find all the permissions that need to be added to the given list of
-- permissions to prove the given block permission
solveForPermListImplBlock :: (NuMatchingAny1 r, 1 <= w, KnownNat w) =>
                             LOwnedPerms ps_l ->
                             ExprVar (LLVMPointerType w) ->
                             Mb vars (LLVMBlockPerm w) ->
                             ImplM vars s r ps ps (NeededPerms vars)

-- If the LHS is empty, return the input block permission
solveForPermListImplBlock MNil x mb_bp =
  pure (neededPerms1 (fmap (const x) mb_bp) (fmap ValPerm_LLVMBlock mb_bp))

-- If the LHS starts with a field permission, treat it like a block permission
solveForPermListImplBlock (ps_l :>: LOwnedPermField e fp_l) x mb_bp =
  solveForPermListImplBlock
  (ps_l :>: LOwnedPermBlock e (llvmFieldPermToBlock fp_l)) x mb_bp

-- If the LHS starts with a block permission bp', remove the range of bp' from
-- the required bp and recurse on the results, setting the lifetime of our block
-- permission to that of bp' if it is not already set
solveForPermListImplBlock (ps_l :>: LOwnedPermBlock (PExpr_Var y) bp_l) x mb_bp
  | Just Refl <- testEquality x y
  , rng_l <- llvmBlockRange bp_l
  , [nuMP| Just mb_bps |] <- mbMatch $ fmap (remLLVMBLockPermRange rng_l) mb_bp =
    tryUnifyLifetimes (llvmBlockLifetime bp_l) (fmap llvmBlockLifetime mb_bp) >>>
    concatSomeRAssign <$> mapM (solveForPermListImplBlock ps_l x) (mbList mb_bps)

-- Otherwise, recurse on the tail of the permission list
solveForPermListImplBlock (ps_l :>: _) x mb_bp =
  solveForPermListImplBlock ps_l x mb_bp


-- | Determine what additional permissions from the variable permissions, if
-- any, would be needed to prove one list of permissions implies another. Also
-- instantiate any existential variables as needed for the implication. This is
-- just a "best guess", so just do nothing and return if nothing can be done.
solveForPermListImpl :: NuMatchingAny1 r => LOwnedPerms ps_l ->
                        Mb vars (LOwnedPerms ps_r) ->
                        ImplM vars s r ps ps (NeededPerms vars)
solveForPermListImpl ps_l mb_ps = case mbMatch mb_ps of

  -- If the RHS is empty, we are done
  [nuMP| MNil |] ->
    pure (Some MNil)

  -- If the RHS starts with a field perm, convert to a block perm and call
  -- solveForPermListImplBlock
  [nuMP| mb_ps_r :>: LOwnedPermField (PExpr_Var mb_x) mb_fp |]
    | Right x <- mbNameBoundP mb_x
    , mb_bp <- fmap llvmFieldPermToBlock mb_fp ->
      do needed1 <- solveForPermListImplBlock ps_l x mb_bp
         needed2 <- solveForPermListImpl ps_l mb_ps_r
         pure (apSomeRAssign needed1 needed2)

  -- If the RHS starts with a block perm, call solveForPermListImplBlock
  [nuMP| mb_ps_r :>: LOwnedPermBlock (PExpr_Var mb_x) mb_bp |]
    | Right x <- mbNameBoundP mb_x ->
      do needed1 <- solveForPermListImplBlock ps_l x mb_bp
         needed2 <- solveForPermListImpl ps_l mb_ps_r
         pure (apSomeRAssign needed1 needed2)

  -- If the RHS is an lowned perm that is in the LHS, return nothing
  --
  -- FIXME HERE: recursively call solveForPermListImpl on the the lists of
  -- permissions in the lifetimes
  [nuMP| mb_ps_r :>: LOwnedPermLifetime (PExpr_Var mb_l) _ _ |]
    | Right l <- mbNameBoundP mb_l
    , RL.foldr (\lop rest ->
                 case lop of
                   LOwnedPermLifetime (PExpr_Var l') _ _
                     | l == l' -> True
                   _ -> rest) False ps_l ->
      solveForPermListImpl ps_l mb_ps_r

  -- If the RHS is an lowned perm not in the LHS, return the RHS
  [nuMP| mb_ps_r :>: LOwnedPermLifetime (PExpr_Var mb_l) mb_ps_in mb_ps_out |] ->
    apSomeRAssign (neededPerms1 mb_l (mbMap2 ValPerm_LOwned mb_ps_in mb_ps_out)) <$>
    solveForPermListImpl ps_l mb_ps_r

  -- Otherwise, we don't know what to do, so do nothing and return
  _ ->
    pure (Some MNil)

concatSomeRAssign :: [Some (RAssign f)] -> Some (RAssign f)
concatSomeRAssign = foldl apSomeRAssign (Some MNil) 
-- foldl is intentional, appending RAssign matches on the second argument

apSomeRAssign :: Some (RAssign f) -> Some (RAssign f) -> Some (RAssign f)
apSomeRAssign (Some x) (Some y) = Some (RL.append x y)

----------------------------------------------------------------------
-- * Proving Field Permissions
----------------------------------------------------------------------

-- | Prove an LLVM field permission @x:ptr((rw,off) |-> p)@ from permission @pi@
-- assuming that the the current permissions @x:(p1 * ... *pn)@ for @x@ are on
-- the top of the stack, and ensuring that any remaining permissions for @x@ get
-- popped back to the primary permissions for @x@
proveVarLLVMField ::
  (1 <= w, KnownNat w, 1 <= sz, KnownNat sz, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> [AtomicPerm (LLVMPointerType w)] -> Int ->
  PermExpr (BVType w) -> Mb vars (LLVMFieldPerm w sz) ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()

-- Special case: if the LHS is a memblock perm, unfold it and prove again
proveVarLLVMField x ps i _ mb_fp
  | Perm_LLVMBlock bp <- ps!!i =
    implExtractConjM x ps i >>> implPopM x (ValPerm_Conj $ deleteNth i ps) >>>
    implElimPopLLVMBlock x bp >>>
    proveVarImplInt x (fmap (ValPerm_Conj1 . Perm_LLVMField) mb_fp)

proveVarLLVMField x ps i off mb_fp =
  (if i < length ps then pure () else
     error "proveVarLLVMField: index too large") >>>= \() ->
  implExtractConjM x ps i >>>
  let ps_rem = deleteNth i ps in
  implPopM x (ValPerm_Conj ps_rem) >>>
  getPSubst >>>= \psubst ->
  extractNeededLLVMFieldPerm x (ps!!i) off psubst mb_fp >>>= \(fp,maybe_p_rem) ->
  (case maybe_p_rem of
      Just p_rem ->
        implPushM x (ValPerm_Conj ps_rem) >>>
        implInsertConjM x p_rem ps_rem i >>>
        implPopM x (ValPerm_Conj (take i ps_rem ++ [p_rem] ++ drop i ps_rem))
      Nothing -> implDropM x ValPerm_True) >>>
  proveVarLLVMFieldFromField x fp off mb_fp


-- | Prove an LLVM field permission from another one that is on the top of the
-- stack, by casting the offset, changing the lifetime if needed, and proving
-- the contents
proveVarLLVMFieldFromField ::
  (1 <= w, KnownNat w, 1 <= sz, KnownNat sz, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> LLVMFieldPerm w sz ->
  PermExpr (BVType w) -> Mb vars (LLVMFieldPerm w sz) ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()
proveVarLLVMFieldFromField x fp off' mb_fp =
  -- Step 1: make sure to have a variable for the contents
  implElimLLVMFieldContentsM x fp >>>= \y ->
  let fp' = fp { llvmFieldContents = ValPerm_Eq (PExpr_Var y) } in

  -- Step 2: cast the field offset to off' if necessary
  (if bvEq (llvmFieldOffset fp') off' then
     pure fp'
   else
     implTryProveBVProp x (BVProp_Eq (llvmFieldOffset fp') off') >>>
     implSimplM Proxy (SImpl_CastLLVMFieldOffset x fp' off') >>>
     pure (fp' { llvmFieldOffset = off' })) >>>= \fp'' ->

  -- Step 3: prove the contents
  proveVarImplInt y (fmap llvmFieldContents mb_fp) >>>
  partialSubstForceM (fmap llvmFieldContents mb_fp)
  "proveVarLLVMFieldFromField" >>>= \p_y ->
  let fp''' = fp'' { llvmFieldContents = p_y } in
  introLLVMFieldContentsM x y fp''' >>>

  -- Step 4: change the lifetime if needed. This is done after proving the
  -- contents, so that, if we need to split the lifetime, we don't split the
  -- lifetime of a pointer permission with eq(y) permissions, as that would
  -- require the pointer to be constant until the end of the new lifetime.
  let (f, args) = fieldToLTFunc fp''' in
  proveVarLifetimeFunctor x f args (llvmFieldLifetime fp''') (fmap
                                                              llvmFieldLifetime
                                                              mb_fp)


-- | Extract an LLVM field permission from the given atomic permission, leaving
-- as much of the original atomic permission as possible on the top of the stack
-- (which could be none of it, i.e., @true@). At the end of this function, the
-- top of the stack should look like
--
-- > x:ptr((rw,off) -> p) * x:rem
--
-- where @rem@ is the remainder of the input atomic permission, which is either
-- a single atomic permission or @true@. The field permission and remaining
-- atomic permission (if any) are the return values of this function.
extractNeededLLVMFieldPerm ::
  (1 <= w, KnownNat w, 1 <= sz, KnownNat sz, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> AtomicPerm (LLVMPointerType w) ->
  PermExpr (BVType w) -> PartialSubst vars -> Mb vars (LLVMFieldPerm w sz) ->
  ImplM vars s r (ps :> LLVMPointerType w :> LLVMPointerType w)
  (ps :> LLVMPointerType w)
  (LLVMFieldPerm w sz, Maybe (AtomicPerm (LLVMPointerType w)))

-- If proving x:ptr((rw,off) |-> p) |- x:ptr((z,off') |-> p') for an RWModality
-- variable z, set z = rw and recurse
extractNeededLLVMFieldPerm x p@(Perm_LLVMField fp) off' psubst mb_fp
  | Just Refl <- testEquality (llvmFieldSize fp) (mbLift $
                                                  fmap llvmFieldSize mb_fp)
  , [nuMP| PExpr_Var z |] <- mbMatch $ fmap llvmFieldRW mb_fp
  , Left memb <- mbNameBoundP z
  , Nothing <- psubstLookup psubst memb =
    setVarM memb (llvmFieldRW fp) >>>
    extractNeededLLVMFieldPerm x p off' psubst
    (fmap (\fp' -> fp' { llvmFieldRW = llvmFieldRW fp }) mb_fp)

-- If proving x:ptr((rw,off) |-> p) |- x:ptr((z,off') |-> p') where z is
-- defined, substitute for z and recurse
extractNeededLLVMFieldPerm x p@(Perm_LLVMField fp) off' psubst mb_fp
  | Just Refl <- testEquality (llvmFieldSize fp) (mbLift $
                                                  fmap llvmFieldSize mb_fp)
  , [nuMP| PExpr_Var z |] <- mbMatch $ fmap llvmFieldRW mb_fp
  , Left memb <- mbNameBoundP z
  , Just rw <- psubstLookup psubst memb =
    extractNeededLLVMFieldPerm x p off' psubst
    (fmap (\fp' -> fp' { llvmFieldRW = rw }) mb_fp)

-- If proving x:ptr((R,off) |-> p) |- x:ptr((R,off') |-> p'), just copy the read
-- permission
extractNeededLLVMFieldPerm x (Perm_LLVMField fp) _ _ mb_fp
  | Just Refl <- testEquality (llvmFieldSize fp) (mbLift $
                                                  fmap llvmFieldSize mb_fp)
  , PExpr_Read <- llvmFieldRW fp
  , [nuMP| PExpr_Read |] <- mbMatch $ fmap llvmFieldRW mb_fp
  = implCopyConjM x [Perm_LLVMField fp] 0 >>>
    pure (fp, Just (Perm_LLVMField fp))

-- Cannot prove x:ptr((rw,off) |-> p) |- x:ptr((W,off') |-> p') if rw is not W,
-- so fail
extractNeededLLVMFieldPerm x ap@(Perm_LLVMField fp) _ _ mb_fp
  | Just Refl <- testEquality (llvmFieldSize fp) (mbLift $
                                                  fmap llvmFieldSize mb_fp)
  , PExpr_Write /= llvmFieldRW fp
  , [nuMP| PExpr_Write |] <- mbMatch $ fmap llvmFieldRW mb_fp
  = implFailVarM "extractNeededLLVMFieldPerm" x (ValPerm_Conj1 $ ap)
    (fmap (ValPerm_Conj1 . Perm_LLVMField) mb_fp)

-- If proving x:[l1]ptr((rw,off) |-> p) |- x:[l2]ptr((R,off') |-> p') for rw not
-- equal to R (i.e., equal to W or to a variable), demote rw to R and copy it
extractNeededLLVMFieldPerm x (Perm_LLVMField fp) _ _ mb_fp
  | Just Refl <- testEquality (llvmFieldSize fp) (mbLift $
                                                  fmap llvmFieldSize mb_fp)
  , PExpr_Read /= llvmFieldRW fp
  , [nuMP| PExpr_Read |] <- mbMatch $ fmap llvmFieldRW mb_fp
  = let fp' = fp in
    implSimplM Proxy (SImpl_DemoteLLVMFieldRW x fp') >>>
    let fp'' = fp' { llvmFieldRW = PExpr_Read } in
    implCopyConjM x [Perm_LLVMField fp''] 0 >>>
    pure (fp'', Just (Perm_LLVMField fp''))

-- If proving x:ptr((rw,off) |-> p) |- x:ptr((rw,off') |-> p') for any other
-- case, just push a true permission, because there is no remaining permission
extractNeededLLVMFieldPerm x (Perm_LLVMField fp) _ _ mb_fp
  | Just Refl <- testEquality (llvmFieldSize fp) (mbLift $
                                                  fmap llvmFieldSize mb_fp)
  , mbLift (fmap ((llvmFieldRW fp ==) . llvmFieldRW) mb_fp)
  = introConjM x >>> pure (fp, Nothing)

-- If proving x:array(off,<len,*stride,fps,bs) |- x:ptr((R,off) |-> p) such that
-- off=i*stride+j and the jth field of the ith index of the array is of the
-- right size and is a read containing only copyable permissions, copy that
-- field
extractNeededLLVMFieldPerm x (Perm_LLVMArray ap) off' _ mb_fp
  | Just ix <- matchLLVMArrayField ap off'
  , LLVMArrayField fp <- llvmArrayFieldWithOffset ap ix
  , Just Refl <- testEquality (llvmFieldSize fp) (mbLift $
                                                  fmap llvmFieldSize mb_fp)
  , PExpr_Read <- llvmFieldRW fp
  , permIsCopyable (llvmFieldContents fp)
  , [nuMP| PExpr_Read |] <- mbMatch $ fmap llvmFieldRW mb_fp =
    implLLVMArrayIndexCopy x ap ix >>>
    pure (fp, Just (Perm_LLVMArray ap))

-- If proving x:array(off,<len,*stride,fps,bs) |- x:ptr((rw,off) |-> p) such
-- that off=i*stride+j and the corresponding array field is of the right size in
-- any other case, borrow that field
extractNeededLLVMFieldPerm x (Perm_LLVMArray ap) off' psubst mb_fp
  | Just ix <- matchLLVMArrayField ap off'
  , LLVMArrayField fp <- llvmArrayFieldWithOffset ap ix
  , Just Refl <- testEquality (llvmFieldSize fp) (mbLift $
                                                  fmap llvmFieldSize mb_fp) =
    implLLVMArrayIndexBorrow x ap ix >>>= \(ap', _) ->
    implSwapM x (ValPerm_Conj1 $ Perm_LLVMField fp) x (ValPerm_Conj1 $
                                                       Perm_LLVMArray ap') >>>
    extractNeededLLVMFieldPerm x (Perm_LLVMField fp) off' psubst mb_fp >>>=
    \(fp', maybe_p_rem) ->
    -- NOTE: it is safe to just drop the remaining permission on the stack,
    -- because it is either Nothing (for a write) or a copy of the field
    -- permission (for a read)
    implDropM x (maybe ValPerm_True ValPerm_Conj1 maybe_p_rem) >>>
    implSwapM x (ValPerm_Conj1 $
                 Perm_LLVMArray ap') x (ValPerm_Conj1 $ Perm_LLVMField fp) >>>
    pure (fp', Just (Perm_LLVMArray ap'))

-- If proving x:array(off,<len,*stride,fps,bs) |- x:ptr((rw,off) |-> p) such
-- that off=i*stride+j but the corresponding array field is of a smaller size,
-- borrow a sub-array for the correct size and cast it to a field permission
extractNeededLLVMFieldPerm x (Perm_LLVMArray ap) off' _ mb_fp
  | stride_bits <- llvmArrayStrideBits ap
  , sz <- mbLift $ fmap llvmFieldSize mb_fp
  , len <- bvInt (intValue sz `div` stride_bits)
  , sub_ap <- ap { llvmArrayOffset = off', llvmArrayLen = len,
                   llvmArrayBorrows = [] }
  , isJust $ llvmArrayIsOffsetArray ap sub_ap
  , Just fp <- llvmArrayToField sz sub_ap
  , ap' <- llvmArrayAddBorrow (llvmSubArrayBorrow ap sub_ap) ap =
    implLLVMArrayBorrow x ap sub_ap >>>
    implSwapM x (ValPerm_Conj1 $
                 Perm_LLVMArray sub_ap) x (ValPerm_Conj1 $
                                           Perm_LLVMArray ap') >>>
    implSimplM Proxy (SImpl_LLVMArrayToField x sub_ap sz) >>>
    -- NOTE: extractNeededLLVMFieldPerm is responsible for setting the
    -- rwmodality, so we include this proveEqCast for just it here
    proveEqCast x (\rw -> ValPerm_Conj1 $ Perm_LLVMField $
                          fp { llvmFieldRW = rw })
    (llvmFieldRW fp) (fmap llvmFieldRW mb_fp) >>>
    implSwapM x (ValPerm_Conj1 $
                 Perm_LLVMArray ap') x (ValPerm_Conj1 $
                                        Perm_LLVMField fp) >>>
    pure (fp, Just (Perm_LLVMArray ap'))


-- All other cases fail
extractNeededLLVMFieldPerm x ap _ _ mb_fp =
  implFailVarM "extractNeededLLVMFieldPerm" x (ValPerm_Conj1 $ ap)
  (fmap (ValPerm_Conj1 . Perm_LLVMField) mb_fp)


----------------------------------------------------------------------
-- * Proving LLVM Array Permissions
----------------------------------------------------------------------

-- | FIXME HERE NOW: document, especially the bool flag = first iteration and
-- that the bools with each perm are whether they can be used
proveVarLLVMArray ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) => ExprVar (LLVMPointerType w) ->
  Bool -> [AtomicPerm (LLVMPointerType w)] -> LLVMArrayPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()

proveVarLLVMArray x first_p ps ap =
  implTraceM (\i ->
               pretty "proveVarLLVMArray:" <+> permPretty i x <> colon <>
               align (sep [PP.group (permPretty i (ValPerm_Conj ps)),
                           pretty "-o",
                           PP.group (permPretty i (ValPerm_Conj1 $
                                                   Perm_LLVMArray ap))])) >>>
  proveVarLLVMArrayH x first_p ps ap


-- | FIXME HERE NOW: document, especially the bool flag = first iteration and
-- that the bools with each perm are whether they can be used
proveVarLLVMArrayH ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) => ExprVar (LLVMPointerType w) ->
  Bool -> [AtomicPerm (LLVMPointerType w)] -> LLVMArrayPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()

-- When len = 0, we are done
proveVarLLVMArrayH x _ ps ap
  | bvEq (llvmArrayLen ap) (bvInt 0) =
    implPopM x (ValPerm_Conj ps) >>> implLLVMArrayEmpty x ap

-- If the offset of our array permission is inside a memblock permission,
-- eliminate that memblock permission and try again
proveVarLLVMArrayH x _ ps ap
  | Just i <- findIndex (isLLVMAtomicPermWithOffset $ llvmArrayOffset ap) ps
  , Perm_LLVMBlock bp <- ps!!i =
    implGetPopConjM x ps i >>> implElimPopLLVMBlock x bp >>>
    mbVarsM (ValPerm_LLVMArray ap) >>>= \mb_p ->
    proveVarImplInt x mb_p

-- If the required array permission ap is equivalent to a sequence of field
-- permissions that we have all of, then prove it by proving those field
-- permissions. This is accomplished by first proving the array with the
-- un-borrowed cell that is allowed by 'implLLVMArrayOneCell' and then
-- recursively proving the desired array permission by calling proveVarImplInt,
-- which will remove the necessary borrows.
proveVarLLVMArrayH x _ ps ap
  | Just (flds1, flds2) <- llvmArrayAsFields ap
  , all (\fld ->
          any (isLLVMFieldPermWithOffset
               (llvmArrayFieldOffset fld)) ps) (flds1 ++ flds2) =
    implPopM x (ValPerm_Conj ps) >>>
    mbVarsM (ValPerm_Conj $
             map llvmArrayFieldToAtomicPerm flds1) >>>= \mb_p_flds ->
    proveVarImplInt x mb_p_flds >>>
    let ap' = llvmArrayAddBorrows (map (fromJust
                                        . offsetToLLVMArrayBorrow ap
                                        . llvmArrayFieldOffset) flds2) ap in
    implLLVMArrayOneCell x ap' >>>
    implPopM x (ValPerm_Conj1 $ Perm_LLVMArray ap') >>>
    mbVarsM (ValPerm_Conj1 $ Perm_LLVMArray ap) >>>= \mb_p ->
    proveVarImplInt x mb_p

-- Otherwise, choose the best-matching array permission and copy, borrow, or use
-- it directly (beg, borrow, or steal it)
--
-- FIXME: need to handle the case where we have a field permission for the first
-- cell of an array and an array permission for the rest
proveVarLLVMArrayH x first_p ps ap =
  let best_elems :: [(Bool, a)] -> [a]
      best_elems xs | Just i <- findIndex fst xs = [snd $ xs !! i]
      best_elems xs = map snd xs in

  mbVarsM (Perm_LLVMArray ap) >>>= \mb_p ->
  foldr1WithDefault implCatchM (proveVarAtomicImplUnfoldOrFail x ps mb_p) $
  best_elems $
  (let off = llvmArrayOffset ap in
   catMaybes $
   zipWith (\p i -> case p of
               Perm_LLVMArray ap_lhs
                 | precise <- bvEq off (llvmArrayOffset ap_lhs)
                 , (first_p || precise)
                 , Just cell_num <- llvmArrayIsOffsetArray ap_lhs ap
                 , bvCouldBeInRange cell_num (llvmArrayCells ap_lhs)
                 , llvmArrayFields ap_lhs == llvmArrayFields ap ->
                   Just (precise, proveVarLLVMArray_ArrayStep x ps ap i ap_lhs)
               _ -> Nothing)
   ps [0..])


-- | FIXME HERE NOW: document this
proveVarLLVMArray_ArrayStep ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) => ExprVar (LLVMPointerType w) ->
  [AtomicPerm (LLVMPointerType w)] -> LLVMArrayPerm w ->
  Int -> LLVMArrayPerm w ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()

-- If there is a borrow in ap_lhs that is not in ap but might overlap with ap,
-- return it to ap_lhs
--
-- FIXME: when an array ap_ret is being borrowed from ap_lhs, this code requires
-- all of it to be returned, with no borrows, even though it could be that ap
-- allows some of ap_ret to be borrowed
proveVarLLVMArray_ArrayStep x ps ap i ap_lhs
  | Just ap_cell_off <- llvmArrayIsOffsetArray ap_lhs ap
  , Just b <-
    find (\b ->
           bvRangesCouldOverlap (llvmArrayBorrowAbsOffsets ap b)
           (llvmArrayAbsOffsets ap) &&
           not (elem b $ llvmArrayBorrows ap))
         (map (cellOffsetLLVMArrayBorrow ap_cell_off) $
          llvmArrayBorrows ap_lhs) =

      -- Prove the rest of ap with b borrowed
      let ap' = llvmArrayAddBorrow b ap in
      proveVarLLVMArray_ArrayStep x ps ap' i ap_lhs >>>

      -- Prove the borrowed perm
      let p = permForLLVMArrayBorrow ap b in
      mbVarsM p >>>= \mb_p ->
      proveVarImplInt x mb_p >>>
      implSwapM x (ValPerm_Conj1 $ Perm_LLVMArray ap') x p >>>

      -- Return the borrowed perm to ap' to get ap
      implLLVMArrayReturnBorrow x ap' b

-- If there is a borrow in ap that is not in ap_lhs, borrow it from ap_lhs. Note
-- the assymmetry with the previous case: we only add borrows if we definitely
-- have to, but we remove borrows if we might have to.
proveVarLLVMArray_ArrayStep x ps ap i ap_lhs
  | Just ap_lhs_cell_off <- llvmArrayIsOffsetArray ap ap_lhs
  , Just b <-
    find (\b ->
           let b' = cellOffsetLLVMArrayBorrow ap_lhs_cell_off b in
           bvRangesOverlap (llvmArrayBorrowAbsOffsets ap b)
                           (llvmArrayAbsOffsets ap_lhs) &&
           not (elem b' (llvmArrayBorrows ap_lhs)))
         (llvmArrayBorrows ap) =

    -- Prove the rest of ap without b borrowed
    let ap' = llvmArrayRemBorrow b ap in
    proveVarLLVMArray_ArrayStep x ps ap' i ap_lhs >>>

    -- Borrow the permission if that is possible; this will fail if ap has a
    -- borrow that is not actually in its range. Note that the borrow is always
    -- added to the front of the list of borrows, so we need to rearrange.
    implLLVMArrayBorrowBorrow x ap' b >>>= \p ->
    recombinePerm x p >>>
    implLLVMArrayRearrange x (llvmArrayAddBorrow b ap') ap

-- If ap and ap_lhs are equal up to the order of their borrows, just rearrange
-- the borrows and we should be good
proveVarLLVMArray_ArrayStep x ps ap i ap_lhs
  | bvEq (llvmArrayOffset ap_lhs) (llvmArrayOffset ap)
  , bvEq (llvmArrayLen ap_lhs) (llvmArrayLen ap)
  , llvmArrayStride ap_lhs == llvmArrayStride ap
  , llvmArrayFields ap_lhs == llvmArrayFields ap =
    implGetPopConjM x ps i >>>
    implLLVMArrayRearrange x ap_lhs ap

-- If ap is contained inside ap_lhs at a cell boundary then copy or borrow ap
-- from ap_lhs depending on whether they are copyable
proveVarLLVMArray_ArrayStep x ps ap i ap_lhs
  | all bvPropCouldHold (bvPropRangeSubset
                         (llvmArrayAbsOffsets ap) (llvmArrayAbsOffsets ap_lhs))
  , llvmArrayStride ap_lhs == llvmArrayStride ap
  , llvmArrayFields ap_lhs == llvmArrayFields ap
  , Just (LLVMArrayIndex _ 0) <-
      matchLLVMArrayField ap_lhs (llvmArrayOffset ap) =
    implExtractConjM x ps i >>>
    implPopM x (ValPerm_Conj $ deleteNth i ps) >>>
    if atomicPermIsCopyable (Perm_LLVMArray ap) then
      implLLVMArrayCopy x ap_lhs ap >>>
      recombinePerm x (ValPerm_Conj1 $ Perm_LLVMArray ap_lhs)
    else
      implLLVMArrayBorrow x ap_lhs ap >>>
      recombinePerm x (ValPerm_Conj1 $ Perm_LLVMArray $
                       llvmArrayAddBorrow (llvmSubArrayBorrow ap_lhs ap) ap_lhs)

-- If we get to this case but ap is still at a cell boundary in ap_lhs then
-- ap_lhs only satisfies some initial portion of ap, so borrow or copy that part
-- of ap_lhs and continue proving the rest of ap
proveVarLLVMArray_ArrayStep x ps ap i ap_lhs
  | llvmArrayStride ap_lhs == llvmArrayStride ap
  , llvmArrayFields ap_lhs == llvmArrayFields ap
  , Just (LLVMArrayIndex ap_cell_num 0) <-
      matchLLVMArrayField ap_lhs (llvmArrayOffset ap) =

    -- Split ap into ap_first = the portion of ap covered by ap_lhs and ap_rest
    let (ap_first, ap_rest) =
          llvmArrayPermDivide ap (bvSub (llvmArrayLen ap_lhs) ap_cell_num) in

    -- Copy or borrow ap_first from ap_lhs, leaving some ps' on top of the stack
    -- and ap_first just below it
    implExtractConjM x ps i >>>
    implPopM x (ValPerm_Conj $ deleteNth i ps) >>>
    (if atomicPermIsCopyable (Perm_LLVMArray ap_first) then
       implLLVMArrayCopy x ap_lhs ap_first >>>
       implPushM x (ValPerm_Conj $ deleteNth i ps) >>>
       implInsertConjM x (Perm_LLVMArray ap_lhs) (deleteNth i ps) i >>>
       pure ps
     else
       implLLVMArrayBorrow x ap_lhs ap_first >>>
       implPushM x (ValPerm_Conj $ deleteNth i ps) >>>
       let ap_lhs' =
             llvmArrayAddBorrow (llvmSubArrayBorrow ap_lhs ap_first) ap_lhs in
       implInsertConjM x (Perm_LLVMArray ap_lhs') (deleteNth i ps) i >>>
       pure (replaceNth i (Perm_LLVMArray ap_lhs') ps)) >>>= \ps' ->

    -- Recursively prove ap_rest
    proveVarLLVMArray x False ps' ap_rest >>>

    -- Combine ap_first and ap_rest to get out ap
    implLLVMArrayAppend x ap_first ap_rest


-- Otherwise we don't know what to do so we fail
proveVarLLVMArray_ArrayStep _x _ps _ap _i _ap_lhs =
  implFailMsgM "proveVarLLVMArray_ArrayStep"


----------------------------------------------------------------------
-- * Proving Named Permission Arguments
----------------------------------------------------------------------

-- | Prove @P<args1> |- P<args2>@ by weakening the arguments in @args1@ and
-- substituting for free variablers in @args2@ until the arguments are
-- equal. The weakening steps include:
--
-- * Replacing 'Write' arguments with 'Read';
--
-- * Replacing a bigger lifetime @l1@ with a smaller one @l2@, defined by the
-- existence of a @l2:[l1]lcurrent@;
--
-- * Replacing all lifetime arguments with a single @lowned@ lifetime @l@, by
-- splitting the lifetime of the input permission
--
-- FIXME: currently this does not do the lifetime splitting step
proveNamedArgs :: NuMatchingAny1 r => ExprVar a ->
                  NamedPermName ns args a -> PermExprs args ->
                  PermOffset a -> Mb vars (PermExprs args) ->
                  ImplM vars s r (ps :> a) (ps :> a) ()
proveNamedArgs x npn args off mb_args =
  do _ <- implTraceM (\i -> pretty "proveNamedArgs:" <> softline <>
                       ppImpl i x (ValPerm_Named npn args off)
                       (fmap (\args' -> ValPerm_Named npn args' off) mb_args))
     psubst <- getPSubst
     mapM_ (\case Some memb ->
                    proveNamedArg x npn args off memb psubst $
                    fmap (`nthPermExpr` memb) mb_args)
       (getPermExprsMembers args)


-- | Prove @P<args1,arg,args2> |- P<args1,arg',args2>@ where @arg@ is specified
-- by a 'Member' proof in the input @args@ and @arg'@ potentially has
-- existential variables. Assume the LHS is on the top of the stack and leave
-- the RHS, if proved, on the top of the stack.
proveNamedArg :: NuMatchingAny1 r => ExprVar a ->
                 NamedPermName ns args a -> PermExprs args ->
                 PermOffset a -> Member args b -> PartialSubst vars ->
                 Mb vars (PermExpr b) ->
                 ImplM vars s r (ps :> a) (ps :> a) ()
proveNamedArg x npn args off memb psubst arg = case mbMatch arg of

  -- Prove P<args1,always,args2> -o P<args1,l,args2> for free variable l
  [nuMP| PExpr_Var z |]
    | PExpr_Always <- nthPermExpr args memb
    , Right l <- mbNameBoundP z ->
      implSimplM Proxy (SImpl_NamedArgAlways x npn args off memb (PExpr_Var l))

  -- Prove P<args1,always,args2> -o P<args1,l,args2> for assigned variable l
  [nuMP| PExpr_Var z |]
    | PExpr_Always <- nthPermExpr args memb
    , Left memb_z <- mbNameBoundP z
    , Just e <- psubstLookup psubst memb_z ->
      implSimplM Proxy (SImpl_NamedArgAlways x npn args off memb e)

  -- Prove P<args1,l1,args2> -o P<args1,l2,args2> for l1/=l2 using l1:[l2]lcurrent
  [nuMP| PExpr_Var z |]
    | Right l1 <- mbNameBoundP z
    , LifetimeRepr <- cruCtxLookup (namedPermNameArgs npn) memb
    , PExpr_Var l2 <- nthPermExpr args memb
    , l1 /= l2 ->
      proveVarImplInt l1 (fmap (const $ ValPerm_LCurrent $ PExpr_Var l2) arg) >>>
      implSimplM Proxy (SImpl_NamedArgCurrent x npn args off memb (PExpr_Var l2))

  -- Prove P<args1,W,args2> -o P<args1,rw,args2> for any variable rw
  [nuMP| PExpr_Var z |]
    | Right rw <- mbNameBoundP z
    , PExpr_RWModality Write <- nthPermExpr args memb ->
      implSimplM Proxy (SImpl_NamedArgWrite x npn args off memb (PExpr_Var rw))

  -- Prove P<args1,rw,args2> -o P<args1,R,args2> for any rw
  [nuMP| PExpr_RWModality Read |] ->
    implSimplM Proxy (SImpl_NamedArgRead x npn args off memb)

  -- Otherwise, prove P<args1,e1,args2> -o P<args1,e2,args2> by proving e1=e2
  _ ->
    proveEqCast x (\e -> ValPerm_Named npn (setNthPermExpr args memb e) off)
    (nthPermExpr args memb) arg


{-
  -- Prove x:P<args,p1> -o x:P<args,p2> when P is a reachability permission by
  -- eliminating the LHS into x:P<args,eq(y)> and y:p1, proving y:P<args,p2>, and
  -- applying transitivity of reachability permissions
  [nuMP| PExpr_ValPerm mb_p |]
    | RecursiveSortRepr b TrueRepr <- namedPermNameSort npn
    , NameReachConstr <- namedPermNameReachConstr npn ->
      implLookupNamedPerm npn >>>= \(NamedPerm_Rec rp) ->
      implElimReachabilityPermM x rp args off p >>>= \y ->
      proveVarImpl y (fmap (\e' ->
                             ValPerm_Named npn (PExprs_Cons
                                                args e') off) mb_e) >>>
      partialSubstForceM mb_p
      "proveNamedArg: incomplete psubst: p_y" >>>= \p_y ->
      implSimplM Proxy (SImpl_ReachabilityTrans x rp args off y p_y)
-}

{-
  -- Fail in any other case
  _ ->
    implFailVarM "proveNamedArg" x
    (ValPerm_Named npn args off)
    (fmap (\args' ->
            ValPerm_Named npn (setNthPermExpr args memb args') off) mb_arg)
-}

----------------------------------------------------------------------
-- * Proving LLVM Block Permissions
----------------------------------------------------------------------

-- | Prove a @memblock@ permission from the conjunction of the supplied atomic
-- permissions which are on the top of the stack
proveVarLLVMBlock ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) => ExprVar (LLVMPointerType w) ->
  [AtomicPerm (LLVMPointerType w)] -> Mb vars (LLVMBlockPerm w) ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()
proveVarLLVMBlock x ps mb_bp =
  do psubst <- getPSubst
     proveVarLLVMBlocks x ps psubst (fmap (: []) mb_bp) (fmap (const []) mb_bp)


-- | Prove a conjunction of block and atomic permissions for @x@, assuming all
-- of the permissions for @x@ are on the top of the stack and given by the
-- second argument. The block permissions are the ones that we are currently
-- working on, and when they are all proved we bottom out to 'proveVarConjImpl'.
proveVarLLVMBlocks ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) => ExprVar (LLVMPointerType w) ->
  [AtomicPerm (LLVMPointerType w)] -> PartialSubst vars ->
  Mb vars [LLVMBlockPerm w] -> Mb vars [AtomicPerm (LLVMPointerType w)] ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()

proveVarLLVMBlocks x ps psubst mb_bps mb_ps =
  implTraceM
  (\i -> sep [pretty "proveVarLLVMBlocks",
              permPretty i x <> colon <> permPretty i ps,
              pretty "-o", permPretty i mb_bps, permPretty i mb_ps]) >>>
  proveVarLLVMBlocks' x ps psubst mb_bps mb_ps


-- | Call 'proveVarLLVMBlock' in a context extended with a fresh existential
-- variable, which is used only in the first block permission we want to prove,
-- and return the value assigned to that evar
proveVarLLVMBlocksExt1 ::
  (1 <= w, KnownNat w, KnownRepr TypeRepr tp, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> [AtomicPerm (LLVMPointerType w)] ->
  PartialSubst vars -> Mb (vars :> tp) (LLVMBlockPerm w) ->
  Mb vars [LLVMBlockPerm w] -> Mb vars [AtomicPerm (LLVMPointerType w)] ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) (PermExpr tp)
proveVarLLVMBlocksExt1 x ps psubst mb_bp_ext mb_bps mb_ps =
  fmap snd $ withExtVarsM $
  proveVarLLVMBlocks x ps (extPSubst psubst) (mbMap2 (:) mb_bp_ext $
                                              extMb mb_bps) (extMb mb_ps)

-- | Like 'proveVarLLVMBlockExt1' but bind 2 existential variables, which can be
-- used in 0 or more block permissions we want to prove
proveVarLLVMBlocksExt2 ::
  (1 <= w, KnownNat w, KnownRepr TypeRepr tp1,
   KnownRepr TypeRepr tp2, NuMatchingAny1 r) =>
  ExprVar (LLVMPointerType w) -> [AtomicPerm (LLVMPointerType w)] ->
  PartialSubst vars -> Mb (vars :> tp1 :> tp2) [LLVMBlockPerm w] ->
  Mb vars [LLVMBlockPerm w] -> Mb vars [AtomicPerm (LLVMPointerType w)] ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w)
  (PermExpr tp1, PermExpr tp2)
proveVarLLVMBlocksExt2 x ps psubst mb_bps_ext mb_bps mb_ps =
  withExtVarsM
  (withExtVarsM $
   proveVarLLVMBlocks x ps (extPSubst $ extPSubst psubst)
   (mbMap2 (++) mb_bps_ext (extMb $ extMb mb_bps))
   (extMb $ extMb mb_ps)) >>= \((_,e2),e1) ->
  pure (e1,e2)


-- | The "real" version of 'proveVarLLVMBlocks'; that function is just a debug
-- printing wrapper around this one
proveVarLLVMBlocks' ::
  (1 <= w, KnownNat w, NuMatchingAny1 r) => ExprVar (LLVMPointerType w) ->
  [AtomicPerm (LLVMPointerType w)] -> PartialSubst vars ->
  Mb vars [LLVMBlockPerm w] -> Mb vars [AtomicPerm (LLVMPointerType w)] ->
  ImplM vars s r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()
proveVarLLVMBlocks' x ps psubst mb_bps_in mb_ps = case mbMatch mb_bps_in of

  -- If we are done with blocks, call proveVarConjImpl
  [nuMP| [] |] ->
    proveVarConjImpl x ps mb_ps

  -- If the offset, length, and shape of the top block matches one that we already
  -- have, just cast the rwmodality and lifetime and prove the remaining perms
  [nuMP| mb_bp : mb_bps |]
    | Just off <- partialSubst psubst $ fmap llvmBlockOffset mb_bp
    , Just len <- partialSubst psubst $ fmap llvmBlockLen mb_bp
    , Just i <- findIndex (\case
                              Perm_LLVMBlock bp ->
                                bvEq (llvmBlockOffset bp) off &&
                                bvEq (llvmBlockLen bp) len &&
                                mbLift (fmap ((== llvmBlockShape bp)
                                              . llvmBlockShape) mb_bp)
                              _ -> False) ps
    , Perm_LLVMBlock bp <- ps!!i ->

      -- Copy or extract the memblock perm we chose to the top of the stack
      (if atomicPermIsCopyable (ps!!i) then
         implCopySwapConjM x ps i >>> pure ps
       else
         implExtractSwapConjM x ps i >>> pure (deleteNth i ps)) >>>= \ps' ->

      -- Cast it to have the correct RW modality
      (case (llvmBlockRW bp, fmap llvmBlockRW mb_bp) of
          -- If the modalities are already equal, do nothing
          (rw, mb_rw) | mbLift (fmap (== rw) mb_rw) -> pure ()
          (_, mbMatch -> [nuMP| PExpr_Read |]) ->
            implSimplM Proxy (SImpl_DemoteLLVMBlockRW x bp)
          _ ->
            proveEqCast x (\rw -> ValPerm_LLVMBlock $ bp { llvmBlockRW = rw })
            (llvmBlockRW bp) (fmap llvmBlockRW mb_bp)) >>>
      getTopDistPerm x >>>= \(ValPerm_LLVMBlock bp') ->

      -- Get the lifetime correct
      let (f, args) = blockToLTFunc bp' in
      proveVarLifetimeFunctor x f args (llvmBlockLifetime bp) (fmap
                                                               llvmBlockLifetime
                                                               mb_bp) >>>
      getTopDistPerm x >>>= \(ValPerm_LLVMBlock bp'') ->

      -- Move it down below ps'
      implSwapM x (ValPerm_Conj ps') x (ValPerm_LLVMBlock bp'') >>>

      -- Recursively prove the remaining perms
      proveVarLLVMBlocks x ps' psubst mb_bps mb_ps >>>
      getTopDistPerm x >>>= \(ValPerm_Conj ps_out) ->

      -- Finally, combine the one memblock perm we chose with the rest of them
      implInsertConjM x (Perm_LLVMBlock bp'') ps_out 0


  -- If proving the empty shape for length 0, recursively prove everything else
  -- and then use the empty introduction rule
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_EmptyShape |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , Just len <- partialSubst psubst $ fmap llvmBlockLen mb_bp
    , bvIsZero len ->

      -- Do the recursive call without the empty shape and remember what
      -- permissions it proved
      proveVarLLVMBlocks x ps psubst mb_bps mb_ps >>>
      getTopDistPerm x >>>= \(ValPerm_Conj ps_out) ->

      -- Substitute into the required block perm and prove it with
      -- SImpl_IntroLLVMBlockEmpty
      --
      -- FIXME: if the rwmodality or lifetime are still unset at this point, we
      -- could set them to default values, but this will be a rare case
      partialSubstForceM mb_bp "proveVarLLVMBlock" >>>= \bp ->
      implSimplM Proxy (SImpl_IntroLLVMBlockEmpty x bp) >>>

      -- Finally, recombine the resulting permission with the rest of them
      implSwapInsertConjM x (Perm_LLVMBlock bp) ps_out 0


  -- If proving the empty shape otherwise, prove an arbitrary memblock permission,
  -- i.e., with shape y for evar y, and coerce it to the empty shape
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_EmptyShape |] <- mbMatch $ fmap llvmBlockShape mb_bp ->

      -- Locally bind z_sh for the shape of the memblock perm and recurse
      let mb_bp' =
            mbCombine RL.typeCtxProxies $ flip fmap mb_bp $ \bp ->
            nu $ \z_sh -> bp { llvmBlockShape = PExpr_Var z_sh } in
      proveVarLLVMBlocksExt1 x ps psubst mb_bp' mb_bps mb_ps >>>

      -- Extract out the block perm we proved and coerce it to the empty shape
      getTopDistPerm x >>>= \(ValPerm_Conj ps_out) ->
      let (Perm_LLVMBlock bp : ps_out') = ps_out in
      implSplitSwapConjsM x ps_out 1 >>>
      implSimplM Proxy (SImpl_CoerceLLVMBlockEmpty x bp) >>>

      -- Finally, recombine the resulting permission with the rest of them
      implSwapInsertConjM x (Perm_LLVMBlock $
                             bp { llvmBlockShape = PExpr_EmptyShape }) ps_out' 0


  -- If proving a memblock permission whose length is longer than the natural
  -- length of its shape, prove the memblock with the natural length as well as an
  -- additional memblock with empty shape and then sequence them together
  [nuMP| mb_bp : mb_bps |]
    | Just len <- partialSubst psubst (fmap llvmBlockLen mb_bp)
    , mbLift $ fmap (\bp ->
                      case llvmShapeLength (llvmBlockShape bp) of
                        Just sh_len -> bvLt sh_len len
                        Nothing -> False) mb_bp ->

      -- First, build the list of the correctly-sized perm + the empty shape one
      let mb_bps' =
            fmap (\bp ->
                   let sh_len = fromJust (llvmShapeLength (llvmBlockShape bp)) in
                   [bp { llvmBlockLen = sh_len },
                    bp { llvmBlockOffset = bvAdd (llvmBlockOffset bp) sh_len,
                         llvmBlockLen = bvSub (llvmBlockLen bp) sh_len,
                         llvmBlockShape = PExpr_EmptyShape }]) mb_bp in

      -- Next, do the recursive call
      proveVarLLVMBlocks x ps psubst (mbMap2 (++) mb_bps' mb_bps) mb_ps >>>

      -- Move the correctly-sized perm + the empty shape one to the top of the
      -- stack and sequence them, and then eliminate the empty shape at the end
      getTopDistPerm x >>>= \(ValPerm_Conj ps') ->
      let (Perm_LLVMBlock bp1 : Perm_LLVMBlock bp2 : ps'') = ps'
          len2 = llvmBlockLen bp2
          bp_out = bp1 { llvmBlockLen = bvAdd (llvmBlockLen bp1) len2 } in
      implSplitSwapConjsM x ps' 2 >>>
      implSplitConjsM x [Perm_LLVMBlock bp1, Perm_LLVMBlock bp2] 1 >>>
      implSimplM Proxy (SImpl_IntroLLVMBlockSeq x bp1 len2 PExpr_EmptyShape) >>>
      implSimplM Proxy (SImpl_ElimLLVMBlockSeqEmpty x bp_out) >>>

      -- Finally, recombine the resulting permission with the rest of them
      implSwapInsertConjM x (Perm_LLVMBlock bp_out) ps'' 0


  -- If proving a named shape, prove its unfolding first and then fold it
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_NamedShape rw l nmsh args |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , [nuMP| TrueRepr |] <- mbMatch $ fmap namedShapeCanUnfoldRepr nmsh
    , [nuMP| Just mb_sh' |] <- mbMatch $ (mbMap3 unfoldModalizeNamedShape rw l nmsh
                                         `mbApply` args) ->
      -- Recurse using the unfolded shape
      let mb_bps' =
            mbMap3 (\bp sh' bps -> (bp { llvmBlockShape = sh' } : bps))
            mb_bp mb_sh' mb_bps in
      proveVarLLVMBlocks' x ps psubst mb_bps' mb_ps >>>

      -- Extract out the block perm we proved
      getTopDistPerm x >>>= \(ValPerm_Conj ps_out) ->
      let (Perm_LLVMBlock bp : ps_out') = ps_out in
      implSplitSwapConjsM x ps_out 1 >>>

      -- Fold the named shape
      partialSubstForceM (fmap
                          llvmBlockShape mb_bp) "proveVarLLVMBlocks" >>>= \sh ->
      let bp' = bp { llvmBlockShape = sh } in
      implIntroLLVMBlockNamed x bp' >>>

      -- Finally, recombine the resulting permission with the rest of them
      implSwapInsertConjM x (Perm_LLVMBlock bp') ps_out' 0


  -- If proving an equality shape eqsh(z) for evar z which has already been set,
  -- substitute for z and recurse
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_EqShape (PExpr_Var mb_z) |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , Left memb <- mbNameBoundP mb_z
    , Just blk <- psubstLookup psubst memb ->
      proveVarLLVMBlocks x ps psubst
      (mbMap2 (:) (fmap (\bp -> bp { llvmBlockShape =
                                       PExpr_EqShape blk }) mb_bp) mb_bps)
      mb_ps


  -- If proving an equality shape eqsh(z) for unset evar z, prove any memblock
  -- perm with the given offset and length and eliminate it to an llvmblock with
  -- an equality shape
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_EqShape (PExpr_Var mb_z) |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , Left memb <- mbNameBoundP mb_z
    , Nothing <- psubstLookup psubst memb ->

      -- Locally bind z_sh for the shape of the memblock perm and recurse
      let mb_bp' =
            mbCombine RL.typeCtxProxies $ flip fmap mb_bp $ \bp ->
            nu $ \z_sh -> bp { llvmBlockShape = PExpr_Var z_sh } in
      proveVarLLVMBlocksExt1 x ps psubst mb_bp' mb_bps mb_ps >>>

      -- Extract out the block perm we proved
      getTopDistPerm x >>>= \(ValPerm_Conj ps_out) ->
      let (Perm_LLVMBlock bp : ps_out') = ps_out in
      implSplitSwapConjsM x ps_out 1 >>>

      -- Eliminate that block perm to have an equality shape, and set z to the
      -- resulting block
      implElimLLVMBlockToEq x bp >>>= \y_blk ->
      let bp' = bp { llvmBlockShape = PExpr_EqShape $ PExpr_Var y_blk } in
      setVarM memb (PExpr_Var y_blk) >>>

      -- Finally, recombine the resulting permission with the rest of them
      implSwapInsertConjM x (Perm_LLVMBlock bp') ps_out' 0


  -- If z is a free variable, the only way to prove the memblock permission is to
  -- have it on the left, but we don't have a memblock permission on the left with
  -- this exactly offset, length, and shape, because it would have matched the
  -- first case above, so try to eliminate a memblock and recurse
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_EqShape (PExpr_Var mb_z) |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , Right _ <- mbNameBoundP mb_z
    , Just off <- partialSubst psubst $ fmap llvmBlockOffset mb_bp
    , Just i <- findIndex (\case
                              p@(Perm_LLVMBlock _) ->
                                isJust (llvmPermContainsOffset off p)
                              _ -> False) ps
    , Perm_LLVMBlock bp <- ps!!i ->
      implGetPopConjM x ps i >>> implElimPopLLVMBlock x bp >>>
      proveVarImplInt x (fmap ValPerm_Conj $
                         mbMap2 (++)
                         (fmap (map Perm_LLVMBlock) $ mbMap2 (:) mb_bp mb_bps)
                         mb_ps)

  -- If proving a pointer shape, prove the required permission by adding it to ps;
  -- this requires the pointed-to shape to have a well-defined length
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_PtrShape mb_rw mb_l mb_sh |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , mbLift $ fmap (isJust . llvmShapeLength) mb_sh ->

      -- Add a permission for a pointer to the required shape to mb_ps, and
      -- recursively call proveVarLLVMBlocks to prove it and everything else
      let mb_p_ptr =
            mbMap4 (\bp maybe_rw maybe_l sh ->
                      (llvmBlockPtrAtomicPerm $
                       llvmBlockAdjustModalities maybe_rw maybe_l $
                       bp { llvmBlockLen = fromJust (llvmShapeLength sh),
                            llvmBlockShape = sh }))
            mb_bp mb_rw mb_l mb_sh in
      proveVarLLVMBlocks x ps psubst mb_bps (mbMap2 (:) mb_p_ptr mb_ps) >>>

      -- Move the pointer permission we proved to the top of the stack
      getTopDistPerm x >>>= \(ValPerm_Conj ps') ->
      let i = mbLift (fmap length mb_bps) in
      implExtractSwapConjM x ps' i >>>

      -- Use the SImpl_IntroLLVMBlockPtr rule to prove the required memblock perm
      partialSubstForceM mb_bp "proveVarLLVMBlocks" >>>= \bp ->
      let PExpr_PtrShape maybe_rw maybe_l sh = llvmBlockShape bp in
      let Just sh_len = llvmShapeLength sh in
      implSimplM Proxy (SImpl_IntroLLVMBlockPtr x maybe_rw maybe_l $
                        bp { llvmBlockLen = sh_len, llvmBlockShape = sh }) >>>

      -- Finally, move the memblock perm we proved back into position
      implSwapInsertConjM x (Perm_LLVMBlock bp) (deleteNth i ps') 0


  -- If proving a field shape, prove the required permission by adding it to ps
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_FieldShape
           (LLVMFieldShape mb_p) |] <- mbMatch $ fmap llvmBlockShape mb_bp ->

      -- Add the field permission to the required permission to mb_ps, and
      -- recursively call proveVarLLVMBlocks to prove it and everything else
      let mb_fp =
            mbMap2 (\bp p ->
                     (llvmBlockPtrFieldPerm bp) { llvmFieldContents = p })
            mb_bp mb_p in
      let mb_p' = fmap Perm_LLVMField mb_fp in
      proveVarLLVMBlocks x ps psubst mb_bps (mbMap2 (:) mb_p' mb_ps) >>>

      -- Move the pointer permission we proved to the top of the stack
      getTopDistPerm x >>>= \(ValPerm_Conj ps') ->
      let i = mbLift (fmap length mb_bps) in
      implExtractSwapConjM x ps' i >>>

      -- Use the SImpl_IntroLLVMBlockField rule to prove the required memblock perm
      partialSubstForceM (mbMap2 (,)
                          mb_bp mb_fp) "proveVarLLVMBlocks" >>>= \(bp,fp) ->
      implSimplM Proxy (SImpl_IntroLLVMBlockField x fp) >>>

      -- Finally, move the memblock perm we proved back into position
      implSwapInsertConjM x (Perm_LLVMBlock bp) (deleteNth i ps') 0


  -- If proving an array shape, just like in the field case, prove the required
  -- array permission and then pad it out with an empty memblock permission
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_ArrayShape _ _ _ |] <- mbMatch $ fmap llvmBlockShape mb_bp ->

      -- Add the array permission to the required permission to mb_ps, and
      -- recursively call proveVarLLVMBlocks to prove it and everything else
      let mb_ap = fmap llvmArrayBlockToArrayPerm mb_bp in
      let mb_p = fmap Perm_LLVMArray mb_ap in
      proveVarLLVMBlocks x ps psubst mb_bps (mbMap2 (:) mb_p mb_ps) >>>

      -- Move the pointer permission we proved to the top of the stack
      getTopDistPerm x >>>= \(ValPerm_Conj ps') ->
      let i = mbLift (fmap length mb_bps) in
      implExtractSwapConjM x ps' i >>>

      -- Use the SImpl_IntroLLVMBlockArray rule to prove the memblock perm
      partialSubstForceM (mbMap2 (,)
                          mb_bp mb_ap) "proveVarLLVMBlocks" >>>= \(bp,ap) ->
      implSimplM Proxy (SImpl_IntroLLVMBlockArray x ap) >>>

      -- Finally, move the memblock perm we proved back into position
      implSwapInsertConjM x (Perm_LLVMBlock bp) (deleteNth i ps') 0


  -- If proving a sequence shape, prove the two shapes and combine them; this
  -- requires the first shape to have a well-defined length
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_SeqShape mb_sh1 _ |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , mbLift $ fmap (isJust . llvmShapeLength) mb_sh1 ->

      -- Add the two shapes to mb_bps and recursively call proveVarLLVMBlocks
      let mb_bps12 =
            fmap (\bp ->
                   let PExpr_SeqShape sh1 sh2 = llvmBlockShape bp in
                   let Just len1 = llvmShapeLength sh1 in
                   [bp { llvmBlockLen = len1, llvmBlockShape = sh1 },
                    bp { llvmBlockOffset = bvAdd (llvmBlockOffset bp) len1,
                         llvmBlockLen = bvSub (llvmBlockLen bp) len1,
                         llvmBlockShape = sh2 }]) mb_bp in
      proveVarLLVMBlocks x ps psubst (mbMap2 (++) mb_bps12 mb_bps) mb_ps >>>

      -- Move the block permissions we proved to the top of the stack
      getTopDistPerm x >>>= \(ValPerm_Conj ps') ->
      let (Perm_LLVMBlock bp1 : Perm_LLVMBlock bp2 : ps'') = ps'
          len2 = llvmBlockLen bp2
          sh2 = llvmBlockShape bp2 in
      implSplitSwapConjsM x ps' 2 >>>

      -- Use the SImpl_IntroLLVMBlockSeq rule combine them into one memblock perm
      implSplitConjsM x [Perm_LLVMBlock bp1, Perm_LLVMBlock bp2] 1 >>>
      implSimplM Proxy (SImpl_IntroLLVMBlockSeq x bp1 len2 sh2) >>>

      -- Finally, move the memblock perm we proved back into position
      partialSubstForceM mb_bp "proveVarLLVMBlock" >>>= \bp ->
      implSwapInsertConjM x (Perm_LLVMBlock bp) ps'' 0


  -- If proving a disjunctive shape, try to prove one of the disjuncts
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_OrShape mb_sh1 mb_sh2 |] <- mbMatch $ fmap llvmBlockShape mb_bp ->

      -- Build a computation that tries returning True here, and if that fails
      -- returns False; True is used for sh1 while False is used for sh2
      implCatchM (pure True) (pure False) >>>= \is_case1 ->

      -- Prove the chosen shape by recursively calling proveVarLLVMBlocks
      let mb_sh = if is_case1 then mb_sh1 else mb_sh2 in
      let mb_bp' = mbMap2 (\bp sh -> bp { llvmBlockShape = sh }) mb_bp mb_sh in
      proveVarLLVMBlocks x ps psubst (mbMap2 (:) mb_bp' mb_bps) mb_ps >>>

      -- Move the block permission we proved to the top of the stack
      getTopDistPerm x >>>= \(ValPerm_Conj ps') ->
      implSplitSwapConjsM x ps' 1 >>>

      -- Prove the disjunction of the two memblock permissions
      partialSubstForceM mb_bp "proveVarLLVMBlock" >>>= \bp ->
      let PExpr_OrShape sh1 sh2 = llvmBlockShape bp in
      let introM = if is_case1 then introOrLM else introOrRM in
      introM x (ValPerm_LLVMBlock $ bp { llvmBlockShape = sh1 })
      (ValPerm_LLVMBlock $ bp { llvmBlockShape = sh2 }) >>>

      -- Now coerce the disjunctive permission on top of the stack to an or shape,
      -- and move it back into position
      implSimplM Proxy (SImpl_IntroLLVMBlockOr
                        x (bp { llvmBlockShape = sh1 }) sh2) >>>
      implSwapInsertConjM x (Perm_LLVMBlock bp) (tail ps') 0


  -- If proving an existential shape, introduce an evar and recurse
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_ExShape mb_mb_sh |] <- mbMatch $ fmap llvmBlockShape mb_bp ->

      -- Prove the sub-shape in the context of a new existential variable
      let mb_bp' =
            mbCombine RL.typeCtxProxies $
            mbMap2 (\bp mb_sh ->
                     fmap (\sh -> bp { llvmBlockShape = sh }) mb_sh)
            mb_bp mb_mb_sh in
      proveVarLLVMBlocksExt1 x ps psubst mb_bp' mb_bps mb_ps >>>= \e ->

      -- Move the block permission we proved to the top of the stack
      getTopDistPerm x >>>= \(ValPerm_Conj ps') ->
      implSplitSwapConjsM x ps' 1 >>>

      -- Prove an existential around the memblock permission we proved
      partialSubstForceM (mbMap2 (,)
                          mb_bp mb_mb_sh) "proveVarLLVMBlock" >>>= \(bp,mb_sh) ->
      introExistsM x e (fmap (\sh -> ValPerm_LLVMBlock $
                                     bp { llvmBlockShape = sh }) mb_sh) >>>

      -- Now coerce the existential permission on top of the stack to a memblock
      -- perm with existential shape, and move it back into position
      implSimplM Proxy (SImpl_IntroLLVMBlockEx x bp) >>>
      implSwapInsertConjM x (Perm_LLVMBlock bp) (tail ps') 0


  -- If proving an evar shape that has already been set, substitute and recurse
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_Var mb_z |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , Left memb <- mbNameBoundP mb_z
    , Just sh <- psubstLookup psubst memb ->
      let mb_bp' = fmap (\bp -> bp { llvmBlockShape = sh }) mb_bp in
      proveVarLLVMBlocks x ps psubst (mbMap2 (:) mb_bp' mb_bps) mb_ps


  -- If z is unset and len == 0, just set z to the empty shape and recurse in
  -- order to call the len == 0 empty shape case above
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_Var mb_z |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , Left memb <- mbNameBoundP mb_z
    , Nothing <- psubstLookup psubst memb
    , Just len <- partialSubst psubst (fmap llvmBlockLen mb_bp)
    , bvIsZero len ->
      setVarM memb PExpr_EmptyShape >>>
      let mb_bp' = fmap (\bp -> bp { llvmBlockShape = PExpr_EmptyShape }) mb_bp in
      proveVarLLVMBlocks x ps psubst (mbMap2 (:) mb_bp' mb_bps) mb_ps


  -- If z is unset and there is a field permission with the required offset and
  -- length, set z to a field shape with equality permission to an existential
  -- variable, which is the most general field permission we can make
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_Var mb_z |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , Left memb <- mbNameBoundP mb_z
    , Nothing <- psubstLookup psubst memb
    , Just off <- partialSubst psubst (fmap llvmBlockOffset mb_bp)
    , Just len <- partialSubst psubst (fmap llvmBlockLen mb_bp)
    , Just i <- findIndex (isLLVMAtomicPermWithOffset off) ps
    , Perm_LLVMField (fp :: LLVMFieldPerm w sz) <- ps!!i
    , bvEq len (llvmFieldLen fp) ->

      -- Recursively prove a membblock with shape fieldsh(eq(y)) for fresh evar y
      let mb_bp' =
            mbCombine RL.typeCtxProxies $ flip fmap mb_bp $ \bp ->
            nu $ \(y :: ExprVar (LLVMPointerType sz)) ->
            bp { llvmBlockShape =
                   PExpr_FieldShape $ LLVMFieldShape $
                   ValPerm_Eq $ PExpr_Var y } in
      proveVarLLVMBlocksExt1 x ps psubst mb_bp' mb_bps mb_ps >>>= \e ->

      -- Set z = fieldsh(eq(e)) where e was the value we determined for y;
      -- otherwise we are done, because our required block perm is already proved
      -- and in the correct spot on the stack
      setVarM memb (PExpr_FieldShape $ LLVMFieldShape $ ValPerm_Eq e)


  -- If z is unset and there is an atomic permission with the required offset and
  -- length (which is not a field permission, because otherwise the previous case
  -- would match), set z to the shape of that atomic permission and recurse
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_Var mb_z |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , Left memb <- mbNameBoundP mb_z
    , Nothing <- psubstLookup psubst memb
    , Just off <- partialSubst psubst (fmap llvmBlockOffset mb_bp)
    , Just len <- partialSubst psubst (fmap llvmBlockLen mb_bp)
    , Just i <- findIndex (isLLVMAtomicPermWithOffset off) ps
    , Just bp_lhs <- llvmAtomicPermToBlock (ps!!i)
    , bvEq len (llvmBlockLen bp_lhs)
    , sh_lhs <- llvmBlockShape bp_lhs ->

      setVarM memb sh_lhs >>>
      let mb_bp' = fmap (\bp -> bp { llvmBlockShape = sh_lhs }) mb_bp in
      proveVarLLVMBlocks x ps psubst (mbMap2 (:) mb_bp' mb_bps) mb_ps


  -- If z is unset and there is an atomic permission with the required offset (but
  -- not the required length, because otherwise it would have matched the previous
  -- case), split our memblock permission into two memblock permissions with
  -- unknown shapes but where the first has the length of this atomic permission
  -- (so the previous case will match), and then recurse
  [nuMP| mb_bp : mb_bps |]
    | [nuMP| PExpr_Var mb_z |] <- mbMatch $ fmap llvmBlockShape mb_bp
    , Left memb <- mbNameBoundP mb_z
    , Nothing <- psubstLookup psubst memb
    , Just off <- partialSubst psubst (fmap llvmBlockOffset mb_bp)
    , Just i <- findIndex (isLLVMAtomicPermWithOffset off) ps
    , Just len1 <- llvmAtomicPermLen (ps!!i)
    , not (bvIsZero len1) ->

      -- Build existential memblock perms with fresh variables for shapes, where
      -- the first one has the length of the atomic perm we found and the other
      -- has the remaining length, and recurse
      let mb_bps12 =
            mbCombine RL.typeCtxProxies $ flip fmap mb_bp $ \bp ->
            nuMulti (MNil :>: Proxy :>: Proxy) $ \(_ :>: z_sh1 :>: z_sh2) ->
            [bp { llvmBlockLen = len1, llvmBlockShape = PExpr_Var z_sh1 },
             bp { llvmBlockOffset = bvAdd (llvmBlockOffset bp) len1,
                  llvmBlockLen = bvSub (llvmBlockLen bp) len1,
                  llvmBlockShape = PExpr_Var z_sh2 }] in
      proveVarLLVMBlocksExt2 x ps psubst mb_bps12 mb_bps mb_ps >>>

      -- Move the two block permissions we proved to the top of the stack
      getTopDistPerm x >>>= \(ValPerm_Conj ps_ret) ->
      let (Perm_LLVMBlock bp1 : Perm_LLVMBlock bp2 : ps_ret') = ps_ret
          len2 = llvmBlockLen bp2
          sh2 = llvmBlockShape bp2 in
      implSplitSwapConjsM x ps_ret 2 >>>
      implSplitConjsM x (map Perm_LLVMBlock [bp1,bp2]) 1 >>>

      -- Sequence these two block permissions together
      implSimplM Proxy (SImpl_IntroLLVMBlockSeq x bp1 len2 sh2) >>>
      let bp = bp1 { llvmBlockLen = bvAdd (llvmBlockLen bp1) len2,
                     llvmBlockShape = PExpr_SeqShape (llvmBlockShape bp1) sh2 } in

      -- Finally, set z to the memblock permission we ended up proving, and move
      -- this proof back into position
      setVarM memb (llvmBlockShape bp) >>>
      implSwapInsertConjM x (Perm_LLVMBlock bp) ps_ret' 0


  _ ->
    implFailVarM "proveVarLLVMBlock" x (ValPerm_Conj ps)
    (fmap ValPerm_Conj $
     mbMap2 (++) (fmap (map Perm_LLVMBlock) mb_bps_in) mb_ps)


----------------------------------------------------------------------
-- * Proving and Eliminating Recursive Permissions
----------------------------------------------------------------------

-- | Prove @x:p1 |- x:p2@ by unfolding a foldable named permission in @p1@ and
-- then recursively proving @x:p2@ from the resulting permissions. If an 'Int'
-- @i@ is supplied, then @p1@ is a conjunctive permission whose @i@th conjunct
-- is the named permisison to be unfolded; otherwise @p1@ itself is the named
-- permission to be unfolded. Assume that @x:p1@ is on top of the stack.
proveVarImplUnfoldLeft :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
                          Mb vars (ValuePerm a) ->
                          Maybe Int -> ImplM vars s r (ps :> a) (ps :> a) ()

proveVarImplUnfoldLeft x (ValPerm_Named npn args off) mb_p Nothing
  | TrueRepr <- nameCanFoldRepr npn =
    (case namedPermNameSort npn of
        RecursiveSortRepr _ _ -> implSetRecRecurseLeftM
        _ -> pure ()) >>>
    implUnfoldNamedM x npn args off >>>= \p' ->
    implPopM x p' >>>
    proveVarImplInt x mb_p

proveVarImplUnfoldLeft x (ValPerm_Conj ps) mb_p (Just i)
  | i < length ps
  , Perm_NamedConj npn args off <- ps!!i
  , TrueRepr <- nameCanFoldRepr npn =
    (case namedPermNameSort npn of
        RecursiveSortRepr _ _ -> implSetRecRecurseLeftM
        _ -> pure ()) >>>
    implExtractConjM x ps i >>> implPopM x (ValPerm_Conj $ deleteNth i ps) >>>
    implNamedFromConjM x npn args off >>>
    implUnfoldNamedM x npn args off >>>= \p' ->
    recombinePerm x p' >>>
    proveVarImplInt x mb_p

proveVarImplUnfoldLeft _ _ _ _ =
  error ("proveVarImplUnfoldLeft: malformed inputs")


-- | Prove @x:p1 |- x:P<args>\@off@ where @P@ is foldable by first proving the
-- unfolding of @P@ folding it. Assume that @x:p1@ is on top of the stack.
proveVarImplFoldRight :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
                         Mb vars (ValuePerm a) ->
                         ImplM vars s r (ps :> a) (ps :> a) ()
proveVarImplFoldRight x p mb_p = case mbMatch mb_p of
  [nuMP| ValPerm_Named mb_npn mb_args mb_off |]
    | npn <- mbLift mb_npn
    , TrueRepr <- nameCanFoldRepr npn ->
      (case namedPermNameSort npn of
          RecursiveSortRepr _ _ -> implSetRecRecurseRightM
          _ -> pure ()) >>>
      implLookupNamedPerm npn >>>= \np ->
      implPopM x p >>>
      proveVarImplInt x (mbMap2 (unfoldPerm np) mb_args mb_off) >>>
      partialSubstForceM (mbMap2 (,) mb_args mb_off)
      "proveVarImplFoldRight" >>>= \(args,off) ->
      implFoldNamedM x npn args off
  _ ->
    error ("proveVarImplFoldRight: malformed inputs")


----------------------------------------------------------------------
-- * Proving Atomic Permissions
----------------------------------------------------------------------

-- | We were not able to prove @x:(p1 * ... * pn) |- x:p@ as is, so try
-- unfolding named permissions in the @pi@s as a last resort. If there are none,
-- or our recursion flag does not allow it, then fail.
proveVarAtomicImplUnfoldOrFail :: NuMatchingAny1 r => ExprVar a ->
                                  [AtomicPerm a] -> Mb vars (AtomicPerm a) ->
                                  ImplM vars s r (ps :> a) (ps :> a) ()
proveVarAtomicImplUnfoldOrFail x ps mb_ap =
  do let p_l = ValPerm_Conj ps
         mb_p_r = fmap ValPerm_Conj1 mb_ap
     flag <- use implStateRecRecurseFlag
     case () of
       -- We can always unfold a defined name on the left
       _ | Just i <- findIndex isDefinedConjPerm ps ->
           proveVarImplUnfoldLeft x p_l mb_p_r (Just i)

       -- If flag allows it, we can unfold a recursive name on the left
       _ | Just i <- findIndex isRecursiveConjPerm ps
         , flag /= RecRight ->
           proveVarImplUnfoldLeft x p_l mb_p_r (Just i)

       -- Otherwise, we fail
       _ -> implFailVarM "proveVarAtomicImpl" x p_l mb_p_r


-- | Prove @x:(p1 * ... * pn) |- x:p@ for some atomic permission @p@, assuming
-- the LHS is on the top of the stack and represents all the permissions on @x@,
-- i.e., we also assume the variable permissions for @x@ are currently
-- @true@. Any remaining perms for @x@ are popped off of the stack.
proveVarAtomicImpl ::
  NuMatchingAny1 r =>
  ExprVar a ->
  [AtomicPerm a] ->
  Mb vars (AtomicPerm a) ->
  ImplM vars s r (ps :> a) (ps :> a) ()
proveVarAtomicImpl x ps mb_p = case mbMatch mb_p of

  [nuMP| Perm_LLVMField mb_fp |] ->
    partialSubstForceM (fmap llvmFieldOffset mb_fp) "proveVarPtrPerms" >>>= \off ->
    foldMapWithDefault implCatchM
    (proveVarAtomicImplUnfoldOrFail x ps mb_p)
    (\(i,_) -> proveVarLLVMField x ps i off mb_fp)
    (findMaybeIndices (llvmPermContainsOffset off) ps)

  [nuMP| Perm_LLVMArray mb_ap |] ->
    partialSubstForceM mb_ap "proveVarPtrPerms" >>>= \ap ->
    proveVarLLVMArray x True ps ap

  [nuMP| Perm_LLVMBlock mb_bp |] ->
    proveVarLLVMBlock x ps mb_bp

  [nuMP| Perm_LLVMFree mb_e |] ->
    partialSubstForceM mb_e "proveVarAtomicImpl" >>>= \e ->
    case findMaybeIndices (\case
                              Perm_LLVMFree e' -> Just e'
                              _ -> Nothing) ps of
      (i, e'):_ ->
        implCopyConjM x ps i >>> implPopM x (ValPerm_Conj ps) >>>
        castLLVMFreeM x e' e
      _ -> proveVarAtomicImplUnfoldOrFail x ps mb_p

  [nuMP| Perm_LLVMFunPtr tp mb_p' |] ->
    partialSubstForceM mb_p' "proveVarAtomicImpl" >>>= \p ->
    case elemIndex (Perm_LLVMFunPtr (mbLift tp) p) ps of
      Just i -> implCopyConjM x ps i >>> implPopM x (ValPerm_Conj ps)
      _ -> proveVarAtomicImplUnfoldOrFail x ps mb_p

  [nuMP| Perm_IsLLVMPtr |]
    | Just i <- elemIndex Perm_IsLLVMPtr ps ->
      implCopyConjM x ps i >>> implPopM x (ValPerm_Conj ps)

  [nuMP| Perm_IsLLVMPtr |]
    | Just i <- findIndex isLLVMFieldPerm ps
    , p@(Perm_LLVMField fp) <- ps !! i ->
      implExtractConjM x ps i >>> implPopM x (ValPerm_Conj $ deleteNth i ps) >>>
      implSimplM Proxy (SImpl_LLVMFieldIsPtr x fp) >>>
      implPushM x (ValPerm_Conj $ deleteNth i ps) >>>
      implInsertConjM x p (deleteNth i ps) i >>>
      implPopM x (ValPerm_Conj ps)

  [nuMP| Perm_IsLLVMPtr |]
    | Just i <- findIndex isLLVMArrayPerm ps
    , p@(Perm_LLVMArray ap) <- ps !! i ->
      implExtractConjM x ps i >>> implPopM x (ValPerm_Conj $ deleteNth i ps) >>>
      implSimplM Proxy (SImpl_LLVMArrayIsPtr x ap) >>>
      implPushM x (ValPerm_Conj $ deleteNth i ps) >>>
      implInsertConjM x p (deleteNth i ps) i >>>
      implPopM x (ValPerm_Conj ps)

  [nuMP| Perm_IsLLVMPtr |]
    | Just i <- findIndex isLLVMBlockPerm ps
    , p@(Perm_LLVMBlock bp) <- ps !! i ->
      implExtractConjM x ps i >>> implPopM x (ValPerm_Conj $ deleteNth i ps) >>>
      implSimplM Proxy (SImpl_LLVMBlockIsPtr x bp) >>>
      implPushM x (ValPerm_Conj $ deleteNth i ps) >>>
      implInsertConjM x p (deleteNth i ps) i >>>
      implPopM x (ValPerm_Conj ps)

  [nuMP| Perm_IsLLVMPtr |] ->
    proveVarAtomicImplUnfoldOrFail x ps mb_p

  [nuMP| Perm_LLVMBlockShape mb_sh |]
    | Just i <- findIndex (\case
                              Perm_LLVMBlockShape _ -> True
                              _ -> False) ps
    , Perm_LLVMBlockShape sh <- ps!!i ->
      implGetPopConjM x ps i >>>
      proveEqCast x (ValPerm_Conj1 . Perm_LLVMBlockShape) sh mb_sh

  [nuMP| Perm_NamedConj mb_n mb_args mb_off |] ->
    let n = mbLift mb_n in
    proveVarImplH x (ValPerm_Conj ps) (mbMap2 (ValPerm_Named n)
                                       mb_args mb_off) >>>
    partialSubstForceM (mbMap2 (,)
                        mb_args mb_off) "proveVarAtomicImpl" >>>= \(args,off) ->
    implNamedToConjM x n args off

  [nuMP| Perm_LLVMFrame mb_fperms |]
    | [Perm_LLVMFrame fperms] <- ps ->
      proveEq fperms mb_fperms >>>= \eqp ->
      implCastPermM x (fmap (ValPerm_Conj1 . Perm_LLVMFrame) eqp)

  [nuMP| Perm_LOwned mb_ps_inR mb_ps_outR |]
    | [Perm_LOwned ps_inL ps_outL] <- ps ->

      -- First, simplify both sides using any current equality permissions. This
      -- just builds the equality proofs and computes the new LHS and RHS, but
      -- we don't actually perform the casts until later.
      substEqsWithProof (ps_inL, ps_outL) >>>= \eqp_psL ->
      get >>>= \s ->
      give (cruCtxProxies (view implStateVars s))
        (substEqsWithProof (mb_ps_inR, mb_ps_outR)) >>>= \eqp_mb_psR ->
      let (ps_inL',ps_outL') = someEqProofRHS eqp_psL
          (mb_ps_inR',mb_ps_outR') = someEqProofRHS eqp_mb_psR in

      -- Pop ps from the stack, so we can push it to the top of the stack later
      implPopM x (ValPerm_Conj ps) >>>

      -- Compute the necessary "permission subtractions" to figure out what
      -- additional permissions are needed to prove both ps_inR -o ps_inL and
      -- ps_outL -o ps_outR. These required permissions are calls ps1 and ps2,
      -- respectively. Note that the RHS for both of these implications needs to
      -- be in a name-binding for the evars and the LHS needs to not be in a
      -- name-binding, so ps_inR cannot have any evars.
      partialSubstForceM mb_ps_inR' "proveVarAtomicImpl" >>>= \ps_inR' ->
      let mb_ps_inL' = fmap (const ps_inL') mb_ps_inR' in
      solveForPermListImpl ps_inR' mb_ps_inL' >>>= \(Some neededs1) ->
      solveForPermListImpl ps_outL' mb_ps_outR' >>>= \(Some neededs2) ->
      uses implStateVars cruCtxProxies >>>= \prxs ->
      let mb_ps1 = neededPermsToExDistPerms prxs neededs1
          mb_ps2 = neededPermsToExDistPerms prxs neededs2 in

      -- Prove ps1 and ps2, which can have evars, and then look at the
      -- substitution instances of ps1 and ps2 that were actually proved on top
      -- of the stack. We do it this way because we can't substitute expressions
      -- for variables in a DistPerms, because DistPerms need to have variables
      -- on the LHSs and not arbitrary expressions
      getDistPerms >>>= \before_ps ->
      proveVarsImplAppendInt (mbMap2 RL.append mb_ps1 mb_ps2) >>>
      getDistPerms >>>= \top_ps ->
      let ps12 = snd $ RL.split before_ps (RL.append neededs1 neededs2) top_ps
          (ps1,ps2) = RL.split neededs1 neededs2 ps12 in
      partialSubstForceM mb_ps_outR' "proveVarAtomicImpl" >>>= \ps_outR' ->
      getPSubst >>>= \psubst ->
      let eqp_R =
            fmap (\(mb_ps_in,mb_ps_out) ->
                   ValPerm_LOwned
                   (partialSubstForce psubst mb_ps_in "proveVarAtomicImpl")
                   (partialSubstForce psubst mb_ps_out "proveVarAtomicImpl"))
            eqp_mb_psR in

      -- Build the local implications ps_inR -o ps_inL and ps_outL -o ps_outR
      (case (lownedPermsToDistPerms ps_inL', lownedPermsToDistPerms ps_outL',
             lownedPermsToDistPerms ps_inR', lownedPermsToDistPerms ps_outR') of
          (Just dps_inL, Just dps_outL, Just dps_inR, Just dps_outR) ->
            pure (dps_inL, dps_outL, dps_inR, dps_outR)
          _ -> implFailM "proveVarAtomicImpl: lownedPermsToDistPerms")
      >>>= \(dps_inL, dps_outL, dps_inR, dps_outR) ->
      localProveVars (RL.append ps1 dps_inR) dps_inL >>>= \impl_in ->
      localProveVars (RL.append ps2 dps_outL) dps_outR >>>= \impl_out ->

      -- Finally, apply the MapLifetime proof step, first pushing the input
      -- lowned permissions and casting it, and then cast the result
      implPushM x (ValPerm_Conj ps) >>>
      implCastPermM x (fmap (\(ps_in,ps_out) ->
                              ValPerm_LOwned ps_in ps_out) eqp_psL) >>>
      implSimplM Proxy (SImpl_MapLifetime x ps_inL' ps_outL' ps_inR' ps_outR'
                        ps1 ps2 impl_in impl_out) >>>
      implCastPermM x (someEqProofSym eqp_R)

  [nuMP| Perm_LCurrent mb_l' |] ->
    partialSubstForceM mb_l' "proveVarAtomicImpl" >>>= \l' ->
    case ps of
      _ | l' == PExpr_Var x ->
          implPopM x (ValPerm_Conj ps) >>>
          implSimplM Proxy (SImpl_LCurrentRefl x)
      [Perm_LCurrent l] | l == l' -> pure ()
      [Perm_LCurrent (PExpr_Var l)] ->
        proveVarImplInt l (fmap ValPerm_Conj1 mb_p) >>>
        implSimplM Proxy (SImpl_LCurrentTrans x l l')
      _ -> proveVarAtomicImplUnfoldOrFail x ps mb_p

  -- If we have a struct permission on the left, eliminate it to a sequence of
  -- variables and prove the required permissions for each variable
  [nuMP| Perm_Struct mb_str_ps |]
    | Just i <- findIndex isStructPerm ps
    , Perm_Struct str_ps <- ps!!i ->
      getDistPerms >>>= \perms ->
      implGetPopConjM x ps i >>> implElimStructAllFields x str_ps >>>= \ys ->
      proveVarsImplAppendInt (fmap (valuePermsToDistPerms ys) mb_str_ps) >>>
      partialSubstForceM mb_str_ps "proveVarAtomicImpl" >>>= \str_ps' ->
      implMoveUpM (distPermsSnoc perms) str_ps' x MNil >>>
      implIntroStructAllFields x

  -- If we do not have a struct permission on the left, introduce a vacuous struct
  -- permission and fall back to the previous case
  [nuMP| Perm_Struct mb_str_ps |] ->
    let prxs = mbLift $ fmap (RL.map (const Proxy)) mb_str_ps in
    implSimplM Proxy (SImpl_IntroStructTrue x prxs) >>>
    implInsertConjM x (Perm_Struct $ trueValuePerms prxs) ps (length ps) >>>
    proveVarAtomicImpl x (ps ++ [Perm_Struct $ trueValuePerms prxs]) mb_p

  -- NOTE: existential Perm_Fun vars don't seem to make sense, as they translate
  -- to a weird form of polymorphism...
  {-
  [nuMP| Perm_Fun (PExpr_Var z) |]
    | [Perm_Fun fun_perm] <- ps
    , Left memb <- mbNameBoundP z ->
      getPSubst >>>= \psubst ->
      case psubstLookup psubst memb of
        Just fun_perm'
          | Just Refl <- funPermEq fun_perm fun_perm' -> pure ()
        Just _ -> implFailM
        Nothing -> setVarM memb fun_perm
  -}

  [nuMP| Perm_Fun mb_fun_perm |] ->
    partialSubstForceM mb_fun_perm "proveVarAtomicImpl" >>>= \fun_perm' ->
    foldr (\(i::Int,p) rest ->
            case p of
              Perm_Fun fun_perm
                | Just (Refl,Refl,Refl) <- funPermEq3 fun_perm fun_perm' ->
                  implCopyConjM x ps i >>> implPopM x (ValPerm_Conj ps)
              _ -> rest)
    (proveVarAtomicImplUnfoldOrFail x ps mb_p)
    (zip [0..] ps)

  [nuMP| Perm_BVProp mb_prop |] ->
    implPopM x (ValPerm_Conj ps) >>>
    partialSubstForceM mb_prop "proveVarAtomicImpl" >>>= \prop ->
    implTryProveBVProp x prop

  _ -> proveVarAtomicImplUnfoldOrFail x ps mb_p


-- | Prove @x:(p1 * ... * pn) |- x:(p1' * ... * pm')@ assuming that the LHS
-- conjunction is on the top of the stack, and push any leftover permissions for
-- @x@ back to the primary permissions for @x@.
--
-- The main complexity here is in dealing with the fact that both the left- and
-- right-hand sides could contain recursive permissions. We can't unfold
-- recursive permissions on both sides, because this could lead to an infinite
-- loop, where proving the unfolded implication depends on proving another copy
-- of the same implication. Instead, when we get to such a case, we have to pick
-- one side or the other to unfold, and then disallow unfolding the other side.
-- The exception is when we have an instance of the same recursive name on each
-- side, in which case we can prove the right-hand one from the left-hand one
-- and not unfold either side.
--
-- Additionally, the existence of recursive names on either side could be masked
-- by the existence of defined names that unfold to recursive names, so we have
-- to resolve all the defined names first.
--
-- Most of this machinery is actually handled by the 'proveVarImplH' cases for
-- recursive and defined names. Here, we just have to make sure to prove defined
-- names first, followed by recursive names and then other permissions.
proveVarConjImpl :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] ->
                    Mb vars [AtomicPerm a] ->
                    ImplM vars s r (ps :> a) (ps :> a) ()

-- If we are done, we are done
proveVarConjImpl x ps (mbMatch -> [nuMP| [] |]) =
  implPopM x (ValPerm_Conj ps) >>> introConjM x

-- If there is a defined or recursive name on the right, prove it first,
-- ensuring that we only choose recursive names if there are no defined ones,
-- and that, in all cases, we choose a permission that is provable with the
-- currently-set evars
proveVarConjImpl x ps mb_ps =
  (psubstMbUnsetVars <$> getPSubst) >>>= \mbUnsetVars ->
  case findBestIndex
       (\mb_ap ->
         case isProvablePerm mbUnsetVars (fmap (const x) mb_ap)
              (fmap ValPerm_Conj1 mb_ap) of
           rank | rank > 0 && mbLift (fmap isDefinedConjPerm mb_ap) ->
             isProvablePermMax + 2
           rank | rank > 0 && mbLift (fmap isRecursiveConjPerm mb_ap) ->
             isProvablePermMax + 1
           rank -> rank)
       (mbList mb_ps) of
    Just i ->
      let mb_p = fmap (!!i) mb_ps in
      let mb_ps' = fmap (deleteNth i) mb_ps in
      proveVarAtomicImpl x ps mb_p >>>
      proveVarImplInt x (fmap ValPerm_Conj mb_ps') >>>
      (partialSubstForceM (mbMap2 (,)
                           mb_ps' mb_p) "proveVarConjImpl") >>>= \(ps',p) ->
      implInsertConjM x p ps' i
    Nothing ->
      implTraceM
      (\i ->
        sep [PP.fillSep [PP.pretty
             "Could not determine enough variables to prove permissions:",
             permPretty i (fmap ValPerm_Conj mb_ps)]]) >>>=
      implFailM


----------------------------------------------------------------------
-- * Proving Permission Implications
----------------------------------------------------------------------

-- | Prove @x:p'@, where @p@ may have existentially-quantified variables in
-- it. The "@Int@" suffix indicates that this call is internal to the
-- implication prover, similar to 'proveVarsImplAppendInt', meaning that this
-- version will not end lifetimes, which must be done at the top level.
proveVarImplInt :: NuMatchingAny1 r => ExprVar a -> Mb vars (ValuePerm a) ->
                   ImplM vars s r (ps :> a) ps ()
proveVarImplInt x mb_p =
  getPerm x >>>= \ !p ->
  implPushM x p >>>
  implTraceM (\i -> pretty "proveVarImpl:" <> softline <> ppImpl i x p mb_p) >>>
  proveVarImplH x p mb_p >>>

  -- Check that the top of the stack == mb_p
  partialSubstForceM mb_p "proveVarImpl" >>>= \p_req ->
  getTopDistPerm x >>>= \p_actual ->
  if p_req == p_actual then pure () else
    implTraceM (\i ->
                 pretty "proveVarImpl: incorrect permission on top of the stack" <> softline <>
                 pretty "expected:" <+> permPretty i p_req <> softline <>
                 pretty "actual:" <+> permPretty i p_actual) >>>= error

-- | Prove @x:p'@ assuming that the primary permissions for @x@ have all been
-- pushed to the top of the stack and are equal to @p@. Pop the remaining
-- permissions for @x@ back to its primary permission when we are finished.
proveVarImplH :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
                 Mb vars (ValuePerm a) ->
                 ImplM vars s r (ps :> a) (ps :> a) ()
proveVarImplH x p mb_p = case (p, mbMatch mb_p) of

  -- Prove an empty conjunction trivially
  (_, [nuMP| ValPerm_Conj [] |]) -> implPopM x p >>> introConjM x

  -- Prove x:eq(e) by calling proveVarEq; note that we do not eliminate
  -- disjunctive permissions first because some trivial equalities do not require
  -- any eq permissions on the left, and we do not eliminate equalities on the
  -- left first because that may be the equality we are trying to prove!
  (_, [nuMP| ValPerm_Eq e |]) -> proveVarEq x p e

  -- Eliminate any disjunctions and existentials on the left
  (ValPerm_Or _ _, _) ->
    elimOrsExistsM x >>>= \ !p' -> proveVarImplH x p' mb_p

  -- Eliminate any disjunctions and existentials on the left
  (ValPerm_Exists _, _) ->
    elimOrsExistsM x >>>= \ !p' -> proveVarImplH x p' mb_p

  -- Eliminate an equality permission for a variable on the left, i.e., prove x:p
  -- from x:eq(y) by first proving y:p and then casting
  (ValPerm_Eq (PExpr_Var y), _) ->
    introEqCopyM x (PExpr_Var y) >>>
    implPopM x p >>>
    proveVarImplInt y mb_p >>>
    partialSubstForceM mb_p "proveVarImpl" >>>= \p' ->
    introCastM x y p'

  -- Prove x:eq(y &+ off) |- x:p by proving y:p@off and then casting
  (ValPerm_Eq e@(PExpr_LLVMOffset y off), _) ->
      introEqCopyM x e >>> implPopM x p >>>
      proveVarImplInt y (fmap (offsetLLVMPerm off) mb_p) >>>
      partialSubstForceM mb_p "proveVarImpl" >>>= \p_r ->
      castLLVMPtrM y (offsetLLVMPerm off p_r) off x

  -- Prove x:(p1 \/ p2) by trying to prove x:p1 and x:p2 in two branches
  (_, [nuMP| ValPerm_Or mb_p1 mb_p2 |]) ->
    implPopM x p >>>
    implCatchM
    (proveVarImplInt x mb_p1 >>>
     partialSubstForceM mb_p1 "proveVarImpl" >>>= \p1 ->
     partialSubstForceM mb_p2 "proveVarImpl" >>>= \p2 ->
     introOrLM x p1 p2)
    (proveVarImplInt x mb_p2 >>>
     partialSubstForceM mb_p1 "proveVarImpl" >>>= \p1 ->
     partialSubstForceM mb_p2 "proveVarImpl" >>>= \p2 ->
     introOrRM x p1 p2)

  -- Prove x:exists (z:tp).p by proving x:p in an extended vars context
  (_, [nuMP| ValPerm_Exists mb_p' |]) ->
    withExtVarsM (proveVarImplH x p (mbCombine RL.typeCtxProxies mb_p')) >>>= \((), e) ->
    partialSubstForceM mb_p' "proveVarImpl" >>>=
    introExistsM x e

  -- If proving P<args1,e1> |- P<args2,e2> for the same reachability permission,
  -- try to prove the RHS by either reflexivity, meaning x:eq(e2), or
  -- transitivity, meaning e1:P<args2,e2>
  (ValPerm_Named npn args1 off, [nuMP| ValPerm_Named mb_npn mb_args2 mb_off |])
    | Just (Refl, Refl, Refl) <- testNamedPermNameEq npn (mbLift mb_npn)
    , mbLift (fmap (offsetsEq off) mb_off)
    , RecursiveSortRepr _ TrueRepr <- namedPermNameSort npn
    , NameReachConstr <- namedPermNameReachConstr npn
    , PExprs_Cons args1_pre e1 <- args1
    , [nuMP| PExprs_Cons mb_args2_pre mb_e2 |] <- mbMatch mb_args2 ->
      implCatchM

      -- Reflexivity branch: pop x:P<...>, prove x:eq(e), and use reflexivity
      (implPopM x p >>> proveVarImplInt x (fmap ValPerm_Eq mb_e2) >>>
       partialSubstForceM mb_args2 "proveVarImpl" >>>= \args2 ->
        implReachabilityReflM x npn args2 off)

      -- Transitivity branch: copy x:P<args1,e1> if possible, equalize the
      -- arguments by proving x:P<args2,e1>, introduce variable y:eq(e1), prove
      -- y:P<args2,e2>, and then finally use transitivity
      (implMaybeCopyPopM x p >>>
       proveNamedArgs x npn args1 off (fmap (:>: e1) mb_args2_pre) >>>
       (case e1 of
           PExpr_Var y -> pure y
           _  ->
             -- If e1 is not a variable, bind a fresh variable y:eq(e1), then
             -- cast x:P<args1,e1> to x:P<args1,y>
             implGetVarType x >>>= \tp ->
             implLetBindVar tp e1 >>>= \y ->
             proveEqCast x (\z -> ValPerm_Named npn (args1_pre :>: z) off) e1
             (fmap (const $ PExpr_Var y) mb_npn) >>>
             pure y) >>>= \y ->
       proveVarImplInt y mb_p >>>
       partialSubstForceM mb_args2 "proveVarImpl" >>>= \args2 ->
       implReachabilityTransM x npn args2 off y)

  -- If proving P<args1> |- P<args2> for the same named permission, try to
  -- equalize the arguments and the offsets using proveNamedArgs. Note that we
  -- currently are *not* solving for offsets on the right, meaning that
  -- proveVarImplInt will fail for offsets with existential variables in them.
  (ValPerm_Named npn args off, [nuMP| ValPerm_Named mb_npn mb_args mb_off |])
    | Just (Refl, Refl, Refl) <- testNamedPermNameEq npn (mbLift mb_npn)
    , mbLift (fmap (offsetsEq off) mb_off) ->
      implMaybeCopyPopM x p >>>
      proveNamedArgs x npn args off mb_args

  -- If proving x:p1 * ... * pn |- P<args>@off where P<args'>@off for some args'
  -- occurs as one of the pi, then reduce to the above case
  --
  -- FIXME: if P is a defined permission, then it is possible that we can't prove
  -- P<args'> |- P<args> but could still prove x:p1 * ... |- P<args> by unfolding
  -- P, so we should also check that args' is compatible in some way with args
  (ValPerm_Conj ps, [nuMP| ValPerm_Named mb_npn mb_args mb_off |])
    | npn <- mbLift mb_npn
    , TrueRepr <- nameIsConjRepr npn
    , (i, (args, off)):_ <-
        findMaybeIndices (\case
                             Perm_NamedConj npn' args off
                               | Just (Refl, Refl, Refl) <-
                                   testNamedPermNameEq npn npn'
                               , mbLift (fmap (offsetsEq off) mb_off) ->
                                 Just (args, off)
                             _ -> Nothing) ps ->
      implGetPopConjM x ps i >>>
      implNamedFromConjM x npn args off >>>
      proveNamedArgs x npn args off mb_args

  -- If proving P<args> where P is defined, unfold P
  (_, [nuMP| ValPerm_Named mb_npn _ _ |])
    | DefinedSortRepr _ <- namedPermNameSort $ mbLift mb_npn ->
      proveVarImplFoldRight x p mb_p

  -- If proving P<args1> |- p where P is defined, unfold P
  (ValPerm_Named npn _ _, _)
    | DefinedSortRepr _ <- namedPermNameSort npn ->
      proveVarImplUnfoldLeft x p mb_p Nothing

  -- If proving x:p1 * ... * P<args1> * ... |- p where P is defined, unfold P
  (ValPerm_Conj ps, _)
    | Just i <- findIndex isDefinedConjPerm ps ->
      proveVarImplUnfoldLeft x p mb_p (Just i)

  -- If proving P1<args1> |- P2<args2> where both P1 and P2 are recursive, try
  -- unfolding P1 or P2, depending on the recursion flags
  (ValPerm_Named npn1 _ _, [nuMP| ValPerm_Named mb_npn2 _ _ |])
    | RecursiveSortRepr _ _ <- namedPermNameSort npn1
    , RecursiveSortRepr _ _ <- namedPermNameSort $ mbLift mb_npn2 ->
      implRecFlagCaseM
      (proveVarImplFoldRight x p mb_p)
      (proveVarImplUnfoldLeft x p mb_p Nothing)

  -- If proving x:p1 * ... |- P<args> where both P and at least one of the pi are
  -- recursive, try unfolding P or the LHS, depending on the recursion flags. Note
  -- that there are no defined perms on the LHS at this point because that would
  -- have been caught by one of the above cases.
  (ValPerm_Conj ps, [nuMP| ValPerm_Named mb_npn _ _ |])
    | Just i <- findIndex isRecursiveConjPerm ps
    , RecursiveSortRepr _ _ <- namedPermNameSort $ mbLift mb_npn ->
      implRecFlagCaseM
      (proveVarImplUnfoldLeft x p mb_p (Just i))
      (proveVarImplFoldRight x p mb_p)

  -- If proving P<args> where P is recursive and we have gotten to this case, we
  -- know there are no recursive perms on the left, so unfold P
  (_, [nuMP| ValPerm_Named mb_npn _ _ |])
    | RecursiveSortRepr _ _ <- namedPermNameSort $ mbLift mb_npn ->
      proveVarImplFoldRight x p mb_p

  -- If proving P<args> |- p1 * ... * pn for a conjoinable P, then change the LHS
  -- to a conjunction and recurse
  (ValPerm_Named npn args off, _)
    | TrueRepr <- nameIsConjRepr npn ->
      implNamedToConjM x npn args off >>>
      proveVarImplH x (ValPerm_Conj1 $ Perm_NamedConj npn args off) mb_p

  -- If proving P<args> |- p1 * ... * pn for a non-conjoinable recursive P, then
  -- we unfold P because we will have to at some point to prove a conjunction
  (ValPerm_Named _ _ _, _) ->
    proveVarImplUnfoldLeft x p mb_p Nothing


  {- FIXME: This is an example of how we used embedMbImplM to prove the body
     of one mu from another; remove it when we have used it for arrays
  (ValPerm_Mu p_body, [nuMP| ValPerm_Mu mb_p'_body |]) ->
    partialSubstForceM mb_p'_body
    "proveVarImpl: incomplete psubst: implMu" >>>= \p'_body ->
    embedMbImplM (fmap (\p -> distPermSet $ distPerms1 x p) p_body)
    (mbMap2 (\p p' -> proveVarImplH x p (emptyMb p') >>> pure Refl)
     p_body p'_body) >>>= \mb_impl ->
    implSimplM Proxy (SImpl_Mu x p_body p'_body mb_impl)
  -}

  -- If x:eq(LLVMword(e)) then we cannot prove any pointer permissions for it
  (ValPerm_Eq (PExpr_LLVMWord _), [nuMP| ValPerm_Conj _ |]) ->
    implFailVarM "proveVarImplH" x p mb_p

  -- If x:eq(struct(e1,...,en)) then we eliminate to x:struct(eq(e1),...,eq(en))
  (ValPerm_Eq (PExpr_Struct exprs), [nuMP| ValPerm_Conj _ |]) ->
    implSimplM Proxy (SImpl_StructEqToPerm x exprs) >>>
    implPopM x (ValPerm_Conj1 $ Perm_Struct $
                RL.map ValPerm_Eq $ exprsToRAssign exprs) >>>
    proveVarImplInt x mb_p

  -- If proving a function permission for an x we know equals a constant function
  -- handle f, look up the function permission for f
  (ValPerm_Eq (PExpr_Fun f), [nuMP| ValPerm_Conj [Perm_Fun mb_fun_perm] |]) ->
    use implStatePermEnv >>>= \env ->
    case lookupFunPerm env f of
      Just (SomeFunPerm fun_perm, ident)
        | [nuMP| Just (Refl,Refl,Refl) |] <-
            mbMatch $ fmap (funPermEq3 fun_perm) mb_fun_perm ->
          introEqCopyM x (PExpr_Fun f) >>>
          implPopM x p >>>
          implSimplM Proxy (SImpl_ConstFunPerm x f fun_perm ident)
      _ -> implFailVarM "proveVarImplH" x p mb_p

  (ValPerm_Eq _, [nuMP| ValPerm_Conj _ |]) ->
    implFailVarM "proveVarImplH" x p mb_p
    -- FIXME HERE: are there other x:eq(e) |- x:pps cases?

  -- For conjunction |- conjunction, call proveVarConjImpl
  (ValPerm_Conj ps, [nuMP| ValPerm_Conj mb_ps |]) ->
    proveVarConjImpl x ps mb_ps

  -- Prove x:p |- x:z@off for existential variable z by setting z = p
  (_, [nuMP| ValPerm_Var z mb_off |])
    | Left memb <- mbNameBoundP z ->
      getPSubst >>>= \psubst ->
      case (partialSubst psubst mb_off, psubstLookup psubst memb) of
        (Just off, Just (PExpr_ValPerm p')) ->
          let mb_p' = fmap (const $ offsetPerm off p') z in
          implTraceM (\i -> pretty "proveVarImplH:" <> softline <> ppImpl i x p mb_p') >>>
          proveVarImplH x p mb_p'
        (Just off, Just (PExpr_Var z')) ->
          let mb_p' = fmap (const $ ValPerm_Var z' off) z in
          implTraceM (\i -> pretty "proveVarImplH:" <> softline <> ppImpl i x p mb_p') >>>
          proveVarImplH x p mb_p'
        (Just off, Nothing) ->
          setVarM memb (PExpr_ValPerm $ offsetPerm (negatePermOffset off) p) >>>
          implMaybeCopyPopM x p
        (Nothing, _) ->
          implFailVarM "proveVarImplH" x p mb_p

  -- Prove x:z@off |- x:z@off for variable z by reflexivity
  (ValPerm_Var z off, [nuMP| ValPerm_Var mb_z' mb_off |])
    | Right z' <- mbNameBoundP mb_z'
    , z' == z
    , mbLift (fmap (offsetsEq off) mb_off) -> pure ()

  -- Fail if nothing else matched
  _ -> implFailVarM "proveVarImplH" x p mb_p


----------------------------------------------------------------------
-- * Proving Permission Implications for Existential Variables
----------------------------------------------------------------------

-- | Prove an existentially-quantified permission where the variable holding the
-- permission could itself be existentially-quantified. If that variable is
-- existentially quantified, be sure to instantiate it with a variable that is
-- locally bound inside the current implication proof, i.e., that is returned by
-- 'getVarVarM'. Return the variable that was used.
proveExVarImpl :: NuMatchingAny1 r => PartialSubst vars -> Mb vars (Name tp) ->
                  Mb vars (ValuePerm tp) ->
                  ImplM vars s r (ps :> tp) ps (Name tp)

-- If the variable is a free variable, just call proveVarImpl
proveExVarImpl _psubst mb_x mb_p
  | Right n <- mbNameBoundP mb_x
  = proveVarImplInt n mb_p >>> pure n

-- If the variable is instantiated to a non-variable expression, bind a fresh
-- variable for it and then call proveVarImpl
proveExVarImpl psubst mb_x mb_p
  | Left memb <- mbNameBoundP mb_x
  , Just _ <- psubstLookup psubst memb =
    getVarVarM memb >>>= \n ->
    proveVarImplInt n mb_p >>> pure n

-- Special case: if proving an LLVM frame permission, look for an LLVM frame in
-- the current context and use it
proveExVarImpl _ mb_x mb_p@(mbMatch -> [nuMP| ValPerm_Conj [Perm_LLVMFrame _] |])
  | Left memb <- mbNameBoundP mb_x =
    getExVarType memb >>>= \x_tp ->
    implFindVarOfType x_tp >>>= \maybe_n ->
    case maybe_n of
      Just n ->
        -- NOTE: we still need to call getVarVarM to get a locally-bound var
        setVarM memb (PExpr_Var n) >>>
        getVarVarM memb >>>= \n' ->
        proveVarImplInt n' mb_p >>> pure n'
      Nothing ->
        implFailMsgM "proveExVarImpl: No LLVM frame pointer in scope"

-- Otherwise we fail
proveExVarImpl _ mb_x mb_p =
  implTraceM (\i -> pretty "proveExVarImpl: existential variable" <+>
                    permPretty i mb_x <+>
                    pretty "not resolved when trying to prove:" <> softline <>
                    permPretty i mb_p) >>>=
  implFailM


----------------------------------------------------------------------
-- * Proving Multiple Permission Implications
----------------------------------------------------------------------

-- | A list of distinguished permissions with existential variables
type ExDistPerms vars ps = Mb vars (DistPerms ps)

-- | Existentially quantify a list of distinguished permissions over the empty
-- set of existential variables
distPermsToExDistPerms :: DistPerms ps -> ExDistPerms RNil ps
distPermsToExDistPerms = emptyMb

-- | Combine a list of names and a sequence of permissions inside a name-binding
-- to get an 'ExDistPerms'
mbValuePermsToExDistPerms :: RAssign Name ps -> Mb vars (ValuePerms ps) ->
                             ExDistPerms vars ps
mbValuePermsToExDistPerms MNil mb_ps = fmap (const DistPermsNil) mb_ps
mbValuePermsToExDistPerms (xs :>: x) mb_ps =
  mbMap2 (\ps p -> DistPermsCons ps x p)
  (mbValuePermsToExDistPerms xs (fmap RL.tail mb_ps))
  (fmap RL.head mb_ps)

-- | Substitute arguments into a function permission to get the existentially
-- quantified input permissions needed on the arguments
funPermExDistIns :: FunPerm ghosts args ret -> RAssign Name args ->
                    ExDistPerms ghosts (ghosts :++: args)
funPermExDistIns fun_perm args =
  fmap (varSubst (permVarSubstOfNames args)) $ mbSeparate args $
  mbValuePermsToDistPerms $ funPermIns fun_perm

-- | A splitting of an existential list of permissions into a prefix, a single
-- variable plus permission, and then a suffix
data ExDistPermsSplit vars ps where
  ExDistPermsSplit :: ExDistPerms vars ps1 ->
                      Mb vars (ExprVar a) -> Mb vars (ValuePerm a) ->
                      ExDistPerms vars ps2 ->
                      ExDistPermsSplit vars (ps1 :> a :++: ps2)

-- | Extend the @ps@ argument of a 'ExDistPermsSplit'
extExDistPermsSplit :: ExDistPermsSplit vars ps ->
                       Mb vars (ExprVar b) -> Mb vars (ValuePerm b) ->
                       ExDistPermsSplit vars (ps :> b)
extExDistPermsSplit (ExDistPermsSplit ps1 mb_x mb_p ps2) y p' =
  ExDistPermsSplit ps1 mb_x mb_p $
  mbMap2 DistPermsCons ps2 y `mbApply` p'


-- | The maximum priority returned by 'isProvablePerm'
isProvablePermMax :: Int
isProvablePermMax = 2

-- | Test if a permission is of a form where 'proveExVarImpl' will succeed,
-- given the current set of existential variables whose values have not been
-- set. Return a priority for the permission, where higher priorities are proved
-- first and 0 means it cannot be proved.
isProvablePerm :: Mb vars (NameSet CrucibleType) ->
                  Mb vars (ExprVar a) -> Mb vars (ValuePerm a) -> Int

-- Lifetime permissions can always be proved, but we want to prove them after
-- any other permissions that might depend on them, so they get priority 1
isProvablePerm _ _ (mbMatch -> [nuMP| ValPerm_Conj mb_ps |])
  | mbLift $ fmap (any (isJust . isLifetimePerm)) mb_ps = 1

-- If x and all the needed vars in p are set, we can prove x:p
isProvablePerm mbUnsetVars mb_x mb_p
  | mbNeeded <- mbMap2 (\x p -> NameSet.insert x $ neededVars p) mb_x mb_p
  , mbLift $ mbMap2 (\s1 s2 ->
                      NameSet.null $
                      NameSet.intersection s1 s2) mbNeeded mbUnsetVars = 2

-- Special case: an LLVMFrame permission can always be proved
isProvablePerm _ _ (mbMatch -> [nuMP| ValPerm_Conj [Perm_LLVMFrame _] |]) = 2

-- Special case: a variable permission X can always be proved when the variable
-- x and the offset are known, since X is either a free variable, so we can
-- substitute the current permissions on x, or X is set to a ground permission,
-- so we can definitely try to prove it
isProvablePerm mbUnsetVars mb_x (mbMatch -> [nuMP| ValPerm_Var _ mb_off |])
  | mbNeeded <- mbMap2 (\x off -> NameSet.insert x $ freeVars off) mb_x mb_off
  , mbLift $ mbMap2 (\s1 s2 ->
                      NameSet.null $
                      NameSet.intersection s1 s2) mbNeeded mbUnsetVars = 2

-- Otherwise we cannot prove the permission, so we return priority 0
isProvablePerm _ _ _ = 0


-- | Choose the next permission in the supplied list to try to prove by picking
-- one with maximal priority, as returned by 'isProvablePerm', and return its
-- location in the supplied list along with its priority. We assume that the
-- list is non-empty.
findProvablePerm :: Mb vars (NameSet CrucibleType) -> ExDistPerms vars ps ->
                    (Int, ExDistPermsSplit vars ps)
findProvablePerm mbUnsetVars mb_ps = case mbMatch mb_ps of

  [nuMP| DistPermsNil |] ->
    error "findProvablePerm: empty list"

  [nuMP| DistPermsCons ps_nil@DistPermsNil mb_x mb_p |] ->
    (isProvablePerm mbUnsetVars mb_x mb_p,
     ExDistPermsSplit ps_nil mb_x mb_p ps_nil)

  [nuMP| DistPermsCons ps mb_x mb_p |] ->
    let (best_rank,best) = findProvablePerm mbUnsetVars ps in
    let rank = isProvablePerm mbUnsetVars mb_x mb_p in
    if rank > best_rank then
      (rank, ExDistPermsSplit ps mb_x mb_p (fmap (const DistPermsNil) mb_p))
    else
      (best_rank, extExDistPermsSplit best mb_x mb_p)


-- | Find all existential lifetime variables that are assigned permissions in an
-- 'ExDistPerms' list, and instantiate them with fresh lifetimes
instantiateLifetimeVars :: NuMatchingAny1 r => ExDistPerms vars ps ->
                           ImplM vars s r ps_in ps_in ()
instantiateLifetimeVars mb_ps =
  do psubst <- getPSubst
     instantiateLifetimeVars' psubst mb_ps

-- | The main loop for 'instantiateLifetimeVars'
instantiateLifetimeVars' :: NuMatchingAny1 r => PartialSubst vars ->
                            ExDistPerms vars ps -> ImplM vars s r ps_in ps_in ()
instantiateLifetimeVars' psubst mb_ps = case mbMatch mb_ps of
  [nuMP| DistPermsNil |] -> pure ()
  [nuMP| DistPermsCons mb_ps' mb_x (ValPerm_Conj1 mb_p) |]
    | Just Refl <- mbLift $ fmap isLifetimePerm mb_p
    , Left memb <- mbNameBoundP mb_x
    , Nothing <- psubstLookup psubst memb ->
      implBeginLifetimeM >>>= \l ->
      setVarM memb (PExpr_Var l) >>>
      instantiateLifetimeVars' (psubstSet memb (PExpr_Var l) psubst) mb_ps'
  [nuMP| DistPermsCons mb_ps' _ _ |] ->
    instantiateLifetimeVars' psubst mb_ps'


-- | Internal-only version of 'proveVarsImplAppend' that is called recursively
-- by the implication prover. The distinction is that this version does not end
-- any lifetimes, because lifetimes are only ended at the top level, by
-- 'proveVarsImplAppend'.
proveVarsImplAppendInt :: NuMatchingAny1 r => ExDistPerms vars ps ->
                          ImplM vars s r (ps_in :++: ps) ps_in ()
proveVarsImplAppendInt (mbMatch -> [nuMP| DistPermsNil |]) = return ()
proveVarsImplAppendInt ps =
  getPSubst >>>= \psubst ->
  use implStatePerms >>>= \cur_perms ->
  case findProvablePerm (psubstMbUnsetVars psubst) ps of
    ((> 0) -> True, ExDistPermsSplit ps1 mb_x mb_p ps2) ->
      proveExVarImpl psubst mb_x mb_p >>>= \x ->
      proveVarsImplAppendInt (mbMap2 appendDistPerms ps1 ps2) >>>
      implMoveUpM cur_perms (mbDistPermsToProxies ps1) x (mbDistPermsToProxies ps2)
    _ ->
      implTraceM
      (\i ->
        sep [PP.fillSep [PP.pretty
             "Could not determine enough variables to prove permissions:",
             permPretty i ps]]) >>>=
      implFailM

-- | Prove a list of existentially-quantified distinguished permissions and put
-- those proofs onto the stack. This is the same as 'proveVarsImplAppendInt'
-- except that the stack starts out empty and is replaced by the proofs, rather
-- than appending the proofs to the stack that is already there.
proveVarsImplInt :: NuMatchingAny1 r => ExDistPerms vars as ->
                    ImplM vars s r as RNil ()
proveVarsImplInt ps
  | Refl <- mbLift (fmap RL.prependRNilEq $ mbDistPermsToValuePerms ps) =
    proveVarsImplAppendInt ps

-- | Prove one sequence of permissions from another and capture the proof as a
-- 'LocalPermImpl'
localProveVars :: NuMatchingAny1 r => DistPerms ps_in -> DistPerms ps_out ->
                  ImplM vars s r ps ps (LocalPermImpl ps_in ps_out)
localProveVars ps_in ps_out =
  implTraceM (\i -> sep [pretty "localProveVars:", permPretty i ps_in,
                         pretty "-o", permPretty i ps_out]) >>>
  LocalPermImpl <$>
  embedImplM ps_in (recombinePerms ps_in >>>
                    proveVarsImplInt (emptyMb ps_out) >>>
                    pure (LocalImplRet Refl))


----------------------------------------------------------------------
-- * External Entrypoints to the Implication Prover
----------------------------------------------------------------------

-- | Prove a list of existentially-quantified distinguished permissions, adding
-- those proofs to the top of the stack. In the case that a the variable itself
-- whose permissions are being proved is existentially-quantified --- that is,
-- if we are proving @x:p@ for existentially-quantified @x@ --- then the
-- resulting permission on top of the stack will be @y:[e/x]p@, where @y@ is a
-- fresh variable and @e@ is the expression used to instantiate @x@.
proveVarsImplAppend :: NuMatchingAny1 r => ExDistPerms vars ps ->
                       ImplM vars s r (ps_in :++: ps) ps_in ()
proveVarsImplAppend mb_ps =
  use implStatePerms >>>= \(_ :: PermSet ps_in) ->
  let prx :: Proxy ps_in = Proxy in
  lifetimesThatCouldProve mb_ps >>>= \ls_ps ->
  foldr1 implCatchM
  ((proveVarsImplAppendInt mb_ps)
   :
   flip map ls_ps
   (\case
       (l,l_p@(Perm_LOwned ps_in@(lownedPermsToDistPerms ->
                                  Just dps_in) ps_out)) ->
         implTraceM (\i ->
                      sep [pretty "Ending lifetime" <+> permPretty i l,
                           pretty "in order to prove:",
                           permPretty i mb_ps]) >>>
         proveVarsImplAppendInt (fmap (const dps_in) mb_ps) >>>
         implPushM l (ValPerm_Conj1 l_p) >>>
         implEndLifetimeM prx l ps_in ps_out >>>
         implTraceM (\i -> pretty "Lifetime" <+> permPretty i l
                           <+> pretty "ended") >>>
         proveVarsImplAppend mb_ps
       _ -> error "proveVarsImplAppend: unexpected lifetimesThatCouldProve result"))

-- | Prove a list of existentially-quantified distinguished permissions and put
-- those proofs onto the stack. This is the same as 'proveVarsImplAppend' except
-- that the stack starts out empty and is replaced by the proofs, rather than
-- appending the proofs to the stack that is already there.
proveVarsImpl :: NuMatchingAny1 r => ExDistPerms vars as ->
                 ImplM vars s r as RNil ()
proveVarsImpl ps
  | Refl <- mbLift (fmap RL.prependRNilEq $ mbDistPermsToValuePerms ps) =
    proveVarsImplAppend ps

-- | Prove a list of existentially-quantified permissions and put the proofs on
-- the stack, similarly to 'proveVarsImpl', but ensure that the existential
-- variables are themselves only instanitated with variables, not arbitrary
-- terms. The variables must be distinct from each other and from any other
-- variables in scope. Return the variables used to instantiate the evars.
proveVarsImplVarEVars :: NuMatchingAny1 r => ExDistPerms vars as ->
                         ImplM vars s r as RNil (RAssign ExprVar vars)
proveVarsImplVarEVars mb_ps =
  proveVarsImpl mb_ps >>>
  use implStateVars >>>= \vars ->
  -- gmodify (over implStatePSubst (completePSubst vars)) >>>
  traverseRAssign getVarVarM (RL.members $ cruCtxProxies vars) >>>= \xs ->
  getPSubst >>>= \psubst ->
  let s = completePSubst vars psubst in
  let vars_eqpf =
        traverseRAssign (\(Pair x e) -> someEqProofPerm x e False) $
        RL.map2 Pair xs (exprsOfSubst s) in
  let perms_eqpf = fmap (\es -> subst (substOfExprs es) $
                                mbDistPermsToValuePerms mb_ps) vars_eqpf in
  implCastStackM perms_eqpf >>>
  pure xs

-- | Prove @x:p'@, where @p@ may have existentially-quantified variables in it.
proveVarImpl :: NuMatchingAny1 r => ExprVar a -> Mb vars (ValuePerm a) ->
                ImplM vars s r (ps :> a) ps ()
proveVarImpl x mb_p = proveVarsImplAppend $ fmap (distPerms1 x) mb_p
