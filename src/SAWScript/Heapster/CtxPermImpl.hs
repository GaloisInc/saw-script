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

module SAWScript.Heapster.CtxPermImpl where

import Data.Kind
import Data.Parameterized.Ctx
import Data.Parameterized.Context
import Data.Parameterized.NatRepr

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core

import SAWScript.Heapster.Permissions
import SAWScript.Heapster.CtxMonad as C


----------------------------------------------------------------------
-- * Permission Implications
----------------------------------------------------------------------

data PermImpl (f :: Ctx CrucibleType -> Data.Kind.*) (ctx :: Ctx CrucibleType) where
  Impl_Done :: f ctx -> PermImpl f ctx
  -- ^ No more elimination; i.e., implements the rule
  --
  -- -------------------------------
  -- Gin | Pin |- Pin

  Impl_Fail :: PermImpl f ctx
  -- ^ The empty tree, with no disjunctive possibilities; i.e., implements the
  -- rule
  --
  -- ------------------------------
  -- Gin | Pin |- Pany

  Impl_Catch :: PermImpl f ctx -> PermImpl f ctx -> PermImpl f ctx
  -- ^ Copy the same permissions into two different elimination trees, where an
  -- 'Impl_Fail' in the first tree "calls" the second tree, just like a
  -- try-catch block for exceptions. This implements the rule:
  --
  -- pf1 = Gin | Pin |- rets1    pf2 = Gin | Pin |- rets2
  -- ----------------------------------------------------
  -- Gin | Pin |- rets1, rets2

  Impl_ElimOr :: Index ctx a -> PermImpl f ctx -> PermImpl f ctx -> PermImpl f ctx
  -- ^ Eliminate a 'ValPerm_Or' on the given variable, replacing it with the
  -- left- and right-hand sides in the two sub-eliminations
  --
  -- pf1 = Gin | Pin, x:p1 |- GsPs1     pf2 = Gin | Pin, x:p2 |- GsPs2
  -- -----------------------------------------------------------------
  -- Gin | Pin, x:(p1 \/ p2) |- GsPs1, GsPs2

  Impl_IntroOrL :: Index ctx a -> PermImpl f ctx -> PermImpl f ctx
  -- ^ @Impl_IntroOrL x p2 pf@ is the left disjunction introduction rule
  --
  -- > pf = Gamma | Pin |- e:p1, Pout
  -- > ---------------------------------
  -- > Gamma | Pin |- e:(p1 \/ p2), Pout

  Impl_IntroOrR :: Index ctx a -> PermImpl f ctx -> PermImpl f ctx
  -- ^ @Impl_IntroOrR x p1 pf@ is the right disjunction introduction rule
  --
  -- > pf = Gamma | Pin |- e:p2, Pout
  -- > ---------------------------------
  -- > Gamma | Pin |- e:(p1 \/ p2), Pout

  Impl_ElimExists :: Index ctx a -> TypeRepr tp -> PermImpl f (ctx ::> tp) ->
                     PermImpl f ctx
  -- ^ Eliminate an existential, i.e., a 'ValPerm_Exists', on the given variable
  --
  -- pf = Gin, z:tp | Pin, x:p, z:true |- rets
  -- ------------------------------------------------------
  -- Gin | x:(exists z:tp. p)  |- rets

  Impl_IntroExists :: Index ctx a -> TypeRepr tp -> PermExpr ctx tp ->
                      ValuePerm (ctx ::> tp) a ->
                      PermImpl f ctx -> PermImpl f ctx
  -- ^ @Intro_Exists x tp e p pf@ is the existential introduction rule
  --
  -- > pf = Gamma | Pin |- x:[e'/z]p, Pout
  -- > --------------------------------------
  -- > Gamma | Pin |- x:(exists z:tp.p), Pout


instance C.Weakenable f => C.Weakenable (PermImpl f) where
  weaken _ _ _ = error "FIXME HERE: Weakenable instance for PermImpl"


----------------------------------------------------------------------
-- * Permission Implication Monad
----------------------------------------------------------------------

newtype ValuePerms ctx a = ValuePerms [ValuePerm ctx a]

newtype MultiPermSet ctx =
  MultiPermSet (Assignment (ValuePerms ctx) ctx)

instance C.Weakenable MultiPermSet where
  weaken w sz (MultiPermSet asgn) =
    error "FIXME HERE: need Weakenable for ValuePerm"

type PImplM f =
  C.CStateT MultiPermSet (C.CContT (PermImpl f) CIdentity)

newtype Flip f a ctx = Flip { unFlip :: f ctx a }

instance C.Weakenable (Flip ValuePerms a) where
  weaken _ _ _ = error "FIXME HERE: Weakenable for Flip"

getMultiPerms :: CExpr MultiPermSet ctx -> CExpr (CVar a) ctx ->
                 CExpr (Flip ValuePerms a) ctx
getMultiPerms =
  cOp2 (\(MultiPermSet perms) (CVar ix) -> Flip (perms ! ix))

lookupPerm :: C.Weakenable  f =>
              CExpr (CVar a :->: PImplM f (Flip ValuePerms a)) ectx
lookupPerm =
  clam $ \x ->
  C.cget C.>>>= \perms ->
  C.creturn $ getMultiPerms perms x
