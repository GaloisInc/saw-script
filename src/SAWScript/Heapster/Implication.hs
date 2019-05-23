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

module SAWScript.Heapster.Implication where

import Data.Kind
import Data.Functor.Const
import Data.Functor.Product
import Control.Monad
-- import Control.Monad.State
import Data.Parameterized.Ctx
import Data.Parameterized.Context
import Data.Parameterized.NatRepr
import Data.Parameterized.TraversableFC
import Data.Parameterized.Some

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core

import SAWScript.Heapster.Permissions hiding ((>>>=))


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


----------------------------------------------------------------------
-- * Permission Implication Monad
----------------------------------------------------------------------

newtype ValuePerms ctx a = ValuePerms [ValuePerm ctx a]

instance Weakenable' ValuePerms where
  weaken' w (ValuePerms ps) = ValuePerms $ map (weaken' w) ps

newtype MultiPermSet ctx =
  MultiPermSet (Assignment (ValuePerms ctx) ctx)

instance Weakenable MultiPermSet where
  weaken w (MultiPermSet asgn) =
    MultiPermSet $ weakenAssignment (\_ -> ValuePerms []) w $
    fmapFC (weaken' w) asgn

getMultiPerms :: MultiPermSet ctx -> PermVar ctx a -> ValuePerms ctx a
getMultiPerms (MultiPermSet perms) (PermVar _ ix) = perms ! ix

extendMultiPerms :: MultiPermSet ctx -> MultiPermSet (ctx ::> tp)
extendMultiPerms (MultiPermSet asgn) =
  MultiPermSet $ extend (fmapFC (weaken' mkWeakening1) asgn) (ValuePerms [])

data ImplState ctx =
  ImplState { implCtx :: CtxRepr ctx,
              implPerms :: MultiPermSet ctx }

extendImplState :: ImplState ctx -> TypeRepr tp -> ImplState (ctx ::> tp)
extendImplState (ImplState {..}) tp =
  ImplState { implCtx = extend implCtx tp,
              implPerms = extendMultiPerms implPerms }

newtype ImplM fin fout ctx a =
  ImplM { unImplM :: forall ctx'. Weakening ctx ctx' -> ImplState ctx' ->
                     (forall ctx''. Weakening ctx' ctx'' ->
                      ImplState ctx'' -> a -> fin ctx'') ->
                     fout ctx' }

runImplM :: ImplM (Const a) fout ctx a -> ImplState ctx -> fout ctx
runImplM (ImplM m) s = m identityWeakening s $ \_ _ a -> Const a

infixl 1 >>>=
(>>>=) :: ImplM f2 f3 ctx a -> (a -> ImplM f1 f2 ctx b) ->
          ImplM f1 f3 ctx b
(ImplM m) >>>= f =
  ImplM $ \w s k ->
  m w s $ \w' s' a ->
  unImplM (f a) (composeWeakenings w w') s' $ \w'' -> k (composeWeakenings w' w'')

instance Functor (ImplM f f ctx) where
  fmap f m = m >>= return . f

instance Applicative (ImplM f f ctx) where
  pure = return
  (<*>) = ap

instance Monad (ImplM f f ctx) where
  return x = ImplM $ \w s k -> k identityWeakening s x
  m >>= f = m >>>= f

cstate :: (forall ctx'. Weakening ctx ctx' -> ImplState ctx' ->
           (a, ImplState ctx')) ->
          ImplM f f ctx a
cstate f = ImplM $ \w s k ->
  let (a, s') = f w s in
  k identityWeakening s a

lookupType :: PermVar ctx a -> ImplM f f ctx (TypeRepr a)
lookupType x =
  cstate $ \w s -> (implCtx s ! indexOfPermVar (weaken' w x), s)

withVarPerms :: PermVar ctx tp ->
                (forall ctx'. Weakening ctx ctx' -> ValuePerms ctx' tp ->
                 ImplM fin fout ctx' a) ->
                ImplM fin fout ctx a
withVarPerms x f =
  ImplM $ \w s k ->
  unImplM (f w (getMultiPerms (implPerms s) (weaken' w x))) identityWeakening s k

cmapCont :: (forall ctx'. Weakening ctx ctx' -> fout ctx' -> fout' ctx') ->
            ImplM fin fout ctx a -> ImplM fin fout' ctx a
cmapCont f (ImplM m) =
  ImplM $ \w s k ->
  f w $ m w s $ \w' s' a -> k w' s' a

cmapContIn :: (forall ctx'. Weakening ctx ctx' -> fin' ctx' -> fin ctx') ->
              ImplM fin fout ctx a -> ImplM fin' fout ctx a
cmapContIn f m =
  m >>>= \a -> cmapCont f (return a)

cmapContBind :: TypeRepr tp ->
                (forall ctx'. Weakening ctx ctx' ->
                 fout (ctx' ::> tp) -> fout' ctx') ->
                ImplM fin fout (ctx ::> tp) a -> ImplM fin fout' ctx a
cmapContBind tp f (ImplM m) =
  ImplM $ \w s k ->
  f w $ m (weakenWeakening1 w) (extendImplState s tp) $ \w' s' a ->
  k (composeWeakenings mkWeakening1 w') s' a
