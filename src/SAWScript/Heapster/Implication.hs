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

module SAWScript.Heapster.Implication where

import Data.Kind
import Data.Functor.Const
import Data.Functor.Product
import Control.Lens
import Control.Monad
import Control.Monad.Trans
import Control.Monad.State

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
-- * Multi-Valued Permission Sets
----------------------------------------------------------------------

-- | A list of 0 or more 'ValuePerm's
newtype ValuePerms ctx a = ValuePerms { unValuePerms :: [ValuePerm ctx a] }

instance Weakenable' ValuePerms where
  weaken' w (ValuePerms ps) = ValuePerms $ map (weaken' w) ps

valuePermsIso :: Iso' (ValuePerms ctx a) [ValuePerm ctx a]
valuePermsIso = iso unValuePerms ValuePerms

-- | A set of 0 or more permissions for each variable in scope
newtype MultiPermSet ctx =
  MultiPermSet { unMultiPermSet :: (Assignment (ValuePerms ctx) ctx) }

instance Weakenable MultiPermSet where
  weaken w (MultiPermSet asgn) =
    MultiPermSet $ weakenAssignment (\_ -> ValuePerms []) w $
    fmapFC (weaken' w) asgn

-- | Weaken a 'MultiPermSet'
weaken1MultiPerms :: MultiPermSet ctx -> MultiPermSet (ctx ::> tp)
weaken1MultiPerms (MultiPermSet asgn) =
  MultiPermSet $ extend (fmapFC (weaken' mkWeakening1) asgn) (ValuePerms [])

multiPermSetIso :: Iso' (MultiPermSet ctx) (Assignment (ValuePerms ctx) ctx)
multiPermSetIso = iso unMultiPermSet MultiPermSet

varPerms :: PermVar ctx a -> Lens' (MultiPermSet ctx) [ValuePerm ctx a]
varPerms (PermVar _ ix) = multiPermSetIso . ixF' ix . valuePermsIso

-- | A location in a 'MultiPermSet' of a specific permission on a variable
data PermLoc ctx a = PermLoc (PermVar ctx a) Int

instance Weakenable' PermLoc where
  weaken' w (PermLoc x i) = PermLoc (weaken' w x) i

varLoc0 :: PermVar ctx a -> PermLoc ctx a
varLoc0 x = PermLoc x 0

weaken1PermLoc :: PermLoc ctx a -> PermLoc (ctx ::> tp) a
weaken1PermLoc = weaken' mkWeakening1

varPerm :: PermLoc ctx a -> Lens' (MultiPermSet ctx) (ValuePerm ctx a)
varPerm (PermLoc x i) =
  -- FIXME: there should be a nicer way of doing this...
  lens
  (\perms ->
    case perms ^? (varPerms x . element i) of
      Just p -> p
      Nothing -> error ("varPerm: no permission at position " ++ show i))
  (\perms p ->
    over (varPerms x)
    (\ps ->
      if i < length ps then (element i .~ p) ps else
        error ("varPerm: no permission at position " ++ show i))
    perms)

{-
modifyVarPerm :: MultiPermSet ctx -> PermLoc ctx a ->
                 (ValuePerm ctx a -> ValuePerm ctx a) ->
                 MultiPermSet ctx
modifyVarPerm perms l f = over (varPerm l) f perms
-}


----------------------------------------------------------------------
-- * Permission Sets with Existentials
----------------------------------------------------------------------

-- | A set of permissions with existentially quantified variables
data ExPermSet vars ctx =
  ExPermSet
  { exPermSetVars :: Size vars,
    _exPermSetPerms :: Assignment (ValuePerm (ctx <+> vars)) ctx }

instance Weakenable (ExPermSet vars) where
  weaken w (ExPermSet sz asgn) =
    ExPermSet sz $ weakenAssignment (\_ -> ValPerm_True) w $
    fmapFC (weaken' $ weakenWeakening sz w) asgn

exPermSetPerms :: Lens' (ExPermSet vars ctx)
                  (Assignment (ValuePerm (ctx <+> vars)) ctx)
exPermSetPerms =
  lens _exPermSetPerms (\eperms perms -> eperms { _exPermSetPerms = perms })

exVarPerm :: PermVar ctx a ->
             Lens' (ExPermSet vars ctx) (ValuePerm (ctx <+> vars) a)
exVarPerm (PermVar _ ix) = exPermSetPerms . ixF' ix


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

  Impl_ElimOr :: PermLoc ctx a -> PermImpl f ctx -> PermImpl f ctx -> PermImpl f ctx
  -- ^ Eliminate a 'ValPerm_Or' on the given variable, replacing it with the
  -- left- and right-hand sides in the two sub-eliminations
  --
  -- pf1 = Gin | Pin, x:p1 |- GsPs1     pf2 = Gin | Pin, x:p2 |- GsPs2
  -- -----------------------------------------------------------------
  -- Gin | Pin, x:(p1 \/ p2) |- GsPs1, GsPs2

  Impl_IntroOrL :: PermLoc ctx a -> ValuePerm ctx a -> PermImpl f ctx ->
                   PermImpl f ctx
  -- ^ @Impl_IntroOrL x p2 pf@ is the left disjunction introduction rule
  --
  -- > pf = Gamma | Pin, x:(p1 \/ p2) |- Pout
  -- > --------------------------------------
  -- > Gamma | Pin, x:p1 |- rets

  Impl_IntroOrR :: PermLoc ctx a -> ValuePerm ctx a -> PermImpl f ctx ->
                   PermImpl f ctx
  -- ^ @Impl_IntroOrR x p1 pf@ is the right disjunction introduction rule
  --
  -- > pf = Gamma | Pin, x:(p1 \/ p2) |- Pout
  -- > --------------------------------------
  -- > Gamma | Pin, x:p2 |- rets

  Impl_ElimExists :: PermLoc ctx a -> TypeRepr tp -> PermImpl f (ctx ::> tp) ->
                     PermImpl f ctx
  -- ^ Eliminate an existential, i.e., a 'ValPerm_Exists', on the given variable
  --
  -- pf = Gin, z:tp | Pin, x:p |- rets
  -- ------------------------------------------------------
  -- Gin | x:(exists z:tp. p)  |- rets

  Impl_IntroExists :: PermLoc ctx a -> TypeRepr tp -> PermExpr ctx tp ->
                      ValuePerm (ctx ::> tp) a ->
                      PermImpl f ctx -> PermImpl f ctx
  -- ^ @Intro_Exists x tp e p pf@ is the existential introduction rule
  --
  -- > pf = Gamma | Pin, x:(exists z:tp.p) |- Pout
  -- > -------------------------------------------
  -- > Gamma | Pin, x:[e'/z]p |- Pout


----------------------------------------------------------------------
-- * Applying Implication Rules to Permission Sets
----------------------------------------------------------------------

orPermLeft :: ValuePerm ctx a -> ValuePerm ctx a
orPermLeft (ValPerm_Or p _) = p
orPermLeft _ = error "orPermLeft"

orPermRight :: ValuePerm ctx a -> ValuePerm ctx a
orPermRight (ValPerm_Or _ p) = p
orPermRight _ = error "orPermRight"

exPermBody :: TypeRepr tp -> ValuePerm ctx a -> ValuePerm (ctx ::> tp) a
exPermBody tp (ValPerm_Exists tp' p)
  | Just Refl <- testEquality tp tp' = p
exPermBody _ _ = error "exPermBody"


permsElimOr :: PermLoc ctx a -> MultiPermSet ctx ->
               (MultiPermSet ctx, MultiPermSet ctx)
permsElimOr l perms =
  (over (varPerm l) orPermLeft perms, over (varPerm l) orPermRight perms)

permsIntroOrL :: PermLoc ctx a -> ValuePerm ctx a -> MultiPermSet ctx ->
                 MultiPermSet ctx
permsIntroOrL l p2 = over (varPerm l) (\p1 -> ValPerm_Or p1 p2)

permsIntroOrR :: PermLoc ctx a -> ValuePerm ctx a -> MultiPermSet ctx ->
                 MultiPermSet ctx
permsIntroOrR l p1 = over (varPerm l) (\p2 -> ValPerm_Or p1 p2)

permsElimExists :: PermLoc ctx a -> TypeRepr tp -> MultiPermSet ctx ->
                   MultiPermSet (ctx ::> tp)
permsElimExists l tp perms =
  set
  (varPerm $ weaken1PermLoc l)
  (exPermBody tp $ perms ^. varPerm l)
  (weaken1MultiPerms perms)

permsIntroExists :: PermLoc ctx a -> TypeRepr tp -> PermExpr ctx tp ->
                    ValuePerm (ctx ::> tp) a ->
                    MultiPermSet ctx -> MultiPermSet ctx
permsIntroExists l tp _e p =
  -- FIXME: check that the existing perm for l = [e/z]p
  set (varPerm l) (ValPerm_Exists tp p)


----------------------------------------------------------------------
-- * Permission Implication Monad
----------------------------------------------------------------------

class PermState s where
  weakenPermState1 :: s ctx -> TypeRepr tp -> s (ctx ::> tp)
  permStatePerms :: Lens' (s ctx) (MultiPermSet ctx)

-- | The contextual continuation state transformer
newtype CCST s fin fout ctx m a =
  CCST { unCCST ::
           forall ctx'. Weakening ctx ctx' -> s ctx' ->
           (forall ctx''. Weakening ctx' ctx'' -> s ctx'' -> a -> m (fin ctx'')) ->
           m (fout ctx') }

runCCST :: Monad m => CCST s (Const ()) fout ctx m () -> s ctx -> m (fout ctx)
runCCST (CCST m) s =
  m identityWeakening s $ \_ _ _ -> return $ Const ()

infixl 1 >>>=
(>>>=) :: CCST s f2 f3 ctx m a -> (a -> CCST s f1 f2 ctx m b) ->
          CCST s f1 f3 ctx m b
(CCST m) >>>= f =
  CCST $ \w s k ->
  m w s $ \w' s' a ->
  unCCST (f a) (composeWeakenings w w') s' $ \w'' -> k (composeWeakenings w' w'')

instance Functor (CCST s f f ctx m) where
  fmap f m = m >>= return . f

instance Applicative (CCST s f f ctx m) where
  pure = return
  (<*>) = ap

instance Monad (CCST s f f ctx m) where
  return x = CCST $ \w s k -> k identityWeakening s x
  m >>= f = m >>>= f

instance MonadTrans (CCST s f f ctx) where
  lift m = CCST $ \_ s k -> m >>= \a -> k identityWeakening s a

instance MonadState s' m => MonadState s' (CCST s f f ctx m) where
  get = lift get
  put s = lift (put s)

cstate :: (forall ctx'. Weakening ctx ctx' -> s ctx' -> (a, s ctx')) ->
          CCST s f f ctx m a
cstate f = CCST $ \w s k ->
  let (a, s') = f w s in
  k identityWeakening s a

cmodify :: (forall ctx'. Weakening ctx ctx' -> s ctx' -> s ctx') ->
           CCST s f f ctx m ()
cmodify f = cstate (\w s -> ((), f w s))

{-
lookupType :: PermVar ctx a -> CCST f f ctx (TypeRepr a)
lookupType x =
  cstate $ \w s -> (implCtx s ! indexOfPermVar (weaken' w x), s)
-}

cwithState :: (forall ctx'.
               Weakening ctx ctx' -> s ctx' -> CCST s fin fout ctx' m a) ->
              CCST s fin fout ctx m a
cwithState f = CCST $ \w s k -> unCCST (f w s) identityWeakening s k

cchangeState :: (forall ctx'. Weakening ctx ctx' -> s ctx' -> s' ctx') ->
                (forall ctx'. Weakening ctx ctx' -> s' ctx' -> s ctx') ->
                CCST s' fin fout ctx m a ->
                CCST s fin fout ctx m a
cchangeState sto sfrom (CCST m) =
  CCST $ \w s k ->
  m w (sto w s) $ \w' s' a -> k w' (sfrom (composeWeakenings w w') s') a

cmapCont :: Monad m =>
            (forall ctx'. Weakening ctx ctx' -> fout ctx' -> fout' ctx') ->
            CCST s fin fout ctx m a -> CCST s fin fout' ctx m a
cmapCont f (CCST m) =
  CCST $ \w s k -> f w <$> (m w s $ \w' s' a -> k w' s' a)

cmapCont2 :: Monad m =>
             (forall ctx'. Weakening ctx ctx' ->
              fout1 ctx' -> fout2 ctx' -> fout' ctx') ->
             CCST s fin fout1 ctx m a -> CCST s fin fout2 ctx m a ->
             CCST s fin fout' ctx m a
cmapCont2 f (CCST m1) (CCST m2) =
  CCST $ \w s k ->
  f w <$> (m1 w s $ \w' s' a -> k w' s' a) <*>
  (m2 w s $ \w' s' a -> k w' s' a)

cmapContIn :: Monad m =>
              (forall ctx'. Weakening ctx ctx' -> fin' ctx' -> fin ctx') ->
              CCST s fin fout ctx m a -> CCST s fin' fout ctx m a
cmapContIn f m = m >>>= \a -> cmapCont f (return a)

cmapContBind :: (Monad m, PermState s) => TypeRepr tp ->
                (forall ctx'. Weakening ctx ctx' ->
                 fout (ctx' ::> tp) -> fout' ctx') ->
                CCST s fin fout (ctx ::> tp) m a -> CCST s fin fout' ctx m a
cmapContBind tp f (CCST m) =
  CCST $ \w s k ->
  f w <$> (m (weakenWeakening1 w) (weakenPermState1 s tp) $ \w' s' a ->
            k (composeWeakenings mkWeakening1 w') s' a)

cmapContStateBind ::
  Monad m =>
  (forall ctx'. Weakening ctx ctx' -> fout (ctx' ::> tp) -> fout' ctx') ->
  (forall ctx'. Weakening ctx ctx' -> s ctx' -> s (ctx' ::> tp)) ->
  CCST s fin fout (ctx ::> tp) m a ->
  CCST s fin fout' ctx m a
cmapContStateBind fret fs (CCST m) =
  CCST $ \w s k ->
  fret w <$> (m (weakenWeakening1 w) (fs w s) $ \w' s' a ->
               k (composeWeakenings mkWeakening1 w') s' a)


----------------------------------------------------------------------
-- * Monadic Proof Operations
----------------------------------------------------------------------

introOrLM :: (Monad m, PermState s) =>
             PermLoc ctx a -> ValuePerm ctx a ->
             CCST s (PermImpl f) (PermImpl f) ctx m ()
introOrLM l p2 =
  cmapCont (\w -> Impl_IntroOrL (weaken' w l) (weaken' w p2)) $
  cmodify (\w -> over permStatePerms $
                 permsIntroOrL (weaken' w l) (weaken' w p2))

introOrRM :: (Monad m, PermState s) =>
             PermLoc ctx a -> ValuePerm ctx a ->
             CCST s (PermImpl f) (PermImpl f) ctx m ()
introOrRM l p1 =
  cmapCont (\w -> Impl_IntroOrR (weaken' w l) (weaken' w p1)) $
  cmodify (\w -> over permStatePerms $
                 permsIntroOrR (weaken' w l) (weaken' w p1))

introExistsM :: (Monad m, PermState s) =>
                PermLoc ctx a -> TypeRepr tp -> PermExpr ctx tp ->
                ValuePerm (ctx ::> tp) a ->
                CCST s (PermImpl f) (PermImpl f) ctx m ()
introExistsM l tp e p =
  cmapCont (\w -> Impl_IntroExists (weaken' w l) tp (weaken' w e)
                  (weaken' (weakenWeakening1 w) p)) $
  cmodify (\w -> over permStatePerms $
                 permsIntroExists (weaken' w l) tp (weaken' w e)
                 (weaken' (weakenWeakening1 w) p))

elimOrM :: (Monad m, PermState s) =>
           PermLoc ctx a -> CCST s (PermImpl f) (PermImpl f) ctx m ()
elimOrM l =
  cmapCont2 (\w -> Impl_ElimOr (weaken' w l))
  (cmodify (\w -> over permStatePerms (fst . permsElimOr (weaken' w l))))
  (cmodify (\w -> over permStatePerms (snd . permsElimOr (weaken' w l))))

elimExistsM :: (Monad m, PermState s) =>
               PermLoc ctx a -> TypeRepr tp ->
               CCST s (PermImpl f) (PermImpl f) ctx m ()
elimExistsM l tp =
  cmapContStateBind (\w -> Impl_ElimExists (weaken' w l) tp)
  (\w s ->
    set permStatePerms
    (permsElimExists (weaken' w l) tp $ s^.permStatePerms)
    (weakenPermState1 s tp))
  (return ())

-- | Eliminate disjunctives and existentials on a variable
elimOrsExistsM :: (Monad m, PermState s) =>
                  PermLoc ctx a -> CCST s (PermImpl f) (PermImpl f) ctx m ()
elimOrsExistsM x =
  cwithState $ \w s ->
  case s^.(permStatePerms . varPerm (weaken' w x)) of
    ValPerm_Or _ _ ->
      elimOrM (weaken' w x) >> elimOrsExistsM (weaken' w x)
    ValPerm_Exists tp _ ->
      elimExistsM (weaken' w x) tp >> elimOrsExistsM (weaken' w x)
    _ -> return ()


----------------------------------------------------------------------
-- * Introduction Proof Steps for Permission Implications
----------------------------------------------------------------------

data Intros vars ctx where
  Intros_Done :: Intros vars ctx
  Intros_OrL :: PermVar ctx a -> ValuePerm (ctx <+> vars) a ->
                Intros vars ctx -> Intros vars ctx
  Intros_OrR :: PermVar ctx a -> ValuePerm (ctx <+> vars) a ->
                Intros vars ctx -> Intros vars ctx
  Intros_Exists :: PermVar ctx a -> TypeRepr tp ->
                   ValuePerm (ctx <+> vars ::> tp) a ->
                   Intros vars ctx -> Intros (vars ::> tp) ctx

weakenIntros :: Size vars -> Weakening ctx ctx' -> Intros vars ctx ->
                 Intros vars ctx'
weakenIntros _ _ Intros_Done = Intros_Done
weakenIntros sz w (Intros_OrL x p2 intros) =
  Intros_OrL (weaken' w x) (weaken' (weakenWeakening sz w) p2)
  (weakenIntros sz w intros)
weakenIntros sz w (Intros_OrR x p1 intros) =
  Intros_OrR (weaken' w x) (weaken' (weakenWeakening sz w) p1)
  (weakenIntros sz w intros)
weakenIntros sz w (Intros_Exists x tp p intros) =
  Intros_Exists (weaken' w x) tp
  (weaken' (weakenWeakening sz w) p)
  (weakenIntros (decSize sz) w intros)

data ImplState vars ctx =
  ImplState { _implStatePerms :: MultiPermSet ctx,
              _implStateVars :: CtxRepr vars,
              _implStatePSubst :: PartialSubst vars ctx,
              _implStateIntros :: Intros vars ctx }
makeLenses ''ImplState

instance Weakenable (ImplState vars) where
  weaken w (ImplState {..}) =
    ImplState { _implStatePerms = weaken w _implStatePerms,
                _implStateVars = _implStateVars,
                _implStatePSubst = weaken w _implStatePSubst,
                _implStateIntros =
                  weakenIntros (size _implStateVars) w _implStateIntros }

instance PermState (ImplState vars) where
  weakenPermState1 s _ = weaken mkWeakening1 s
  permStatePerms = implStatePerms

applyIntros :: (Monad m, PermState s) =>
               PermSubst (ctx <+> vars) ctx -> Intros vars ctx ->
               CCST s (PermImpl f) (PermImpl f) ctx m ()
applyIntros _ Intros_Done = return ()
applyIntros s (Intros_OrL x p2 intros) =
  introOrLM (varLoc0 x) (subst' s p2) >>
  applyIntros s intros
applyIntros s (Intros_OrR x p1 intros) =
  introOrRM (varLoc0 x) (subst' s p1) >>
  applyIntros s intros
applyIntros s (Intros_Exists x tp p intros) =
  let (s', e) = unconsPermSubst s in
  introExistsM (varLoc0 x) tp e (subst' (weakenSubst1 s') p) >>
  applyIntros s' intros
