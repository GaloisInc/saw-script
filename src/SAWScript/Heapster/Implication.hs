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

module SAWScript.Heapster.Implication where

import Data.Maybe
import Data.List
import Data.Kind as Kind
import Data.Functor.Product
import GHC.TypeLits
import Control.Lens hiding ((:>))
import Control.Monad
import Data.Functor.Identity
import Control.Applicative hiding (empty)
import qualified Control.Applicative as Applicative
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Trans.Maybe

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core

import Data.Binding.Hobbits
import SAWScript.Heapster.Permissions


----------------------------------------------------------------------
-- * Permission Implications
----------------------------------------------------------------------

-- | A @'PermImpl' r ls@ is a proof tree of the judgment
--
-- > Gamma | Pl * P |- (Gamma1 | Pl1 * P1) \/ ... \/ (Gamman | Pln * Pn)
--
-- that contains an element of type @r@ at each leaf of the proof tree. Each
-- disjunct on the right of the judgment corresponds to a different leaf in the
-- tree, while each @Gammai@ denotes the variables that are bound on the path
-- from the root to that leaf. The @ls@ argument captures the form of the
-- "distinguished" left-hand side permissions @Pl@.
--
-- FIXME: explain that @Pl@ is like a stack, and that intro rules apply to the
-- top of the stack
data PermImpl r ls where
  Impl_Done :: r -> PermImpl r ls
  -- ^ The proof is finished; i.e., implements the rule
  --
  -- > -------------------------------
  -- > Gin | Pl * Pin |- . | Pin

  Impl_Fail :: PermImpl r ls
  -- ^ The empty tree, with no disjunctive possibilities; i.e., implements the
  -- rule
  --
  -- > ------------------------------
  -- > Gin | Pl * Pin |- anything

  Impl_Catch :: PermImpl r ls -> PermImpl r ls -> PermImpl r ls
  -- ^ Copy the same permissions into two different elimination trees, where an
  -- 'Impl_Fail' in the first tree "calls" the second tree, just like a
  -- try-catch block for exceptions. This implements the rule:
  --
  -- > pf1 = Gin | Pl * Pin |- rets1    pf2 = Gin | Pl * Pin |- rets2
  -- > --------------------------------------------------------------
  -- > Gin | Pl * Pin |- rets1, rets2

  Impl_Push :: PermLoc a -> ValuePerm a -> PermImpl r (ls :> PermExpr a) ->
               PermImpl r ls
  -- ^ "Push" a permission from the input permission set to the stack of
  -- distinguished permissions:
  --
  -- > Gin | Pl,x:p * Pin |- rets
  -- > ---------------------------
  -- > Gin | Pl * Pin, x:p |- rets

  Impl_ElimOr :: PermLoc a -> PermImpl r ls -> PermImpl r ls ->
                 PermImpl r ls
  -- ^ Eliminate a 'ValPerm_Or' on the given variable, replacing it with the
  -- left- and right-hand sides in the two sub-eliminations
  --
  -- > pf1 = Gin | Pin, x:p1 |- GsPs1     pf2 = Gin | Pin, x:p2 |- GsPs2
  -- > -----------------------------------------------------------------
  -- > Gin | Pin, x:(p1 \/ p2) |- GsPs1, GsPs2

  Impl_IntroOrL :: ExprVar a -> ValuePerm a ->
                   PermImpl r (ls :> PermExpr a) ->
                   PermImpl r (ls :> PermExpr a)
  -- ^ @Impl_IntroOrL x p2 pf@ applies left disjunction introduction to the top
  -- permission on the stack:
  --
  -- > pf = Gamma | Pl, x:(p1 \/ p2) * Pin |- Pout
  -- > -------------------------------------------
  -- > Gamma | Pl, x:p1 * Pin |- rets

  Impl_IntroOrR :: ExprVar a -> ValuePerm a ->
                   PermImpl r (ls :> PermExpr a) ->
                   PermImpl r (ls :> PermExpr a)
  -- ^ @Impl_IntroOrR x p1 pf@ applies right disjunction introduction to the top
  -- permission on the stack:
  --
  -- > pf = Gamma | Pl, x:(p1 \/ p2) * Pin |- Pout
  -- > -------------------------------------------
  -- > Gamma | Pl, x:p2 * Pin |- rets

  Impl_ElimExists :: PermLoc a -> TypeRepr tp ->
                     Binding (PermExpr tp) (PermImpl r ls) ->
                     PermImpl r ls
  -- ^ Eliminate an existential, i.e., a 'ValPerm_Exists', on the given variable
  --
  -- pf = Gin, z:tp | Pin, x:p |- rets
  -- ------------------------------------------------------
  -- Gin | x:(exists z:tp. p)  |- rets

  Impl_IntroExists :: ExprVar a -> TypeRepr tp -> PermExpr tp ->
                      Binding (PermExpr tp) (ValuePerm a) ->
                      PermImpl r (ls :> PermExpr a) ->
                      PermImpl r (ls :> PermExpr a)
  -- ^ @Intro_Exists x tp e p pf@ applies existential introduction to the top
  -- permission on the stack:
  --
  -- > pf = Gamma | Pl, x:(exists z:tp.p) * Pin |- Pout
  -- > ------------------------------------------------
  -- > Gamma | Pl, x:[e'/z]p * Pin |- Pout

  Impl_IntroTrue :: ExprVar a -> PermImpl r (ls :> PermExpr a) ->
                    PermImpl r ls
  -- ^ Introduce a true permission onto the stack of distinguished permissions:
  --
  -- > Gin | Pl,x:true * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_IntroCast :: ExprVar a -> ExprVar a ->
                    PermImpl r (ls :> PermExpr a) ->
                    PermImpl r (ls :> PermExpr a :> PermExpr a)
  -- ^ Cast a proof of @y:p@ to one of @x:p@ using @x:eq(y)@:
  --
  -- > Gin | Pl,x:p * Pin |- rets
  -- > ----------------------------------
  -- > Gin | Pl,x:eq(y),y:p * Pin |- rets

  Impl_IntroEqRefl :: ExprVar a -> PermImpl r (ls :> PermExpr a) ->
                      PermImpl r ls
  -- ^ Introduce a proof that @x:eq(x)@:
  --
  -- > Gin | Pl,x:eq(x) * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_IntroEqCopy :: PermLoc a -> PermImpl r (ls :> PermExpr a) ->
                      PermImpl r ls
  -- ^ Copy a proof that @x:eq(e)@ from the normal permissions to the stack:
  --
  -- > Gin | Pl,x:eq(e) * Pin,x:eq(e) |- rets
  -- > --------------------------------------
  -- > Gin | Pl * Pin,x:eq(e) |- rets

  Impl_AssertBVEq :: ExprVar (BVType w) -> PermExpr (BVType w) ->
                     PermImpl r (ls :> PermExpr (BVType w)) ->
                     PermImpl r ls
  -- ^ Introduce a proof that @x:eq(e)@ at bitvector type (which becomes a
  -- dynamic check that @x=e@):
  --
  -- > Gin | Pl,x:eq(e) * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_IntroCastLLVMWord ::
    ExprVar (LLVMPointerType w) -> PermExpr (BVType w) -> PermExpr (BVType w) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w))
  -- ^ Cast a proof that @x:eq(word(e1))@ to one that @x:eq(word(e2))@ with a
  -- dynamic check that @e1=e2@:
  --
  -- > Gin | Pl,x:eq(word(e2)) * Pin |- rets
  -- > -------------------------------------
  -- > Gin | Pl,x:eq(word(e1)) * Pin |- rets

  Impl_ElimLLVMStar :: PermLoc (LLVMPointerType w) -> PermImpl r ls ->
                       PermImpl r ls
  -- ^ Eliminate an @x:ptr(p1 * p2)@ into @x:ptr(p1)@ and @x:ptr(p2)@, putting
  -- the latter into a new location for @x@:
  --
  -- > Gin | Pl * Pin, x:ptr(p1), x:ptr(p2) |- rets
  -- > --------------------------------------------
  -- > Gin | Pl * Pin, x:ptr(p1 * p2) |- rets

  Impl_IntroLLVMStar ::
    ExprVar (LLVMPointerType w) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w)
                :> PermExpr (LLVMPointerType w))
  -- ^ Combine proofs of @x:ptr(p1)@ and @x:ptr(p2)@ on the top of the
  -- permission stack into a proof of @x:ptr(p1 * p2)@:
  --
  -- > Gin | Pl, x:ptr(p1 * p2) * Pin |- rets
  -- > --------------------------------------------
  -- > Gin | Pl, x:ptr(p1), x:ptr(p2) * Pin |- rets

  Impl_IntroLLVMFree :: PermLoc (LLVMPointerType w) ->
                        PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
                        PermImpl r ls
  -- ^ Copy a proof of @x:ptr(free(e))@ to the top of the stack:
  --
  -- > Gin | Pl, x:ptr(free(e)) * Pin, x:ptr(free(e)) |- rets
  -- > ------------------------------------------------------
  -- > Gin | Pl * Pin, x:ptr(free(e)) |- rets

  Impl_CastLLVMFree :: ExprVar (LLVMPointerType w) ->
                       PermExpr (BVType w) -> PermExpr (BVType w) ->
                       PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
                       PermImpl r (ls :> PermExpr (LLVMPointerType w))
  -- ^ Cast a proof of @x:ptr(free(e1))@ on the top of the stack to one of
  -- @x:ptr(free(e2))@:
  --
  -- > Gin | Pl, x:ptr(free(e2)) * Pin |- rets
  -- > ---------------------------------------
  -- > Gin | Pl, x:ptr(free(e1)) * Pin |- rets

  Impl_ElimLLVMField ::
    PermLoc (LLVMPointerType w) ->
    Binding (PermExpr (LLVMPointerType w)) (PermImpl r ls) ->
    PermImpl r ls
  -- ^ Eliminate a field permission @x:ptr((off,S) |-> p)@ into a permission
  -- @x:ptr((off,S) |-> eq(y))@ that the field contains a fresh variable @y@ and
  -- a permission @y:p@ on @y@:
  --
  -- > Gin | Pl * Pin, x:ptr((off,S) |-> eq(y)), y:p |- rets
  -- > -----------------------------------------------------
  -- > Gin | Pl * Pin, x:ptr((off,S) |-> p) |- rets

  Impl_IntroLLVMField ::
    ExprVar (LLVMPointerType w) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w)
                :> PermExpr (LLVMPointerType w))
  -- ^ Combine proofs of @x:ptr((off,S) |-> eq(y))@ and @y:p@ on the top of the
  -- permission stack into a proof of @x:ptr((off,S) |-> p)@:
  --
  -- > Gin | Pl, x:ptr((off,S) |-> p) * Pin |- rets
  -- > -----------------------------------------------------
  -- > Gin | Pl, x:ptr((off,S) |-> eq(y)), y:p * Pin |- rets


----------------------------------------------------------------------
-- * Generalized Monads
----------------------------------------------------------------------

-- | A generalized monad has additional "input" and "output" types, that
-- sequence together "backwards" through the generalized bind operation. Mostly
-- this is to support 'GenContT', below.
--
-- Note that a generalized monad @m@ should always be a standard monad when the
-- input and output types are the same; i.e., @m r r@ should always be a
-- monad. I do not know a nice way to encode this in Haskell, however...
class GenMonad (m :: Kind.* -> Kind.* -> Kind.* -> Kind.*) where
  -- | Generalized return
  greturn :: a -> m r r a
  -- | Generalized bind, that passes the output of @f@ to the input of @m@
  (>>>=) :: m r2 r3 a -> (a -> m r1 r2 b) -> m r1 r3 b
  -- | Insert a mapping function from the input to the output
  gmapRet :: (rin -> rout) -> m rin rout ()
  -- | Run two computations in parallel, combining their output at the end
  gparallel :: m r1 r2 a -> m r1 r3 a -> m r1 (r2, r3) a
  -- | FIXME: explain this one
  gopenBinding :: Binding a b -> m r (Binding a r) (Name a, b)

infixl 1 >>>=
infixl 1 >>>

(>>>) :: GenMonad m => m r2 r3 () -> m r1 r2 a -> m r1 r3 a
m1 >>> m2 = m1 >>>= \() -> m2

class GenMonadT (t :: (Kind.* -> Kind.* -> Kind.* -> Kind.*) ->
                Kind.* -> Kind.* -> Kind.* -> Kind.*) where
  glift :: GenMonad m => m rin rout a -> t m rin rout a

-- | The generalized continuation transformer, which can have different types
-- for the input vs output continuations
newtype GenContT (m :: Kind.* -> Kind.*) rin rout a =
  GenContT { unGenContT :: (a -> m rin) -> m rout }

instance Functor (GenContT m r r) where
  fmap f m = m >>= return . f

instance Applicative (GenContT m r r) where
  pure = return
  (<*>) = ap

instance Monad (GenContT m r r) where
  return x = GenContT $ \k -> k x
  GenContT m >>= f = GenContT $ \k -> m $ \a -> unGenContT (f a) k

{-
instance MonadTrans (GenContT r r) where
  lift m = GenContT $ \k -> m >>= \a -> k a
-}

instance MonadStrongBind m => GenMonad (GenContT m) where
  greturn x = GenContT $ \k -> k x
  (GenContT m) >>>= f =
    GenContT $ \k -> m $ \a -> unGenContT (f a) k
  gmapRet f = GenContT $ \k -> fmap f $ k ()
  gparallel (GenContT m1) (GenContT m2) =
    GenContT $ \k -> (\x y -> (x,y)) <$> m1 k <*> m2 k
  gopenBinding b =
    GenContT $ \k -> strongMbM $ nuWithElim1 (\nm b_body -> k (nm, b_body)) b

-- | The generalized state monad. We use 'StateT' underneath to take advantage
-- of some of its methods
newtype GenStateT s (m :: Kind.* -> Kind.* -> Kind.* -> Kind.*) rin rout a =
  GenStateT { unGenStateT :: StateT s (m rin rout) a }

runGenStateT :: GenStateT s m rin rout a -> s -> m rin rout (a, s)
runGenStateT m s = runStateT (unGenStateT m) s

-- | Helper to tell GHC how to type-check
gget :: (GenMonad m, MonadState s (m r r)) => m r r s
gget = get

instance Functor (m r r) => Functor (GenStateT s m r r) where
  fmap f (GenStateT m) = GenStateT $ fmap f m

instance Monad (m r r) => Applicative (GenStateT s m r r) where
  pure = return
  (<*>) = ap

instance Monad (m r r) => Monad (GenStateT s m r r) where
  return = GenStateT . return
  (GenStateT m) >>= f =
    GenStateT $ m >>= unGenStateT . f

instance Monad (m r r) => MonadState s (GenStateT s m r r) where
  get = GenStateT get
  put s = GenStateT $ put s

instance GenMonadT (GenStateT s) where
  glift m = GenStateT $ StateT $ \s -> m >>>= \a -> greturn (a, s)

instance GenMonad m => GenMonad (GenStateT s m) where
  greturn x = GenStateT $ StateT $ \s -> greturn (x, s)
  (GenStateT (StateT m)) >>>= f =
    GenStateT $ StateT $ \s -> m s >>>= \(a, s') ->
    runStateT (unGenStateT $ f a) s'
  gmapRet f = glift $ gmapRet f
  gparallel m1 m2 =
    GenStateT $ StateT $ \s ->
    gparallel (runGenStateT m1 s) (runGenStateT m2 s)
  gopenBinding b = glift $ gopenBinding b


-- | Transformer for pattern-matching in a generalized monad; although it itself
-- is a monad transformer, it is not a generalized transformer, because it only
-- supports a restricted form of the @>>>=@ operator
newtype MatchT m rin rout a =
  MatchT
  { unMatchT ::
      (a -> m rin rout () -> m rin rout ()) -> m rin rout () -> m rin rout () }

instance Functor (MatchT m rin rout) where
  fmap f m = m >>= return . f

instance Applicative (MatchT m rin rout) where
  pure = return
  (<*>) = ap

instance Monad (MatchT m rin rout) where
  return a = MatchT $ \ks kf -> ks a kf
  (MatchT m) >>= f =
    MatchT $ \ks kf -> m (\a kf' -> unMatchT (f a) ks kf') kf

instance Alternative (MatchT m rin rout) where
  empty = MatchT $ \_ kf -> kf
  (MatchT m1) <|> (MatchT m2) = MatchT $ \ks kf -> m1 ks (m2 ks kf)

instance MonadPlus (MatchT m r r) where
  mzero = Applicative.empty
  mplus = (<|>)

{-
instance GenMonadT MatchT where
  glift m = MatchT $ \ks kf -> m >>>= \a -> ks a kf
-}

{-
instance GenMonad m => GenMonad (MatchT m) where
  greturn a = MatchT $ \ks kf -> ks a kf
  (MatchT m) >>>= f =
    MatchT $ \ks kf -> m (\a -> unMatchT (f a) ks kf) kf
  gmapRet f = glift $ gmapRet f
  gparallel (MatchT m1) (MatchT m2) =
    MatchT $ \ks kf -> gparallel (m1 ks kf) (m2 ks kf)
  gopenBinding b =glift $ gopenBinding b
-}

-- FIXME: this may not be useful...
matchBind :: MatchT m rin rout a -> (a -> MatchT m rin rout b) ->
             MatchT m rin rout b
matchBind (MatchT m) f =
  MatchT $ \ks kf -> m (\a kf' -> unMatchT (f a) ks kf') kf

-- | Pattern-match on the result of a computation with an optional value,
-- calling the given function if the value is there and giving up on the current
-- match case otherwise
matchCase :: GenMonad m => m rout rout (Maybe a) ->
             (a -> MatchT m rin rout b) -> MatchT m rin rout b
matchCase m f =
  MatchT $ \ks kf -> m >>>= maybe kf (\a -> unMatchT (f a) ks kf)

-- | A pure case that does not use any monadic effects
matchPure :: GenMonad m => a -> Matcher a b ->
             (b -> MatchT m rin rout c) -> MatchT m rin rout c
matchPure a matcher = matchCase (greturn (matcher a))

-- | Build a pattern-matching computation that always succeeds and runs the
-- given computation as its result
matchBody :: m rin rout () -> MatchT m rin rout a
matchBody m = MatchT $ \_ _ -> m

-- | Give up on the current pattern-matching case
matchFail :: MatchT m rin rout a
matchFail = MatchT $ \_ kf -> kf

-- | Run a pattern-matching computation, using the given underlying computation
-- as the default case
runMatchT :: m rin rout () -> MatchT m rin rout () -> m rin rout ()
runMatchT kf (MatchT f) = f (\() m -> m) kf


----------------------------------------------------------------------
-- * Permission Implication Monad
----------------------------------------------------------------------

-- | State type @s@ is a permission state type iff it contains a permission set
class PermState s where
  permStatePerms :: Lens' s PermSet

-- | The general monad for manipulating permissions
newtype PermM s rin rout a =
  PermM { unPermM :: GenStateT s (GenContT Identity) rin rout a }

deriving instance (Functor (PermM s r r))
deriving instance (Applicative (PermM s r r))
deriving instance (Monad (PermM s r r))
deriving instance (GenMonad (PermM s))
deriving instance (MonadState s (PermM s r r))

data ImplState vars =
  ImplState { _implStatePerms :: PermSet,
              _implStateVars :: CruCtx vars,
              _implStatePSubst :: PartialSubst vars }
makeLenses ''ImplState

mkImplState :: CruCtx vars -> PermSet -> ImplState vars
mkImplState vars perms =
  ImplState { _implStateVars = vars,
              _implStatePerms = perms,
              _implStatePSubst = emptyPSubst vars }

extImplState :: KnownRepr TypeRepr tp => ImplState vars ->
                ImplState (vars :> PermExpr tp)
extImplState s =
  s { _implStateVars = extCruCtx (_implStateVars s),
      _implStatePSubst = extPSubst (_implStatePSubst s) }

unextImplState :: ImplState (vars :> PermExpr a) -> ImplState vars
unextImplState s =
  s { _implStateVars = unextCruCtx (_implStateVars s),
      _implStatePSubst = unextPSubst (_implStatePSubst s) }

instance PermState (ImplState vars) where
  permStatePerms = implStatePerms

-- | The implication monad is the permission monad that uses 'ImplState'
type ImplM vars r ls1 ls2 =
  PermM (ImplState vars) (PermImpl r ls1) (PermImpl r ls2)


-- | Run a permissions computation with a different state type @s2@ inside one
-- with state type @s1@, using a lens-like pair of a getter function to extract
-- out the starting inner @s2@ state from the outer @s1@ state and an update
-- function to update the resulting outer @s1@ state with the final inner @s2@
-- state. (We do not use a lens here because we do not actually require these
-- functions to form a lens, and in fact 'withExtVarsM' below uses a pair of
-- functions that is not a lens.)
withAltStateM :: (s1 -> s2) -> (s1 -> s2 -> s1) -> PermM s2 rin rout a ->
                 PermM s1 rin rout a
withAltStateM s_get s_update (PermM m) =
  gget >>>= \s ->
  PermM (glift (runGenStateT m (s_get s))) >>>= \(a, s') ->
  put (s_update s s') >>>
  greturn a

-- | Run an implication computation with one more existential variable,
-- returning the optional expression it was bound to in the current partial
-- substitution when it is done
withExtVarsM :: KnownRepr TypeRepr tp =>
                ImplM (vars :> PermExpr tp) r ls1 ls2 a ->
                ImplM vars r ls1 ls2 (a, Maybe (PermExpr tp))
withExtVarsM m =
  withAltStateM extImplState (const unextImplState) $
  (m >>>= \a ->
    getPSubst >>>= \psubst ->
    greturn (a, psubstLookup psubst Member_Base))

-- | Run an 'ImplM' computation inside a 'PermM' computation with a possibly
-- different state type
runImplM :: PermState s => CruCtx vars ->
            ImplM vars r ls1 ls2 a ->
            PermM s (PermImpl r ls1) (PermImpl r ls2) (a, PermSubst vars)
runImplM vars m =
  withAltStateM (\s -> mkImplState vars (s ^. permStatePerms))
  (\s s' -> set permStatePerms (s' ^. implStatePerms) s)
  (m >>>= \a ->
    getPSubst >>>= \psubst ->
    greturn (a, completePSubst vars psubst))


----------------------------------------------------------------------
-- * Permissions Operations in a Permission Monad
----------------------------------------------------------------------

-- | Look up the current partial substitution
getPSubst :: ImplM vars r ls ls (PartialSubst vars)
getPSubst = view implStatePSubst <$> gget

-- | Apply the current partial substitution to an expression, raising an error
-- with the given string if the partial substitution is not complete enough
partialSubstForceM :: Substable PartialSubst a Maybe => Mb vars a -> String ->
                      ImplM vars r ls ls a
partialSubstForceM mb_e msg =
  getPSubst >>>= \psubst ->
  greturn (partialSubstForce psubst mb_e msg)

-- | Modify the current partial substitution
modifyPSubst :: (PartialSubst vars -> PartialSubst vars) ->
                ImplM vars r ls ls ()
modifyPSubst f = modify (over implStatePSubst f)

-- | Look up the current permissions for a variable
getPerms :: PermState s => ExprVar a -> PermM s r r [ValuePerm a]
getPerms x = view (permStatePerms . varPerms x) <$> gget

-- | Look up the locations associated with a variable
getVarLocs :: PermState s => ExprVar a -> PermM s r r [PermLoc a]
getVarLocs x =
  gget >>>= \s -> return $ allLocsForVar (s ^. permStatePerms) x

-- | Look up the current permission at a specific location
getPerm :: PermState s => PermLoc a -> PermM s r r (ValuePerm a)
getPerm l = view (permStatePerms . varPerm l) <$> gget

-- | Terminate the current proof branch with a failure
implFailM :: PermM s rany (PermImpl r ls) ()
implFailM = gmapRet (const Impl_Fail)

-- | Finish the current proof branch successfully with an 'Impl_Done'
implDoneM :: PermM s r (PermImpl r ls) ()
implDoneM = gmapRet Impl_Done

-- | Push a permission from the permission set to the permission stack
implPushM :: PermState s => PermLoc a -> ValuePerm a ->
             PermM s (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()
implPushM l p =
  gmapRet (Impl_Push l p) >>>
  modify (over permStatePerms $ permDelete l p)

-- | Produce a branching proof tree, that performs the first implication and, if
-- that one fails, falls back on the second
implCatchM :: PermM s rany (PermImpl r ls) () ->
              PermM s rany (PermImpl r ls) () ->
              PermM s rany (PermImpl r ls) ()
implCatchM m1 m2 =
  gmapRet (\(impl1, impl2) -> Impl_Catch impl1 impl2) >>>
  gparallel m1 m2

-- | Apply the left or-introduction rule to the top of the permission stack,
-- changing it from @x:p1@ to @x:(p1 \/ p2)@
introOrLM :: PermState s => ExprVar a -> ValuePerm a ->
             PermM s (PermImpl r (ls :> PermExpr a))
             (PermImpl r (ls :> PermExpr a)) ()
introOrLM x p2 = gmapRet (Impl_IntroOrL x p2)

-- | Apply the right or-introduction rule to the top of the permission stack,
-- changing it from @x:p2@ to @x:(p1 \/ p2)@
introOrRM :: ExprVar a -> ValuePerm a ->
             PermM s (PermImpl r (ls :> PermExpr a))
             (PermImpl r (ls :> PermExpr a)) ()
introOrRM x p1 = gmapRet (Impl_IntroOrR x p1)

-- | Apply existential introduction to the top of the permission stack, changing
-- it from @[e/x]p@ to @exists (x:tp).p@
--
-- FIXME: is there some way we could "type-check" this, to ensure that the
-- permission on the top of the stack really equals @[e/x]p@?
introExistsM :: ExprVar a -> TypeRepr tp -> PermExpr tp ->
                Binding (PermExpr tp) (ValuePerm a) ->
                PermM s (PermImpl r (ls :> PermExpr a))
                (PermImpl r (ls :> PermExpr a)) ()
introExistsM x tp e p_body = gmapRet (Impl_IntroExists x tp e p_body)

-- | Eliminate a disjunctive permission @x:(p1 \/ p2)@, building proof trees
-- that proceed with both @x:p1@ and @x:p2@
elimOrM :: PermState s => PermLoc a ->
           PermM s (PermImpl r ls) (PermImpl r ls) ()
elimOrM l =
  gmapRet (\(impl1, impl2) -> Impl_ElimOr l impl1 impl2) >>>
  gparallel
  (modify (over (permStatePerms . varPerm l) orPermLeft))
  (modify (over (permStatePerms . varPerm l) orPermRight))

-- | Eliminate an existential permission @x:(exists (y:tp).p)@ in the current
-- permission set
elimExistsM :: PermState s => PermLoc a -> TypeRepr tp ->
               PermM s (PermImpl r ls) (PermImpl r ls) ()
elimExistsM l tp =
  gget >>>= \s ->
  gmapRet (Impl_ElimExists l tp) >>>
  gopenBinding (exPermBody tp $
                s ^. permStatePerms . varPerm l) >>>= \(nm, p_body) ->
  put (set (permStatePerms . varPerm l) p_body s)

-- | Eliminate disjunctives and existentials at a specific location
elimOrsExistsM :: PermState s => PermLoc a ->
                  PermM s (PermImpl r ls) (PermImpl r ls) ()
elimOrsExistsM l =
  getPerm l >>>= \p ->
  case p of
    ValPerm_Or _ _ -> elimOrM l >>> elimOrsExistsM l
    ValPerm_Exists (_ :: Binding (PermExpr a) _) ->
      elimExistsM l (knownRepr :: TypeRepr a) >>> elimOrsExistsM l
    _ -> return ()

-- | Eliminate all disjunctives and existentials on a variable
elimAllOrsExistsM :: PermState s => ExprVar a ->
                     PermM s (PermImpl r ls) (PermImpl r ls) ()
elimAllOrsExistsM x =
  getVarLocs x >>= mapM_ elimOrsExistsM

-- | Introduce a proof of @x:true@ onto the top of the stack
introTrueM :: ExprVar a ->
              PermM s (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()
introTrueM x = gmapRet (Impl_IntroTrue x)

-- | Introduce a proof of @x:eq(x)@ onto the top of the stack
introEqReflM :: ExprVar a ->
                PermM s (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()
introEqReflM x = gmapRet (Impl_IntroEqRefl x)

-- | Copy an @x:eq(e)@ permission to the top of the stack
introEqCopyM :: PermState s => PermLoc a ->
                PermM s (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()
introEqCopyM l =
  getPerm l >>>= \p ->
  if isEqPerm p then gmapRet (Impl_IntroEqCopy l)
  else error "introEqCopyM: not an eq(e) proof!"

-- | Assert that @x = e@ at bitvector type, and push an @x:eq(e)@ permission to
-- the top of the stack
introAssertBVEq :: ExprVar (BVType w) -> PermExpr (BVType w) ->
                   PermM s (PermImpl r (ls :> PermExpr (BVType w)))
                   (PermImpl r ls) ()
introAssertBVEq x e = gmapRet (Impl_AssertBVEq x e)

-- | Cast a proof of @x:eq(LLVMWord(e1))@ to @x:eq(LLVMWord(e2))@ on the top of
-- the stack
introCastLLVMWordEq ::
  PermState s => ExprVar (LLVMPointerType w) ->
  PermExpr (BVType w) -> PermExpr (BVType w) ->
  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
  (PermImpl r (ls :> PermExpr (LLVMPointerType w))) ()
introCastLLVMWordEq x e1 e2 = gmapRet (Impl_IntroCastLLVMWord x e1 e2)


-- | Eliminate an @x:ptr(p1 * p2)@ into @x:ptr(p1)@ and @x:ptr(p2)@, putting
-- the latter into a new location for @x@
elimLLVMStarM :: PermState s => PermLoc (LLVMPointerType w) ->
                 PermM s (PermImpl r ls) (PermImpl r ls) ()
elimLLVMStarM l =
  gmapRet (Impl_ElimLLVMStar l) >>>
  getPerm l >>>= \p ->
  case p of
    ValPerm_LLVMPtr (LLVMStarPerm p1 p2) ->
      modify (set (permStatePerms . varPerm l) (ValPerm_LLVMPtr p1) .
              over permStatePerms (permAdd (locVar l) (ValPerm_LLVMPtr p2)))
    _ -> error "elimLLVMStar: not an LLVMStar permission!"

-- | Combine proofs of @x:ptr(p1)@ and @x:ptr(p2)@ on the top of the
-- permission stack into a proof of @x:ptr(p1 * p2)@
introLLVMStarM ::
  PermState s => ExprVar (LLVMPointerType w) ->
  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
  (PermImpl r (ls :> PermExpr (LLVMPointerType w)
               :> PermExpr (LLVMPointerType w))) ()
introLLVMStarM x = gmapRet (Impl_IntroLLVMStar x)


-- | Eliminate disjunctives, existentials, and stars at a specific location
elimOrsExistsStarsM :: PermState s => PermLoc a ->
                       PermM s (PermImpl r ls) (PermImpl r ls) ()
elimOrsExistsStarsM l =
  getPerm l >>>= \p ->
  case p of
    ValPerm_Or _ _ -> elimOrM l >>> elimOrsExistsStarsM l
    ValPerm_Exists (_ :: Binding (PermExpr a) _) ->
      elimExistsM l (knownRepr :: TypeRepr a) >>> elimOrsExistsStarsM l
    ValPerm_LLVMPtr (LLVMStarPerm _ _) ->
      -- FIXME HERE: need to also eliminate the new RHS perm!
      elimLLVMStarM l >>> elimOrsExistsStarsM l
    _ -> return ()


-- | Copy a proof of @x:ptr(free(e))@ to the top of the stack
introLLVMFreeM :: PermState s => PermLoc (LLVMPointerType w) ->
                  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
                  (PermImpl r ls) ()
introLLVMFreeM l = gmapRet (Impl_IntroLLVMFree l)

-- | Cast a proof of @x:ptr(free(e1))@ on the top of the stack to one of
-- @x:ptr(free(e2))@
castLLVMFreeM :: PermState s => ExprVar (LLVMPointerType w) ->
                 PermExpr (BVType w) -> PermExpr (BVType w) ->
                 PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
                 (PermImpl r (ls :> PermExpr (LLVMPointerType w))) ()
castLLVMFreeM x e1 e2 = gmapRet (Impl_CastLLVMFree x e1 e2)

-- | Eliminate an @x:ptr((off,S) |-> p)@ into @x:ptr((off,S) |-> eq(y))@ and
-- @y:p@ for a fresh variable @y@, returning the fresh variable @y@
elimLLVMFieldM :: PermState s => PermLoc (LLVMPointerType w) ->
                  PermM s (PermImpl r ls) (PermImpl r ls)
                  (ExprVar (LLVMPointerType w))
elimLLVMFieldM l =
  getPerm l >>>= \p ->
  case p of
    ValPerm_LLVMPtr (LLVMFieldPerm {..}) ->
      gmapRet (Impl_ElimLLVMField l) >>>
      gopenBinding (nu $ \y -> y) >>>= \(y, _) ->
      modify (set (permStatePerms . varPerm l)
              (setLLVMFieldPerm p (ValPerm_Eq (PExpr_Var y))) .
              set (permStatePerms . varPerms y) [llvmFieldPerm]) >>>
      greturn y
    _ ->
      error "elimLLVMFieldM: not an LLVM field permission!"

-- | Combine proofs of @x:ptr(p1)@ and @x:ptr(p2)@ on the top of the
-- permission stack into a proof of @x:ptr(p1 * p2)@
introLLVMFieldM ::
  PermState s => ExprVar (LLVMPointerType w) ->
  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
  (PermImpl r (ls :> PermExpr (LLVMPointerType w)
               :> PermExpr (LLVMPointerType w))) ()
introLLVMFieldM x = gmapRet (Impl_IntroLLVMField x)


----------------------------------------------------------------------
-- * Pattern-Matching Monadic Operations
----------------------------------------------------------------------

-- | The type of a pattern-matching computation over 'ImplM'
type ImplMatch vars r ls1 ls2 =
  MatchT (PermM (ImplState vars)) (PermImpl r ls1) (PermImpl r ls2)

type ImplMatcher vars a =
  forall r ls1 ls2.
  (a -> ImplMatch vars r ls1 ls2 ()) -> ImplMatch vars r ls1 ls2 ()

-- | Run a pattern-matching computation, calling 'implFailM' on failure
implMatchM :: ImplMatch vars r ls1 ls2 () -> ImplM vars r ls1 ls2 ()
implMatchM = runMatchT implFailM

-- | Test whether substituting the current partial substitution into an object
-- succeeds
matchGround :: Substable PartialSubst a Maybe => (Mb vars a) ->
               ImplMatcher vars a
matchGround a =
  matchCase (getPSubst >>>= \psubst -> greturn (partialSubst psubst a))

-- | Test if an expression-in-binding is a variable that is unassigned in the
-- current partial substitution
matchUnassignedVar :: Mb vars (PermExpr a) ->
                      ImplMatcher vars (Member vars (PermExpr a))
{-
                      (Member vars (PermExpr a) -> ImplMatch vars rin rout ()) ->
                      ImplMatch vars rin rout ()
-}
matchUnassignedVar mb_e =
  matchCase
  (getPSubst >>>= \psubst ->
   case mb_e of
     ([nuP| PExpr_Var z |])
       | Left memb <- mbNameBoundP z
       , Nothing <- psubstLookup psubst memb ->
         greturn $ Just memb
     _ -> greturn Nothing)

-- | Test if a splitting-in-binding is a variable that is unassigned in the
-- current partial substitution
matchUnassignedSplVar ::
  Mb vars SplittingExpr ->
  ImplMatcher vars (Member vars (PermExpr SplittingType))
matchUnassignedSplVar mb_spl =
  matchCase
  (getPSubst >>>= \psubst ->
    case mb_spl of
      [nuP| SplExpr_Var z |]
        | Left memb <- mbNameBoundP z
        , Nothing <- psubstLookup psubst memb ->
          greturn $ Just memb
      _ -> greturn Nothing)

-- | Test if a splitting-in-binding is the complete splitting
matchSplAll :: Mb vars SplittingExpr -> ImplMatcher vars ()
matchSplAll [nuP| SplExpr_All |] f = f ()
matchSplAll _ _ = matchFail

-- | Find all permissions on a variable that match a 'Matcher', returning the
-- matched values and also locations of those permissions
matchPerms :: ExprVar a -> Matcher (ValuePerm a) r ->
              ImplMatcher vars [(PermLoc a, r)]
matchPerms x matcher =
  matchCase
  (gget >>>= \s ->
    greturn $ Just $ permFindAll matcher x (s ^. implStatePerms))

-- | Find the first permission on a variable that matches a 'Matcher', returning
-- the matched value and also location of the permission
matchPerm :: ExprVar a -> Matcher (ValuePerm a) r ->
             ImplMatcher vars (PermLoc a, r)
matchPerm x matcher =
  matchCase
  (gget >>>= \s -> greturn $ permFind matcher x (s ^. implStatePerms))


----------------------------------------------------------------------
-- * Proving Equality Permissions
----------------------------------------------------------------------

proveVarEq :: ExprVar a -> Mb vars (PermExpr a) ->
              ImplM vars r (ls :> PermExpr a) ls ()
proveVarEq x mb_e =
  implMatchM $

  -- Prove x:eq(z) for evar z by setting z=x
  (matchUnassignedVar mb_e $ \memb ->
    matchBody $
    modifyPSubst (psubstSet memb (PExpr_Var x)) >>> introEqReflM x)
  <|>

  -- Prove x:eq(x) using introEqReflM
  (matchGround mb_e $ \e ->
    matchPure e (matchEq (PExpr_Var x)) $ \_ ->
    matchBody $ introEqReflM x)
  <|>

  -- Prove x:eq(e) |- x:eq(e) using introEqCopyM
  (matchPerm x (matchEqPerm >=> matchEq (PExpr_Var x)) $ \(l, _) ->
    matchBody $ introEqCopyM l)
  <|>

  (case mb_e of
      [nuP| PExpr_LLVMWord mb_e' |] ->
        -- Prove x:eq(word(x_e)) |- x:eq(word(z)) by setting z=x_e
        (matchUnassignedVar mb_e' $ \memb ->
          matchPerm x (matchEqPerm >=> matchLLVMWordExpr) $ \(l, x_e) ->
          matchBody $
          modifyPSubst (psubstSet memb x_e) >>> introEqCopyM l)
        <|>

        -- Prove x:eq(word(x_e)) |- x:eq(word(e)) by first proving
        -- x:eq(word(x_e)) and then casting e to e'
        (matchGround mb_e' $ \e ->
          matchPerm x (matchEqPerm >=> matchLLVMWordExpr) $ \(l, x_e) ->
          matchBody $
          introEqCopyM l >>> introCastLLVMWordEq x x_e e)

      _ -> matchFail)
  <|>

  -- Try to eliminate disjuncts and existentials to expose a new eq(e) perm; we
  -- then recursively call proveVarEq (not proveVarEqH) because the permissions
  -- have changed
  (matchPerm x matchNestedEqPerm $ \(l, ()) ->
   matchBody $ elimOrsExistsM l >>> proveVarEq x mb_e)


{-
-- | Build a proof on the top of the stack that @x:eq(e)@
proveVarEq :: ExprVar a -> Mb vars (PermExpr a) ->
              ImplM vars (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()
proveVarEq x mb_e =
  getPerms x >>>= \perms ->
  getPSubst >>>= \psubst ->
  proveVarEqH x mb_e perms psubst

-- | Main helper function for 'proveVarEq'
proveVarEqH :: ExprVar a -> Mb vars (PermExpr a) ->
               [ValuePerm a] -> PartialSubst vars ->
               ImplM vars (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()

-- Prove x:eq(z) for evar z by setting z=x
proveVarEqH x [nuP| PExpr_Var z |] _ psubst
  | Left memb <- mbNameBoundP z
  , Nothing <- psubstLookup psubst memb
  = modifyPSubst (psubstSet memb (PExpr_Var x)) >>> introEqReflM x

-- Prove x:eq(x) by reflexivity
proveVarEqH x mb_e _ psubst
  | Just (PExpr_Var y) <- partialSubst psubst mb_e
  , x == y
  = introEqReflM x

-- Prove x:eq(e) |- x:eq(e) using introEqCopyM
proveVarEqH x mb_e perms psubst
  | Just e <- partialSubst psubst mb_e
  , Just (l, _) <- find (\(_, e') -> e == e') (findEqPerms x perms)
  = introEqCopyM l

-- Prove x:eq(word(e)) |- x:eq(word(z)) by setting z=e
proveVarEqH x [nuP| PExpr_LLVMWord (PExpr_Var z) |] perms psubst
  | Left memb <- mbNameBoundP z
  , Nothing <- psubstLookup psubst memb
  , Just (l, ValPerm_Eq (PExpr_LLVMWord e')) <-
      findPerm isEqLLVMWordPerm x perms
  = modifyPSubst (psubstSet memb e') >>> introEqCopyM l

-- Prove x:eq(word(e)) |- x:eq(word(e')) by first proving x:eq(word(e)) and then
-- casting e to e'
proveVarEqH x [nuP| PExpr_LLVMWord mb_e |] perms psubst
  | Just e <- partialSubst psubst mb_e
  , Just (l, ValPerm_Eq (PExpr_LLVMWord e')) <-
      findPerm isEqLLVMWordPerm x perms
  = introEqCopyM l >>> introCastLLVMWordEq (locVar l) e e'

-- Try to eliminate disjuncts and existentials to expose a new eq(e) perm; we
-- then recursively call proveVarEq (not proveVarEqH) because the permissions
-- have changed
proveVarEqH x p perms _
  | Just (l, _) <- findPerm isNestedEqPerm x perms
  = elimOrsExistsM l >>> proveVarEq x p

-- Otherwise give up!
proveVarEqH _ _ _ _ = implFailM
-}


----------------------------------------------------------------------
-- * Proving Field Permissions
----------------------------------------------------------------------

proveVarField :: (1 <= w, KnownNat w) =>
                 ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                 Mb vars SplittingExpr ->
                 Mb vars (ValuePerm (LLVMPointerType w)) ->
                 ImplM vars r (ls :> PermExpr (LLVMPointerType w)) ls ()
proveVarField x off mb_spl mb_p =
  implMatchM $

  -- Prove x:ptr((off,All) |-> p1) |- x:ptr((off,All) |-> p2) by first
  -- eliminating the LHS to x:ptr((off,All) |-> eq(y)), y:p1 for fresh y,
  -- proving x:ptr((off,All) |-> eq(y)),y:p1 |- x:ptr((off,All) |-> eq(y)),y:p2,
  -- and then re-combining the RHS into x:ptr((off,All) |-> p2)
  (matchPerm x (matchPtrPerm $ matchFieldPtrPermOff off) $ \(l, (spl1, p1)) ->
    matchSplAll mb_spl $ \() ->
    matchBody $
    elimLLVMFieldM l >>>= \y ->
    implPushM l (ValPerm_LLVMPtr
                 (LLVMFieldPerm off spl1 (ValPerm_Eq (PExpr_Var y)))) >>>
    proveVarImpl y mb_p >>>
    introLLVMFieldM x)

{-
proveVarField :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                 Mb vars SplittingExpr ->
                 Mb vars (ValuePerm (LLVMPointerType w)) ->
                 ImplM vars r (ls :> PermExpr (LLVMPointerType w)) ls ()
proveVarField x off mb_spl mb_p =
  getPerms x >>>= \perms ->
  proveVarFieldH x off mb_spl mb_p perms


proveVarFieldH :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                  Mb vars SplittingExpr ->
                  Mb vars (ValuePerm (LLVMPointerType w)) ->
                  [ValuePerm (LLVMPointerType w)] ->
                  ImplM vars r (ls :> PermExpr (LLVMPointerType w)) ls ()

-- Prove x:ptr((off,All) |-> p1) |- x:ptr((off,All) |-> p2) by first eliminating
-- the LHS to x:ptr((off,All) |-> eq(y)), y:p1 for a fresh variable y, then
-- proving x:ptr((off,All) |-> eq(y)),y:p1 |- x:ptr((off,All) |-> eq(y)),y:p2,
-- and then re-combining the RHS into x:ptr((off,All) |-> p2)
proveVarFieldH x off mb_spl mb_p perms
  | Just (l, ValPerm_LLVMPtr (LLVMFieldPerm _ spl' p')) <-
      findPerm (isFieldPtrPermOff off) perms
  = error "FIXME HERE NOW"
-}      

----------------------------------------------------------------------
-- * Proving Permission Implications
----------------------------------------------------------------------

-- | Prove @x:p@, where @p@ may have existentially-quantified variables in it
proveVarImpl :: ExprVar a -> Mb vars (ValuePerm a) ->
                ImplM vars r (ls :> PermExpr a) ls ()

-- Prove x:true vacuously
proveVarImpl x [nuP| ValPerm_True |] = introTrueM x

-- Prove x:(p1 \/ p2) by trying to prove x:p1 and x:p2 in two branches
proveVarImpl x [nuP| ValPerm_Or p1 p2 |] =
  implCatchM
  (proveVarImpl x p1 >>>
   partialSubstForceM p2
   "proveVarImpl: incomplete psubst: introOrL" >>>= introOrLM x)
  (proveVarImpl x p2 >>>
   partialSubstForceM p2
   "proveVarImpl: incomplete psubst: introOrR" >>>= introOrRM x)

-- Prove x:exists (z:tp).p by proving x:p in an extended vars context
proveVarImpl x [nuP| ValPerm_Exists p |] =
  withExtVarsM (proveVarImpl x $ mbCombine p) >>>= \((), maybe_e) ->
  let e = fromMaybe (zeroOfType knownRepr) maybe_e in
  partialSubstForceM p "proveVarImpl: incomplete psubst: introExists" >>>=
  introExistsM x knownRepr e

-- Prove x:eq(e) by calling proveVarEq
proveVarImpl x [nuP| ValPerm_Eq e |] = proveVarEq x e

-- Prove x:ptr(p1 * p2) by proving x:ptr(p1) and x:ptr(p2) and then combining
-- the two proofs
proveVarImpl x [nuP| ValPerm_LLVMPtr (LLVMStarPerm p1 p2) |] =
  proveVarImpl x (fmap ValPerm_LLVMPtr p1) >>>
  proveVarImpl x (fmap ValPerm_LLVMPtr p2) >>>
  introLLVMStarM x

-- Prove x:ptr(free(e))
proveVarImpl x p@([nuP| ValPerm_LLVMPtr (LLVMFreePerm mb_e) |]) =
  implMatchM $

  -- Prove x:ptr(free(e')) |- x:ptr(free(e)) by first proving x:ptr(free(e'))
  -- and then casting e' to e
  (matchPerm x (matchPtrPerm matchFreePtrPerm) $ \(l, e') ->
    matchGround mb_e $ \e ->
    matchBody $ introLLVMFreeM l >>> castLLVMFreeM x e' e)
  <|>

  -- If there are any x:ptr(free(e')) perms under existentials, ors, and/or
  -- stars, eliminate them
  (matchPerm x (matchInExsOrsStars matchFreePtrPerm) $ \(l,_) ->
    matchBody $ elimOrsExistsStarsM l >>> proveVarImpl x p)

-- Prove x:ptr((off,spl) |-> p)
proveVarImpl x [nuP| ValPerm_LLVMPtr
                   (LLVMFieldPerm mb_off mb_spl mb_p) |] =
  partialSubstForceM mb_off
  "proveVarImpl: incomplete psubst: LLVM field" >>>= \off ->
  proveVarField x off mb_spl mb_p


data ReqPerm vars a where
  ReqPerm :: ExprVar a -> Mb vars (ValuePerm a) -> ReqPerm vars (PermExpr a)

proveVarsImpl :: MapRList (ReqPerm vars) ls -> ImplM vars r ls RNil ()
proveVarsImpl MNil = return ()
proveVarsImpl (reqs :>: ReqPerm x p) = proveVarsImpl reqs >>> proveVarImpl x p
