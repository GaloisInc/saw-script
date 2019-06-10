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

{-
  Impl_Push :: PermLoc a -> ValuePerm a -> PermImpl r (ls :> PermExpr a) ->
               PermImpl r ls
  -- ^ "Push" a permission from the input permission set to the stack of
  -- distinguished permissions:
  --
  -- > Gin | Pl,x:p * Pin |- rets
  -- > ---------------------------
  -- > Gin | Pl * Pin, x:p |- rets
-}

  Impl_ElimOr :: ExprVar a -> PermImpl r ls -> PermImpl r ls ->
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

  Impl_ElimExists :: ExprVar a -> TypeRepr tp ->
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

  Impl_IntroEqCopy :: ExprVar a -> PermExpr a ->
                      PermImpl r (ls :> PermExpr a) -> PermImpl r ls
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

  Impl_CastLLVMWord ::
    ExprVar (LLVMPointerType w) -> PermExpr (BVType w) -> PermExpr (BVType w) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w))
  -- ^ Cast a proof that @x:eq(word(e1))@ to one that @x:eq(word(e2))@ with a
  -- dynamic check that @e1=e2@:
  --
  -- > Gin | Pl,x:eq(word(e2)) * Pin |- rets
  -- > -------------------------------------
  -- > Gin | Pl,x:eq(word(e1)) * Pin |- rets

  Impl_IntroLLVMPtr :: ExprVar (LLVMPointerType w) ->
                       PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
                       PermImpl r ls
  -- ^ Prove an empty pointer permission @x:ptr()@ from any pointer permission
  -- @x:ptr(pps)@ on the left:
  --
  -- > Gin | Pl, x:ptr() * Pin, x:ptr(pps) |- rets
  -- > -------------------------------------------
  -- > Gin | Pl * Pin, x:ptr(pps) |- rets

  Impl_CastLLVMPtr :: ExprVar (LLVMPointerType w) ->
                      PermExpr (BVType w) ->
                      ExprVar (LLVMPointerType w) ->
                      PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
                      PermImpl r (ls :> PermExpr (LLVMPointerType w)
                                  :> PermExpr (LLVMPointerType w))
  -- ^ Cast a @y:ptr(pps)@ on the top of the stack to @x:ptr(pps - off)@ using a
  -- proof of @x:eq(y+off)@ just below it on the stack:
  --
  -- > Gin | Pl, x:ptr(pps - off) * Pin, x:ptr(pps) |- rets
  -- > ----------------------------------------------------
  -- > Gin | Pl, x:eq(y+off),y:ptr(pps) * Pin |- rets

  Impl_IntroLLVMFree :: ExprVar (LLVMPointerType w) -> Int ->
                        PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
                        PermImpl r (ls :> PermExpr (LLVMPointerType w))
  -- ^ Copy a free pointer permission to the pointer permission on the top of
  -- the stack, using the 'Int' as the index into the pointer perms in @Pin@,
  -- i.e., the length of @pps1@:
  --
  -- > Gin | Pl, x:ptr(pps, free(e)) * Pin, x:ptr(pps1, free(e), pps2) |- rets
  -- > -----------------------------------------------------------------------
  -- > Gin | Pl, x:ptr(pps) * Pin, x:ptr(pps1, free(e), pps2) |- rets

  Impl_CastLLVMFree :: ExprVar (LLVMPointerType w) ->
                       PermExpr (BVType w) -> PermExpr (BVType w) ->
                       PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
                       PermImpl r (ls :> PermExpr (LLVMPointerType w))
  -- ^ Cast a proof of @x:ptr(free(e1))@ on the top of the stack to one of
  -- @x:ptr(free(e2))@:
  --
  -- > Gin | Pl, x:ptr(pps, free(e2)) * Pin |- rets
  -- > --------------------------------------------
  -- > Gin | Pl, x:ptr(pps, free(e1)) * Pin |- rets

  Impl_ElimLLVMField ::
    ExprVar (LLVMPointerType w) -> Int ->
    Binding (PermExpr (LLVMPointerType w)) (PermImpl r ls) ->
    PermImpl r ls
  -- ^ Eliminate a field permission @x:ptr((off,S) |-> p)@ into a permission
  -- @x:ptr((off,S) |-> eq(y))@ that the field contains a fresh variable @y@ and
  -- a permission @y:p@ on @y@:
  --
  -- > Gin | Pl * Pin, x:ptr(pps1, (off,S) |-> eq(y), pps2), y:p |- rets
  -- > -----------------------------------------------------------------
  -- > Gin | Pl * Pin, x:ptr(pps1, (off,S) |-> p, pps2) |- rets

  Impl_IntroLLVMFieldAll ::
    ExprVar (LLVMPointerType w) -> Int ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w))
  -- ^ Move a field permission, which should contain an equals permission, into
  -- the pointer permission on the top of the stack:
  --
  -- > Gin | Pl, x:ptr(pps, x:ptr((off,spl) |-> eq(y)))
  -- >       * Pin, x:ptr(pps1, pps2) |- rets
  -- > ---------------------------------------------------------------
  -- > Gin | Pl, x:ptr(pps)
  -- >       * Pin, x:ptr(pps1, (off,spl) |-> eq(y), pps2) |- rets

  Impl_IntroLLVMFieldSplit ::
    ExprVar (LLVMPointerType w) -> Int -> SplittingExpr ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w)) ->
    PermImpl r (ls :> PermExpr (LLVMPointerType w))
  -- ^ Move a field permission of the form @(off,spl) |-> eq(e)@ into two
  -- copies, keeping the left half in the current permission set and pushing the
  -- right half onto the stack:
  --
  -- > Gin | Pl, x:ptr(pps, x:ptr((off,right spl) |-> eq(y)))
  -- >       * Pin, x:ptr(pps1, (off,left spl) |-> eq(y), pps2) |- rets
  -- > ---------------------------------------------------------------
  -- > Gin | Pl, x:ptr(pps)
  -- >       * Pin, x:ptr(pps1, (off,spl) |-> eq(y), pps2) |- rets

  Impl_IntroLLVMFieldContents ::
    ExprVar (LLVMPointerType w) -> ExprVar (LLVMPointerType w) ->
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
matchPure :: GenMonad m => a -> (a -> Maybe b) ->
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

-- | Set the value for an existential variable in the current substitution,
-- raising an error if it is already set
setVarM :: Member vars (PermExpr a) -> PermExpr a -> ImplM vars r ls ls ()
setVarM x e = modifyPSubst (psubstSet x e)

-- | Look up the current permission for a given variable
getPerm :: PermState s => ExprVar a -> PermM s r r (ValuePerm a)
getPerm x = view (permStatePerms . varPerm x) <$> gget

-- | Set the current permission for a given variable
setPerm :: PermState s => ExprVar a -> ValuePerm a -> PermM s r r ()
setPerm x p = modify $ set (permStatePerms . varPerm x) p

-- | Get the pointer permissions for a variable @x@, assuming @x@ has LLVM
-- pointer permissions
getLLVMPtrPerms :: PermState s => ExprVar (LLVMPointerType w) ->
                   PermM s r r [LLVMPtrPerm w]
getLLVMPtrPerms x =
  getPerm x >>>= \p ->
  case p of
    ValPerm_LLVMPtr pps -> greturn pps
    _ -> error "getLLVMPtrPerms"

-- | Terminate the current proof branch with a failure
implFailM :: PermM s rany (PermImpl r ls) ()
implFailM = gmapRet (const Impl_Fail)

-- | Finish the current proof branch successfully with an 'Impl_Done'
implDoneM :: PermM s r (PermImpl r ls) ()
implDoneM = gmapRet Impl_Done

{-
-- | Push a permission from the permission set to the permission stack
implPushM :: PermState s => PermLoc a -> ValuePerm a ->
             PermM s (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()
implPushM l p =
  gmapRet (Impl_Push l p) >>>
  modify (over permStatePerms $ permDelete l p)
-}

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
elimOrM :: PermState s => ExprVar a ->
           PermM s (PermImpl r ls) (PermImpl r ls) ()
elimOrM x =
  gmapRet (\(impl1, impl2) -> Impl_ElimOr x impl1 impl2) >>>
  gparallel
  (modify (over (permStatePerms . varPerm x) orPermLeft))
  (modify (over (permStatePerms . varPerm x) orPermRight))

-- | Eliminate an existential permission @x:(exists (y:tp).p)@ in the current
-- permission set
elimExistsM :: PermState s => ExprVar a -> TypeRepr tp ->
               PermM s (PermImpl r ls) (PermImpl r ls) ()
elimExistsM x tp =
  gget >>>= \s ->
  gmapRet (Impl_ElimExists x tp) >>>
  gopenBinding (exPermBody tp $
                s ^. permStatePerms . varPerm x) >>>= \(nm, p_body) ->
  put (set (permStatePerms . varPerm x) p_body s)

-- | Eliminate disjunctives and existentials at a specific location
elimOrsExistsM :: PermState s => ExprVar a ->
                  PermM s (PermImpl r ls) (PermImpl r ls) ()
elimOrsExistsM x =
  getPerm x >>>= \p ->
  case p of
    ValPerm_Or _ _ -> elimOrM x >>> elimOrsExistsM x
    ValPerm_Exists (_ :: Binding (PermExpr a) _) ->
      elimExistsM x (knownRepr :: TypeRepr a) >>> elimOrsExistsM x
    _ -> return ()

-- | Introduce a proof of @x:true@ onto the top of the stack
introTrueM :: ExprVar a ->
              PermM s (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()
introTrueM x = gmapRet (Impl_IntroTrue x)

-- | Introduce a proof of @x:eq(x)@ onto the top of the stack
introEqReflM :: ExprVar a ->
                PermM s (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()
introEqReflM x = gmapRet (Impl_IntroEqRefl x)

-- | Copy an @x:eq(e)@ permission to the top of the stack
introEqCopyM :: PermState s => ExprVar a -> PermExpr a ->
                PermM s (PermImpl r (ls :> PermExpr a)) (PermImpl r ls) ()
introEqCopyM x e =
  getPerm x >>>= \p ->
  case p of
    ValPerm_Eq e' | e' == e -> gmapRet (Impl_IntroEqCopy x e)
    ValPerm_Eq _ -> error "introEqCopyM: incorrect expression!"
    _ -> error "introEqCopyM: not an eq(e) proof!"

-- | Assert that @x = e@ at bitvector type, and push an @x:eq(e)@ permission to
-- the top of the stack
introAssertBVEq :: ExprVar (BVType w) -> PermExpr (BVType w) ->
                   PermM s (PermImpl r (ls :> PermExpr (BVType w)))
                   (PermImpl r ls) ()
introAssertBVEq x e = gmapRet (Impl_AssertBVEq x e)

-- | Cast a proof of @x:eq(LLVMWord(e1))@ to @x:eq(LLVMWord(e2))@ on the top of
-- the stack
castLLVMWordEq ::
  PermState s => ExprVar (LLVMPointerType w) ->
  PermExpr (BVType w) -> PermExpr (BVType w) ->
  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
  (PermImpl r (ls :> PermExpr (LLVMPointerType w))) ()
castLLVMWordEq x e1 e2 = gmapRet (Impl_CastLLVMWord x e1 e2)


-- | Prove an empty @x:ptr()@ permission from any @x:ptr(pps)@ permissionx
introLLVMPtrM ::
  PermState s => ExprVar (LLVMPointerType w) ->
  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w))) (PermImpl r ls) ()
introLLVMPtrM x = gmapRet (Impl_IntroLLVMPtr x)

-- | Cast a @y:ptr(pps)@ on the top of the stack to @x:ptr(pps - off)@ using a
-- proof of @x:eq(y+off)@ just below it on the stack
castLLVMPtrM :: PermState s =>
                ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                ExprVar (LLVMPointerType w) ->
                PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
                (PermImpl r (ls :> PermExpr (LLVMPointerType w)
                             :> PermExpr (LLVMPointerType w))) ()
castLLVMPtrM y off x = gmapRet (Impl_CastLLVMPtr y off x)


-- | Copy a proof of @x:ptr(free(e))@, from the current permission
-- @x:ptr(pps1,free(e),pps2)@, into the @x:ptr(pps)@ permission on the top of
-- the stack, where the 'Int' index gives the size of @pps1@
introLLVMFreeM :: PermState s => ExprVar (LLVMPointerType w) -> Int ->
                  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
                  (PermImpl r (ls :> PermExpr (LLVMPointerType w))) ()
introLLVMFreeM x i = gmapRet (Impl_IntroLLVMFree x i)

-- | Cast a proof of @x:ptr(pps, free(e1))@ on the top of the stack to one of
-- @x:ptr(pps, free(e2))@
castLLVMFreeM :: PermState s => ExprVar (LLVMPointerType w) ->
                 PermExpr (BVType w) -> PermExpr (BVType w) ->
                 PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
                 (PermImpl r (ls :> PermExpr (LLVMPointerType w))) ()
castLLVMFreeM x e1 e2 = gmapRet (Impl_CastLLVMFree x e1 e2)

-- | Eliminate a permission @x:ptr(pps1,(off,S) |-> p,pps2)@ into permissions
-- @x:ptr(pps1,(off,S) |-> eq(y),pps2)@ and @y:p@ for a fresh variable @y@,
-- returning the fresh variable @y@
elimLLVMFieldM :: PermState s => ExprVar (LLVMPointerType w) -> Int ->
                  PermM s (PermImpl r ls) (PermImpl r ls)
                  (ExprVar (LLVMPointerType w))
elimLLVMFieldM x i =
  getPerm x >>>= \p ->
  case p of
    ValPerm_LLVMPtr pps
      | LLVMFieldPerm { llvmFieldPerm =
                          ValPerm_Eq (PExpr_Var y) } <- pps !! i ->
        -- If the p permission is already of the form eq(y), just return y
        greturn y
      | LLVMFieldPerm {..} <- pps !! i ->
        gmapRet (Impl_ElimLLVMField x i) >>>
        gopenBinding (nu $ \y -> y) >>>= \(y, _) ->
        let pps' =
              set (element i)
              (LLVMFieldPerm { llvmFieldPerm = ValPerm_Eq (PExpr_Var y), .. })
              pps in
        setPerm x (ValPerm_LLVMPtr pps') >>>
        setPerm y llvmFieldPerm >>>
        greturn y
    _ ->
      error "elimLLVMFieldM: not an LLVM field permission!"

-- | Move a field permission of the form @(off,All) |-> eq(e)@ to the
-- @x:ptr(pps)@ permission on the top of of the stack
introLLVMFieldAllM ::
  PermState s => ExprVar (LLVMPointerType w) -> Int ->
  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
  (PermImpl r (ls :> PermExpr (LLVMPointerType w))) ()
introLLVMFieldAllM x i =
  getPerm x >>>= \p ->
  case p of
    ValPerm_LLVMPtr pps
      | i < length pps
      , LLVMFieldPerm _ SplExpr_All (ValPerm_Eq _) <- pps !! i ->
        gmapRet (Impl_IntroLLVMFieldAll x i) >>>
        setPerm x (ValPerm_LLVMPtr $ deleteNth i pps)
    _ -> error "introLLVMFieldAllM"

-- | Split a field permission @(off,spl) |-> eq(e)@ into two, leaving the left
-- half in the current permission stack and moving the right half to the top of
-- of the stack
introLLVMFieldSplitM ::
  PermState s => ExprVar (LLVMPointerType w) -> Int -> SplittingExpr ->
  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
  (PermImpl r (ls :> PermExpr (LLVMPointerType w))) ()
introLLVMFieldSplitM x i spl =
  getPerm x >>>= \p ->
  case p of
    ValPerm_LLVMPtr pps
      | i < length pps
      , LLVMFieldPerm off spl' (ValPerm_Eq e) <- pps !! i
      , spl' == spl ->
        gmapRet (Impl_IntroLLVMFieldSplit x i spl) >>>
        setPerm x (ValPerm_LLVMPtr $
                   set (element i)
                   (LLVMFieldPerm off (SplExpr_L spl) (ValPerm_Eq e)) pps)
    _ -> error "introLLVMFieldSplitM"

-- | Combine proofs of @x:ptr(pps,(off,spl) |-> eq(y))@ and @y:p@ on the top of
-- the permission stack into a proof of @x:ptr(pps,(off,spl |-> p))@
introLLVMFieldContentsM ::
  PermState s => ExprVar (LLVMPointerType w) ->
  ExprVar (LLVMPointerType w) ->
  PermM s (PermImpl r (ls :> PermExpr (LLVMPointerType w)))
  (PermImpl r (ls :> PermExpr (LLVMPointerType w)
               :> PermExpr (LLVMPointerType w))) ()
introLLVMFieldContentsM x y = gmapRet (Impl_IntroLLVMFieldContents x y)


----------------------------------------------------------------------
-- * Pattern-Matching Monadic Operations
----------------------------------------------------------------------

{- FIXME: use or remove these!
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
-}


----------------------------------------------------------------------
-- * Proving Equality Permissions
----------------------------------------------------------------------

{-
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
          introEqCopyM l >>> castLLVMWordEq x x_e e)

      _ -> matchFail)
  <|>

  -- Try to eliminate disjuncts and existentials to expose a new eq(e) perm; we
  -- then recursively call proveVarEq (not proveVarEqH) because the permissions
  -- have changed
  (matchPerm x matchNestedEqPerm $ \(l, ()) ->
   matchBody $ elimOrsExistsM l >>> proveVarEq x mb_e)
-}


-- | Build a proof on the top of the stack that @x:eq(e)@
proveVarEq :: ExprVar a -> Mb vars (PermExpr a) ->
              ImplM vars r (ls :> PermExpr a) ls ()
proveVarEq x mb_e =
  getPerm x >>>= \perm ->
  getPSubst >>>= \psubst ->
  proveVarEqH x perm psubst mb_e

-- | Main helper function for 'proveVarEq'
proveVarEqH :: ExprVar a -> ValuePerm a -> PartialSubst vars ->
               Mb vars (PermExpr a) ->
               ImplM vars r (ls :> PermExpr a) ls ()

-- Prove x:eq(z) for evar z by setting z=x
proveVarEqH x _ psubst [nuP| PExpr_Var z |]
  | Left memb <- mbNameBoundP z
  , Nothing <- psubstLookup psubst memb
  = setVarM memb (PExpr_Var x) >>> introEqReflM x

-- Prove x:eq(x) by reflexivity
proveVarEqH x _ psubst mb_e
  | Just (PExpr_Var y) <- partialSubst psubst mb_e
  , x == y
  = introEqReflM x

-- Prove x:eq(e) |- x:eq(e) using introEqCopyM
proveVarEqH x (ValPerm_Eq e) psubst mb_e
  | Just e' <- partialSubst psubst mb_e
  , e' == e
  = introEqCopyM x e

-- Prove x:eq(word(e)) |- x:eq(word(z)) by setting z=e
proveVarEqH x (ValPerm_Eq
               (PExpr_LLVMWord e)) psubst [nuP| PExpr_LLVMWord (PExpr_Var z) |]
  | Left memb <- mbNameBoundP z
  , Nothing <- psubstLookup psubst memb
  = setVarM memb e >>> introEqCopyM x (PExpr_LLVMWord e)

-- Prove x:eq(word(e')) |- x:eq(word(e)) by first proving x:eq(word(e')) and
-- then casting e' to e
proveVarEqH x (ValPerm_Eq
               (PExpr_LLVMWord e')) psubst [nuP| PExpr_LLVMWord mb_e |]
  | Just e <- partialSubst psubst mb_e
  = introEqCopyM x (PExpr_LLVMWord e') >>> castLLVMWordEq x e' e

-- Eliminate disjunctive and/or existential permissions
proveVarEqH x (ValPerm_Or _ _) _ mb_e =
  elimOrsExistsM x >>> proveVarEq x mb_e

-- Eliminate disjunctive and/or existential permissions
proveVarEqH x (ValPerm_Exists _) _ mb_e =
  elimOrsExistsM x >>> proveVarEq x mb_e

-- Otherwise give up!
proveVarEqH _ _ _ _ = implFailM


----------------------------------------------------------------------
-- * Proving Field Permissions
----------------------------------------------------------------------

proveVarField :: ExprVar (LLVMPointerType w) -> [LLVMPtrPerm w] ->
                 PermExpr (BVType w) -> Mb vars SplittingExpr ->
                 Mb vars (ValuePerm (LLVMPointerType w)) ->
                 ImplM vars r (ls :> PermExpr (LLVMPointerType w))
                 (ls :> PermExpr (LLVMPointerType w)) ()
proveVarField x pps off [nuP| SplExpr_All |] mb_p
  | Just (i, (x_spl, x_p)) <- findFieldPerm off pps =
    case x_spl of
      SplExpr_All ->
        elimLLVMFieldM x i >>>= \y ->
        introLLVMFieldAllM x i >>>
        proveVarImpl y mb_p >>>
        introLLVMFieldContentsM x y
      _ ->
        -- If we need All and we have less than All, we fail, because, if there
        -- is some other permission with All that matches off, then the current
        -- permissions should be unsatisfiable anyway, so it shouldn't matter
        implFailM

proveVarField x pps off [nuP| SplExpr_Var z |] mb_p
  | Just (i, (x_spl, x_p)) <- findFieldPerm off pps
  , Left memb <- mbNameBoundP z =
    elimLLVMFieldM x i >>>= \y ->
    introLLVMFieldSplitM x i x_spl >>>
    setVarM memb (PExpr_Spl $ SplExpr_R x_spl) >>>
    proveVarImpl y mb_p >>>
    introLLVMFieldContentsM x y

proveVarField x pps off mb_spl mb_p =
  error "FIXME HERE: proveVarField"

{-
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
-- * Proving LLVM Pointer Permissions
----------------------------------------------------------------------

-- FIXME: documentation; note that we expect x:ptr(pps)
proveVarPtrPerms :: ExprVar (LLVMPointerType w) ->
                    [Mb vars (LLVMPtrPerm w)] ->
                    ImplM vars r (ls :> PermExpr (LLVMPointerType w))
                    (ls :> PermExpr (LLVMPointerType w)) ()

-- If the required permissions are empty, we are done!
proveVarPtrPerms x [] = greturn ()

-- Prove x:ptr(free(e')) |- x:ptr(free(e)) (where e' is not necessarily distinct
-- from e) by first proving x:ptr(free(e')) and then casting e' to e (if needed)
proveVarPtrPerms x ([nuP| LLVMFreePerm mb_e |] : mb_pps') =
  partialSubstForceM mb_e
  "proveVarPtrPerms: incomplete psubst: LLVM free size" >>>= \e ->
  getLLVMPtrPerms x >>>= \pps ->
  case findFreePerm pps of
    Just (i, e') ->
      introLLVMFreeM x i >>> castLLVMFreeM x e' e >>>
      proveVarPtrPerms x mb_pps'
    _ -> implFailM

proveVarPtrPerms x ([nuP| LLVMFieldPerm mb_off mb_spl mb_p |] : mb_pps') =
  partialSubstForceM mb_off
  "proveVarPtrPerms: incomplete psubst: LLVM field offset" >>>= \off ->
  getLLVMPtrPerms x >>>= \pps ->
  proveVarField x pps off mb_spl mb_p >>>
  proveVarPtrPerms x mb_pps'

proveVarPtrPerms _ _ = error "FIXME HERE: proveVarPtrPerms"


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

-- Prove x:eq(e) by calling proveVarEq; note that we do not eliminate
-- disjunctive permissions because some trivial equalities do not require any eq
-- permissions on the left
proveVarImpl x [nuP| ValPerm_Eq e |] = proveVarEq x e

-- Prove x:ptr(pps) by eliminating non-atomic permissions and case-splitting on
-- what is left
proveVarImpl x [nuP| ValPerm_LLVMPtr mb_pps |] =
  elimOrsExistsM x >>> getPerm x >>>= \x_p ->
  case x_p of
    ValPerm_LLVMPtr _ ->
      -- If we have x:ptr(x_pps) on the left, introduce x:ptr() on the stack and
      -- then prove the individual pointer perms by calling proveVarPtrPerms
      introLLVMPtrM x >>> proveVarPtrPerms x (mbList mb_pps)

    ValPerm_Eq (PExpr_Var y) ->
      -- If we have x:eq(y) on the left, prove y:ptr(pps) and then cast the
      -- result
      introEqCopyM x (PExpr_Var y) >>>
      proveVarImpl y (fmap ValPerm_LLVMPtr mb_pps) >>>
      castLLVMPtrM y (intBVExpr 0) x

    ValPerm_Eq (PExpr_LLVMOffset y off) ->
      -- If we have x:eq(y+off) on the left, prove y:ptr(pps+off) and then cast
      -- the result
      introEqCopyM x (PExpr_LLVMOffset y off) >>>
      proveVarImpl y (fmap (ValPerm_LLVMPtr .
                            map (offsetLLVMPtrPerm off)) mb_pps) >>>
      castLLVMPtrM y off x

    _ ->
      -- Otherwise fail
      implFailM

-- We do not yet handle mu
proveVarImpl _ [nuP| ValPerm_Mu _ |] = implFailM

-- We do not yet handle permission variables
proveVarImpl _ [nuP| ValPerm_Var _ |] = implFailM


data ReqPerm vars a where
  ReqPerm :: ExprVar a -> Mb vars (ValuePerm a) -> ReqPerm vars (PermExpr a)

proveVarsImpl :: MapRList (ReqPerm vars) ls -> ImplM vars r ls RNil ()
proveVarsImpl MNil = return ()
proveVarsImpl (reqs :>: ReqPerm x p) = proveVarsImpl reqs >>> proveVarImpl x p
