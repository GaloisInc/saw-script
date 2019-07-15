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
import Data.Functor.Compose
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
                   PermImpl r (ls :> a) ->
                   PermImpl r (ls :> a)
  -- ^ @Impl_IntroOrL x p2 pf@ applies left disjunction introduction to the top
  -- permission on the stack:
  --
  -- > pf = Gamma | Pl, x:(p1 \/ p2) * Pin |- Pout
  -- > -------------------------------------------
  -- > Gamma | Pl, x:p1 * Pin |- rets

  Impl_IntroOrR :: ExprVar a -> ValuePerm a ->
                   PermImpl r (ls :> a) ->
                   PermImpl r (ls :> a)
  -- ^ @Impl_IntroOrR x p1 pf@ applies right disjunction introduction to the top
  -- permission on the stack:
  --
  -- > pf = Gamma | Pl, x:(p1 \/ p2) * Pin |- Pout
  -- > -------------------------------------------
  -- > Gamma | Pl, x:p2 * Pin |- rets

  Impl_ElimExists :: KnownRepr TypeRepr tp => ExprVar a ->
                     Binding (PermExpr tp) (PermImpl r ls) ->
                     PermImpl r ls
  -- ^ Eliminate an existential, i.e., a 'ValPerm_Exists', on the given variable
  --
  -- pf = Gin, z:tp | Pin, x:p |- rets
  -- ------------------------------------------------------
  -- Gin | x:(exists z:tp. p)  |- rets

  Impl_IntroExists :: KnownRepr TypeRepr tp => ExprVar a -> PermExpr tp ->
                      Binding (PermExpr tp) (ValuePerm a) ->
                      PermImpl r (ls :> a) ->
                      PermImpl r (ls :> a)
  -- ^ @Intro_Exists x tp e p pf@ applies existential introduction to the top
  -- permission on the stack:
  --
  -- > pf = Gamma | Pl, x:(exists z:tp.p) * Pin |- Pout
  -- > ------------------------------------------------
  -- > Gamma | Pl, x:[e'/z]p * Pin |- Pout

  Impl_IntroTrue :: ExprVar a -> PermImpl r (ls :> a) -> PermImpl r ls
  -- ^ Introduce a true permission onto the stack of distinguished permissions:
  --
  -- > Gin | Pl,x:true * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_IntroCast :: ExprVar a -> ExprVar a ->
                    PermImpl r (ls :> a) ->
                    PermImpl r (ls :> a :> a)
  -- ^ Cast a proof of @y:p@ to one of @x:p@ using @x:eq(y)@:
  --
  -- > Gin | Pl,x:p * Pin |- rets
  -- > ----------------------------------
  -- > Gin | Pl,x:eq(y),y:p * Pin |- rets

  Impl_IntroEqRefl :: ExprVar a -> PermImpl r (ls :> a) ->
                      PermImpl r ls
  -- ^ Introduce a proof that @x:eq(x)@:
  --
  -- > Gin | Pl,x:eq(x) * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_IntroEqCopy :: ExprVar a -> PermExpr a ->
                      PermImpl r (ls :> a) -> PermImpl r ls
  -- ^ Copy a proof that @x:eq(e)@ from the normal permissions to the stack:
  --
  -- > Gin | Pl,x:eq(e) * Pin,x:eq(e) |- rets
  -- > --------------------------------------
  -- > Gin | Pl * Pin,x:eq(e) |- rets

  Impl_AssertBVEq :: ExprVar (BVType w) -> PermExpr (BVType w) ->
                     PermImpl r (ls :> (BVType w)) ->
                     PermImpl r ls
  -- ^ Introduce a proof that @x:eq(e)@ at bitvector type (which becomes a
  -- dynamic check that @x=e@):
  --
  -- > Gin | Pl,x:eq(e) * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_CastLLVMWord ::
    ExprVar (LLVMPointerType w) -> PermExpr (BVType w) -> PermExpr (BVType w) ->
    PermImpl r (ls :> (LLVMPointerType w)) ->
    PermImpl r (ls :> (LLVMPointerType w))
  -- ^ Cast a proof that @x:eq(word(e1))@ to one that @x:eq(word(e2))@ with a
  -- dynamic check that @e1=e2@:
  --
  -- > Gin | Pl,x:eq(word(e2)) * Pin |- rets
  -- > -------------------------------------
  -- > Gin | Pl,x:eq(word(e1)) * Pin |- rets

  Impl_IntroLLVMPtr :: ExprVar (LLVMPointerType w) ->
                       PermImpl r (ls :> (LLVMPointerType w)) ->
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
                      PermImpl r (ls :> (LLVMPointerType w)) ->
                      PermImpl r (ls :> (LLVMPointerType w)
                                  :> (LLVMPointerType w))
  -- ^ Cast a @y:ptr(pps)@ on the top of the stack to @x:ptr(pps - off)@ using a
  -- proof of @x:eq(y+off)@ just below it on the stack:
  --
  -- > Gin | Pl, x:ptr(pps - off) * Pin, x:ptr(pps) |- rets
  -- > ----------------------------------------------------
  -- > Gin | Pl, x:eq(y+off),y:ptr(pps) * Pin |- rets

  Impl_IntroLLVMFree :: ExprVar (LLVMPointerType w) -> Int ->
                        PermImpl r (ls :> (LLVMPointerType w)) ->
                        PermImpl r (ls :> (LLVMPointerType w))
  -- ^ Copy a free pointer permission to the pointer permission on the top of
  -- the stack, using the 'Int' as the index into the pointer perms in @Pin@,
  -- i.e., the length of @pps1@:
  --
  -- > Gin | Pl, x:ptr(pps, free(e)) * Pin, x:ptr(pps1, free(e), pps2) |- rets
  -- > -----------------------------------------------------------------------
  -- > Gin | Pl, x:ptr(pps) * Pin, x:ptr(pps1, free(e), pps2) |- rets

  Impl_CastLLVMFree :: ExprVar (LLVMPointerType w) -> Int ->
                       PermExpr (BVType w) -> PermExpr (BVType w) ->
                       PermImpl r (ls :> (LLVMPointerType w)) ->
                       PermImpl r (ls :> (LLVMPointerType w))
  -- ^ Cast a proof of @x:ptr(free(e1))@ on the top of the stack to one of
  -- @x:ptr(free(e2))@:
  --
  -- > Gin | Pl, x:ptr(pps1, free(e2), pps2) * Pin |- rets
  -- > ---------------------------------------------------
  -- > Gin | Pl, x:ptr(pps1, free(e1), pps2) * Pin |- rets

  Impl_ElimLLVMFieldContents ::
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
    PermImpl r (ls :> (LLVMPointerType w)) ->
    PermImpl r (ls :> (LLVMPointerType w))
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
    PermImpl r (ls :> (LLVMPointerType w)) ->
    PermImpl r (ls :> (LLVMPointerType w))
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
    PermImpl r (ls :> (LLVMPointerType w)) ->
    PermImpl r (ls :> (LLVMPointerType w) :> (LLVMPointerType w))
  -- ^ Combine proofs of @x:ptr((off,S) |-> eq(y))@ and @y:p@ on the top of the
  -- permission stack into a proof of @x:ptr((off,S) |-> p)@:
  --
  -- > Gin | Pl, x:ptr((off,S) |-> p) * Pin |- rets
  -- > -----------------------------------------------------
  -- > Gin | Pl, x:ptr((off,S) |-> eq(y)), y:p * Pin |- rets

  Impl_DivideLLVMArray :: ExprVar (LLVMPointerType w) -> Int ->
                          PermExpr (BVType w) -> PermImpl r ps -> PermImpl r ps
  -- ^ Divide an array permission @x:ptr((off,*stride,<len,S) |-> p)@ into two
  -- arrays, one of length @e@ starting at @off@ and one of length @len-e@
  -- starting at offset @off+e*stride@:
  --
  -- > Gin | Pl * Pin, x:ptr(pps1, (off+e*stride,*stride,<e,S) |-> fps,
  -- >                       pps2, (off,*stride,<len-e, S) |-> fps) |- rets
  -- > -----------------------------------------------------------------------
  -- > Gin | Pl * Pin, x:ptr(pps1, (off,*stride,<len,S) |-> fps, pps2) |- rets

  Impl_IndexLLVMArray :: ExprVar (LLVMPointerType w) -> Int ->
                         PermImpl r ps -> PermImpl r ps
  -- ^ Perform an array indexing of the first cell of an array, by separating an
  -- array permission @x:ptr((off,*stride,<len,S) |-> pps)@ into one array cell,
  -- containing a copy of the pointer permissions @pps@ starting at offset
  -- @off@, along with the remaining array @x:ptr((off+1,*stride,<len,S) |->
  -- pps)@:
  --
  -- > Gin | Pl * Pin, x:ptr(pps1, (off+1,*stride,<e,S) |-> fps,
  -- >                       pps2, fps + off) |- rets
  -- > -----------------------------------------------------------------------
  -- > Gin | Pl * Pin, x:ptr(pps1, (off,*stride,<len,S) |-> fps, pps2) |- rets

  Impl_CastLLVMFieldOffsetM :: ExprVar (LLVMPointerType w) ->
                               PermExpr (BVType w) -> PermExpr (BVType w) ->
                               PermImpl r (ps :> LLVMPointerType w) ->
                               PermImpl r (ps :> LLVMPointerType w)
  -- ^ Assert that @off = off'@ at bitvector type, and cast the last field perm
  -- at the top of the stack from @(off,S) |-> p@ to @(off',S) |-> p@:
  --
  -- > Gin | Pl * Pin, x:ptr(pps, (off',S) |-> p) |- rets
  -- > -----------------------------------------------------------------------
  -- > Gin | Pl * Pin, x:ptr(pps, (off,S) |-> p) |- rets

$(mkNuMatching [t| forall r ps. NuMatching r => PermImpl r ps |])


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
class GenMonad (m :: k -> k -> Kind.* -> Kind.*) where
  -- | Generalized return
  greturn :: a -> m r r a
  -- | Generalized bind, that passes the output of @f@ to the input of @m@
  (>>>=) :: m r2 r3 a -> (a -> m r1 r2 b) -> m r1 r3 b

  {-
  -- | Insert a mapping function from the input to the output
  gmapRet :: (rin -> rout) -> m rin rout ()
  -- | Run two computations in parallel, combining their output at the end
  gparallel :: m r1 r2 a -> m r1 r3 a -> m r1 (r2, r3) a
  -- | FIXME: explain this one
  gopenBinding :: Binding a b -> m r (Binding a r) (Name a, b)
  -}

infixl 1 >>>=
infixl 1 >>>

(>>>) :: GenMonad m => m r2 r3 () -> m r1 r2 a -> m r1 r3 a
m1 >>> m2 = m1 >>>= \() -> m2

class GenMonadT (t :: (k -> k -> Kind.* -> Kind.*) ->
                k -> k -> Kind.* -> Kind.*) where
  glift :: GenMonad m => m rin rout a -> t m rin rout a

-- | The generalized continuation transformer, which can have different types
-- for the input vs output continuations
newtype GenContT (r :: k -> Kind.*) (m :: Kind.* -> Kind.*) pin pout a =
  GenContT { unGenContT :: (a -> m (r pin)) -> m (r pout) }

liftGenContT :: Monad m => m a -> GenContT r m p p a
liftGenContT m = GenContT $ \k -> m >>= k

instance Functor (GenContT r m p p) where
  fmap f m = m >>= return . f

instance Applicative (GenContT r m p p) where
  pure = return
  (<*>) = ap

instance Monad (GenContT r m p p) where
  return x = GenContT $ \k -> k x
  GenContT m >>= f = GenContT $ \k -> m $ \a -> unGenContT (f a) k

{-
instance MonadTrans (GenContT r r) where
  lift m = GenContT $ \k -> m >>= \a -> k a
-}

instance GenMonad (GenContT r m) where
  greturn x = GenContT $ \k -> k x
  (GenContT m) >>>= f = GenContT $ \k -> m $ \a -> unGenContT (f a) k

  {-
  gmapRet f = GenContT $ \k -> fmap f $ k ()
  gparallel (GenContT m1) (GenContT m2) =
    GenContT $ \k -> (\x y -> (x,y)) <$> m1 k <*> m2 k
  gopenBinding b =
    GenContT $ \k -> strongMbM $ nuWithElim1 (\nm b_body -> k (nm, b_body)) b
  -}

-- | Change the return type constructor @r@ by mapping the new input type to the
-- old and mapping the old output type to the new
withAltContM :: Functor m => (r2 pin -> r1 pin) -> (r1 pout -> r2 pout) ->
                GenContT r1 m pin pout a -> GenContT r2 m pin pout a
withAltContM f_in f_out (GenContT m) =
  GenContT $ \k -> fmap f_out (m (fmap f_in . k))

-- | This is like shift, but where the current continuation need not be in a
-- monad; this is useful for dealing with name-binding operations
--
-- FIXME: remove this...?
gcaptureCC :: ((a -> m (r p1)) -> m (r p2)) -> GenContT r m p1 p2 a
gcaptureCC f = GenContT f

class GenMonad m => GenMonadShift r m | m -> r where
  gshift :: ((a -> m p1 p1 (r p2)) -> m p3 p4 (r p3)) -> m p2 p4 a

instance Monad m => GenMonadShift r (GenContT r m) where
  gshift f = GenContT $ \k -> unGenContT (f (\a -> liftGenContT (k a))) return

-- | FIXME: The shift for GenStateT does not quite fit...
gshiftSt :: GenMonadShift r m =>
            ((a -> s p2 -> GenStateT s m p1 p1 (r p2)) ->
             GenStateT s m p3 p4 (r p3)) ->
            GenStateT s m p2 p4 a
gshiftSt f = GenStateT $ \s4 ->
  gshift $ \k ->
  unGenStateT (f $ \a s2 -> liftGenStateT id (k (a, s2))) s4 >>>= \(r, _) ->
  greturn r

-- | The generalized state monad
newtype GenStateT s (m :: k -> k -> Kind.* -> Kind.*) p1 p2 a =
  GenStateT { unGenStateT :: s p2 -> m p1 p2 (a, s p1) }

runGenStateT :: GenStateT s m p1 p2 a -> s p2 -> m p1 p2 (a, s p1)
runGenStateT m s = unGenStateT m s

-- | Helper to tell GHC how to type-check
gget :: GenMonad m => GenStateT s m p p (s p)
gget = GenStateT $ \s -> greturn (s, s)

instance Monad (m r r) => Functor (GenStateT s m r r) where
  fmap f m = m >>= return . f

instance Monad (m r r) => Applicative (GenStateT s m r r) where
  pure = return
  (<*>) = ap

instance Monad (m r r) => Monad (GenStateT s m r r) where
  return x = GenStateT $ \s -> return (x, s)
  (GenStateT m) >>= f =
    GenStateT $ \s -> m s >>= \(a, s') -> unGenStateT (f a) s'

instance Monad (m p p) => MonadState (s p) (GenStateT s m p p) where
  get = GenStateT $ \s -> return (s, s)
  put s = GenStateT $ \_ -> return ((), s)

-- NOTE: lift only works for p1 = p2
{-
instance GenMonadT (GenStateT s) where
  glift m = GenStateT $ \s -> m >>>= \a -> greturn (a, s)
-}

instance GenMonad m => GenMonad (GenStateT s m) where
  greturn x = GenStateT $ \s -> greturn (x, s)
  (GenStateT m) >>>= f =
    GenStateT $ \s -> m s >>>= \(a, s') -> unGenStateT (f a) s'
  {-
  gmapRet f = glift $ gmapRet f
  gparallel m1 m2 =
    GenStateT $ StateT $ \s ->
    gparallel (runGenStateT m1 s) (runGenStateT m2 s)
  gopenBinding b = glift $ gopenBinding b
  -}


-- | FIXME: documentation
liftGenStateT :: GenMonad m => (s p2 -> s p1) -> m p1 p2 a ->
                 GenStateT s m p1 p2 a
liftGenStateT f m = GenStateT $ \s -> m >>>= \a -> greturn (a, f s)

-- | Run a generalized state computation with a different state type @s2@ inside
-- one with state type @s1@, using a lens-like pair of a getter function to
-- extract out the starting inner @s2@ state from the outer @s1@ state and an
-- update function to update the resulting outer @s1@ state with the final inner
-- @s2@ state.
withAltStateM :: GenMonad m => (s1 p2 -> s2 p2) -> (s1 p2 -> s2 p1 -> s1 p1) ->
                 GenStateT s2 m p1 p2 a -> GenStateT s1 m p1 p2 a
withAltStateM s_get s_update (GenStateT m) =
  GenStateT $ \s ->
  m (s_get s) >>>= \(a, s') ->
  greturn (a, s_update s s')

-- | FIXME: remove this...?
gcaptureCCMapState :: (s p2 -> s p1) -> ((a -> m (r p1)) -> m (r p2)) ->
                      GenStateT s (GenContT r m) p1 p2 a
gcaptureCCMapState f_st f_k = liftGenStateT f_st $ gcaptureCC f_k

-- | FIXME: documentation
gmapRetAndState :: Monad m => (s p2 -> s p1) -> (r p1 -> r p2) ->
                   GenStateT s (GenContT r m) p1 p2 ()
gmapRetAndState f_st f_ret =
  gget >>>= \s1 ->
  gshiftSt $ \k ->
  k () (f_st s1) >>>= \r ->
  greturn (f_ret r)
  -- gcaptureCCMapState f_st (\k -> f_ret <$> k ())

-- | Name-binding in the generzlied continuation monad (FIXME: explain)
class GenMonad m => GenMonadBind r p1 p2 m | m -> r where
  gmbM :: (Mb ctx (r p2) -> r p2) ->
          Mb ctx (m p1 p2 a) -> m p1 p2 a

instance (MonadBind m, NuMatching (r p2)) =>
         GenMonadBind r p1 p2 (GenContT r m) where
  gmbM f_ret mb_m =
    GenContT $ \k ->
    f_ret <$> mbM (fmap (\m -> unGenContT m k) mb_m)

instance (GenMonadBind r p1 p2 m) =>
         GenMonadBind r p1 p2 (GenStateT s m) where
  gmbM f_ret mb_m =
    GenStateT $ \s ->
    gmbM f_ret $ fmap (\m -> unGenStateT m s) mb_m

-- | Running generalized computations in "parallel"
class GenMonad m => GenMonadPar r m | m -> r where
  gparallel :: (r p2 -> r p2 -> r p2) -> m p1 p2 a -> m p1 p2 a -> m p1 p2 a

instance Monad m => GenMonadPar r (GenContT r m) where
  gparallel f (GenContT m1) (GenContT m2) =
    GenContT $ \k -> f <$> m1 k <*> m2 k

instance GenMonadPar r m => GenMonadPar r (GenStateT s m) where
  gparallel f m1 m2 =
    GenStateT $ \s ->
    gparallel f (runGenStateT m1 s) (runGenStateT m2 s)

{-
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
-}


----------------------------------------------------------------------
-- * Permission Implication Monad
----------------------------------------------------------------------

{-
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
-}

data ImplState vars ps =
  ImplState { _implStatePerms :: PermSet ps,
              _implStateVars :: CruCtx vars,
              _implStatePSubst :: PartialSubst vars }
makeLenses ''ImplState

mkImplState :: CruCtx vars -> PermSet ps -> ImplState vars ps
mkImplState vars perms =
  ImplState { _implStateVars = vars,
              _implStatePerms = perms,
              _implStatePSubst = emptyPSubst vars }

extImplState :: KnownRepr TypeRepr tp => ImplState vars ps ->
                ImplState (vars :> PermExpr tp) ps
extImplState s =
  s { _implStateVars = extCruCtx (_implStateVars s),
      _implStatePSubst = extPSubst (_implStatePSubst s) }

unextImplState :: ImplState (vars :> PermExpr a) ps -> ImplState vars ps
unextImplState s =
  s { _implStateVars = unextCruCtx (_implStateVars s),
      _implStatePSubst = unextPSubst (_implStatePSubst s) }

{-
instance PermState (ImplState vars) where
  permStatePerms = implStatePerms
-}

-- | The implication monad is the permission monad that uses 'ImplState'
type ImplM vars r ps_out ps_in =
  GenStateT (ImplState vars) (GenContT (PermImpl r) Identity) ps_out ps_in


-- | Run an implication computation with one more existential variable,
-- returning the optional expression it was bound to in the current partial
-- substitution when it is done
withExtVarsM :: KnownRepr TypeRepr tp =>
                ImplM (vars :> PermExpr tp) r ps1 ps2 a ->
                ImplM vars r ps1 ps2 (a, Maybe (PermExpr tp))
withExtVarsM m =
  withAltStateM extImplState (const unextImplState) $
  (m >>>= \a ->
    getPSubst >>>= \psubst ->
    greturn (a, psubstLookup psubst Member_Base))


{- FIXME: figure out our run method

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
-}

----------------------------------------------------------------------
-- * Permissions Operations in a Permission Monad
----------------------------------------------------------------------

-- | Look up the current partial substitution
getPSubst :: ImplM vars r ps ps (PartialSubst vars)
getPSubst = view implStatePSubst <$> gget

-- | Apply the current partial substitution to an expression, raising an error
-- with the given string if the partial substitution is not complete enough
partialSubstForceM :: Substable PartialSubst a Maybe => Mb vars a -> String ->
                      ImplM vars r ps ps a
partialSubstForceM mb_e msg =
  getPSubst >>>= \psubst ->
  greturn (partialSubstForce psubst mb_e msg)

-- | Modify the current partial substitution
modifyPSubst :: (PartialSubst vars -> PartialSubst vars) ->
                ImplM vars r ps ps ()
modifyPSubst f = modify (over implStatePSubst f)

-- | Set the value for an existential variable in the current substitution,
-- raising an error if it is already set
setVarM :: Member vars (PermExpr a) -> PermExpr a -> ImplM vars r ps ps ()
setVarM x e = modifyPSubst (psubstSet x e)

-- | Get the current 'PermSet'
getPerms :: ImplM vars r ps ps (PermSet ps)
getPerms = view implStatePerms <$> gget

-- | Look up the current permission for a given variable
getPerm :: ExprVar a -> ImplM vars r ps ps (ValuePerm a)
getPerm x = view (implStatePerms . varPerm x) <$> gget

-- | Get the pointer permissions for a variable @x@, assuming @x@ has LLVM
-- pointer permissions
getLLVMPtrPerms :: ExprVar (LLVMPointerType w) ->
                   ImplM vars r ps ps [LLVMPtrPerm w]
getLLVMPtrPerms x =
  view (implStatePerms . varPerm x . llvmPtrPerms) <$> gget

-- | Get the top permission in the stack
getTopDistPerm :: ExprVar a -> ImplM vars r (ps :> a) (ps :> a) (ValuePerm a)
getTopDistPerm x = view (implStatePerms . topDistPerm x) <$> gget

-- | Get the index of the last 'LLVMPtrPerm' in the @x:ptr(pps)@ permission on
-- the top of the stack
getTopPermLastLLVMIx :: ExprVar (LLVMPointerType w) ->
                        ImplM vars r (ps :> LLVMPointerType w)
                        (ps :> LLVMPointerType w) Int
getTopPermLastLLVMIx x =
  getTopDistPerm x >>>= \p ->
  let ret = length (p ^. llvmPtrPerms) - 1 in
  if ret >= 0 then greturn ret else
    error "getTopPermLastLLVMIx"

-- | Set the current 'PermSet'
setPerms :: PermSet ps -> ImplM vars r ps ps ()
setPerms perms = modify $ set (implStatePerms) perms

-- | Set the current permission for a given variable
setPerm :: ExprVar a -> ValuePerm a -> ImplM vars r ps ps ()
setPerm x p = modify $ set (implStatePerms . varPerm x) p

-- | Map the final return value and the current permissions
gmapRetAndPerms :: (PermSet ps2 -> PermSet ps1) ->
                   (PermImpl r ps1 -> PermImpl r ps2) ->
                   ImplM vars r ps1 ps2 ()
gmapRetAndPerms f_perms f_impl =
  gmapRetAndState (over implStatePerms f_perms) f_impl

-- | Terminate the current proof branch with a failure
implFailM :: ImplM vars r ps_any ps ()
implFailM =
  gmapRetAndState (const $ error "implFailM: unreachable") (const Impl_Fail)

{- FIXME: this should be part of the run method for ImplM...?
-- | Finish the current proof branch successfully with an 'Impl_Done'
implDoneM :: ImplM vars r ps ps ()
implDoneM = gmapRetAndState id Impl_Done
-}

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
implCatchM :: ImplM vars r ps1 ps2 () -> ImplM vars r ps1 ps2 () ->
              ImplM vars r ps1 ps2 ()
implCatchM m1 m2 =
  -- FIXME: figure out the "right" way to write this with shift and reset!
  GenStateT $ \s -> GenContT $ \k ->
  Impl_Catch <$> (unGenContT (unGenStateT m1 s) k)
  <*> (unGenContT (unGenStateT m2 s) k)
  {-
  gmapRet (\(impl1, impl2) -> Impl_Catch impl1 impl2) >>>
  gparallel m1 m2
  -}

-- | Apply the left or-introduction rule to the top of the permission stack,
-- changing it from @x:p1@ to @x:(p1 \/ p2)@
introOrLM :: ExprVar a -> ValuePerm a -> ImplM vars r (ps :> a) (ps :> a) ()
introOrLM x p2 = gmapRetAndPerms (introOrL x p2) (Impl_IntroOrL x p2)

-- | Apply the right or-introduction rule to the top of the permission stack,
-- changing it from @x:p2@ to @x:(p1 \/ p2)@
introOrRM :: ExprVar a -> ValuePerm a -> ImplM vars r (ps :> a) (ps :> a) ()
introOrRM x p1 = gmapRetAndPerms (introOrR x p1) (Impl_IntroOrR x p1)

-- | Apply existential introduction to the top of the permission stack, changing
-- it from @[e/x]p@ to @exists (x:tp).p@
--
-- FIXME: is there some way we could "type-check" this, to ensure that the
-- permission on the top of the stack really equals @[e/x]p@?
introExistsM :: KnownRepr TypeRepr tp => ExprVar a -> PermExpr tp ->
                Binding (PermExpr tp) (ValuePerm a) ->
                ImplM vars r (ps :> a) (ps :> a) ()
introExistsM x e p_body =
  gmapRetAndPerms (introExists x e p_body) (Impl_IntroExists x e p_body)

-- | Eliminate a disjunctive permission @x:(p1 \/ p2)@, building proof trees
-- that proceed with both @x:p1@ and @x:p2@
elimOrM :: ExprVar a -> ImplM vars r ps ps ()
elimOrM x =
  gparallel (\impl1 impl2 -> Impl_ElimOr x impl1 impl2)
  (modify (over (implStatePerms . varPerm x) orPermLeft))
  (modify (over (implStatePerms . varPerm x) orPermRight))

-- | Eliminate an existential permission @x:(exists (y:tp).p)@ in the current
-- permission set
elimExistsM :: (KnownRepr TypeRepr tp, NuMatching r) => ExprVar a -> f tp ->
               ImplM vars r ps ps ()
elimExistsM x (_ :: f tp) =
  getPerms >>>= \perms ->
  gmbM (Impl_ElimExists x) $
  flip nuWithElim1 (elimExists x (knownRepr :: TypeRepr tp) perms) $ \_nm perms' ->
  setPerms perms'

-- | Eliminate disjunctives and existentials for a specific variable
elimOrsExistsM :: NuMatching r => ExprVar a -> ImplM vars r ps ps ()
elimOrsExistsM x =
  getPerm x >>>= \p ->
  case p of
    ValPerm_Or _ _ -> elimOrM x >>> elimOrsExistsM x
    ValPerm_Exists (_ :: Binding (PermExpr a) _) ->
      elimExistsM x (knownRepr :: TypeRepr a) >>> elimOrsExistsM x
    _ -> return ()

-- | Introduce a proof of @x:true@ onto the top of the stack
introTrueM :: ExprVar a -> ImplM vars r (ps :> a) ps ()
introTrueM x = gmapRetAndPerms (introTrue x) (Impl_IntroTrue x)

-- | Introduce a proof of @x:eq(x)@ onto the top of the stack
introEqReflM :: ExprVar a -> ImplM vars r (ps :> a) ps ()
introEqReflM x = gmapRetAndPerms (introEqRefl x) (Impl_IntroEqRefl x)

-- | Copy an @x:eq(e)@ permission to the top of the stack
introEqCopyM :: ExprVar a -> PermExpr a -> ImplM vars r (ps :> a) ps ()
introEqCopyM x e =
  getPerm x >>>= \p ->
  case p of
    ValPerm_Eq e'
      | e' == e -> gmapRetAndPerms (introEqCopy x e) (Impl_IntroEqCopy x e)
    ValPerm_Eq _ -> error "introEqCopyM: incorrect expression!"
    _ -> error "introEqCopyM: not an eq(e) proof!"

-- | Assert that @x = e@ at bitvector type, and push an @x:eq(e)@ permission to
-- the top of the stack
introAssertBVEq :: ExprVar (BVType w) -> PermExpr (BVType w) ->
                   ImplM vars r (ps :> BVType w) ps ()
introAssertBVEq x e =
  gmapRetAndPerms (pushPerm x (ValPerm_Eq e)) (Impl_AssertBVEq x e)

-- | Cast a proof of @x:eq(LLVMWord(e1))@ to @x:eq(LLVMWord(e2))@ on the top of
-- the stack
castLLVMWordEqM ::
  ExprVar (LLVMPointerType w) -> PermExpr (BVType w) -> PermExpr (BVType w) ->
  ImplM vars r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()
castLLVMWordEqM x e1 e2 =
  gmapRetAndPerms (castLLVMWordEq x e1 e2) (Impl_CastLLVMWord x e1 e2)


-- | Prove an empty @x:ptr()@ permission from any @x:ptr(pps)@ permissionx
introLLVMPtrM :: ExprVar (LLVMPointerType w) ->
                 ImplM vars r (ps :> LLVMPointerType w) ps ()
introLLVMPtrM x = gmapRetAndPerms (introLLVMPtr x) (Impl_IntroLLVMPtr x)

-- | Cast a @y:ptr(pps)@ on the top of the stack to @x:ptr(pps - off)@ using a
-- proof of @x:eq(y+off)@ just below it on the stack
castLLVMPtrM :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                ExprVar (LLVMPointerType w) ->
                ImplM vars r (ps :> LLVMPointerType w)
                (ps :> LLVMPointerType w :> LLVMPointerType w) ()
castLLVMPtrM y off x =
  gmapRetAndPerms (castLLVMPtr y off x) (Impl_CastLLVMPtr y off x)


-- | Copy an LLVM free permission @free(e)@ from the current
-- @x:ptr(pps1,free(e),pps2)@ permission into the @x:ptr(pps)@ permission on the
-- top of the stack, where the 'Int' index gives the size of @pps1@.
introLLVMFreeM :: ExprVar (LLVMPointerType w) -> Int ->
                  ImplM vars r (ps :> LLVMPointerType w)
                  (ps :> LLVMPointerType w) ()
introLLVMFreeM x i =
  gmapRetAndPerms (introLLVMFree x i) (Impl_IntroLLVMFree x i)

-- | Cast a proof of @x:ptr(pps1, free(e1), pps2)@ on the top of the stack to
-- one of @x:ptr(pps1, free(e2), pps2)@
castLLVMFreeM :: ExprVar (LLVMPointerType w) -> Int ->
                 PermExpr (BVType w) -> PermExpr (BVType w) ->
                 ImplM vars r (ps :> LLVMPointerType w)
                 (ps :> LLVMPointerType w) ()
castLLVMFreeM x i e1 e2 =
  gmapRetAndPerms (castLLVMFree x i e1 e2) (Impl_CastLLVMFree x i e1 e2)

-- | Move a field permission of the form @(off,All) |-> eq(e)@ to the
-- @x:ptr(pps)@ permission on the top of of the stack
introLLVMFieldAllM :: ExprVar (LLVMPointerType w) -> Int ->
                      ImplM vars r (ps :> LLVMPointerType w)
                      (ps :> LLVMPointerType w) ()
introLLVMFieldAllM x i =
  gmapRetAndPerms (introLLVMFieldAll x i) (Impl_IntroLLVMFieldAll x i)

-- | Split a field permission @(off,spl) |-> eq(e)@ into two, leaving the left
-- half in the current permission stack and moving the right half to the top of
-- of the stack
introLLVMFieldSplitM :: ExprVar (LLVMPointerType w) -> Int -> SplittingExpr ->
                        ImplM vars r (ps :> LLVMPointerType w)
                        (ps :> LLVMPointerType w) ()
introLLVMFieldSplitM x i spl =
  gmapRetAndPerms (introLLVMFieldSplit x i spl)
  (Impl_IntroLLVMFieldSplit x i spl)

-- | Combine proofs of @x:ptr(pps,(off,spl) |-> eq(y))@ and @y:p@ on the top of
-- the permission stack into a proof of @x:ptr(pps,(off,spl |-> p))@
introLLVMFieldContentsM ::
  ExprVar (LLVMPointerType w) ->
  ExprVar (LLVMPointerType w) ->
  ImplM vars r (ps :> LLVMPointerType w)
  (ps :> LLVMPointerType w :> LLVMPointerType w) ()
introLLVMFieldContentsM x y =
  gmapRetAndPerms (introLLVMFieldContents x y) (Impl_IntroLLVMFieldContents x y)

-- | Eliminate a permission @x:ptr(pps1,(off,S) |-> p,pps2)@ into permissions
-- @x:ptr(pps1,(off,S) |-> eq(y),pps2)@ and @y:p@ for a fresh variable @y@,
-- returning the fresh variable @y@
elimLLVMFieldContentsM :: NuMatching r => ExprVar (LLVMPointerType w) -> Int ->
                          ImplM vars r ps ps (ExprVar (LLVMPointerType w))
elimLLVMFieldContentsM x i =
  getPerms >>>= \perms ->
  case elimLLVMFieldContents x i perms of
    Left y -> greturn y
    Right mb_perms' ->
      gmbM (Impl_ElimLLVMFieldContents x i) $
      flip nuWithElim1 mb_perms' $ \y perms' ->
      setPerms perms' >>> greturn y

-- | Divide an array permission @x:ptr((off,*stride,<len,S) |-> p)@ into two
-- arrays, one of length @e@ starting at @off@ and one of length @len-e@
-- starting at offset @off+e*stride@. The latter permission (at offset
-- @off+e*stride@) stays at the same index, while the former (at the original
-- offset) is moved to the end of the field permissions for @x@.
divideLLVMArrayM :: ExprVar (LLVMPointerType w) -> Int -> PermExpr (BVType w) ->
                    ImplM vars r ps ps ()
divideLLVMArrayM x i arr_ix =
  gmapRetAndPerms (divideLLVMArray x i arr_ix) (Impl_DivideLLVMArray x i arr_ix)

-- | Perform an array indexing of the first cell of an array, by separating an
-- array permission @x:ptr((off,*stride,<len,S) |-> pps)@ into one array cell,
-- containing a copy of the pointer permissions @pps@ starting at offset @off@,
-- along with the remaining array @x:ptr((off+1,*stride,<len,S) |->
-- pps)@. Return the new permission set along with the indices of the new @pps@
-- pointer permissions.
indexLLVMArrayM :: ExprVar (LLVMPointerType w) -> Int ->
                   ImplM vars r ps ps [(Int, LLVMFieldPerm w)]
indexLLVMArrayM x i =
  getPerms >>>= \perms ->
  gmapRetAndPerms (const $ fst $
                   indexLLVMArray x i perms) (Impl_IndexLLVMArray x i) >>>
  greturn (snd $ indexLLVMArray x i perms)

-- | Assert that @off = off'@ at bitvector type, and cast the last pointer
-- permission at the top of the stack from @(off,S) |-> p@ to @(off',S) |-> p@
castLLVMFieldOffsetM :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                        PermExpr (BVType w) ->
                        ImplM vars r (ps :> LLVMPointerType w)
                        (ps :> LLVMPointerType w) ()
castLLVMFieldOffsetM x off off' =
  gmapRetAndPerms (castLLVMFieldOffset x off off')
  (Impl_CastLLVMFieldOffsetM x off off')


{- FIXME: remove these if we no longer need them!
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
-}


----------------------------------------------------------------------
-- * Proving Equality Permissions
----------------------------------------------------------------------

-- | Build a proof on the top of the stack that @x:eq(e)@
proveVarEq :: NuMatching r => ExprVar a -> Mb vars (PermExpr a) ->
              ImplM vars r (ps :> a) ps ()
proveVarEq x mb_e =
  getPerm x >>>= \perm ->
  getPSubst >>>= \psubst ->
  proveVarEqH x perm psubst mb_e

-- | Main helper function for 'proveVarEq'
proveVarEqH :: NuMatching r => ExprVar a -> ValuePerm a ->
               PartialSubst vars -> Mb vars (PermExpr a) ->
               ImplM vars r (ps :> a) ps ()

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
  = introEqCopyM x (PExpr_LLVMWord e') >>> castLLVMWordEqM x e' e

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

-- | Attempt to prove @x:ptr(pps', off |-> (S,p))@ on the top of the stack from
-- the current permissions @x:ptr(pps)@ for @x@, assuming that @x:ptr(pps')@ is
-- already on the top of the stack.
--
-- FIXME: update this documentation
proveVarField :: NuMatching r => ExprVar (LLVMPointerType w) ->
                 LLVMFieldMatch w ->
                 PermExpr (BVType w) -> Mb vars (LLVMFieldPerm w) ->
                 ImplM vars r (ps :> LLVMPointerType w)
                 (ps :> LLVMPointerType w) ()

-- Case for x:ptr((off',All) |-> p') |- x:ptr((off,All) |-> p)
proveVarField x (FieldMatchField
                 is_def i fp) off [nuP| LLVMFieldPerm _ SplExpr_All mb_p |]
  | SplExpr_All <- llvmFieldSplitting fp =
    -- NOTE: If we need "All" and don't have it, we fail, because we have set
    -- things up to ensure that we cannot "piece together" an All from multiple
    -- different pointer permissions: specifically, we make sure that the
    -- pointer permissions in the permission have overlapping splittings. That
    -- is why this case requires the splitting in fp to be "All".
    elimLLVMFieldContentsM x i >>>= \y ->
    introLLVMFieldAllM x i >>>
    proveVarImpl y mb_p >>>
    introLLVMFieldContentsM x y >>>
    if is_def then greturn () else
      castLLVMFieldOffsetM x (llvmFieldOffset fp) off

-- Case for x:ptr((off',spl') |-> p') |- x:ptr((off,z) |-> p), setting z=R(spl')
proveVarField x (FieldMatchField
                 is_def i fp) off [nuP| LLVMFieldPerm _ (SplExpr_Var z) mb_p |]
  | Left memb <- mbNameBoundP z =
    elimLLVMFieldContentsM x i >>>= \y ->
    introLLVMFieldSplitM x i (llvmFieldSplitting fp) >>>
    setVarM memb (PExpr_Spl $ SplExpr_R $ llvmFieldSplitting fp) >>>
    proveVarImpl y mb_p >>>
    introLLVMFieldContentsM x y >>>
    if is_def then greturn () else
      castLLVMFieldOffsetM x (llvmFieldOffset fp) off

proveVarField x (FieldMatchArray _ i ap arr_ix fld_i) off mb_fld =
  (if bvEq off (llvmArrayOffset ap) then greturn () else
     divideLLVMArrayM x i arr_ix) >>>
  indexLLVMArrayM x i >>>= \is_flds ->
  proveVarField x (FieldMatchField True (fst (is_flds !! fld_i))
                   (snd (is_flds !! fld_i))) off mb_fld


----------------------------------------------------------------------
-- * Proving LLVM Pointer Permissions
----------------------------------------------------------------------

-- FIXME: documentation; note that we expect x:ptr(pps)
proveVarPtrPerms :: (1 <= w, KnownNat w, NuMatching r) =>
                    ExprVar (LLVMPointerType w) ->
                    [Mb vars (LLVMPtrPerm w)] ->
                    ImplM vars r (ps :> LLVMPointerType w)
                    (ps :> LLVMPointerType w) ()

-- If the required permissions are empty, we are done!
proveVarPtrPerms x [] = greturn ()

-- Prove x:ptr(free(e')) |- x:ptr(free(e)) (where e' is not necessarily distinct
-- from e) by first proving x:ptr(free(e')) and then casting e' to e (if needed)
proveVarPtrPerms x ([nuP| LLVMPP_Free mb_e |] : mb_pps') =
  partialSubstForceM mb_e
  "proveVarPtrPerms: incomplete psubst: LLVM free size" >>>= \e ->
  getLLVMPtrPerms x >>>= \pps ->
  case findFreePerm pps of
    Just (i, e') ->
      introLLVMFreeM x i >>>
      getTopPermLastLLVMIx x >>>= \i_x ->
      castLLVMFreeM x i_x e' e >>>
      proveVarPtrPerms x mb_pps'
    _ -> implFailM

proveVarPtrPerms x ([nuP| LLVMPP_Field mb_fp@(LLVMFieldPerm mb_off _ _) |]
                    : mb_pps') =
  partialSubstForceM mb_off
  "proveVarPtrPerms: incomplete psubst: LLVM field offset" >>>= \off ->
  getLLVMPtrPerms x >>>= \pps ->
  let matches = findFieldMatches off pps in
  (case find fieldMatchDefinite matches of
      Just match -> proveVarField x match off mb_fp
      Nothing ->
        foldr (\match rest ->
                implCatchM (proveVarField x match off mb_fp) rest)
        implFailM
        matches) >>>
  proveVarPtrPerms x mb_pps'

proveVarPtrPerms _ _ =
  error "FIXME HERE: proveVarPtrPerms: arrays not yet supported"


----------------------------------------------------------------------
-- * Proving Permission Implications
----------------------------------------------------------------------

-- | Prove @x:p@, where @p@ may have existentially-quantified variables in it
proveVarImpl :: NuMatching r => ExprVar a -> Mb vars (ValuePerm a) ->
                ImplM vars r (ps :> a) ps ()

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
  introExistsM x e

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
      castLLVMPtrM y (bvInt 0) x

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
  ReqPerm :: ExprVar a -> Mb vars (ValuePerm a) -> ReqPerm vars a

proveVarsImpl :: NuMatching r => MapRList (ReqPerm vars) ls ->
                 ImplM vars r ls RNil ()
proveVarsImpl MNil = return ()
proveVarsImpl (reqs :>: ReqPerm x p) = proveVarsImpl reqs >>> proveVarImpl x p
