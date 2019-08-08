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

-- FIXME: add error messages to Impl_Fail, for debugging by the user

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
--
-- FIXME: it would be nice to have PermImpl r ps_out ps_in, where ps_out is
-- guaranteed to be the stack shape at any Impl_Done, but this would make our
-- generalized monad below more complicated...
data PermImpl r ps where
  Impl_Done :: r ps -> PermImpl r ps
  -- ^ The proof is finished; i.e., implements the rule
  --
  -- > -------------------------------
  -- > Gin | Pl * Pin |- . | Pin

  Impl_Fail :: PermImpl r ps
  -- ^ The empty tree, with no disjunctive possibilities; i.e., implements the
  -- rule
  --
  -- > ------------------------------
  -- > Gin | Pl * Pin |- anything

  Impl_Catch :: PermImpl r ps -> PermImpl r ps -> PermImpl r ps
  -- ^ Copy the same permissions into two different elimination trees, where an
  -- 'Impl_Fail' in the first tree "calls" the second tree, just like a
  -- try-catch block for exceptions. This implements the rule:
  --
  -- > pf1 = Gin | Pl * Pin |- rets1    pf2 = Gin | Pl * Pin |- rets2
  -- > --------------------------------------------------------------
  -- > Gin | Pl * Pin |- rets1, rets2

{-
  Impl_Push :: PermLoc a -> ValuePerm a -> PermImpl r (ps :> PermExpr a) ->
               PermImpl r ps
  -- ^ "Push" a permission from the input permission set to the stack of
  -- distinguished permissions:
  --
  -- > Gin | Pl,x:p * Pin |- rets
  -- > ---------------------------
  -- > Gin | Pl * Pin, x:p |- rets
-}

  Impl_ElimOr :: ExprVar a -> PermImpl r ps -> PermImpl r ps ->
                 PermImpl r ps
  -- ^ Eliminate a 'ValPerm_Or' on the given variable, replacing it with the
  -- left- and right-hand sides in the two sub-eliminations
  --
  -- > pf1 = Gin | Pin, x:p1 |- GsPs1     pf2 = Gin | Pin, x:p2 |- GsPs2
  -- > -----------------------------------------------------------------
  -- > Gin | Pin, x:(p1 \/ p2) |- GsPs1, GsPs2

  Impl_IntroOrL :: ExprVar a -> ValuePerm a ->
                   PermImpl r (ps :> a) ->
                   PermImpl r (ps :> a)
  -- ^ @Impl_IntroOrL x p2 pf@ applies left disjunction introduction to the top
  -- permission on the stack:
  --
  -- > pf = Gamma | Pl, x:(p1 \/ p2) * Pin |- Pout
  -- > -------------------------------------------
  -- > Gamma | Pl, x:p1 * Pin |- rets

  Impl_IntroOrR :: ExprVar a -> ValuePerm a ->
                   PermImpl r (ps :> a) ->
                   PermImpl r (ps :> a)
  -- ^ @Impl_IntroOrR x p1 pf@ applies right disjunction introduction to the top
  -- permission on the stack:
  --
  -- > pf = Gamma | Pl, x:(p1 \/ p2) * Pin |- Pout
  -- > -------------------------------------------
  -- > Gamma | Pl, x:p2 * Pin |- rets

  Impl_ElimExists :: KnownRepr TypeRepr tp => ExprVar a ->
                     Binding tp (PermImpl r ps) ->
                     PermImpl r ps
  -- ^ Eliminate an existential, i.e., a 'ValPerm_Exists', on the given variable
  --
  -- pf = Gin, z:tp | Pin, x:p |- rets
  -- ------------------------------------------------------
  -- Gin | x:(exists z:tp. p)  |- rets

  Impl_IntroExists :: KnownRepr TypeRepr tp => ExprVar a -> PermExpr tp ->
                      Binding tp (ValuePerm a) ->
                      PermImpl r (ps :> a) ->
                      PermImpl r (ps :> a)
  -- ^ @Intro_Exists x tp e p pf@ applies existential introduction to the top
  -- permission on the stack:
  --
  -- > pf = Gamma | Pl, x:(exists z:tp.p) * Pin |- Pout
  -- > ------------------------------------------------
  -- > Gamma | Pl, x:[e'/z]p * Pin |- Pout

  Impl_IntroTrue :: ExprVar a -> PermImpl r (ps :> a) -> PermImpl r ps
  -- ^ Introduce a true permission onto the stack of distinguished permissions:
  --
  -- > Gin | Pl,x:true * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_RecombineTrue :: ExprVar a -> PermImpl r ps -> PermImpl r (ps :> a)
  -- ^ "Recombine" a true proof on the top of the stack by dropping it
  --
  -- > Gin | Pl * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl,x:true * Pin |- rets

  Impl_IntroCast :: ExprVar a -> ExprVar a ->
                    PermImpl r (ps :> a) ->
                    PermImpl r (ps :> a :> a)
  -- ^ Cast a proof of @y:p@ to one of @x:p@ using @x:eq(y)@:
  --
  -- > Gin | Pl,x:p * Pin |- rets
  -- > ----------------------------------
  -- > Gin | Pl,x:eq(y),y:p * Pin |- rets

  Impl_IntroEqRefl :: ExprVar a -> PermImpl r (ps :> a) ->
                      PermImpl r ps
  -- ^ Introduce a proof that @x:eq(x)@:
  --
  -- > Gin | Pl,x:eq(x) * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_IntroEqCopy :: ExprVar a -> PermExpr a ->
                      PermImpl r (ps :> a) -> PermImpl r ps
  -- ^ Copy a proof that @x:eq(e)@ from the normal permissions to the stack:
  --
  -- > Gin | Pl,x:eq(e) * Pin,x:eq(e) |- rets
  -- > --------------------------------------
  -- > Gin | Pl * Pin,x:eq(e) |- rets

  Impl_AssertBVEq :: ExprVar (BVType w) -> PermExpr (BVType w) ->
                     PermImpl r (ps :> (BVType w)) ->
                     PermImpl r ps
  -- ^ Introduce a proof that @x:eq(e)@ at bitvector type (which becomes a
  -- dynamic check that @x=e@):
  --
  -- > Gin | Pl,x:eq(e) * Pin |- rets
  -- > -----------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_CastLLVMWord ::
    ExprVar (LLVMPointerType w) -> PermExpr (BVType w) -> PermExpr (BVType w) ->
    PermImpl r (ps :> (LLVMPointerType w)) ->
    PermImpl r (ps :> (LLVMPointerType w))
  -- ^ Cast a proof that @x:eq(word(e1))@ to one that @x:eq(word(e2))@ with a
  -- dynamic check that @e1=e2@:
  --
  -- > Gin | Pl,x:eq(word(e2)) * Pin |- rets
  -- > -------------------------------------
  -- > Gin | Pl,x:eq(word(e1)) * Pin |- rets

  Impl_IntroLLVMPtr :: ExprVar (LLVMPointerType w) ->
                       PermImpl r (ps :> (LLVMPointerType w)) ->
                       PermImpl r ps
  -- ^ Prove an empty pointer permission @x:ptr()@ from any pointer permission
  -- @x:ptr(pps)@ on the left:
  --
  -- > Gin | Pl, x:ptr() * Pin, x:ptr(pps) |- rets
  -- > -------------------------------------------
  -- > Gin | Pl * Pin, x:ptr(pps) |- rets

  Impl_CastLLVMPtr :: ExprVar (LLVMPointerType w) ->
                      PermExpr (BVType w) ->
                      ExprVar (LLVMPointerType w) ->
                      PermImpl r (ps :> (LLVMPointerType w)) ->
                      PermImpl r (ps :> (LLVMPointerType w)
                                  :> (LLVMPointerType w))
  -- ^ Cast a @y:ptr(pps)@ on the top of the stack to @x:ptr(pps - off)@ using a
  -- proof of @x:eq(y+off)@ just below it on the stack:
  --
  -- > Gin | Pl, x:ptr(pps - off) * Pin, x:ptr(pps) |- rets
  -- > ----------------------------------------------------
  -- > Gin | Pl, x:eq(y+off),y:ptr(pps) * Pin |- rets

  Impl_IntroLLVMFree :: ExprVar (LLVMPointerType w) -> Int ->
                        PermImpl r (ps :> (LLVMPointerType w)) ->
                        PermImpl r (ps :> (LLVMPointerType w))
  -- ^ Copy a free pointer permission to the pointer permission on the top of
  -- the stack, using the 'Int' as the index into the pointer perms in @Pin@,
  -- i.e., the length of @pps1@:
  --
  -- > Gin | Pl, x:ptr(pps, free(e)) * Pin, x:ptr(pps1, free(e), pps2) |- rets
  -- > -----------------------------------------------------------------------
  -- > Gin | Pl, x:ptr(pps) * Pin, x:ptr(pps1, free(e), pps2) |- rets

  Impl_CastLLVMFree :: ExprVar (LLVMPointerType w) -> Int ->
                       PermExpr (BVType w) -> PermExpr (BVType w) ->
                       PermImpl r (ps :> (LLVMPointerType w)) ->
                       PermImpl r (ps :> (LLVMPointerType w))
  -- ^ Cast a proof of @x:ptr(free(e1))@ on the top of the stack to one of
  -- @x:ptr(free(e2))@:
  --
  -- > Gin | Pl, x:ptr(pps1, free(e2), pps2) * Pin |- rets
  -- > ---------------------------------------------------
  -- > Gin | Pl, x:ptr(pps1, free(e1), pps2) * Pin |- rets

  Impl_ElimLLVMFieldContents ::
    ExprVar (LLVMPointerType w) -> Int ->
    Binding (LLVMPointerType w) (PermImpl r ps) ->
    PermImpl r ps
  -- ^ Eliminate a field permission @x:ptr((off,S) |-> p)@ into a permission
  -- @x:ptr((off,S) |-> eq(y))@ that the field contains a fresh variable @y@ and
  -- a permission @y:p@ on @y@:
  --
  -- > Gin | Pl * Pin, x:ptr(pps1, (off,S) |-> eq(y), pps2), y:p |- rets
  -- > -----------------------------------------------------------------
  -- > Gin | Pl * Pin, x:ptr(pps1, (off,S) |-> p, pps2) |- rets

  Impl_IntroLLVMFieldAll ::
    ExprVar (LLVMPointerType w) -> Int ->
    PermImpl r (ps :> (LLVMPointerType w)) ->
    PermImpl r (ps :> (LLVMPointerType w))
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
    PermImpl r (ps :> (LLVMPointerType w)) ->
    PermImpl r (ps :> (LLVMPointerType w))
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
    PermImpl r (ps :> (LLVMPointerType w)) ->
    PermImpl r (ps :> (LLVMPointerType w) :> (LLVMPointerType w))
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


-- | Typeclass for lifting the 'NuMatching' constraint to functors on arbitrary
-- kinds that do not require any constraints on their input types
class NuMatchingAny1 (f :: k -> Type) where
  nuMatchingAny1Proof :: MbTypeRepr (f a)

instance {-# INCOHERENT #-} NuMatchingAny1 f => NuMatching (f a) where
  nuMatchingProof = nuMatchingAny1Proof


$(mkNuMatching [t| forall r ps. NuMatchingAny1 r => PermImpl r ps |])


----------------------------------------------------------------------
-- * Generalized Monads
----------------------------------------------------------------------

type family Fst (p :: (k1,k2)) :: k1 where
  Fst '(x,_) = x

type family Snd (p :: (k1,k2)) :: k2 where
  Snd '(_,y) = y


-- | A generalized monad has additional "input" and "output" types, that
-- sequence together "backwards" through the generalized bind operation. Mostly
-- this is to support 'GenContM', below.
--
-- Note that a generalized monad @m@ should always be a standard monad when the
-- input and output types are the same; i.e., @m r r@ should always be a
-- monad. I do not know a nice way to encode this in Haskell, however...
class GenMonad (m :: k -> k -> Kind.* -> Kind.*) where
  -- | Generalized return
  greturn :: a -> m r r a
  -- | Generalized bind, that passes the output of @f@ to the input of @m@
  (>>>=) :: m r2 r3 a -> (a -> m r1 r2 b) -> m r1 r3 b

infixl 1 >>>=
infixl 1 >>>

(>>>) :: GenMonad m => m r2 r3 () -> m r1 r2 a -> m r1 r3 a
m1 >>> m2 = m1 >>>= \() -> m2

class GenMonadT (t :: (k1 -> k1 -> Kind.* -> Kind.*) ->
                 k2 -> k2 -> Kind.* -> Kind.*) p1 p2 q1 q2 |
  t q1 q2 -> p1 p2 , t q1 p2 -> q2 p1 , t p1 q2 -> p2 q1 where
  glift :: GenMonad m => m p1 p2 a -> t m q1 q2 a


-- | The generalized continuation transformer, which can have different types
-- for the input vs output continuations
newtype GenContM rin rout a =
  GenContM { runGenContM :: (a -> rin) -> rout }

liftGenContM :: Monad m => m a -> GenContM (m b) (m b) a
liftGenContM m = GenContM $ \k -> m >>= k

instance Functor (GenContM r r) where
  fmap f m = m >>= return . f

instance Applicative (GenContM r r) where
  pure = return
  (<*>) = ap

instance Monad (GenContM r r) where
  return x = GenContM $ \k -> k x
  GenContM m >>= f = GenContM $ \k -> m $ \a -> runGenContM (f a) k

instance GenMonad GenContM where
  greturn x = GenContM $ \k -> k x
  (GenContM m) >>>= f = GenContM $ \k -> m $ \a -> runGenContM (f a) k

{-
-- | Change the return type constructor @r@ by mapping the new input type to the
-- old and mapping the old output type to the new
withAltContM :: (r2 pin2 -> r1 pin1) -> (r1 pout1 -> r2 pout2) ->
                GenContM r1 pin1 pout1 a -> GenContM r2 pin2 pout2 a
withAltContM f_in f_out (GenContM m) =
  GenContM $ \k -> f_out (m (f_in . k))
-}

-- | Typeclass for generalized monads that allow a pure capture of the CC
class GenMonad m => GenMonadCaptureCC rin rout m p1 p2 |
  m p1 -> rin , m p2 -> rout , m p1 rout -> p2 , m p2 rin -> p1 where
  gcaptureCC :: ((a -> rin) -> rout) -> m p1 p2 a

instance GenMonadCaptureCC r1 r2 GenContM r1 r2 where
  gcaptureCC f = GenContM f

instance GenMonadCaptureCC rin rout m q1 q2 =>
         GenMonadCaptureCC rin rout (GenStateT m) '(s,q1) '(s,q2) where
  gcaptureCC f = glift $ gcaptureCC f

gmapRet :: GenMonadCaptureCC rin rout m p1 p2 => (rin -> rout) -> m p1 p2 ()
gmapRet f_ret =
  gcaptureCC $ \k -> f_ret $ k ()

-- | Name-binding in the generalized continuation monad (FIXME: explain)
gopenBinding :: (GenMonadCaptureCC rin rout m p1 p2, TypeCtx ctx) =>
                (Mb ctx rin -> rout) -> Mb ctx a ->
                m p1 p2 (MapRList Name ctx, a)
gopenBinding f_ret mb_a =
  gcaptureCC $ \k ->
  f_ret $ flip nuMultiWithElim1 mb_a $ \names a ->
  k (names, a)

gopenBinding1 :: GenMonadCaptureCC rin rout m p1 p2 =>
                 (Binding a rin -> rout) -> Binding a b ->
                 m p1 p2 (Name a, b)
gopenBinding1 f_ret mb_b =
  gopenBinding f_ret mb_b >>>= \(_ :>: nm, b) -> greturn (nm,b)


{-
class GenMonad m => GenMonadShift r m | m -> r where
  gshift :: ((a -> m p1 p1 (r p2)) -> m p3 p4 (r p3)) -> m p2 p4 a

instance GenMonadShift r (GenContM r) where
  gshift f = GenContM $ \k -> runGenContM (f (\a -> greturn (k a))) id
-}


-- | Running generalized computations in "parallel"
class GenMonad m => GenMonadPar r m p1 p2 | m p1 p2 -> r where
  gparallel :: (r -> r -> r) -> m p1 p2 a -> m p1 p2 a -> m p1 p2 a

instance GenMonadPar r2 GenContM r1 r2 where
  gparallel f (GenContM m1) (GenContM m2) =
    GenContM $ \k -> f (m1 k) (m2 k)

instance GenMonadPar r m q1 q2 =>
         GenMonadPar r (GenStateT m) '(s1,q1) '(s2,q2) where
  gparallel f m1 m2 =
    GenStateT $ \s ->
    gparallel f
    (unGenStateT m1 s) (unGenStateT m2 s)

-- | The generalized state monad. Don't get confused: the parameters are
-- reversed, so @p2@ is the /input/ state param type and @p1@ is the /output/.
newtype GenStateT (m :: k -> k -> Kind.* -> Kind.*) p1 p2 a =
  GenStateT { unGenStateT :: Fst p2 -> m (Snd p1) (Snd p2) (a, Fst p1) }

-- | This version of 'unGenStateT' tells GHC to make the parameters into actual
-- type-level pairs, i.e., it makes GHC reason extensionally about pairs
runGenStateT :: GenStateT m '(s1,q1) '(s2,q2) a -> s2 -> m q1 q2 (a, s1)
runGenStateT = unGenStateT

instance Monad (m (Snd p) (Snd p)) => Functor (GenStateT m p p) where
  fmap f m = m >>= return . f

instance Monad (m (Snd p) (Snd p)) => Applicative (GenStateT m p p) where
  pure = return
  (<*>) = ap

instance Monad (m (Snd p) (Snd p)) => Monad (GenStateT m p p) where
  return x = GenStateT $ \s -> return (x, s)
  (GenStateT m) >>= f =
    GenStateT $ \s -> m s >>= \(a, s') -> unGenStateT (f a) s'

instance GenMonadT GenStateT q1 q2 '(s,q1) '(s,q2) where
  glift m = GenStateT $ \s -> m >>>= \a -> greturn (a, s)

instance GenMonad m => GenMonad (GenStateT m) where
  greturn x = GenStateT $ \s -> greturn (x, s)
  (GenStateT m) >>>= f =
    GenStateT $ \s -> m s >>>= \(a, s') -> unGenStateT (f a) s'

-- | FIXME: documentation
gliftGenStateT :: (GenMonad m) =>
                  m q1 q2 a -> GenStateT m '(s, q1) '(s, q2) a
gliftGenStateT m = glift m

-- | Run a generalized state computation with a different state type @s2@ inside
-- one with state type @s1@, using a lens-like pair of a getter function to
-- extract out the starting inner @s2@ state from the outer @s1@ state and an
-- update function to update the resulting outer @s1@ state with the final inner
-- @s2@ state.
withAltStateM :: GenMonad m => (s2' -> s2) -> (s2' -> s1 -> s1') ->
                 GenStateT m '(s1,q1) '(s2,q2) a ->
                 GenStateT m '(s1',q1) '(s2',q2) a
withAltStateM s_get s_update m =
  gget >>>= \s ->
  gput (s_get s) >>>
  m >>>= \a ->
  gget >>>= \s' ->
  gput (s_update s s') >>>
  greturn a

instance (Monad (m (Snd p) (Snd p)), s ~ Fst p) =>
         MonadState s (GenStateT m p p) where
  get = GenStateT $ \s -> return (s, s)
  put s = GenStateT $ \_ -> return ((), s)

class GenMonad m => GenMonadGet s m p | m p -> s where
  gget :: m p p s

class GenMonad m => GenMonadPut s m p1 p2 | m p1 p2 -> s where
  gput :: s -> m p1 p2 ()

instance GenMonad m => GenMonadGet s (GenStateT m) '(s,q) where
  gget = GenStateT $ \s -> greturn (s, s)

instance GenMonad m =>
         GenMonadPut s1 (GenStateT m) '(s1,q) '(s2,q) where
  gput s = GenStateT $ \_ -> greturn ((), s)

gmodify :: (GenMonadGet s1 m p2, GenMonadPut s2 m p1 p2) =>
           (s1 -> s2) -> m p1 p2 ()
gmodify f =
  gget >>>= \s -> gput (f s)

{-
class GenMonad m =>
      GenMonadState (s :: sk -> Type) (m :: k -> k -> Type -> Type) | m -> s where
  type GStateParam m (p :: k) :: sk
  gget :: m p p (s (GStateParam m p))
  gput :: s (GStateParam m p) -> m p p ()

instance GenMonad m => GenMonadState s (GenStateT s m) where
  type GStateParam (GenStateT s m) p = Fst p
  gget = GenStateT $ \s -> greturn (s, s)
  gput s = GenStateT $ \_ -> greturn ((), s)
-}


-- | The generalized state-continuation monad
type GenStateContM s1 r1 s2 r2 = GenStateT GenContM '(s1,r1) '(s2,r2)

{-
-- | Change both the state and return types for the state-continuation monad
withAltContStateM :: (r2 qin -> r1 qin) -> (r1 qout -> r2 qout) ->
                     (s2 pout -> s1 pout) -> (s2 pout -> s1 pin -> s2 pin) ->
                     GenStateContM s1 r1 pin qin pout qout a ->
                     GenStateContM s2 r2 pin qin pout qout a
withAltContStateM f_in f_out s_get s_update m =
  gget >>>= \s ->
  glift (withAltContM f_in f_out $
         runGenStateT m $ s_get s) >>>= \(a,s') ->
  gput (s_update s s') >>>
  greturn a
-}

-- | Map both the state and return types for the state-continuation monad
gmapRetAndState :: (s2 -> s1) -> (r1 -> r2) -> GenStateContM s1 r1 s2 r2 ()
gmapRetAndState f_st f_ret =
  gmodify f_st >>> gmapRet f_ret

-- | Abort the current state-continuation computation and just return an @r2@
--
-- FIXME: figure out how to write this with something like 'gcaptureCC'...? The
-- problem is that 'gcaptureCC' will not allow us to change the state type...
gabortM :: r2 -> GenStateContM s1 r1 s2 r2 a
gabortM ret = GenStateT $ \_ -> GenContM $ \_ -> ret


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
                ImplState (vars :> tp) ps
extImplState s =
  s { _implStateVars = extCruCtx (_implStateVars s),
      _implStatePSubst = extPSubst (_implStatePSubst s) }

unextImplState :: ImplState (vars :> a) ps -> ImplState vars ps
unextImplState s =
  s { _implStateVars = unextCruCtx (_implStateVars s),
      _implStatePSubst = unextPSubst (_implStatePSubst s) }

{-
instance PermState (ImplState vars) where
  permStatePerms = implStatePerms
-}

-- | The implication monad is the permission monad that uses 'ImplState'
type ImplM vars r ps_out ps_in =
  GenStateContM (ImplState vars ps_out) (PermImpl r ps_out)
  (ImplState vars ps_in) (PermImpl r ps_in)


-- | Run an 'ImplM' computation by passing it a @vars@ context, a starting
-- permission set, and an @r@
runImplM :: CruCtx vars -> PermSet ps_in -> r ps_out ->
            ImplM vars r ps_out ps_in () -> PermImpl r ps_in
runImplM vars perms r m =
  runGenContM (runGenStateT m (mkImplState vars perms)) (const $ Impl_Done r)


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
modifyPSubst f = gmodify (over implStatePSubst f)

-- | Set the value for an existential variable in the current substitution,
-- raising an error if it is already set
setVarM :: Member vars a -> PermExpr a -> ImplM vars r ps ps ()
setVarM x e = modifyPSubst (psubstSet x e)

-- | Run an implication computation with one more existential variable,
-- returning the optional expression it was bound to in the current partial
-- substitution when it is done
withExtVarsM :: KnownRepr TypeRepr tp =>
                ImplM (vars :> tp) r ps1 ps2 a ->
                ImplM vars r ps1 ps2 (a, Maybe (PermExpr tp))
withExtVarsM m =
  withAltStateM extImplState (const unextImplState) $
  (m >>>= \a ->
    getPSubst >>>= \psubst ->
    greturn (a, psubstLookup psubst Member_Base))

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

-- | Get the distinguished permission stack
getDistPerms :: ImplM vars r ps ps (DistPerms ps)
getDistPerms = view (implStatePerms . distPerms) <$> gget

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
implFailM :: ImplM vars r ps_any ps a
implFailM = gabortM Impl_Fail

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
implCatchM m1 m2 = gparallel Impl_Catch m1 m2
  -- FIXME: figure out the "right" way to write this with shift and reset!
  {-
  GenStateT $ \s -> GenContT $ \k ->
  Impl_Catch <$> (unGenContT (unGenStateT m1 s) k)
  <*> (unGenContT (unGenStateT m2 s) k)
  -}
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
                Binding tp (ValuePerm a) ->
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
elimExistsM :: (KnownRepr TypeRepr tp, NuMatchingAny1 r) => ExprVar a -> f tp ->
               ImplM vars r ps ps ()
elimExistsM x (_ :: f tp) =
  getPerms >>>= \perms ->
  gopenBinding1 (Impl_ElimExists x) (elimExists x (knownRepr :: TypeRepr tp)
                                     perms) >>>= \(_nm, perms') ->
  setPerms perms'

-- | Eliminate disjunctives and existentials for a specific variable
elimOrsExistsM :: NuMatchingAny1 r => ExprVar a -> ImplM vars r ps ps ()
elimOrsExistsM x =
  getPerm x >>>= \p ->
  case p of
    ValPerm_Or _ _ -> elimOrM x >>> elimOrsExistsM x
    ValPerm_Exists (_ :: Binding a _) ->
      elimExistsM x (knownRepr :: TypeRepr a) >>> elimOrsExistsM x
    _ -> return ()

-- | Introduce a proof of @x:true@ onto the top of the stack
introTrueM :: ExprVar a -> ImplM vars r (ps :> a) ps ()
introTrueM x = gmapRetAndPerms (introTrue x) (Impl_IntroTrue x)

-- | Recombine an @x:true@ proof on the top of the stack by dropping it
recombineTrueM :: ExprVar a -> ImplM vars r ps (ps :> a) ()
recombineTrueM x = gmapRetAndPerms (recombineTrue x) (Impl_RecombineTrue x)

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
elimLLVMFieldContentsM :: NuMatchingAny1 r => ExprVar (LLVMPointerType w) ->
                          Int -> ImplM vars r ps ps (ExprVar (LLVMPointerType w))
elimLLVMFieldContentsM x i =
  getPerms >>>= \perms ->
  case elimLLVMFieldContents x i perms of
    Left y -> greturn y
    Right mb_perms' ->
      gopenBinding1 (Impl_ElimLLVMFieldContents x i) mb_perms' >>>= \(y,perms') ->
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


----------------------------------------------------------------------
-- * Proving Equality Permissions
----------------------------------------------------------------------

-- | Build a proof on the top of the stack that @x:eq(e)@
proveVarEq :: NuMatchingAny1 r => ExprVar a -> Mb vars (PermExpr a) ->
              ImplM vars r (ps :> a) ps ()
proveVarEq x mb_e =
  getPerm x >>>= \perm ->
  getPSubst >>>= \psubst ->
  proveVarEqH x perm psubst mb_e

-- | Main helper function for 'proveVarEq'
proveVarEqH :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
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
proveVarField :: NuMatchingAny1 r => ExprVar (LLVMPointerType w) ->
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
proveVarPtrPerms :: (1 <= w, KnownNat w, NuMatchingAny1 r) =>
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
proveVarImpl :: NuMatchingAny1 r => ExprVar a -> Mb vars (ValuePerm a) ->
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

-- | A list of distinguished permissions with existential variables
data ExDistPerms vars ps where
  ExDistPermsNil :: ExDistPerms vars RNil
  ExDistPermsCons :: ExDistPerms vars ps -> ExprVar a -> Mb vars (ValuePerm a) ->
                     ExDistPerms vars (ps :> a)

$(mkNuMatching [t| forall vars ps. ExDistPerms vars ps |])

-- | Existentially quantify a list of distinguished permissions over the empty
-- set of existential variables
distPermsToExDistPerms :: DistPerms ps -> ExDistPerms RNil ps
distPermsToExDistPerms DistPermsNil = ExDistPermsNil
distPermsToExDistPerms (DistPermsCons ps x p) =
  ExDistPermsCons (distPermsToExDistPerms ps) x (emptyMb p)

-- | Prove a list of existentially-quantified distinguished permissions
proveVarsImpl :: NuMatchingAny1 r => ExDistPerms vars as ->
                 ImplM vars r as RNil ()
proveVarsImpl ExDistPermsNil = return ()
proveVarsImpl (ExDistPermsCons ps x p) = proveVarsImpl ps >>> proveVarImpl x p


----------------------------------------------------------------------
-- * Recombining Permissions
----------------------------------------------------------------------

-- | Recombine the distinguished permission @p_dist@ on @x@ back into the
-- existing permission @p@ on @x@
recombinePerm :: ExprVar a -> ValuePerm a -> ValuePerm a ->
                 ImplM RNil r as (as :> a) ()
recombinePerm x ValPerm_True _ = recombineTrueM x
recombinePerm _ _ _ = error "FIXME HERE: finish recombinePerm!"

-- | Recombine the distinguished permissions back into the permission set
recombinePerms :: ImplM RNil r RNil as ()
recombinePerms =
  getDistPerms >>>= \stack ->
  case stack of
    DistPermsNil -> greturn ()
    DistPermsCons _ x p_dist ->
      getPerm x >>>= \p_x -> recombinePerm x p_dist p_x >>> recombinePerms
