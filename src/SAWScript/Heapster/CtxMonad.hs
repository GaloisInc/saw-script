{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module SAWScript.Heapster.CtxMonad where

import           Control.Monad.Except
import qualified Control.Category as Cat
import           Data.Type.Equality
import           Data.Kind
import           Data.Proxy
import           Data.Reflection

import           Data.Parameterized.Ctx
import           Data.Parameterized.Context


----------------------------------------------------------------------
-- * The standard backtracking monad
----------------------------------------------------------------------

-- | Backtracking search monad
newtype BackM err a =
  BackM { unBackM :: forall r. (a -> (err -> r) -> r) -> (err -> r) -> r }

instance Functor (BackM err) where
  fmap f m = m >>= return . f

instance Applicative (BackM err) where
  pure = return
  (<*>) = ap

instance Monad (BackM err) where
  return a = BackM $ \ks kf -> ks a kf
  m >>= f = BackM $ \ks kf -> unBackM m (\a kf' -> unBackM (f a) ks kf') kf

instance MonadError err (BackM err) where
  throwError err = BackM $ \_ kf -> kf err
  catchError m f = BackM $ \ks kf -> unBackM m ks (\err -> unBackM (f err) ks kf)


----------------------------------------------------------------------
-- * Contextual types: types that are relative to a type context
----------------------------------------------------------------------

-- | A context-dependent type is a type that depends on a context
type CType k = Ctx k -> *

-- | Class for "good" contextual types = can lift elements into extended
-- contexts. Having a separate typeclass, rather than just using
-- 'ExtendContext', ensures we do not pollute the namespace of the latter with
-- our incoherent instances below.
class ValidCType a where
  extContext :: Diff ctx ctx' -> a ctx -> a ctx'

-- | Class for "good" unary contextual type constructors
class ValidCType1 (f :: (Ctx k -> *) -> Ctx k -> *) where
  extContext1 :: ValidCType a => Diff ctx ctx' -> f a ctx -> f a ctx'

instance {-# INCOHERENT #-} (ValidCType1 f, ValidCType a) => ValidCType (f a) where
  extContext = extContext1

-- | Class for "good" binary contextual type constructors
class ValidCType2 (f :: (Ctx k -> *) -> (Ctx k -> *) -> Ctx k -> *) where
  extContext2 :: (ValidCType a, ValidCType b) =>
                    Diff ctx ctx' -> f a b ctx -> f a b ctx'

instance {-# INCOHERENT #-} (ValidCType2 f, ValidCType a) => ValidCType1 (f a) where
  extContext1 = extContext2

-- | Apply a type function to a contextual type
infixl 2 :@:
newtype (:@:) (f :: * -> *) (b :: CType k) ctx =
  CApplyF { unCApplyF :: f (b ctx) }

instance Functor f => ValidCType1 ((:@:) f) where
  extContext1 diff = CApplyF . fmap (extContext diff) . unCApplyF

-- | The pair type-in-context
infixr 1 :*:
data (:*:) a b (ctx :: Ctx k) = CPair (a ctx) (b ctx)

instance ValidCType2 (:*:) where
  extContext2 diff (CPair a b) =
    CPair (extContext diff a) (extContext diff b)

-- | The unit type-in-context
data CUnit (ctx :: Ctx k) = CUnit

instance ValidCType CUnit where
  extContext _ _ = CUnit

-- | Lift a standard type to a contextual type that ignores its context
newtype CConst a (ctx :: Ctx k) = CConst { unCConst :: a }

instance ValidCType (CConst a) where
  extContext _ (CConst a) = CConst a

-- | The function type-in-context, that can be applied in any extension of the
-- current context
infixr 0 :->:
newtype (:->:) a b (ctx :: Ctx k) =
  CFun { unCFun :: forall ctx'. Diff ctx ctx' -> a ctx' -> b ctx' }

instance ValidCType2 (:->:) where
  extContext2 diff (CFun f) = CFun $ \diff' -> f (diff' Cat.. diff)


----------------------------------------------------------------------
-- * Contextual expressions: expressions over contextual types
----------------------------------------------------------------------

-- | An "expression context" is a representation of contexts as sequences of
-- contexts that are to be appended. That is, the expression context
--
-- > BaseCtx ctx :<+>: '(ctx1, sz1) :<+>: ... :<+>: '(ctxn, szn)
--
-- represents the context
--
-- > ctx <+> ctx1 <+> ... <+> ctxn
--
-- This expression context is used to represent the context inside @n@
-- contextual lambdas (see 'clam'), each of which builds a function body that
-- can be called in an extension @cur_ctx <+> ctx@ of the current context
-- @cur_ctx@. By using type-level constructors in a representation, rather than
-- using the @n@-fold context append explicitly, we make things easier for GHC
-- (and so also for us).
--
-- The @sz@ type is a type-level variable that 'Reifies' a 'Size' object for
-- each context using type-level reflection. That is, an expression context is
-- intuitively a sequence of pairs of a context and its 'Size'.
--
-- Note that there are multiple different expression
-- contexts that represent the same underlying context, but that will not
-- actually be an issue here.
data ExprCtx k1 k2
  = BaseCtx (Ctx k1)
  | ExprCtx k1 k2 :<+>: (Ctx k1, k2)

-- | Convert an expression context to the context it reprsents
type family CtxOfExprCtx (ctx :: ExprCtx k *) :: Ctx k where
  CtxOfExprCtx (BaseCtx ctx) = ctx
  CtxOfExprCtx (ectx :<+>: '(ctx, _)) = CtxOfExprCtx ectx <+> ctx

-- NOTE: cannot write this in the Unsafe representation of contexts; this is why
-- we need WeakensTo, below
-- flattenDiff :: Diff ectx1 ectx2 -> Diff (CtxOfExprCtx ectx1) (CtxOfExprCtx ectx2)

-- | Proof that @ectx1@ can be extended to @ectx2@
newtype WeakensToPf ectx1 ectx2 =
  WeakensToPf (Diff (CtxOfExprCtx ectx1) (CtxOfExprCtx ectx2))

-- | Any expression context weakens to itself
weakensRefl :: WeakensToPf ectx ectx
weakensRefl = WeakensToPf noDiff

-- | Add an extra context to the right of an existing weakening proof
weakensCons :: Reifies s (Size ctx) => WeakensToPf ectx1 ectx2 -> Proxy s ->
               WeakensToPf ectx1 (ectx2 :<+>: '(ctx, s))
weakensCons (WeakensToPf diff) sz =
  WeakensToPf $ appendDiff (reflect sz) Cat.. diff

-- | Typeclass version of 'WeakensToPf'
class WeakensTo ectx1 ectx2 where
  weakensTo :: WeakensToPf ectx1 ectx2

instance WeakensTo ectx ectx where
  weakensTo = weakensRefl

instance {-# INCOHERENT #-} (WeakensTo ectx1 ectx2, Reifies s (Size ctx)) =>
                            WeakensTo ectx1 (ectx2 :<+>: '(ctx, s)) where
  weakensTo = weakensCons weakensTo Proxy

-- | A contextual expression of contextual type @a@ in expression context @ectx@
newtype CExpr (a :: CType k) (ectx :: ExprCtx k *) =
  CExpr { unCExpr :: (a (CtxOfExprCtx ectx)) }

-- | Extract a contextual value from a top-level contextual expression
runCExpr :: CExpr a (BaseCtx ctx) -> a ctx
runCExpr = unCExpr

-- | Weaken the context of a contextual expression
weakenExprPf :: ValidCType a => WeakensToPf ectx1 ectx2 ->
                CExpr a ectx1 -> CExpr a ectx2
weakenExprPf (WeakensToPf diff) (CExpr a) = CExpr $ extContext diff a

-- | Weaken the context of a contextual expression using 'WeakensTo'
weakenExpr :: (ValidCType a, WeakensTo ectx1 ectx2) =>
              CExpr a ectx1 -> CExpr a ectx2
weakenExpr = weakenExprPf weakensTo

-- | Helper function for 'clam'
clamH :: (forall ctx s. Reifies s (Size ctx) =>
          CExpr a (ectx :<+>: '(ctx, s)) -> CExpr b (ectx :<+>: '(ctx, s))) ->
         CExpr (a :->: b) ectx
clamH f =
  CExpr $ CFun $ \diff a ->
  case diffIsAppend diff of
    IsAppend (sz :: Size ctx'') ->
      reify sz $ \(p :: Proxy s) ->
      unCExpr $ f @ctx'' @s (CExpr a)

-- | Build an expression for a contextual function 
clam :: ValidCType a =>
        (forall ctx s. Reifies s (Size ctx) =>
         (forall ectx'.
          WeakensTo (ectx :<+>: '(ctx, s)) ectx' => CExpr a ectx') ->
         CExpr b (ectx :<+>: '(ctx, s))) ->
        CExpr (a :->: b) ectx
clam f = clamH (\a -> f $ weakenExpr a)

-- | Apply a contextual function expression
(@@) :: CExpr (a :->: b) ectx -> CExpr a ectx -> CExpr b ectx
(CExpr f) @@ (CExpr arg) = CExpr $ unCFun f noDiff arg

-- | A version of '(@@)' with low precedence, to work like '($)'
infixr 0 $$
($$) :: CExpr (a :->: b) ectx -> CExpr a ectx -> CExpr b ectx
($$) = (@@)

-- | Typeclass for lifting operators to contextual expressions
class CExprOp eop where
  type CExprOpType eop
  cexprOp :: CExprOpType eop -> eop
  cexprUnOp :: eop -> CExprOpType eop

instance CExprOp (CExpr a ectx) where
  type CExprOpType (CExpr a ectx) = a (CtxOfExprCtx ectx)
  cexprOp = CExpr
  cexprUnOp = unCExpr

instance CExprOp eop => CExprOp (CExpr a ectx -> eop) where
  type CExprOpType (CExpr a ectx -> eop) =
    a (CtxOfExprCtx ectx) -> CExprOpType eop
  cexprOp f = cexprOp . f . unCExpr
  cexprUnOp f = cexprUnOp . f . CExpr

cOp1 :: (forall ctx. a ctx -> b ctx) -> CExpr a ectx -> CExpr b ectx
cOp1 f (CExpr a) = CExpr $ f a

cOp2 :: (forall ctx. a ctx -> b ctx -> c ctx) ->
        CExpr a ectx -> CExpr b ectx -> CExpr c ectx
cOp2 f (CExpr a) (CExpr b) = CExpr $ f a b


-- | Build a contextual expression for a pair
cpair :: CExpr a ectx -> CExpr b ectx -> CExpr (a :*: b) ectx
cpair = cexprOp CPair

-- | Pattern-match a contextual expression for a pair
cunpair :: CExpr (a :*: b) ectx -> (CExpr a ectx, CExpr b ectx)
cunpair (CExpr (CPair a b)) = (CExpr a, CExpr b)

-- | Build a contextual unit expression
cunit :: CExpr CUnit ectx
cunit = CExpr CUnit

-- | Lift an element of a standard type to a contextual expression
cconst :: a -> CExpr (CConst a) ectx
cconst = CExpr . CConst

-- | Un-lift a contextual expression of lifted type to a normal value
cunconst :: CExpr (CConst a) ectx -> a
cunconst (CExpr (CConst a)) = a

test1 :: ValidCType a => CExpr (a :->: a) ectx
test1 = clam $ \x -> x

test2 :: (ValidCType a, ValidCType b) =>
         CExpr (a :->: b :->: a) ectx
test2 = clam $ \x -> clam $ \y -> x


----------------------------------------------------------------------
-- * Contextual monads
----------------------------------------------------------------------

-- | Monads over contextual types
class ValidCType1 m => CMonad (m :: (Ctx k -> *) -> Ctx k -> *) where
  creturn :: ValidCType a => CExpr a ectx -> CExpr (m a) ectx
  (>>>=) :: (ValidCType a, ValidCType b) =>
            CExpr (m a) ectx -> CExpr (a :->: m b) ectx -> CExpr (m b) ectx


-- | Contextual monad transformers
class CMonadTrans (t :: ((Ctx k -> *) -> Ctx k -> *) ->
                          ((Ctx k -> *) -> Ctx k -> *)) where
  clift :: CMonad m => CExpr (m a) ectx -> CExpr (t m a) ectx

instance Monad m => CMonad ((:@:) m) where
  creturn = cOp1 (CApplyF . return)
  (>>>=) = cOp2 $ \m f -> CApplyF (unCApplyF m >>= unCApplyF . unCFun f noDiff)

-- | The contextual continuation transformer
newtype CContT res m a (ctx :: Ctx k) =
  CContT { unCContT :: ((a :->: m res) :->: m res) ctx }

instance (ValidCType1 m, ValidCType res) =>
         ValidCType1 (CContT res m) where
  extContext1 diff (CContT m) = CContT $ extContext diff m

instance (CMonad m, ValidCType res) => CMonad (CContT res m) where
  creturn a =
    cOp1 CContT $ clam $ \k -> k @@ weakenExpr a
  m >>>= f =
    cOp1 CContT $ clam $ \k ->
    (cOp1 unCContT $ weakenExpr m) $$ clam $ \a ->
    (cOp1 unCContT $ weakenExpr f @@ a) @@ k


----------------------------------------------------------------------
-- * The contextual continuation monad
----------------------------------------------------------------------
{-


-- | The continuation transformer from ordinary to contextual monads
newtype CtxContM res (m :: * -> *) a (ctx :: Ctx k) =
  CtxContM { unCtxContM :: CtxFun a (CtxMapF m res) ctx -> CtxMapF m res ctx }

instance Monad m => CtxMonad (CtxContM res m) where
  returnC a = CtxContM $ \k -> applyCtxFun k noDiff a
  m >>>= f =
    CtxContM $ \k ->
    unCtxContM m (CtxFun $ \diff a ->
                   unCtxContM (f diff a) (extContext diff k))

-- | Lift a computation in @m@ into one in 'CtxContM res m'
liftCtxContM :: Monad m => m (a ctx) -> CtxContM res m a ctx
liftCtxContM m = CtxContM $ \k -> CtxMapF (m >>= unCtxMapF . applyCtxFun k noDiff)

-- | Contextual monads that support shift and reset
class CtxMonad m => CtxMonadShiftReset res m | m -> res where
  shiftC :: ((forall ctx'. Diff ctx ctx' ->
              a ctx' -> m res ctx') -> m res ctx) -> m a ctx
  resetC :: m res ctx -> m res ctx

instance Monad m => CtxMonadShiftReset res (CtxContM res m) where
  shiftC f =
    CtxContM $ \k ->
    unCtxContM (f (\diff a -> liftCtxContM $ unCtxMapF $ applyCtxFun k diff a))
    (CtxFun $ \diff a -> CtxMapF $ return a)
  resetC m =
    CtxContM $ \k ->
    CtxMapF $
    (unCtxMapF $ unCtxContM m (CtxFun $ \_ -> CtxMapF . return)) >>=
    (unCtxMapF . applyCtxFun k noDiff)


----------------------------------------------------------------------
-- * The contextual state monad
----------------------------------------------------------------------

-- | The contextual state monad
newtype CtxStateT s m a (ctx :: Ctx k) =
  CtxStateT { unCtxStateT :: s ctx -> m (CtxPair s a) ctx }

instance CtxMonad m => CtxMonad (CtxStateT s m) where
  returnC a = CtxStateT $ \s -> returnC (CtxPair s a)
  m >>>= f =
    CtxStateT $ \s -> unCtxStateT m s >>>= \diff (CtxPair s' a) ->
    unCtxStateT (f diff a) s'

instance ValidCType s => CtxMonadTrans (CtxStateT s) where
  liftC m =
    CtxStateT $ \s -> m >>>= \diff a ->
    returnC (CtxPair (extContext diff s) a)

-- | Contextual monads with state
class CtxMonadState s m | m -> s where
  getC :: m s ctx
  putC :: s ctx -> m CtxUnit ctx

instance CtxMonad m => CtxMonadState s (CtxStateT s m) where
  getC = CtxStateT $ \s -> returnC (CtxPair s s)
  putC s = CtxStateT $ \_ -> returnC (CtxPair s CtxUnit)

instance (ValidCType s, CtxMonadShiftReset res m) =>
         CtxMonadShiftReset res (CtxStateT s m) where
  -- FIXME: understand what shift does to the state...
  shiftC f = CtxStateT $ \s -> 
    shiftC $ \k ->
    unCtxStateT (f $ \diff a ->
                  CtxStateT $ \s' ->
                  k diff (CtxPair s' a) >>>= \diff res ->
                  returnC (CtxPair (extContext diff s') res)) s
    >>>= \diff (CtxPair _ res) ->
    returnC res

  -- NOTE: reset throws away the inner state
  resetC m =
    CtxStateT $ \s ->
    resetC (unCtxStateT m s >>>= \diff (CtxPair _ res) ->
             returnC res) >>>= \diff res ->
    returnC (CtxPair (extContext diff s) res)
-}
