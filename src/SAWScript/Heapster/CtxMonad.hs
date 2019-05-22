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
-- * Weakenings on contexts
----------------------------------------------------------------------

-- FIXME HERE: move to Unsafe.hs
-- | Extend the size by a given difference.
unextSize :: Size r -> Diff l r -> Size l
unextSize = error "FIXME HERE: unextSize"


-- | Our variables need to keep the 'Size' of the context around so that we can
-- apply weakenings
newtype CVar a ctx = CVar (Index ctx a)

-- | A weakening is a sequence of 'Diff's on a prefix of the context
data Weakening ctx1 ctx2 where
  WeakeningNil :: Weakening ctx ctx
  Weakening1 :: Diff c1 c2 -> Size c3 -> Weakening (c1 <+> c3) (c2 <+> c3)
  WeakeningComp :: Weakening ctx1 ctx2 -> Weakening ctx2 ctx3 ->
                   Weakening ctx1 ctx3

instance Cat.Category Weakening where
  id = WeakeningNil
  WeakeningNil . w1 = w1
  w2 . WeakeningNil = w2
  w2 . w1 = WeakeningComp w1 w2

mkWeakening1 :: Weakening ctx (ctx ::> tp)
mkWeakening1 = Weakening1 (extendRight noDiff) zeroSize

weakenWeakening1 :: Weakening ctx1 ctx2 -> Weakening (ctx1 ::> tp) (ctx2 ::> tp)
weakenWeakening1 WeakeningNil = WeakeningNil
weakenWeakening1 (Weakening1 d sz) = Weakening1 d (incSize sz)
weakenWeakening1 (WeakeningComp w1 w2) =
  WeakeningComp (weakenWeakening1 w1) (weakenWeakening1 w2)

weakenSize :: Weakening ctx1 ctx2 -> Size ctx1 -> Size ctx2
weakenSize WeakeningNil sz = sz
weakenSize (Weakening1 diff12 sz3) sz13 =
  let sz1 = subtractSize sz13 Proxy sz3 in
  addSize (extSize sz1 diff12) sz3
weakenSize (WeakeningComp w1 w2) sz = weakenSize w2 $ weakenSize w1 sz

unweakenSize :: Weakening ctx1 ctx2 -> Size ctx2 -> Size ctx1
unweakenSize WeakeningNil sz = sz
unweakenSize (Weakening1 diff12 sz3) sz23 =
  let sz2 = subtractSize sz23 Proxy sz3 in
  addSize (unextSize sz2 diff12) sz3
unweakenSize (WeakeningComp w1 w2) sz = unweakenSize w1 $ unweakenSize w2 sz

weakenVar :: Weakening ctx1 ctx2 -> Size ctx2 -> CVar a ctx1 -> CVar a ctx2
weakenVar WeakeningNil _ x = x
weakenVar (Weakening1 diff12 sz3) sz23 (CVar ix) =
  let sz2 = subtractSize sz23 Proxy sz3
      sz1 = unextSize sz2 diff12 in
  CVar $
  case caseIndexAppend sz1 sz3 ix of
    Left ix1 -> extendIndex' (appendDiff sz3 Cat.. diff12) ix1
    Right ix3 -> extendIndexLeft (extSize sz1 diff12) ix3
weakenVar (WeakeningComp w1 w2) sz x =
  weakenVar w2 sz $ weakenVar w1 (unweakenSize w2 sz) x


----------------------------------------------------------------------
-- * Contextual types: types that are relative to a type context
----------------------------------------------------------------------

-- | A context-dependent type is a type that depends on a context
type CType k = Ctx k -> *

-- | A valid contextual type is one that can be mapped via context extensions
class Weakenable a where
  weaken :: Weakening ctx ctx' -> Size ctx' -> a ctx -> a ctx'

-- | A valid unary contextual type function is one that maps valid contextual
-- types to valid contextual types
class Weakenable1 (f :: CType k -> CType k) where
  weaken1 :: Weakenable a => Weakening ctx ctx' -> Size ctx' -> f a ctx -> f a ctx'

instance {-# INCOHERENT #-} (Weakenable1 f, Weakenable a) => Weakenable (f a) where
  weaken = weaken1

-- | A valid binary contextual type function is one that maps pairs of valid
-- contextual types to a valid contextual types
class Weakenable2 (f :: CType k -> CType k -> CType k) where
  weaken2 :: (Weakenable a, Weakenable b) =>
                 Weakening ctx ctx' -> Size ctx' -> f a b ctx -> f a b ctx'

instance {-# INCOHERENT #-} (Weakenable2 f, Weakenable a) => Weakenable1 (f a) where
  weaken1 = weaken2

instance Weakenable (CVar a) where
  weaken = weakenVar

-- | Apply a type function to a contextual type
infixl 2 :@:
newtype (:@:) (f :: * -> *) (b :: CType k) ctx =
  CApplyF { unCApplyF :: f (b ctx) }

instance Functor f => Weakenable1 ((:@:) f) where
  weaken1 w sz = CApplyF . fmap (weaken w sz) . unCApplyF

-- | The pair type-in-context
infixr 1 :*:
data (:*:) a b (ctx :: Ctx k) = CPair (a ctx) (b ctx)

instance Weakenable2 (:*:) where
  weaken2 w sz (CPair a b) =
    CPair (weaken w sz a) (weaken w sz b)

cpairFst :: (a :*: b) ctx -> a ctx
cpairFst (CPair a _) = a

cpairSnd :: (a :*: b) ctx -> b ctx
cpairSnd (CPair _ b) = b

-- | The unit type-in-context
data CUnit (ctx :: Ctx k) = CUnit

instance Weakenable CUnit where
  weaken _ _ _ = CUnit

-- | Lift a standard type to a contextual type that ignores its context
newtype CConst a (ctx :: Ctx k) = CConst { unCConst :: a }

instance Weakenable (CConst a) where
  weaken _ _ (CConst a) = CConst a

-- | The function type-in-context, that can be applied in any extension of the
-- current context
infixr 0 :->:
newtype (:->:) a b (ctx :: Ctx k) =
  CFun { unCFun :: forall ctx'. Weakening ctx ctx' -> a ctx' -> b ctx' }

instance Weakenable2 (:->:) where
  weaken2 w _ (CFun f) = CFun $ \w' -> f (w' Cat.. w)

-- | Represents a contextual type inside a binding for another variable
newtype CNabla (tp :: k) (a :: CType k) (ctx :: Ctx k) =
  CNabla { unCNabla :: a (ctx ::> tp) }

instance Weakenable1 (CNabla tp) where
  weaken1 w sz (CNabla b) =
    CNabla $ weaken (weakenWeakening1 w) (incSize sz) b


----------------------------------------------------------------------
-- * Contextual expressions: expressions over contextual types
----------------------------------------------------------------------

-- FIXME: update documentation

-- | An "expression context" is a sequence
--
-- > BaseCtx ctx0 :<+>: '(ctx1, sz1) :<+>: ... :<+>: '(ctxn, szn)
--
-- of contexts bound at each contextual lambda (see 'clam') containing the
-- current expression. That is, the above expression context is used for the
-- body of a contextual lambda that is nested @n@ levels deep. This expression
-- context is used to represent (using 'CtxOfExprCtx') the @n@-ary append
--
-- > ctx0 <+> ctx1 <+> ... <+> ctxn
--
-- of the contexts contained in it. Intuitively, this is because each contextual
-- lambda could be called in an extension of the previous context.
--
-- Each @szi@ is a type-level variable that 'Reifies' a 'Diff' from @ctx(i-1)@
-- to @ctxi@. This gives GHC enough information to automatically derive a 'Diff'
-- (using the 'WeakensTo' class, below) from any previous context to any later
-- context in the list, which in turn allows us to weaken expressions without
-- having to manually put in all the coercions.
data ExprCtx k1 k2
  = BaseCtx (Ctx k1)
  | ExprCtx k1 k2 :<+>: (Ctx k1, k2)

-- | Defines the constraint required for type variable @sz@ in the expression
-- context @ectx :<+>: (ctx, sz)@
type WConstr (ectx :: ExprCtx k *) (ctx :: Ctx k) (w :: *) =
  Reifies w (Weakening (CtxOfExprCtx ectx) ctx)

-- | Convert an expression context to the context it reprsents
type family CtxOfExprCtx (ctx :: ExprCtx k *) :: Ctx k where
  CtxOfExprCtx (BaseCtx ctx) = ctx
  CtxOfExprCtx (_ :<+>: '(ctx, _)) = ctx

-- | A "weakening" of expression contexts is a 'Diff' from the 'CtxOfExprCtx' of
-- one to that of the other
newtype EWeakening ectx1 ectx2 =
  EWeakening (Weakening (CtxOfExprCtx ectx1) (CtxOfExprCtx ectx2))

-- | Any expression context weakens to itself
eweakeningRefl :: EWeakening ectx ectx
eweakeningRefl = EWeakening Cat.id

-- | Add a context to the right of an existing weakening
eweakeningCons :: WConstr ectx2 ctx w => EWeakening ectx1 ectx2 -> Proxy w ->
                  EWeakening ectx1 (ectx2 :<+>: '(ctx, w))
eweakeningCons (EWeakening w) p =
  EWeakening $ reflect p Cat.. w

-- | Typeclass version of 'Weakening'
class WeakensTo ectx1 ectx2 where
  weakensTo :: EWeakening ectx1 ectx2

instance WeakensTo ectx ectx where
  weakensTo = eweakeningRefl

instance {-# INCOHERENT #-} (WeakensTo ectx1 ectx2, WConstr ectx2 ctx sz) =>
                            WeakensTo ectx1 (ectx2 :<+>: '(ctx, sz)) where
  weakensTo = eweakeningCons weakensTo Proxy

-- | A contextual expression of contextual type @a@ in expression context @ectx@
newtype CExpr (a :: CType k) (ectx :: ExprCtx k *) =
  CExpr { unCExpr :: Size (CtxOfExprCtx ectx) -> (a (CtxOfExprCtx ectx)) }

-- | Extract a contextual value from a top-level contextual expression
runCExpr :: Size ctx -> CExpr a (BaseCtx ctx) -> a ctx
runCExpr sz (CExpr f) = f sz

-- | Weaken the context of a contextual expression
cweakenPf :: Weakenable a => EWeakening ectx1 ectx2 ->
             CExpr a ectx1 -> CExpr a ectx2
cweakenPf (EWeakening w) (CExpr f) =
  CExpr $ \sz -> weaken w sz $ f $ unweakenSize w sz

-- | Weaken the context of a contextual expression using 'WeakensTo'
cweaken :: (Weakenable a, WeakensTo ectx1 ectx2) =>
           CExpr a ectx1 -> CExpr a ectx2
cweaken = cweakenPf weakensTo

-- | Helper function for 'clam'
clamH :: (forall ctx w. WConstr ectx ctx w =>
          CExpr a (ectx :<+>: '(ctx, w)) -> CExpr b (ectx :<+>: '(ctx, w))) ->
         CExpr (a :->: b) ectx
clamH f =
  CExpr $ \sz -> CFun $ \(w :: Weakening _ ctx) a ->
  reify w $ \(p :: Proxy w) ->
  unCExpr (f @ctx @w (CExpr $ const a)) (weakenSize w sz)

-- | The type of a binding expression
type CExprBinder a b ectx =
  (forall ctx w. WConstr ectx ctx w =>
   (forall ectx'.
    WeakensTo (ectx :<+>: '(ctx, w)) ectx' => CExpr a ectx') ->
   CExpr b (ectx :<+>: '(ctx, w)))

-- | Build an expression for a contextual function 
clam :: Weakenable a => CExprBinder a b ectx -> CExpr (a :->: b) ectx
clam f = clamH (\a -> f $ cweaken a)

-- | Apply a contextual function expression
(@@) :: CExpr (a :->: b) ectx -> CExpr a ectx -> CExpr b ectx
(CExpr f) @@ (CExpr arg) = CExpr $ \sz -> unCFun (f sz) Cat.id (arg sz)

-- | A version of '(@@)' with low precedence, to work like '($)'
infixr 0 $$
($$) :: CExpr (a :->: b) ectx -> CExpr a ectx -> CExpr b ectx
($$) = (@@)

-- | Lift a unary operation between contextual types to one on expressions
cOp1 :: (forall ctx. a ctx -> b ctx) -> CExpr a ectx -> CExpr b ectx
cOp1 f (CExpr a) = CExpr (f . a)

-- | Lift a binary operation between contextual types to one on expressions
cOp2 :: (forall ctx. a ctx -> b ctx -> c ctx) ->
        CExpr a ectx -> CExpr b ectx -> CExpr c ectx
cOp2 f (CExpr a) (CExpr b) = CExpr $ \sz -> f (a sz) (b sz)

-- | Build a contextual expression for a pair
cpair :: CExpr a ectx -> CExpr b ectx -> CExpr (a :*: b) ectx
cpair = cOp2 CPair

-- | Pattern-match a contextual expression for a pair
{- NOTE: we could define this, but it would duplicate the body of the CExpr!
cunpair :: CExpr (a :*: b) ectx -> (CExpr a ectx, CExpr b ectx)
cunpair (CExpr (CPair a b)) = (CExpr a, CExpr b)
-}

cfst :: CExpr (a :*: b) ectx -> CExpr a ectx
cfst = cOp1 cpairFst

csnd :: CExpr (a :*: b) ectx -> CExpr b ectx
csnd = cOp1 cpairSnd

-- | Build a contextual unit expression
cunit :: CExpr CUnit ectx
cunit = CExpr $ const CUnit

-- | Lift an element of a standard type to a contextual expression
cconst :: a -> CExpr (CConst a) ectx
cconst a = CExpr $ const $ CConst a

{-
-- | Un-lift a contextual expression of lifted type to a normal value
cunconst :: CExpr (CConst a) ectx -> a
cunconst (CExpr (CConst a)) = a
-}

cnuH :: Size ctx -> (CVar tp :->: a) ctx -> CNabla tp a ctx
cnuH sz f =
  CNabla $ unCFun f mkWeakening1 (CVar $ nextIndex sz)

-- | Bind a variable in the context of an expression
cnu :: CExprBinder (CVar tp) a ectx -> CExpr (CNabla tp a) ectx
cnu f = CExpr $ \sz -> cnuH sz (unCExpr (clam f) sz)

{-
uncbindVar :: CExpr Size ectx -> CExpr (CNabla tp a) ectx ->
              a (CtxOfExprCtx ectx ::> tp)
uncbindVar (CExpr sz) (CExpr b) = unCNabla b noDiff sz
-}

test1 :: Weakenable a => CExpr (a :->: a) ectx
test1 = clam $ \x -> x

test2 :: (Weakenable a, Weakenable b) =>
         CExpr (a :->: b :->: a) ectx
test2 = clam $ \x -> clam $ \y -> x


----------------------------------------------------------------------
-- * Contextual monads
----------------------------------------------------------------------

-- | Monads over contextual types
class Weakenable1 m => CMonad (m :: CType k -> CType k) where
  creturn :: Weakenable a => CExpr (a :->: m a) ctx
  cbind :: (Weakenable a, Weakenable b) =>
           CExpr (m a :->: (a :->: m b) :->: m b) ctx

-- | More traditional bind syntax for 'cbind'
infixl 1 >>>=
(>>>=) :: (CMonad m, Weakenable a, Weakenable b) =>
          CExpr (m a) ectx ->
          CExprBinder a (m b) ectx ->
          CExpr (m b) ectx
m >>>= f = cbind @@ m @@ clam f


-- | Contextual monad transformers
class CMonadTrans (t :: (CType k -> CType k) -> CType k -> CType k) where
  clift :: (CMonad m, Weakenable a) => CExpr (m a :->: t m a) ectx

instance Monad m => CMonad ((:@:) m) where
  creturn = clam $ \x -> cOp1 (CApplyF . return) x
  cbind = clam $ \m -> clam $ \f ->
    cOp2 (\m' f' ->
           CApplyF (unCApplyF m' >>= unCApplyF . unCFun f' Cat.id)) m f


-- | The contextual continuation transformer
newtype CContT res m a (ctx :: Ctx k) =
  CContT { unCContT :: ((a :->: m res) :->: m res) ctx }

instance (Weakenable1 m, Weakenable res) =>
         Weakenable1 (CContT res m) where
  weaken1 w sz (CContT m) = CContT $ weaken w sz m

instance (CMonad m, Weakenable res) => CMonad (CContT res m) where
  creturn =
    clam $ \a -> cOp1 CContT $ clam $ \k -> k @@ a
  cbind =
    clam $ \m -> clam $ \f ->
    cOp1 CContT $ clam $ \k ->
    (cOp1 unCContT m) $$ clam $ \a ->
    cOp1 unCContT (f @@ a) @@ k

instance Weakenable res => CMonadTrans (CContT res) where
  clift = clam $ \m -> cOp1 CContT $ clam $ \k -> m >>>= \a -> k @@ a

-- | Contextual monads that support shift and reset
class (Weakenable res, CMonad m) => CMonadShiftReset res m | m -> res where
  cshift :: Weakenable a => CExpr (((a :->: m res) :->: m res) :->: m a) ctx
  creset :: CExpr (m res :->: m res) ctx

instance (CMonad m, Weakenable res) => CMonadShiftReset res (CContT res m) where
  cshift =
    clam $ \f ->
    cOp1 CContT $ clam $ \k ->
    cOp1 unCContT (f @@ (clam $ \a -> clift @@ (k @@ a))) @@
    (clam $ \res -> creturn @@ res)
  creset =
    clam $ \m ->
    cOp1 CContT $ clam $ \k ->
    cOp1 unCContT m @@ (clam $ \res -> creturn @@ res) >>>= \a -> k @@ a


-- | The contextual state transformer
newtype CStateT s m a (ctx :: Ctx k) =
  CStateT { unCStateT :: (s :->: m (s :*: a)) ctx }

instance (Weakenable1 m, Weakenable s) =>
         Weakenable1 (CStateT s m) where
  weaken1 w sz (CStateT m) = CStateT $ weaken w sz m

instance (CMonad m, Weakenable s) => CMonad (CStateT s m) where
  creturn =
    clam $ \a -> cOp1 CStateT $ clam $ \s -> creturn @@ (cpair s a)
  cbind =
    clam $ \m -> clam $ \f ->
    cOp1 CStateT $ clam $ \s ->
    cOp1 unCStateT m @@ s >>>= \s'a ->
    (cOp1 unCStateT $ f @@ (csnd s'a)) @@ (cfst s'a)

instance Weakenable s => CMonadTrans (CStateT s) where
  clift =
    clam $ \m ->
    cOp1 CStateT $ clam $ \s ->
    m >>>= \a -> creturn @@ (cpair s a)

-- | Contextual state monads
class CMonad m => CMonadState s m where
  cget :: CExpr (m s) ectx
  cput :: CExpr (s :->: m CUnit) ectx

instance (CMonad m, Weakenable s) => CMonadState s (CStateT s m) where
  cget =
    cOp1 CStateT $ clam $ \s -> creturn @@ (cpair s s)
  cput =
    clam $ \s -> cOp1 CStateT $ clam $ \_ -> creturn @@ (cpair s cunit)

instance (Weakenable s, CMonadShiftReset res m) =>
         CMonadShiftReset res (CStateT s m) where
  -- FIXME: understand what shift does to the state...
  cshift =
    clam $ \f ->
    cOp1 CStateT $ clam $ \s ->
    cshift $$ clam $ \k ->
    (cOp1 unCStateT $ f $$ clam $ \a ->
      cget >>>= \s' ->
      clift @@ (k @@ (cpair s' a))) @@ s >>>= \s_res ->
    creturn @@ (csnd s_res)

  -- NOTE: reset throws away the inner state
  creset =
    clam $ \m ->
    cOp1 CStateT $ clam $ \s ->
    creset @@ (cOp1 unCStateT m @@ s >>>= \s_res ->
                creturn @@ (csnd s_res)) >>>= \res' ->
    creturn @@ (cpair s res')
