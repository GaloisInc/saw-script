{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Verifier.SAW.Conversion
  ( (:*:)(..)
  , Net.toPat
  , termToPat
  , Termlike
    -- * Matcher
  , Matcher
  , matcherPat
  , runMatcher
  , thenMatcher
  , asVar
  , asAny
    -- ** Matcher arguments
  , ArgsMatcher(..)
  , ArgsMatchable
  , asEmpty
  , (>:)
  , runArgsMatcher
    -- ** Term matchers
  , asGlobalDef
  , (<:>)
  , (<:>>)
  , asAnyTupleValue
  , asTupleValue
  , asAnyTupleType
  , asTupleType
  , asTupleSelector
  , asAnyRecordValue
  , asAnyRecordType
  , asRecordSelector
  , asCtor
  , asDataType
  , asAnySort
  , asSort
  , asAnyNatLit
  , asAnyVecLit
  , asAnyFloatLit
  , asAnyDoubleLit
  , asExtCns
  , asLocalVar
    -- ** Prelude matchers
  , asBoolType
  , asFinValLit
  , asSuccLit
  , asBvNatLit
    -- ** Matchable typeclass
  , Matchable(..)
    -- ** TermBuilder
  , TermBuilder
  , runTermBuilder
  , mkGlobalDef
  , mkApp
  , pureApp
  , mkTuple
  , mkCtor
  , mkDataType
  , mkNatLit
  , mkVecLit
    -- ** Prelude builders
  , mkBool
  , mkFinVal
  , mkBvNat
    -- * Conversion
  , Conversion(..)
  , runConversion
    -- ** Prelude conversions
  , natConversions
  , finConversions
  , vecConversions
  , bvConversions
  , finInc_FinVal
  , finIncLim_FinVal
  , succ_NatLit
  , addNat_NatLit
  , get_VecLit
  , append_VecLit
  , append_bvNat
  , bvAdd_bvNat
  , bvSub_bvNat
  , bvule_bvNat
  , bvult_bvNat
  , bvsle_bvNat
  , bvslt_bvNat
  , get_bvNat
  , slice_bvNat
  , remove_coerce
  , remove_unsafeCoerce
  ) where

import Control.Applicative (Applicative(..), (<$>), (<*>))
import Control.Lens (view, _1, _2)
import Control.Monad (ap, liftM, liftM2, unless, (>=>), (<=<))
import Data.Bits
import Data.Map (Map)
import qualified Data.Vector as V

import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.Recognizer ((:*:)(..))
import Verifier.SAW.Prim
import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.TypedAST

termToPat :: Termlike t => t -> Net.Pat
termToPat t =
    case unwrapTermF t of
      FTermF (GlobalDef d)      -> Net.Atom (identName d)
      FTermF (Constant d _)     -> Net.Atom (identName d)
      FTermF (Sort s)           -> Net.Atom ('*' : show s)
      FTermF (NatLit n)         -> Net.Atom (show n)
      FTermF (App t1 t2)        -> Net.App (termToPat t1) (termToPat t2)
      FTermF (DataTypeApp c ts) -> foldl Net.App (Net.Atom (identName c)) (map termToPat ts)
      FTermF (CtorApp c ts)     -> foldl Net.App (Net.Atom (identName c)) (map termToPat ts)
      _                         -> Net.Var

instance Net.Pattern Term where
  toPat = termToPat

----------------------------------------------------------------------
-- Matchers for terms

data Matcher m t a = Matcher { matcherPat :: Net.Pat, runMatcher :: t -> m a }

instance Net.Pattern (Matcher m t a) where
    toPat = matcherPat

instance Functor m => Functor (Matcher m t) where
  fmap f (Matcher p m) = Matcher p (fmap f . m)

-- | @thenMatcher 
thenMatcher :: Monad m => Matcher m t a -> (a -> m b) -> Matcher m t b
thenMatcher (Matcher pat match) f = Matcher pat (f <=< match)

asVar :: (t -> m a) -> Matcher m t a
asVar = Matcher Net.Var

asAny :: Applicative m => Matcher m t t
asAny = asVar pure

-- | Match a list of terms as arguments to a term.
-- Note that the pats and arguments are in reverse order.
data ArgsMatcher m t a = ArgsMatcher [Net.Pat] ([t] -> m (a,[t]))

class ArgsMatchable v m t a where
  defaultArgsMatcher :: v m t a -> ArgsMatcher m t a

instance Monad m => ArgsMatchable Matcher m t a where
  defaultArgsMatcher (Matcher p f) = ArgsMatcher [p] match
    where match (h:r) = do v <- f h; return (v,r)
          match [] = fail "empty"

instance ArgsMatchable ArgsMatcher m t a where
  defaultArgsMatcher = id

consArgsMatcher :: (Monad m) => ArgsMatcher m t a -> Matcher m t b -> ArgsMatcher m t (a :*: b)
consArgsMatcher (ArgsMatcher pl f) (Matcher p g) = ArgsMatcher (pl ++ [p]) match
  where match l = do
          (a,l1) <- f l
          case l1 of
            (h:l2) -> do b <- g h; return (a :*: b, l2)
            [] ->  fail "empty"

asEmpty :: (Monad m) => ArgsMatcher m t ()
asEmpty = ArgsMatcher [] (\l -> return ((),l))

infixl 9 >:

-- | @x >: y@ appends @y@ to the list of arguments to match.
(>:) :: (Monad m, ArgsMatchable v m t a) => v m t a -> Matcher m t b -> ArgsMatcher m t (a :*: b)
(>:) = consArgsMatcher . defaultArgsMatcher

runArgsMatcher :: Monad m => ArgsMatcher m t a -> [t] -> m a
runArgsMatcher (ArgsMatcher _ f) l = do
  (v,[]) <- f l
  return v
 
-- | Produces a matcher from an ArgsMatcher and a matcher that yields
-- subterms.
resolveArgs :: (Monad m, ArgsMatchable v m t a)
               -- ^ Given a term, matches arguments to temr.
            => Matcher m t [t] 
            -> v m t a
            -> Matcher m t a
resolveArgs (Matcher p m) (defaultArgsMatcher -> args@(ArgsMatcher pl _)) =
  Matcher (foldl Net.App p pl) (m >=> runArgsMatcher args)

----------------------------------------------------------------------
-- Term matchers

-- | Match a global definition.
asGlobalDef :: (Termlike t, Monad m) => Ident -> Matcher m t ()
asGlobalDef ident = Matcher (Net.Atom (identName ident)) f
  where f (R.asGlobalDef -> Just o) | ident == o = return ()
        f _ = fail (show ident ++ " match failed.")

infixl 8 <:>

-- | Match an application
(<:>) :: (Termlike t, Applicative m, Monad m)
      => Matcher m t a -> Matcher m t b -> Matcher m t (a :*: b)
(<:>) (Matcher p1 f1) (Matcher p2 f2) = Matcher (Net.App p1 p2) match
    where
      match (unwrapTermF -> FTermF (App t1 t2)) = liftM2 (:*:) (f1 t1) (f2 t2)
      match _ = fail "internal: <:> net failed"

-- | Match an application and return second term.
(<:>>) :: (Termlike t, Applicative m, Monad m)
       => Matcher m t a -> Matcher m t b -> Matcher m t b
x <:>> y = fmap (view _2) $ x <:> y


-- | Matches any tuple.
asAnyTupleValue :: (Monad m, Termlike t) => Matcher m t [t]
asAnyTupleValue = asVar $ \t -> do TupleType l <- R.asFTermF t; return l

-- | Matches a tuple with arguments matching constraints.
asTupleValue :: (Monad m, Termlike t, ArgsMatchable v m t a)
             => v m t a -> Matcher m t a
asTupleValue (defaultArgsMatcher -> m) = asVar $ \t -> do
  TupleValue l <- R.asFTermF t
  runArgsMatcher m l

-- | Matches the type of any tuple.
asAnyTupleType :: (Monad m, Termlike t) => Matcher m t [t]
asAnyTupleType = asVar $ \t -> do TupleType l <- R.asFTermF t; return l

-- | Matches a tuple type with arguments matching constraints.
asTupleType :: (Monad m, Termlike t, ArgsMatchable v m t a)
             => v m t a -> Matcher m t a
asTupleType (defaultArgsMatcher -> m) = asVar $ \t -> do
  TupleType l <- R.asFTermF t
  runArgsMatcher m l

asTupleSelector :: (Functor m, Monad m, Termlike t)
                => Matcher m t a -> Matcher m t (a, Int)
asTupleSelector m = asVar $ \t -> _1 (runMatcher m) =<< R.asTupleSelector t

-- | Matches record values, and returns fields.
asAnyRecordValue :: (Monad m, Termlike t) => Matcher m t (Map FieldName t)
asAnyRecordValue = asVar R.asRecordValue

-- | Matches record types, and returns fields.
asAnyRecordType :: (Monad m, Termlike t) => Matcher m t (Map FieldName t)
asAnyRecordType = asVar R.asRecordType

-- | Matches 
asRecordSelector :: (Functor m, Monad m, Termlike t)
                 => Matcher m t a
                 -> Matcher m t (a, FieldName) 
asRecordSelector m = asVar $ \t -> _1 (runMatcher m) =<< R.asRecordSelector t

--TODO: RecordSelector

-- | Match a constructor
asCtor :: (Monad m, Termlike t, ArgsMatchable v m t a)
       => Ident -> v m t a -> Matcher m t a
asCtor o = resolveArgs $ Matcher (Net.Atom (identName o)) match
  where match t = do
          CtorApp c l <- R.asFTermF t
          unless (c == o) $ fail $ "not " ++ show o
          return l

-- | Match a datatype.
asDataType :: (Monad m, Termlike t, ArgsMatchable v m t a)
           => Ident -> v m t a -> Matcher m t a
asDataType o = resolveArgs $ Matcher (Net.Atom (identName o)) match
  where match t = do
          DataTypeApp dt l <- R.asFTermF t
          unless (dt == o) $ fail $ "not " ++ show o
          return l

-- | Match any sort.
asAnySort :: (Termlike t, Monad m) => Matcher m t Sort
asAnySort = asVar $ \t -> do Sort v <- R.asFTermF t; return v

-- | Match a specific sort.
asSort :: (Termlike t, Monad m) => Sort -> Matcher m t ()
asSort s = Matcher (termToPat (Term (FTermF (Sort s)))) fn
  where fn t = do Sort s' <- R.asFTermF t
                  unless (s == s') $ fail "Does not matched expected sort."
            
-- | Match a Nat literal
asAnyNatLit :: (Termlike t, Monad m) => Matcher m t Prim.Nat
asAnyNatLit = asVar $ \t -> do NatLit i <- R.asFTermF t; return (fromInteger i)

-- | Match a Vec literal
asAnyVecLit :: (Termlike t, Monad m) => Matcher m t (t, V.Vector t)
asAnyVecLit = asVar $ \t -> do ArrayValue u xs <- R.asFTermF t; return (u,xs)

-- | Match a Float literal
asAnyFloatLit :: (Termlike t, Monad m) => Matcher m t Float
asAnyFloatLit = asVar $ \t -> do FloatLit i <- R.asFTermF t; return i

-- | Match a Double literal
asAnyDoubleLit :: (Termlike t, Monad m) => Matcher m t Double
asAnyDoubleLit = asVar $ \t -> do DoubleLit i <- R.asFTermF t; return i

-- | Match any external constant.
asExtCns :: (Termlike t, Monad m) => Matcher m t (ExtCns t)
asExtCns = asVar $ \t -> do ExtCns ec <- R.asFTermF t; return ec

-- | Returns index of local var if any.
asLocalVar :: (Termlike t, Monad m) => Matcher m t DeBruijnIndex
asLocalVar = asVar $ \t -> do (i,_) <- R.asLocalVar t; return i

----------------------------------------------------------------------
-- Prelude matchers

asBoolType :: (Monad m, Termlike t) => Matcher m t ()
asBoolType = asDataType "Prelude.Bool" asEmpty

asFinValLit :: (Functor m, Monad m, Termlike t) => Matcher m t Prim.Fin
asFinValLit = (\(i :*: j) -> Prim.FinVal i j)
  <$> asCtor "Prelude.FinVal" (asAnyNatLit >: asAnyNatLit) 

asSuccLit :: (Functor m, Monad m, Termlike t) => Matcher m t Prim.Nat
asSuccLit = asCtor "Prelude.Succ" asAnyNatLit

asBvNatLit :: (Applicative m, Monad m, Termlike t) => Matcher m t Prim.BitVector
asBvNatLit =
  (\(_ :*: n :*: x) -> Prim.bv (fromIntegral n) (toInteger x)) <$>
    (asGlobalDef "Prelude.bvNat" <:> asAnyNatLit <:> asAnyNatLit)

checkedIntegerToNonNegInt :: Monad m => Integer -> m Int
checkedIntegerToNonNegInt x 
  | 0 <= x && x <= toInteger (maxBound :: Int) = return (fromInteger x)
  | otherwise = fail "match out of range"

----------------------------------------------------------------------
-- Matchable

class Matchable m t a where
    defaultMatcher :: Matcher m t a

instance Applicative m => Matchable m t () where
    defaultMatcher = asVar (const (pure ()))

instance Applicative m => Matchable m t t where
    defaultMatcher = asAny

instance (Monad m, Termlike t) => Matchable m t Prim.Nat where
    defaultMatcher = asAnyNatLit

instance (Functor m, Monad m, Termlike t) => Matchable m t Integer where
    defaultMatcher = toInteger <$> asAnyNatLit

instance (Monad m, Termlike t) => Matchable m t Int where
    defaultMatcher = thenMatcher asAnyNatLit (checkedIntegerToNonNegInt . toInteger)

instance (Applicative m, Monad m, Termlike t) => Matchable m t Prim.BitVector where
    defaultMatcher = asBvNatLit

instance (Functor m, Monad m, Termlike t) => Matchable m t Prim.Fin where
    defaultMatcher = asFinValLit

instance (Functor m, Monad m, Termlike t) => Matchable m t (Prim.Vec t t) where
    defaultMatcher = uncurry Prim.Vec <$> asAnyVecLit

----------------------------------------------------------------------
-- Term builders

newtype TermBuilder t v =
    TermBuilder { runTermBuilder :: forall m. Monad m => (TermF t -> m t) -> m v }

instance Monad (TermBuilder t) where
  m >>= h = TermBuilder $ \mk -> do
    r <- runTermBuilder m mk
    runTermBuilder (h r) mk
  return v = TermBuilder $ \_ -> return v

instance Functor (TermBuilder t) where
    fmap = liftM

instance Applicative (TermBuilder t) where
    pure = return
    (<*>) = ap

mkTermF :: TermF t -> TermBuilder t t
mkTermF tf = TermBuilder (\mk -> mk tf)

mkGlobalDef :: Ident -> TermBuilder t t
mkGlobalDef i = mkTermF (FTermF (GlobalDef i))

infixl 9 `mkApp` 
infixl 9 `pureApp`

mkApp :: TermBuilder t t -> TermBuilder t t -> TermBuilder t t
mkApp mx my = do
  x <- mx
  y <- my
  mkTermF (FTermF (App x y))

pureApp :: TermBuilder t t -> t -> TermBuilder t t
pureApp mx y = do
  x <- mx
  mkTermF (FTermF (App x y))

mkTuple :: [TermBuilder t t] -> TermBuilder t t
mkTuple l = mkTermF . FTermF . TupleValue =<< sequence l

mkCtor :: Ident -> [TermBuilder t t] -> TermBuilder t t
mkCtor i l = mkTermF . FTermF . CtorApp i =<< sequence l

mkDataType :: Ident -> [TermBuilder t t] -> TermBuilder t t
mkDataType i l = mkTermF . FTermF . DataTypeApp i =<< sequence l

mkNatLit :: Prim.Nat -> TermBuilder t t
mkNatLit n = mkTermF (FTermF (NatLit (toInteger n)))

mkVecLit :: t -> V.Vector t -> TermBuilder t t
mkVecLit t xs = mkTermF (FTermF (ArrayValue t xs))

mkBool :: Bool -> TermBuilder t t
mkBool True  = mkCtor "Prelude.True" []
mkBool False = mkCtor "Prelude.False" []

mkFinVal :: Prim.Fin -> TermBuilder t t
mkFinVal (Prim.FinVal i j) = mkCtor "Prelude.FinVal" [mkNatLit i, mkNatLit j]

mkBvNat :: Prim.Nat -> Integer -> TermBuilder t t
mkBvNat n x = do
  mkGlobalDef "Prelude.bvNat"
    `mkApp` (mkNatLit n)
    `mkApp` (mkNatLit $ fromInteger $ x .&. bitMask (fromIntegral n))

class Buildable t a where
  defaultBuilder :: a -> TermBuilder t t

instance Buildable t t where
  defaultBuilder = return

instance Buildable t Bool where
  defaultBuilder = mkBool

instance Buildable t Nat where
  defaultBuilder = mkNatLit

instance Buildable t Integer where
  defaultBuilder = mkNatLit . fromInteger

instance Buildable t Int where
  defaultBuilder = mkNatLit . fromIntegral

instance (Buildable t a, Buildable t b) => Buildable t (a, b) where
  defaultBuilder (x, y) = mkTuple [defaultBuilder x, defaultBuilder y]

instance Buildable t Prim.Fin where
  defaultBuilder = mkFinVal

instance Buildable t (Prim.Vec t t) where
  defaultBuilder (Prim.Vec t v) = mkVecLit t v

instance Buildable t Prim.BitVector where
  defaultBuilder (Prim.BV w x) = mkBvNat (fromIntegral w) x

----------------------------------------------------------------------
-- Conversions

-- | These are conversions in the LCF-style term-rewriting sense: A
-- conversion is a function that takes a term and returns (possibly) a
-- rewritten term. We use conversions to model the behavior of
-- primitive operations in SAWCore.

newtype Conversion t = Conversion (Matcher Maybe t (TermBuilder t t))

instance Net.Pattern (Conversion t) where
    toPat (Conversion m) = Net.toPat m

runConversion :: Conversion t -> t -> Maybe (TermBuilder t t)
runConversion (Conversion m) = runMatcher m

-- | This class is meant to include n-ary function types whose
-- arguments are all in class @Matchable t@ and whose result type is
-- in class @Buildable t@. Given a matcher for the global constant
-- itself, we can construct a conversion that applies the function to
-- its arguments and builds the result.

class Conversionable t a where
    convOfMatcher :: Matcher Maybe t a -> Conversion t

instance (Termlike t, Matchable Maybe t a, Conversionable t b) => Conversionable t (a -> b) where
    convOfMatcher m = convOfMatcher
        (thenMatcher (m <:> defaultMatcher) (\(f :*: x) -> Just (f x)))

instance Buildable t a => Conversionable t (Maybe a) where
    convOfMatcher m = Conversion (thenMatcher m (fmap defaultBuilder))

defaultConvOfMatcher :: Buildable t a => Matcher Maybe t a -> Conversion t
defaultConvOfMatcher m = Conversion (thenMatcher m (Just . defaultBuilder))

instance Conversionable t t where
    convOfMatcher = defaultConvOfMatcher

instance Termlike t => Conversionable t Bool where
    convOfMatcher = defaultConvOfMatcher

instance Termlike t => Conversionable t Nat where
    convOfMatcher = defaultConvOfMatcher

instance Termlike t => Conversionable t Integer where
    convOfMatcher = defaultConvOfMatcher

instance Termlike t => Conversionable t Prim.Fin where
    convOfMatcher = defaultConvOfMatcher

instance Termlike t => Conversionable t Prim.BitVector where
    convOfMatcher = defaultConvOfMatcher

instance Termlike t => Conversionable t (Prim.Vec t t) where
    convOfMatcher = defaultConvOfMatcher

instance (Termlike t, Buildable t a, Buildable t b) => Conversionable t (a, b) where
    convOfMatcher = defaultConvOfMatcher

globalConv :: (Termlike t, Conversionable t a) => Ident -> a -> Conversion t
globalConv ident f = convOfMatcher (thenMatcher (asGlobalDef ident) (const (Just f)))

----------------------------------------------------------------------
-- Conversions for Prelude operations

-- | Conversions for operations on Nat literals
natConversions :: Termlike t => [Conversion t]
natConversions = [succ_NatLit, addNat_NatLit, mulNat_NatLit]

succ_NatLit :: Termlike t => Conversion t
succ_NatLit =
    Conversion $ thenMatcher asSuccLit (\n -> return $ mkNatLit (n + 1))

addNat_NatLit :: Termlike t => Conversion t
addNat_NatLit = globalConv "Prelude.addNat" ((+) :: Nat -> Nat -> Nat)

mulNat_NatLit :: Termlike t => Conversion t
mulNat_NatLit = globalConv "Prelude.mulNat" ((*) :: Nat -> Nat -> Nat)

-- | Conversions for operations on Fin literals
finConversions :: Termlike t => [Conversion t]
finConversions = [finInc_FinVal, finIncLim_FinVal]

finInc_FinVal :: Termlike t => Conversion t
finInc_FinVal = globalConv "Prelude.finInc" Prim.finInc

finIncLim_FinVal :: Termlike t => Conversion t
finIncLim_FinVal = globalConv "Prelude.finIncLim" Prim.finIncLim

-- | Conversions for operations on vector literals
vecConversions :: Termlike t => [Conversion t]
vecConversions = [get_VecLit, append_VecLit]

get_VecLit :: forall t. Termlike t => Conversion t
get_VecLit = globalConv "Prelude.get"
    (Prim.get :: Int -> t -> Prim.Vec t t -> Prim.Fin -> t)

append_VecLit :: forall t. Termlike t => Conversion t
append_VecLit = globalConv "Prelude.append"
    (Prim.append :: Int -> Int -> t -> Prim.Vec t t -> Prim.Vec t t -> Prim.Vec t t)


-- | Conversions for operations on bitvector literals
bvConversions :: Termlike t => [Conversion t]
bvConversions =
    [ globalConv "Prelude.bvToNat" Prim.bvToNat
    , append_bvNat
    , bvAdd_bvNat
    , globalConv "Prelude.bvAddWithCarry" Prim.bvAddWithCarry
    , bvSub_bvNat
    , globalConv "Prelude.bvMul"  Prim.bvMul
    , globalConv "Prelude.bvUDiv" Prim.bvUDiv
    , globalConv "Prelude.bvURem" Prim.bvURem
    , globalConv "Prelude.bvSDiv" Prim.bvSDiv
    , globalConv "Prelude.bvSRem" Prim.bvSRem
    , globalConv "Prelude.bvShl"  Prim.bvShl
    , globalConv "Prelude.bvShr"  Prim.bvShr
    , globalConv "Prelude.bvSShr" Prim.bvSShr
    , globalConv "Prelude.bvNot"  Prim.bvNot
    , globalConv "Prelude.bvAnd"  Prim.bvAnd
    , globalConv "Prelude.bvOr"   Prim.bvOr
    , globalConv "Prelude.bvXor"  Prim.bvXor
    , globalConv "Prelude.bvMbit" Prim.bvMbit
    , globalConv "Prelude.bvEq"   Prim.bvEq

    , bvugt_bvNat, bvuge_bvNat, bvult_bvNat, bvule_bvNat
    , bvsgt_bvNat, bvsge_bvNat, bvsle_bvNat, bvslt_bvNat

    , globalConv "Prelude.bvTrunc" Prim.bvTrunc
    , globalConv "Prelude.bvUExt"  Prim.bvUExt
    , globalConv "Prelude.bvSExt"  Prim.bvSExt

    , get_bvNat, slice_bvNat
    , vTake_bvNat, vDrop_bvNat
    ]

append_bvNat :: Termlike t => Conversion t
append_bvNat = globalConv "Prelude.append" Prim.append_bv

bvAdd_bvNat :: Termlike t => Conversion t
bvAdd_bvNat = globalConv "Prelude.bvAdd" Prim.bvAdd

bvSub_bvNat :: Termlike t => Conversion t
bvSub_bvNat = globalConv "Prelude.bvSub" Prim.bvSub

bvugt_bvNat, bvuge_bvNat, bvult_bvNat, bvule_bvNat :: Termlike t => Conversion t
bvugt_bvNat = globalConv "Prelude.bvugt" Prim.bvugt
bvuge_bvNat = globalConv "Prelude.bvuge" Prim.bvuge
bvult_bvNat = globalConv "Prelude.bvult" Prim.bvult
bvule_bvNat = globalConv "Prelude.bvule" Prim.bvule

bvsgt_bvNat, bvsge_bvNat, bvslt_bvNat, bvsle_bvNat :: Termlike t => Conversion t
bvsgt_bvNat = globalConv "Prelude.bvsgt" Prim.bvsgt
bvsge_bvNat = globalConv "Prelude.bvsge" Prim.bvsge
bvslt_bvNat = globalConv "Prelude.bvslt" Prim.bvslt
bvsle_bvNat = globalConv "Prelude.bvsle" Prim.bvsle

get_bvNat :: Termlike t => Conversion t
get_bvNat = globalConv "Prelude.get" Prim.get_bv

vTake_bvNat :: Termlike t => Conversion t
vTake_bvNat = globalConv "Prelude.vTake" Prim.vTake_bv

vDrop_bvNat :: Termlike t => Conversion t
vDrop_bvNat = globalConv "Prelude.vDrop" Prim.vDrop_bv

slice_bvNat :: Termlike t => Conversion t
slice_bvNat = globalConv "Prelude.slice" Prim.slice_bv

mixfix_snd :: (a :*: b) -> b
mixfix_snd (_ :*: y) = y

remove_coerce :: Termlike t => Conversion t
remove_coerce = Conversion $
  return . mixfix_snd <$>
    (asGlobalDef "Prelude.coerce" <:> asAny <:> asAny <:> asAny <:> asAny)
 
remove_unsafeCoerce :: Termlike t => Conversion t
remove_unsafeCoerce = Conversion $
  return . mixfix_snd <$>
    (asGlobalDef "Prelude.unsafeCoerce" <:> asAny <:> asAny <:> asAny)