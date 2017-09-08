{-# LANGUAGE CPP #-}
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

{- |
Module      : Verifier.SAW.Conversion
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Conversion
  ( (:*:)(..)
  , Net.toPat
  , termToPat
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
  , mkBvNat
    -- * Conversion
  , Conversion(..)
  , runConversion
    -- ** Prelude conversions
  , tupleConversion
  , recordConversion
  , eq_Tuple
  , eq_Record
  , natConversions
  , vecConversions
  , bvConversions
  , succ_NatLit
  , addNat_NatLit
  , append_VecLit
  , append_bvNat
  , bvAdd_bvNat
  , bvSub_bvNat
  , bvule_bvNat
  , bvult_bvNat
  , bvsle_bvNat
  , bvslt_bvNat
  , slice_bvNat
  , remove_coerce
  , remove_unsafeCoerce
  , remove_ident_coerce
  , remove_ident_unsafeCoerce
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative(..), (<$>), (<*>))
#endif
import Control.Lens (view, _1, _2)
import Control.Monad (ap, liftM, liftM2, unless, (>=>), (<=<))
import Data.Bits
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.Recognizer ((:*:)(..))
import Verifier.SAW.Prim
import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.Term.Functor

-- | A hack to allow storage of conversions in a term net.
instance Eq (Conversion t) where
    x == y = Net.toPat x == Net.toPat y

instance Show (Conversion t) where
    show x = show (Net.toPat x)

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
               -- Given a term, matches arguments to temr.
            => Matcher m t [t]
            -> v m t a
            -> Matcher m t a
resolveArgs (Matcher p m) (defaultArgsMatcher -> args@(ArgsMatcher pl _)) =
  Matcher (foldl Net.App p pl) (m >=> runArgsMatcher args)

----------------------------------------------------------------------
-- Term matchers

-- | Match a global definition.
asGlobalDef :: (Monad m) => Ident -> Matcher m Term ()
asGlobalDef ident = Matcher (Net.Atom (identName ident)) f
  where f (R.asGlobalDef -> Just o) | ident == o = return ()
        f _ = fail (show ident ++ " match failed.")

infixl 8 <:>

-- | Match an application
(<:>) :: (Applicative m, Monad m)
      => Matcher m Term a -> Matcher m Term b -> Matcher m Term (a :*: b)
(<:>) (Matcher p1 f1) (Matcher p2 f2) = Matcher (Net.App p1 p2) match
    where
      match (unwrapTermF -> App t1 t2) = liftM2 (:*:) (f1 t1) (f2 t2)
      match _ = fail "internal: <:> net failed"

-- | Match an application and return second term.
(<:>>) :: (Applicative m, Monad m)
       => Matcher m Term a -> Matcher m Term b -> Matcher m Term b
x <:>> y = fmap (view _2) $ x <:> y


-- | Matches any tuple.
asAnyTupleValue :: (Monad m) => Matcher m Term [Term]
asAnyTupleValue = asVar R.asTupleValue

-- | Matches a tuple with arguments matching constraints.
asTupleValue :: (Monad m, ArgsMatchable v m Term a)
             => v m Term a -> Matcher m Term a
asTupleValue (defaultArgsMatcher -> m) = asVar $ \t -> do
  l <- R.asTupleValue t
  runArgsMatcher m l

-- | Matches the type of any tuple.
asAnyTupleType :: (Monad m) => Matcher m Term [Term]
asAnyTupleType = asVar R.asTupleType

-- | Matches a tuple type with arguments matching constraints.
asTupleType :: (Monad m, ArgsMatchable v m Term a)
             => v m Term a -> Matcher m Term a
asTupleType (defaultArgsMatcher -> m) = asVar $ \t -> do
  l <- R.asTupleType t
  runArgsMatcher m l

asTupleSelector :: (Functor m, Monad m)
                => Matcher m Term a -> Matcher m Term (a, Int)
asTupleSelector m = asVar $ \t -> _1 (runMatcher m) =<< R.asTupleSelector t

-- | Matches record values, and returns fields.
asAnyRecordValue :: (Monad m) => Matcher m Term (Map FieldName Term)
asAnyRecordValue = asVar R.asRecordValue

-- | Matches record types, and returns fields.
asAnyRecordType :: (Monad m) => Matcher m Term (Map FieldName Term)
asAnyRecordType = asVar R.asRecordType

-- | Matches
asRecordSelector :: (Functor m, Monad m)
                 => Matcher m Term a
                 -> Matcher m Term (a, FieldName)
asRecordSelector m = asVar $ \t -> _1 (runMatcher m) =<< R.asRecordSelector t

--TODO: RecordSelector

-- | Match a constructor
asCtor :: (Monad m, ArgsMatchable v m Term a)
       => Ident -> v m Term a -> Matcher m Term a
asCtor o = resolveArgs $ Matcher (Net.Atom (identName o)) match
  where match t = do
          CtorApp c l <- R.asFTermF t
          unless (c == o) $ fail $ "not " ++ show o
          return l

-- | Match a datatype.
asDataType :: (Monad m, ArgsMatchable v m Term a)
           => Ident -> v m Term a -> Matcher m Term a
asDataType o = resolveArgs $ Matcher (Net.Atom (identName o)) match
  where match t = do
          DataTypeApp dt l <- R.asFTermF t
          unless (dt == o) $ fail $ "not " ++ show o
          return l

-- | Match any sort.
asAnySort :: (Monad m) => Matcher m Term Sort
asAnySort = asVar $ \t -> do Sort v <- R.asFTermF t; return v

-- | Match a specific sort.
asSort :: (Monad m) => Sort -> Matcher m Term ()
asSort s = Matcher (termToPat (Unshared (FTermF (Sort s)))) fn
  where fn t = do s' <- R.asSort t
                  unless (s == s') $ fail "Does not matched expected sort."

-- | Match a Nat literal
asAnyNatLit :: (Monad m) => Matcher m Term Prim.Nat
asAnyNatLit = asVar $ \t -> do NatLit i <- R.asFTermF t; return (fromInteger i)

-- | Match a Vec literal
asAnyVecLit :: (Monad m) => Matcher m Term (Term, V.Vector Term)
asAnyVecLit = asVar $ \t -> do ArrayValue u xs <- R.asFTermF t; return (u,xs)

-- | Match a Float literal
asAnyFloatLit :: (Monad m) => Matcher m Term Float
asAnyFloatLit = asVar $ \t -> do FloatLit i <- R.asFTermF t; return i

-- | Match a Double literal
asAnyDoubleLit :: (Monad m) => Matcher m Term Double
asAnyDoubleLit = asVar $ \t -> do DoubleLit i <- R.asFTermF t; return i

-- | Match any external constant.
asExtCns :: (Monad m) => Matcher m Term (ExtCns Term)
asExtCns = asVar $ \t -> do ExtCns ec <- R.asFTermF t; return ec

-- | Returns index of local var if any.
asLocalVar :: (Monad m) => Matcher m Term DeBruijnIndex
asLocalVar = asVar $ \t -> do i <- R.asLocalVar t; return i

----------------------------------------------------------------------
-- Prelude matchers

asBoolType :: (Monad m) => Matcher m Term ()
asBoolType = asDataType "Prelude.Bool" asEmpty

asSuccLit :: (Functor m, Monad m) => Matcher m Term Prim.Nat
asSuccLit = asCtor "Prelude.Succ" asAnyNatLit

asBvNatLit :: (Applicative m, Monad m) => Matcher m Term Prim.BitVector
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

instance (Monad m) => Matchable m Term Prim.Nat where
    defaultMatcher = asAnyNatLit

instance (Functor m, Monad m) => Matchable m Term Integer where
    defaultMatcher = toInteger <$> asAnyNatLit

instance (Monad m) => Matchable m Term Int where
    defaultMatcher = thenMatcher asAnyNatLit (checkedIntegerToNonNegInt . toInteger)

instance (Applicative m, Monad m) => Matchable m Term Prim.BitVector where
    defaultMatcher = asBvNatLit

instance (Functor m, Monad m) => Matchable m Term (Prim.Vec Term Term) where
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
  mkTermF (App x y)

pureApp :: TermBuilder t t -> t -> TermBuilder t t
pureApp mx y = do
  x <- mx
  mkTermF (App x y)

mkTuple :: [TermBuilder t t] -> TermBuilder t t
mkTuple []       = mkTermF (FTermF UnitValue)
mkTuple (t : ts) = mkTermF . FTermF =<< (PairValue <$> t <*> mkTuple ts)

mkTupleSelector :: Int -> t -> TermBuilder t t
mkTupleSelector i t
  | i == 1 = mkTermF (FTermF (PairLeft t))
  | i > 1  = mkTermF (FTermF (PairRight t)) >>= mkTupleSelector (i - 1)
  | otherwise = fail "mkTupleSelector: non-positive index"

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

instance (Matchable Maybe Term a, Conversionable Term b) => Conversionable Term (a -> b) where
    convOfMatcher m = convOfMatcher
        (thenMatcher (m <:> defaultMatcher) (\(f :*: x) -> Just (f x)))

instance Buildable t a => Conversionable t (Maybe a) where
    convOfMatcher m = Conversion (thenMatcher m (fmap defaultBuilder))

defaultConvOfMatcher :: Buildable t a => Matcher Maybe t a -> Conversion t
defaultConvOfMatcher m = Conversion (thenMatcher m (Just . defaultBuilder))

instance Conversionable t t where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Term Bool where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Term Nat where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Term Integer where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Term Prim.BitVector where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Term (Prim.Vec Term Term) where
    convOfMatcher = defaultConvOfMatcher

instance (Buildable Term a, Buildable Term b) => Conversionable Term (a, b) where
    convOfMatcher = defaultConvOfMatcher

globalConv :: (Conversionable Term a) => Ident -> a -> Conversion Term
globalConv ident f = convOfMatcher (thenMatcher (asGlobalDef ident) (const (Just f)))

----------------------------------------------------------------------
-- Conversions for Prelude operations

-- | Conversion for selector on a tuple
tupleConversion :: Conversion Term
tupleConversion = Conversion $ thenMatcher (asTupleSelector asAnyTupleValue) action
  where action (ts, i) = Just (return (ts !! (i - 1)))

-- | Conversion for selector on a record
recordConversion :: Conversion Term
recordConversion = Conversion $ thenMatcher (asRecordSelector asAnyRecordValue) action
  where action (m, i) = fmap return (Map.lookup i m)

-- | Conversion for equality on tuple types
eq_Tuple :: Conversion Term
eq_Tuple = Conversion $ thenMatcher matcher action
  where
    matcher = asGlobalDef "Prelude.eq" <:> asAnyTupleType <:> asAny <:> asAny
    action (_ :*: ts :*: x :*: y) =
      Just (foldr mkAnd mkTrue (map mkEq (zip [1 ..] ts)))
      where
        mkAnd t1 t2 = mkGlobalDef "Prelude.and" `mkApp` t1 `mkApp` t2
        mkTrue = mkTermF (FTermF (CtorApp "Prelude.True" []))
        mkEq (i, t) = mkGlobalDef "Prelude.eq"
                      `mkApp` return t
                      `mkApp` mkTupleSelector i x
                      `mkApp` mkTupleSelector i y

-- | Conversion for equality on record types
eq_Record :: Conversion Term
eq_Record = Conversion $ thenMatcher matcher action
  where
    matcher = asGlobalDef "Prelude.eq" <:> asAnyRecordType <:> asAny <:> asAny
    action (_ :*: tm :*: x :*: y) =
      Just (foldr mkAnd mkTrue (map mkEq (Map.assocs tm)))
      where
        mkAnd t1 t2 = mkGlobalDef "Prelude.and" `mkApp` t1 `mkApp` t2
        mkTrue = mkTermF (FTermF (CtorApp "Prelude.True" []))
        sel t i = mkTermF . FTermF . RecordSelector t =<< mkTermF (FTermF (StringLit i))
        mkEq (i, t) = mkGlobalDef "Prelude.eq"
                      `mkApp` return t
                      `mkApp` sel x i
                      `mkApp` sel y i

-- | Conversions for operations on Nat literals
natConversions :: [Conversion Term]
natConversions = [ succ_NatLit, addNat_NatLit, subNat_NatLit, mulNat_NatLit
                 , expNat_NatLit, divNat_NatLit, remNat_NatLit, equalNat_NatLit
                 ]

succ_NatLit :: Conversion Term
succ_NatLit =
    Conversion $ thenMatcher asSuccLit (\n -> return $ mkNatLit (n + 1))

addNat_NatLit :: Conversion Term
addNat_NatLit = globalConv "Prelude.addNat" ((+) :: Nat -> Nat -> Nat)

subNat_NatLit :: Conversion Term
subNat_NatLit = Conversion $
  thenMatcher (asGlobalDef "Prelude.subNat" <:> asAnyNatLit <:> asAnyNatLit)
    (\(_ :*: x :*: y) -> if x >= y then Just (mkNatLit (x - y)) else Nothing)

mulNat_NatLit :: Conversion Term
mulNat_NatLit = globalConv "Prelude.mulNat" ((*) :: Nat -> Nat -> Nat)

expNat_NatLit :: Conversion Term
expNat_NatLit = globalConv "Prelude.expNat" ((^) :: Nat -> Nat -> Nat)

divNat_NatLit :: Conversion Term
divNat_NatLit = Conversion $
  thenMatcher (asGlobalDef "Prelude.divNat" <:> asAnyNatLit <:> asAnyNatLit)
    (\(_ :*: x :*: y) ->
         if y /= 0 then Just (mkNatLit (x `div` y)) else Nothing)

remNat_NatLit :: Conversion Term
remNat_NatLit = Conversion $
  thenMatcher (asGlobalDef "Prelude.remNat" <:> asAnyNatLit <:> asAnyNatLit)
    (\(_ :*: x :*: y) ->
         if y /= 0 then Just (mkNatLit (x `rem` y)) else Nothing)

equalNat_NatLit :: Conversion Term
equalNat_NatLit = globalConv "Prelude.equalNat" ((==) :: Nat -> Nat -> Bool)

-- | Conversions for operations on vector literals
vecConversions :: [Conversion Term]
vecConversions = [at_VecLit, atWithDefault_VecLit, append_VecLit]

at_VecLit :: Conversion Term
at_VecLit = globalConv "Prelude.at"
    (Prim.at :: Int -> Term -> Prim.Vec Term Term -> Int -> Term)

atWithDefault_VecLit :: Conversion Term
atWithDefault_VecLit = globalConv "Prelude.atWithDefault"
    (Prim.atWithDefault :: Int -> Term -> Term -> Prim.Vec Term Term -> Int -> Term)

append_VecLit :: Conversion Term
append_VecLit = globalConv "Prelude.append"
    (Prim.append :: Int -> Int -> Term -> Prim.Vec Term Term -> Prim.Vec Term Term -> Prim.Vec Term Term)


-- | Conversions for operations on bitvector literals
bvConversions :: [Conversion Term]
bvConversions =
    [ globalConv "Prelude.bvToNat" Prim.bvToNat
    , append_bvNat
    , bvAdd_bvNat
    , globalConv "Prelude.bvAddWithCarry" Prim.bvAddWithCarry
    , bvSub_bvNat
    , globalConv "Prelude.bvNeg"  Prim.bvNeg
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
    , globalConv "Prelude.bvEq"   Prim.bvEq

    , bvugt_bvNat, bvuge_bvNat, bvult_bvNat, bvule_bvNat
    , bvsgt_bvNat, bvsge_bvNat, bvsle_bvNat, bvslt_bvNat

    , globalConv "Prelude.bvTrunc" Prim.bvTrunc
    , globalConv "Prelude.bvUExt"  Prim.bvUExt
    , globalConv "Prelude.bvSExt"  Prim.bvSExt

    , at_bvNat, atWithDefault_bvNat, slice_bvNat
    , take_bvNat, drop_bvNat
    ]

append_bvNat :: Conversion Term
append_bvNat = globalConv "Prelude.append" Prim.append_bv

bvAdd_bvNat :: Conversion Term
bvAdd_bvNat = globalConv "Prelude.bvAdd" Prim.bvAdd

bvSub_bvNat :: Conversion Term
bvSub_bvNat = globalConv "Prelude.bvSub" Prim.bvSub

bvugt_bvNat, bvuge_bvNat, bvult_bvNat, bvule_bvNat :: Conversion Term
bvugt_bvNat = globalConv "Prelude.bvugt" Prim.bvugt
bvuge_bvNat = globalConv "Prelude.bvuge" Prim.bvuge
bvult_bvNat = globalConv "Prelude.bvult" Prim.bvult
bvule_bvNat = globalConv "Prelude.bvule" Prim.bvule

bvsgt_bvNat, bvsge_bvNat, bvslt_bvNat, bvsle_bvNat :: Conversion Term
bvsgt_bvNat = globalConv "Prelude.bvsgt" Prim.bvsgt
bvsge_bvNat = globalConv "Prelude.bvsge" Prim.bvsge
bvslt_bvNat = globalConv "Prelude.bvslt" Prim.bvslt
bvsle_bvNat = globalConv "Prelude.bvsle" Prim.bvsle

at_bvNat :: Conversion Term
at_bvNat = globalConv "Prelude.at" Prim.at_bv

atWithDefault_bvNat :: Conversion Term
atWithDefault_bvNat =
  Conversion $
  (\(_ :*: n :*: a :*: d :*: x :*: i) ->
    if fromIntegral i < width x then mkBool (Prim.at_bv n a x i) else return d) <$>
  (asGlobalDef "Prelude.atWithDefault" <:>
   defaultMatcher <:> defaultMatcher <:> asAny <:> asBvNatLit <:> asAnyNatLit)

take_bvNat :: Conversion Term
take_bvNat = globalConv "Prelude.take" Prim.take_bv

drop_bvNat :: Conversion Term
drop_bvNat = globalConv "Prelude.drop" Prim.drop_bv

slice_bvNat :: Conversion Term
slice_bvNat = globalConv "Prelude.slice" Prim.slice_bv

mixfix_snd :: (a :*: b) -> b
mixfix_snd (_ :*: y) = y

remove_coerce :: Conversion Term
remove_coerce = Conversion $
  return . mixfix_snd <$>
    (asGlobalDef "Prelude.coerce" <:> asAny <:> asAny <:> asAny <:> asAny)

remove_unsafeCoerce :: Conversion Term
remove_unsafeCoerce = Conversion $
  return . mixfix_snd <$>
    (asGlobalDef "Prelude.unsafeCoerce" <:> asAny <:> asAny <:> asAny)

remove_ident_coerce :: Conversion Term
remove_ident_coerce = Conversion $ thenMatcher pat action
  where pat = asGlobalDef "Prelude.coerce" <:> asAny <:> asAny <:> asAny <:> asAny
        action (() :*: t :*: f :*: _prf :*: x)
          | alphaEquiv t f = return (return x)
          | otherwise = fail "Cannot remove coerce."

remove_ident_unsafeCoerce :: Conversion Term
remove_ident_unsafeCoerce = Conversion $ thenMatcher pat action
  where pat = asGlobalDef "Prelude.unsafeCoerce" <:> asAny <:> asAny <:> asAny
        action (() :*: t :*: f :*: x)
          | alphaEquiv t f = return (return x)
          | otherwise = fail "Cannot remove unsafeCoerce."
