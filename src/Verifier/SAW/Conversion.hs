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
instance Eq Conversion where
    x == y = Net.toPat x == Net.toPat y

instance Show Conversion where
    show x = show (Net.toPat x)

----------------------------------------------------------------------
-- Matchers for terms

data Matcher m a = Matcher { matcherPat :: Net.Pat, runMatcher :: Term -> m a }

instance Net.Pattern (Matcher m a) where
    toPat = matcherPat

instance Functor m => Functor (Matcher m) where
  fmap f (Matcher p m) = Matcher p (fmap f . m)

-- | @thenMatcher
thenMatcher :: Monad m => Matcher m a -> (a -> m b) -> Matcher m b
thenMatcher (Matcher pat match) f = Matcher pat (f <=< match)

asVar :: (Term -> m a) -> Matcher m a
asVar = Matcher Net.Var

asAny :: Applicative m => Matcher m Term
asAny = asVar pure

-- | Match a list of terms as arguments to a term.
-- Note that the pats and arguments are in reverse order.
data ArgsMatcher m a = ArgsMatcher [Net.Pat] ([Term] -> m (a, [Term]))

class ArgsMatchable v m a where
  defaultArgsMatcher :: v m a -> ArgsMatcher m a

instance Monad m => ArgsMatchable Matcher m a where
  defaultArgsMatcher (Matcher p f) = ArgsMatcher [p] match
    where match (h:r) = do v <- f h; return (v,r)
          match [] = fail "empty"

instance ArgsMatchable ArgsMatcher m a where
  defaultArgsMatcher = id

consArgsMatcher :: (Monad m) => ArgsMatcher m a -> Matcher m b -> ArgsMatcher m (a :*: b)
consArgsMatcher (ArgsMatcher pl f) (Matcher p g) = ArgsMatcher (pl ++ [p]) match
  where match l = do
          (a,l1) <- f l
          case l1 of
            (h:l2) -> do b <- g h; return (a :*: b, l2)
            [] ->  fail "empty"

asEmpty :: (Monad m) => ArgsMatcher m ()
asEmpty = ArgsMatcher [] (\l -> return ((),l))

infixl 9 >:

-- | @x >: y@ appends @y@ to the list of arguments to match.
(>:) :: (Monad m, ArgsMatchable v m a) => v m a -> Matcher m b -> ArgsMatcher m (a :*: b)
(>:) = consArgsMatcher . defaultArgsMatcher

runArgsMatcher :: Monad m => ArgsMatcher m a -> [Term] -> m a
runArgsMatcher (ArgsMatcher _ f) l = do
  (v,[]) <- f l
  return v

-- | Produces a matcher from an ArgsMatcher and a matcher that yields
-- subterms.
resolveArgs :: (Monad m, ArgsMatchable v m a)
               -- Given a term, matches arguments to temr.
            => Matcher m [Term]
            -> v m a
            -> Matcher m a
resolveArgs (Matcher p m) (defaultArgsMatcher -> args@(ArgsMatcher pl _)) =
  Matcher (foldl Net.App p pl) (m >=> runArgsMatcher args)

----------------------------------------------------------------------
-- Term matchers

-- | Match a global definition.
asGlobalDef :: (Monad m) => Ident -> Matcher m ()
asGlobalDef ident = Matcher (Net.Atom (identName ident)) f
  where f (R.asGlobalDef -> Just o) | ident == o = return ()
        f _ = fail (show ident ++ " match failed.")

infixl 8 <:>

-- | Match an application
(<:>) :: (Applicative m, Monad m)
      => Matcher m a -> Matcher m b -> Matcher m (a :*: b)
(<:>) (Matcher p1 f1) (Matcher p2 f2) = Matcher (Net.App p1 p2) match
    where
      match (unwrapTermF -> App t1 t2) = liftM2 (:*:) (f1 t1) (f2 t2)
      match _ = fail "internal: <:> net failed"

-- | Match an application and return second term.
(<:>>) :: (Applicative m, Monad m)
       => Matcher m a -> Matcher m b -> Matcher m b
x <:>> y = fmap (view _2) $ x <:> y


-- | Matches any tuple.
asAnyTupleValue :: (Monad m) => Matcher m [Term]
asAnyTupleValue = asVar R.asTupleValue

-- | Matches a tuple with arguments matching constraints.
asTupleValue :: (Monad m, ArgsMatchable v m a)
             => v m a -> Matcher m a
asTupleValue (defaultArgsMatcher -> m) = asVar $ \t -> do
  l <- R.asTupleValue t
  runArgsMatcher m l

-- | Matches the type of any tuple.
asAnyTupleType :: (Monad m) => Matcher m [Term]
asAnyTupleType = asVar R.asTupleType

-- | Matches a tuple type with arguments matching constraints.
asTupleType :: (Monad m, ArgsMatchable v m a)
             => v m a -> Matcher m a
asTupleType (defaultArgsMatcher -> m) = asVar $ \t -> do
  l <- R.asTupleType t
  runArgsMatcher m l

asTupleSelector :: (Functor m, Monad m)
                => Matcher m a -> Matcher m (a, Int)
asTupleSelector m = asVar $ \t -> _1 (runMatcher m) =<< R.asTupleSelector t

-- | Matches record values, and returns fields.
asAnyRecordValue :: (Monad m) => Matcher m (Map FieldName Term)
asAnyRecordValue = asVar R.asRecordValue

-- | Matches record types, and returns fields.
asAnyRecordType :: (Monad m) => Matcher m (Map FieldName Term)
asAnyRecordType = asVar R.asRecordType

-- | Matches
asRecordSelector :: (Functor m, Monad m)
                 => Matcher m a
                 -> Matcher m (a, FieldName)
asRecordSelector m = asVar $ \t -> _1 (runMatcher m) =<< R.asRecordSelector t

--TODO: RecordSelector

-- | Match a constructor
asCtor :: (Monad m, ArgsMatchable v m a)
       => Ident -> v m a -> Matcher m a
asCtor o = resolveArgs $ Matcher (Net.Atom (identName o)) match
  where match t = do
          CtorApp c l <- R.asFTermF t
          unless (c == o) $ fail $ "not " ++ show o
          return l

-- | Match a datatype.
asDataType :: (Monad m, ArgsMatchable v m a)
           => Ident -> v m a -> Matcher m a
asDataType o = resolveArgs $ Matcher (Net.Atom (identName o)) match
  where match t = do
          DataTypeApp dt l <- R.asFTermF t
          unless (dt == o) $ fail $ "not " ++ show o
          return l

-- | Match any sort.
asAnySort :: (Monad m) => Matcher m Sort
asAnySort = asVar $ \t -> do Sort v <- R.asFTermF t; return v

-- | Match a specific sort.
asSort :: (Monad m) => Sort -> Matcher m ()
asSort s = Matcher (termToPat (Unshared (FTermF (Sort s)))) fn
  where fn t = do s' <- R.asSort t
                  unless (s == s') $ fail "Does not matched expected sort."

-- | Match a Nat literal
asAnyNatLit :: (Monad m) => Matcher m Prim.Nat
asAnyNatLit = asVar $ \t -> do NatLit i <- R.asFTermF t; return (fromInteger i)

-- | Match a Vec literal
asAnyVecLit :: (Monad m) => Matcher m (Term, V.Vector Term)
asAnyVecLit = asVar $ \t -> do ArrayValue u xs <- R.asFTermF t; return (u,xs)

-- | Match any external constant.
asExtCns :: (Monad m) => Matcher m (ExtCns Term)
asExtCns = asVar $ \t -> do ExtCns ec <- R.asFTermF t; return ec

-- | Returns index of local var if any.
asLocalVar :: (Monad m) => Matcher m DeBruijnIndex
asLocalVar = asVar $ \t -> do i <- R.asLocalVar t; return i

----------------------------------------------------------------------
-- Prelude matchers

asBoolType :: (Monad m) => Matcher m ()
asBoolType = asDataType "Prelude.Bool" asEmpty

asSuccLit :: (Functor m, Monad m) => Matcher m Prim.Nat
asSuccLit = asCtor "Prelude.Succ" asAnyNatLit

asBvNatLit :: (Applicative m, Monad m) => Matcher m Prim.BitVector
asBvNatLit =
  (\(_ :*: n :*: x) -> Prim.bv (fromIntegral n) (toInteger x)) <$>
    (asGlobalDef "Prelude.bvNat" <:> asAnyNatLit <:> asAnyNatLit)

checkedIntegerToNonNegInt :: Monad m => Integer -> m Int
checkedIntegerToNonNegInt x
  | 0 <= x && x <= toInteger (maxBound :: Int) = return (fromInteger x)
  | otherwise = fail "match out of range"

----------------------------------------------------------------------
-- Matchable

class Matchable m a where
    defaultMatcher :: Matcher m a

instance Applicative m => Matchable m () where
    defaultMatcher = asVar (const (pure ()))

instance Applicative m => Matchable m Term where
    defaultMatcher = asAny

instance (Monad m) => Matchable m Prim.Nat where
    defaultMatcher = asAnyNatLit

instance (Functor m, Monad m) => Matchable m Integer where
    defaultMatcher = toInteger <$> asAnyNatLit

instance (Monad m) => Matchable m Int where
    defaultMatcher = thenMatcher asAnyNatLit (checkedIntegerToNonNegInt . toInteger)

instance (Applicative m, Monad m) => Matchable m Prim.BitVector where
    defaultMatcher = asBvNatLit

instance (Functor m, Monad m) => Matchable m (Prim.Vec Term Term) where
    defaultMatcher = uncurry Prim.Vec <$> asAnyVecLit

----------------------------------------------------------------------
-- Term builders

newtype TermBuilder v =
    TermBuilder { runTermBuilder :: forall m. Monad m => (TermF Term -> m Term) -> m v }

instance Monad TermBuilder where
  m >>= h = TermBuilder $ \mk -> do
    r <- runTermBuilder m mk
    runTermBuilder (h r) mk
  return v = TermBuilder $ \_ -> return v

instance Functor TermBuilder where
    fmap = liftM

instance Applicative TermBuilder where
    pure = return
    (<*>) = ap

mkTermF :: TermF Term -> TermBuilder Term
mkTermF tf = TermBuilder (\mk -> mk tf)

mkGlobalDef :: Ident -> TermBuilder Term
mkGlobalDef i = mkTermF (FTermF (GlobalDef i))

infixl 9 `mkApp`
infixl 9 `pureApp`

mkApp :: TermBuilder Term -> TermBuilder Term -> TermBuilder Term
mkApp mx my = do
  x <- mx
  y <- my
  mkTermF (App x y)

pureApp :: TermBuilder Term -> Term -> TermBuilder Term
pureApp mx y = do
  x <- mx
  mkTermF (App x y)

mkTuple :: [TermBuilder Term] -> TermBuilder Term
mkTuple []       = mkTermF (FTermF UnitValue)
mkTuple (t : ts) = mkTermF . FTermF =<< (PairValue <$> t <*> mkTuple ts)

mkTupleSelector :: Int -> Term -> TermBuilder Term
mkTupleSelector i t
  | i == 1 = mkTermF (FTermF (PairLeft t))
  | i > 1  = mkTermF (FTermF (PairRight t)) >>= mkTupleSelector (i - 1)
  | otherwise = fail "mkTupleSelector: non-positive index"

mkCtor :: Ident -> [TermBuilder Term] -> TermBuilder Term
mkCtor i l = mkTermF . FTermF . CtorApp i =<< sequence l

mkDataType :: Ident -> [TermBuilder Term] -> TermBuilder Term
mkDataType i l = mkTermF . FTermF . DataTypeApp i =<< sequence l

mkNatLit :: Prim.Nat -> TermBuilder Term
mkNatLit n = mkTermF (FTermF (NatLit (toInteger n)))

mkVecLit :: Term -> V.Vector Term -> TermBuilder Term
mkVecLit t xs = mkTermF (FTermF (ArrayValue t xs))

mkBool :: Bool -> TermBuilder Term
mkBool True  = mkCtor "Prelude.True" []
mkBool False = mkCtor "Prelude.False" []

mkBvNat :: Prim.Nat -> Integer -> TermBuilder Term
mkBvNat n x = do
  mkGlobalDef "Prelude.bvNat"
    `mkApp` (mkNatLit n)
    `mkApp` (mkNatLit $ fromInteger $ x .&. bitMask (fromIntegral n))

class Buildable a where
  defaultBuilder :: a -> TermBuilder Term

instance Buildable Term where
  defaultBuilder = return

instance Buildable Bool where
  defaultBuilder = mkBool

instance Buildable Nat where
  defaultBuilder = mkNatLit

instance Buildable Integer where
  defaultBuilder = mkNatLit . fromInteger

instance Buildable Int where
  defaultBuilder = mkNatLit . fromIntegral

instance (Buildable a, Buildable b) => Buildable (a, b) where
  defaultBuilder (x, y) = mkTuple [defaultBuilder x, defaultBuilder y]

instance Buildable (Prim.Vec Term Term) where
  defaultBuilder (Prim.Vec t v) = mkVecLit t v

instance Buildable Prim.BitVector where
  defaultBuilder (Prim.BV w x) = mkBvNat (fromIntegral w) x

----------------------------------------------------------------------
-- Conversions

-- | These are conversions in the LCF-style term-rewriting sense: A
-- conversion is a function that takes a term and returns (possibly) a
-- rewritten term. We use conversions to model the behavior of
-- primitive operations in SAWCore.

newtype Conversion = Conversion (Matcher Maybe (TermBuilder Term))

instance Net.Pattern Conversion where
    toPat (Conversion m) = Net.toPat m

runConversion :: Conversion -> Term -> Maybe (TermBuilder Term)
runConversion (Conversion m) = runMatcher m

-- | This class is meant to include n-ary function types whose
-- arguments are all in class @Matchable m@ and whose result type is
-- in class @Buildable@. Given a matcher for the global constant
-- itself, we can construct a conversion that applies the function to
-- its arguments and builds the result.

class Conversionable a where
    convOfMatcher :: Matcher Maybe a -> Conversion

instance (Matchable Maybe a, Conversionable b) => Conversionable (a -> b) where
    convOfMatcher m = convOfMatcher
        (thenMatcher (m <:> defaultMatcher) (\(f :*: x) -> Just (f x)))

instance Buildable a => Conversionable (Maybe a) where
    convOfMatcher m = Conversion (thenMatcher m (fmap defaultBuilder))

defaultConvOfMatcher :: Buildable a => Matcher Maybe a -> Conversion
defaultConvOfMatcher m = Conversion (thenMatcher m (Just . defaultBuilder))

instance Conversionable Term where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Bool where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Nat where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Integer where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Prim.BitVector where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable (Prim.Vec Term Term) where
    convOfMatcher = defaultConvOfMatcher

instance (Buildable a, Buildable b) => Conversionable (a, b) where
    convOfMatcher = defaultConvOfMatcher

globalConv :: (Conversionable a) => Ident -> a -> Conversion
globalConv ident f = convOfMatcher (thenMatcher (asGlobalDef ident) (const (Just f)))

----------------------------------------------------------------------
-- Conversions for Prelude operations

-- | Conversion for selector on a tuple
tupleConversion :: Conversion
tupleConversion = Conversion $ thenMatcher (asTupleSelector asAnyTupleValue) action
  where action (ts, i) = Just (return (ts !! (i - 1)))

-- | Conversion for selector on a record
recordConversion :: Conversion
recordConversion = Conversion $ thenMatcher (asRecordSelector asAnyRecordValue) action
  where action (m, i) = fmap return (Map.lookup i m)

-- | Conversion for equality on tuple types
eq_Tuple :: Conversion
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
eq_Record :: Conversion
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
natConversions :: [Conversion]
natConversions = [ succ_NatLit, addNat_NatLit, subNat_NatLit, mulNat_NatLit
                 , expNat_NatLit, divNat_NatLit, remNat_NatLit, equalNat_NatLit
                 ]

succ_NatLit :: Conversion
succ_NatLit =
    Conversion $ thenMatcher asSuccLit (\n -> return $ mkNatLit (n + 1))

addNat_NatLit :: Conversion
addNat_NatLit = globalConv "Prelude.addNat" ((+) :: Nat -> Nat -> Nat)

subNat_NatLit :: Conversion
subNat_NatLit = Conversion $
  thenMatcher (asGlobalDef "Prelude.subNat" <:> asAnyNatLit <:> asAnyNatLit)
    (\(_ :*: x :*: y) -> if x >= y then Just (mkNatLit (x - y)) else Nothing)

mulNat_NatLit :: Conversion
mulNat_NatLit = globalConv "Prelude.mulNat" ((*) :: Nat -> Nat -> Nat)

expNat_NatLit :: Conversion
expNat_NatLit = globalConv "Prelude.expNat" ((^) :: Nat -> Nat -> Nat)

divNat_NatLit :: Conversion
divNat_NatLit = Conversion $
  thenMatcher (asGlobalDef "Prelude.divNat" <:> asAnyNatLit <:> asAnyNatLit)
    (\(_ :*: x :*: y) ->
         if y /= 0 then Just (mkNatLit (x `div` y)) else Nothing)

remNat_NatLit :: Conversion
remNat_NatLit = Conversion $
  thenMatcher (asGlobalDef "Prelude.remNat" <:> asAnyNatLit <:> asAnyNatLit)
    (\(_ :*: x :*: y) ->
         if y /= 0 then Just (mkNatLit (x `rem` y)) else Nothing)

equalNat_NatLit :: Conversion
equalNat_NatLit = globalConv "Prelude.equalNat" ((==) :: Nat -> Nat -> Bool)

-- | Conversions for operations on vector literals
vecConversions :: [Conversion]
vecConversions = [at_VecLit, atWithDefault_VecLit, append_VecLit]

at_VecLit :: Conversion
at_VecLit = globalConv "Prelude.at"
    (Prim.at :: Int -> Term -> Prim.Vec Term Term -> Int -> Term)

atWithDefault_VecLit :: Conversion
atWithDefault_VecLit = globalConv "Prelude.atWithDefault"
    (Prim.atWithDefault :: Int -> Term -> Term -> Prim.Vec Term Term -> Int -> Term)

append_VecLit :: Conversion
append_VecLit = globalConv "Prelude.append"
    (Prim.append :: Int -> Int -> Term -> Prim.Vec Term Term -> Prim.Vec Term Term -> Prim.Vec Term Term)


-- | Conversions for operations on bitvector literals
bvConversions :: [Conversion]
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

append_bvNat :: Conversion
append_bvNat = globalConv "Prelude.append" Prim.append_bv

bvAdd_bvNat :: Conversion
bvAdd_bvNat = globalConv "Prelude.bvAdd" Prim.bvAdd

bvSub_bvNat :: Conversion
bvSub_bvNat = globalConv "Prelude.bvSub" Prim.bvSub

bvugt_bvNat, bvuge_bvNat, bvult_bvNat, bvule_bvNat :: Conversion
bvugt_bvNat = globalConv "Prelude.bvugt" Prim.bvugt
bvuge_bvNat = globalConv "Prelude.bvuge" Prim.bvuge
bvult_bvNat = globalConv "Prelude.bvult" Prim.bvult
bvule_bvNat = globalConv "Prelude.bvule" Prim.bvule

bvsgt_bvNat, bvsge_bvNat, bvslt_bvNat, bvsle_bvNat :: Conversion
bvsgt_bvNat = globalConv "Prelude.bvsgt" Prim.bvsgt
bvsge_bvNat = globalConv "Prelude.bvsge" Prim.bvsge
bvslt_bvNat = globalConv "Prelude.bvslt" Prim.bvslt
bvsle_bvNat = globalConv "Prelude.bvsle" Prim.bvsle

at_bvNat :: Conversion
at_bvNat = globalConv "Prelude.at" Prim.at_bv

atWithDefault_bvNat :: Conversion
atWithDefault_bvNat =
  Conversion $
  (\(_ :*: n :*: a :*: d :*: x :*: i) ->
    if fromIntegral i < width x then mkBool (Prim.at_bv n a x i) else return d) <$>
  (asGlobalDef "Prelude.atWithDefault" <:>
   defaultMatcher <:> defaultMatcher <:> asAny <:> asBvNatLit <:> asAnyNatLit)

take_bvNat :: Conversion
take_bvNat = globalConv "Prelude.take" Prim.take_bv

drop_bvNat :: Conversion
drop_bvNat = globalConv "Prelude.drop" Prim.drop_bv

slice_bvNat :: Conversion
slice_bvNat = globalConv "Prelude.slice" Prim.slice_bv

mixfix_snd :: (a :*: b) -> b
mixfix_snd (_ :*: y) = y

remove_coerce :: Conversion
remove_coerce = Conversion $
  return . mixfix_snd <$>
    (asGlobalDef "Prelude.coerce" <:> asAny <:> asAny <:> asAny <:> asAny)

remove_unsafeCoerce :: Conversion
remove_unsafeCoerce = Conversion $
  return . mixfix_snd <$>
    (asGlobalDef "Prelude.unsafeCoerce" <:> asAny <:> asAny <:> asAny)

remove_ident_coerce :: Conversion
remove_ident_coerce = Conversion $ thenMatcher pat action
  where pat = asGlobalDef "Prelude.coerce" <:> asAny <:> asAny <:> asAny <:> asAny
        action (() :*: t :*: f :*: _prf :*: x)
          | alphaEquiv t f = return (return x)
          | otherwise = fail "Cannot remove coerce."

remove_ident_unsafeCoerce :: Conversion
remove_ident_unsafeCoerce = Conversion $ thenMatcher pat action
  where pat = asGlobalDef "Prelude.unsafeCoerce" <:> asAny <:> asAny <:> asAny
        action (() :*: t :*: f :*: x)
          | alphaEquiv t f = return (return x)
          | otherwise = fail "Cannot remove unsafeCoerce."
