{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Conversion
  ( Matcher
  , (<:>)
  , asAny
  , asFinValLit
  , matchGlobalDef
  , thenMatcher
  , TermBuilder
  , runTermBuilder
  , mkAny
  , Conversion(..)
  , runConversion
  -- Prelude conversions
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
  ) where

import Control.Applicative (Applicative(..), (<$>), (<*>))
import Control.Exception (assert)
import Control.Monad (ap, guard, liftM, (>=>))
import Data.Bits
import qualified Data.Vector as V

import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.TypedAST

----------------------------------------------------------------------
-- Matchers for terms

data Matcher t a = Matcher Net.Pat (t -> Maybe a)

thenMatcher :: Matcher t a -> (a -> Maybe b) -> Matcher t b
thenMatcher (Matcher pat match) f = Matcher pat (match >=> f)

asAny :: Matcher t t
asAny = Matcher Net.Var Just

infixl 8 <:>

(<:>) :: Termlike t => Matcher t a -> Matcher t b -> Matcher t (a, b)
(<:>) (Matcher p1 f1) (Matcher p2 f2) = Matcher (Net.App p1 p2) match
    where
      match (unwrapTermF -> FTermF (App t1 t2)) = (,) <$> f1 t1 <*> f2 t2
      match _ = Nothing

asNatLit :: Termlike t => Matcher t Integer
asNatLit = Matcher Net.Var R.asNatLit

asVecLit :: Termlike t => Matcher t (t, V.Vector t)
asVecLit = Matcher Net.Var match
    where
      match (unwrapTermF -> FTermF (ArrayValue t xs)) = Just (t, xs)
      match _ = Nothing

matchGlobalDef :: Termlike t => Ident -> Matcher t ()
matchGlobalDef ident = Matcher (Net.Atom (identName ident)) (R.isGlobalDef ident)

asBoolType :: Termlike t => Matcher t ()
asBoolType = Matcher (Net.Atom (identName bool)) R.asBoolType
    where
      bool = "Prelude.Bool"

asFinValLit :: Termlike t => Matcher t (Integer, Integer)
asFinValLit = Matcher pat match
    where
      pat = Net.App (Net.App (Net.Atom (identName finval)) Net.Var) Net.Var
      match (unwrapTermF -> FTermF (CtorApp ident [x, y]))
          | ident == finval = (,) <$> R.asNatLit x <*> R.asNatLit y
      match _ = Nothing
      finval = "Prelude.FinVal"

asSuccLit :: Termlike t => Matcher t Integer
asSuccLit = Matcher pat match
    where
      pat = Net.App (Net.Atom (identName succId)) Net.Var
      match (unwrapTermF -> FTermF (CtorApp ident [x]))
          | ident == succId = R.asNatLit x
      match _ = Nothing
      succId = "Prelude.Succ"

bitMask :: Integer -> Integer
bitMask n = bit (fromInteger n) - 1

asBvNatLit :: Termlike t => Matcher t (Integer, Integer)
asBvNatLit =
    thenMatcher (matchGlobalDef "Prelude.bvNat" <:> asNatLit <:> asNatLit) $
        \(((), n), x) -> return (n, x .&. bitMask n)

normSignedBV :: Int -> Integer -> Integer
normSignedBV n x | testBit x n = x' - bit (n+1)
                 | otherwise   = x'
  where mask = bit (n+1) - 1
        x' = x .&. mask

asSignedBvNatLit :: Termlike t => Matcher t Integer
asSignedBvNatLit =
    thenMatcher (matchGlobalDef "Prelude.bvNat" <:> asNatLit <:> asNatLit) $
        \(((), n), x) -> return (normSignedBV (fromInteger n) x)

class Matchable t a where
    defaultMatcher :: Matcher t a

instance Matchable t () where
    defaultMatcher = Matcher Net.Var (const (Just ()))

instance Matchable t t where
    defaultMatcher = asAny

instance Termlike t => Matchable t Integer where
    defaultMatcher = asNatLit

instance Termlike t => Matchable t Int where
    defaultMatcher = thenMatcher asNatLit toInt
        where toInt x | 0 <= x && x <= toInteger (maxBound :: Int) = Just (fromInteger x)
                      | otherwise = Nothing

instance Termlike t => Matchable t Prim.BitVector where
    defaultMatcher = thenMatcher asBvNatLit
        (\(w, x) -> Just (Prim.BV (fromInteger w) x))

instance Termlike t => Matchable t Prim.Fin where
    defaultMatcher = thenMatcher asFinValLit
        (\(i, j) -> Just (Prim.FinVal (fromInteger i) (fromInteger j)))

instance Termlike t => Matchable t (Prim.Vec t t) where
    defaultMatcher = thenMatcher asVecLit
        (\(t, v) -> Just (Prim.Vec t v))

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

mkBool :: Bool -> TermBuilder t t
mkBool b = mkTermF (FTermF (CtorApp idSym []))
  where idSym | b = "Prelude.True" 
              | otherwise = "Prelude.False"

mkNatLit :: Integer -> TermBuilder t t
mkNatLit n = mkTermF (FTermF (NatLit n))

mkVecLit :: t -> V.Vector t -> TermBuilder t t
mkVecLit t xs = mkTermF (FTermF (ArrayValue t xs))

mkTuple :: [t] -> TermBuilder t t
mkTuple l = mkTermF (FTermF (TupleValue l))

mkFinVal :: Integer -> Integer -> TermBuilder t t
mkFinVal i j =
    do i' <- mkNatLit i
       j' <- mkNatLit j
       mkTermF (FTermF (CtorApp "Prelude.FinVal" [i', j']))

mkBvNat :: Integer -> Integer -> TermBuilder t t
mkBvNat n x = assert (n >= 0) $
    do n' <- mkNatLit n
       x' <- mkNatLit (x .&. bitMask n)
       t0 <- mkTermF (FTermF (GlobalDef "Prelude.bvNat"))
       t1 <- mkTermF (FTermF (App t0 n'))
       t2 <- mkTermF (FTermF (App t1 x'))
       return t2

class Buildable t a where
    defaultBuilder :: a -> TermBuilder t t

instance Buildable t t where
    defaultBuilder = return

instance Buildable t Bool where
    defaultBuilder = mkBool

instance Buildable t Integer where
    defaultBuilder = mkNatLit

instance Buildable t Int where
    defaultBuilder = mkNatLit . toInteger

instance (Buildable t a, Buildable t b) => Buildable t (a, b) where
    defaultBuilder (x, y) = do
      a <- defaultBuilder x
      b <- defaultBuilder y
      mkTuple [a, b]

instance Buildable t Prim.Fin where
    defaultBuilder (Prim.FinVal i j) = mkFinVal (toInteger i) (toInteger j)

instance Buildable t (Prim.Vec t t) where
    defaultBuilder (Prim.Vec t v) = mkVecLit t v

instance Buildable t Prim.BitVector where
    defaultBuilder (Prim.BV w x) = mkBvNat (toInteger w) x

----------------------------------------------------------------------
-- Conversions

-- | These are conversions in the LCF-style term-rewriting sense: A
-- conversion is a function that takes a term and returns (possibly) a
-- rewritten term. We use conversions to model the behavior of
-- primitive operations in SAWCore.

newtype Conversion t = Conversion (Matcher t (TermBuilder t t))

runConversion :: Conversion t -> t -> Maybe (TermBuilder t t)
runConversion (Conversion (Matcher _ f)) = f

instance Net.Pattern (Conversion t) where
    toPat (Conversion (Matcher pat _)) = pat

-- | This class is meant to include n-ary function types whose
-- arguments are all in class @Matchable t@ and whose result type is
-- in class @Buildable t@. Given a matcher for the global constant
-- itself, we can construct a conversion that applies the function to
-- its arguments and builds the result.

class Conversionable t a where
    convOfMatcher :: Matcher t a -> Conversion t

instance (Termlike t, Matchable t a, Conversionable t b) => Conversionable t (a -> b) where
    convOfMatcher m = convOfMatcher
        (thenMatcher (m <:> defaultMatcher) (\(f, x) -> Just (f x)))

instance Buildable t a => Conversionable t (Maybe a) where
    convOfMatcher m = Conversion (thenMatcher m (fmap defaultBuilder))

defaultConvOfMatcher :: Buildable t a => Matcher t a -> Conversion t
defaultConvOfMatcher m = Conversion (thenMatcher m (Just . defaultBuilder))

instance Conversionable t t where
    convOfMatcher = defaultConvOfMatcher

instance Termlike t => Conversionable t Bool where
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
globalConv ident f = convOfMatcher (thenMatcher (matchGlobalDef ident) (const (Just f)))

----------------------------------------------------------------------
-- Conversions for Prelude operations

-- | Conversions for operations on Nat literals
natConversions :: Termlike t => [Conversion t]
natConversions = [succ_NatLit, addNat_NatLit]

succ_NatLit :: Termlike t => Conversion t
succ_NatLit =
    Conversion $ thenMatcher asSuccLit (\n -> return $ mkNatLit (n + 1))

addNat_NatLit :: Termlike t => Conversion t
addNat_NatLit = globalConv "Prelude.addNat" ((+) :: Integer -> Integer -> Integer)

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
bvule_bvNat = globalConv "Prelude.bvult" Prim.bvule

bvsgt_bvNat, bvsge_bvNat, bvslt_bvNat, bvsle_bvNat :: Termlike t => Conversion t
bvsgt_bvNat = globalConv "Prelude.bvsgt" Prim.bvsgt
bvsge_bvNat = globalConv "Prelude.bvsge" Prim.bvsge
bvslt_bvNat = globalConv "Prelude.bvslt" Prim.bvslt
bvsle_bvNat = globalConv "Prelude.bvslt" Prim.bvsle

get_bvNat :: Termlike t => Conversion t
get_bvNat = globalConv "Prelude.get" Prim.get_bv

vTake_bvNat :: Termlike t => Conversion t
vTake_bvNat = globalConv "Prelude.vTake" Prim.vTake_bv

vDrop_bvNat :: Termlike t => Conversion t
vDrop_bvNat = globalConv "Prelude.vDrop" Prim.vDrop_bv

slice_bvNat :: Termlike t => Conversion t
slice_bvNat = globalConv "Prelude.slice" Prim.slice_bv
