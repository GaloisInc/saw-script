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
    -- * Matcher
  , Matcher
  , runMatcher
  , thenMatcher
  , asVar
  , asAny
    -- ** Matcher arguments
  , ArgsMatcher
  , ArgsMatchable
  , asEmpty
  , (>:)
  , runArgsMatcher
    -- ** Term matchers
  , asGlobalDef
  , (<:>)
  , asAnyTupleValue
  , asTupleValue
  , asAnyTupleType
  , asTupleType
  , asAnyRecordValue
  , asAnyRecordType
  , asCtor
  , asDataType
  , asAnySort
  , asSort
  , asAnyNatLit
  , asAnyVecLit
  , asAnyFloatLit
  , asAnyDoubleLit
    -- ** Prelude matchers
  , asBoolType
  , asFinValLit
  , asSuccLit
  , asBvNatLit
  , asSignedBvNatLit
    -- ** Matchable typeclass
  , Matchable(..)
    -- ** TermBuilder
  , TermBuilder
  , runTermBuilder
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
  ) where

import Control.Applicative (Applicative(..), (<$>), (<*>))
import Control.Exception (assert)
import Control.Monad (ap, liftM, liftM2, unless, (<=<))
import Data.Bits
import Data.Map (Map)
import qualified Data.Vector as V

import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.Recognizer ((:*:)(..))
import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.TypedAST

termToPat :: Termlike t => t -> Net.Pat
termToPat t =
    case unwrapTermF t of
      FTermF (GlobalDef d)      -> Net.Atom (identName d)
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

thenMatcher :: Monad m => Matcher m t a -> (a -> m b) -> Matcher m t b
thenMatcher (Matcher pat match) f = Matcher pat (f <=< match)

asVar :: (t -> m a) -> Matcher m t a
asVar = Matcher Net.Var

asAny :: Applicative m => Matcher m t t
asAny = asVar pure

infixl 8 <:>

-- | Match a list of terms as arguments to a term.
data ArgsMatcher m t a = ArgsMatcher [Net.Pat] ([t] -> m a)

class ArgsMatchable v m t a where
  defaultArgsMatcher :: v m t a -> ArgsMatcher m t a

instance Monad m => ArgsMatchable Matcher m t a where
  defaultArgsMatcher (Matcher p f) = ArgsMatcher [p] match
    where match [h] = f h
          match [] = fail "empty"
          match _ = fail "not singleton"

instance ArgsMatchable ArgsMatcher m t a where
  defaultArgsMatcher = id

infixl 9 >:

asEmpty :: (Monad m) => ArgsMatcher m t ()
asEmpty = ArgsMatcher [] match
  where match l | null l = return ()
                | otherwise = fail "not empty"

(>:) :: (Monad m, ArgsMatchable v m t a) => v m t a -> Matcher m t b -> ArgsMatcher m t (a :*: b)
(>:) (defaultArgsMatcher -> ArgsMatcher pl f) (Matcher p g) = ArgsMatcher (p:pl) match
  where match (h:l) = liftM2 (:*:) (f l) (g h)
        match [] = fail "empty"

runArgsMatcher :: ArgsMatcher m t a -> [t] -> m a
runArgsMatcher (ArgsMatcher _ f) = f . reverse
 
-- | Produces a matcher from an ArgsMatcher and a matcher that yields
-- subterms.
resolveArgs :: (Monad m, ArgsMatchable v m t a)
               -- ^ Given a term, matches arguments to temr.
            => Matcher m t [t] 
            -> v m t a
            -> Matcher m t a
resolveArgs (Matcher p m) (defaultArgsMatcher -> ArgsMatcher pl f)
    = Matcher (foldl Net.App p (reverse pl))
              (f . reverse <=< m)

----------------------------------------------------------------------
-- Term matchers

-- | Match a global definition.
asGlobalDef :: (Termlike t, Monad m) => Ident -> Matcher m t ()
asGlobalDef ident = Matcher (Net.Atom (identName ident)) f
  where f (R.asGlobalDef -> Just o) | ident == o = return ()
        f _ = fail (show ident ++ " match failed.")

-- | Match an application
(<:>) :: (Termlike t, Applicative m, Monad m)
      => Matcher m t a -> Matcher m t b -> Matcher m t (a :*: b)
(<:>) (Matcher p1 f1) (Matcher p2 f2) = Matcher (Net.App p1 p2) match
    where
      match (unwrapTermF -> FTermF (App t1 t2)) = liftM2 (:*:) (f1 t1) (f2 t2)
      match _ = fail "internal: <:> net failed"

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

--TODO: TupleSelector

-- | Matches record values, and returns fields.
asAnyRecordValue :: (Monad m, Termlike t) => Matcher m t (Map FieldName t)
asAnyRecordValue = asVar $ \t -> do RecordValue m <- R.asFTermF t; return m

-- | Matches record types, and returns fields.
asAnyRecordType :: (Monad m, Termlike t) => Matcher m t (Map FieldName t)
asAnyRecordType = asVar $ \t -> do RecordType m <- R.asFTermF t; return m

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
asAnyNatLit :: (Termlike t, Monad m) => Matcher m t Integer
asAnyNatLit = asVar $ \t -> do NatLit i <- R.asFTermF t; return i

-- | Match a Vec literal
asAnyVecLit :: (Termlike t, Monad m) => Matcher m t (t, V.Vector t)
asAnyVecLit = asVar $ \t -> do ArrayValue u xs <- R.asFTermF t; return (u,xs)

-- | Match a Float literal
asAnyFloatLit :: (Termlike t, Monad m) => Matcher m t Float
asAnyFloatLit = asVar $ \t -> do FloatLit i <- R.asFTermF t; return i

-- | Match a Double literal
asAnyDoubleLit :: (Termlike t, Monad m) => Matcher m t Double
asAnyDoubleLit = asVar $ \t -> do DoubleLit i <- R.asFTermF t; return i

----------------------------------------------------------------------
-- Prelude matchers

asBoolType :: (Monad m, Termlike t) => Matcher m t ()
asBoolType = asDataType "Prelude.Bool" asEmpty

asFinValLit :: (Functor m, Monad m, Termlike t) => Matcher m t (Integer, Integer)
asFinValLit = (\(i :*: j) -> (i,j))
  <$> asCtor "Prelude.FinVal" (asAnyNatLit >: asAnyNatLit) 

asSuccLit :: (Functor m, Monad m, Termlike t) => Matcher m t Integer
asSuccLit = asCtor "Prelude.Succ" asAnyNatLit

bitMask :: Integer -> Integer
bitMask n = bit (fromInteger n) - 1

asBvNatLit :: (Applicative m, Monad m, Termlike t) => Matcher m t (Integer, Integer)
asBvNatLit =
  (\(_ :*: n :*: x) -> (n, x .&. bitMask n)) <$>
    (asGlobalDef "Prelude.bvNat" <:> asAnyNatLit <:> asAnyNatLit)

normSignedBV :: Int -> Integer -> Integer
normSignedBV n x | testBit x n = x' - bit (n+1)
                 | otherwise   = x'
  where mask = bit (n+1) - 1
        x' = x .&. mask

checkedIntegerToNonNegInt :: Monad m => Integer -> m Int
checkedIntegerToNonNegInt x 
  | 0 <= x && x <= toInteger (maxBound :: Int) = return (fromInteger x)
  | otherwise = fail "match out of range"

asSignedBvNatLit :: (Applicative m, Monad m, Termlike t) => Matcher m t Integer
asSignedBvNatLit =
   (\(_ :*: n :*: x) -> normSignedBV (fromInteger n) x)
    <$> (asGlobalDef "Prelude.bvNat" <:> asAnyNatLit <:> asAnyNatLit)

----------------------------------------------------------------------
-- Matchable

class Matchable m t a where
    defaultMatcher :: Matcher m t a

instance Applicative m => Matchable m t () where
    defaultMatcher = asVar (const (pure ()))

instance Applicative m => Matchable m t t where
    defaultMatcher = asAny

instance (Monad m, Termlike t) => Matchable m t Integer where
    defaultMatcher = asAnyNatLit

instance (Monad m, Termlike t) => Matchable m t Int where
    defaultMatcher = thenMatcher asAnyNatLit checkedIntegerToNonNegInt

instance (Applicative m, Monad m, Termlike t) => Matchable m t Prim.BitVector where
    defaultMatcher =
        (\(w, x) -> Prim.BV (fromInteger w) x) <$> asBvNatLit

instance (Functor m, Monad m, Termlike t) => Matchable m t Prim.Fin where
    defaultMatcher =
      (\(i, j) -> Prim.FinVal (fromInteger i) (fromInteger j)) <$> asFinValLit

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
