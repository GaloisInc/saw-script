{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{- |
Module      : SAWCore.Conversion
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Conversion
  ( (:*:)(..)
  , termPat
  , termFPat
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
  , asAnySort
  , asSort
  , asAnyNatLit
  , asAnyVecLit
  , asVariable
    -- ** Prelude matchers
  , asBoolType
  , asSuccLit
  , asBvNatLit
    -- ** Matchable typeclass
  , Matchable(..)
    -- ** Prelude builders
  , mkBvNat
    -- * Conversion
  , Conversion(..)
  , newConversion
  , runConversion
  , conversionPat
    -- ** Prelude conversions
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
  ) where

import Control.Lens (view, _1, _2)
import Control.Monad (guard, liftM2, (>=>), (<=<))
import Data.Bits
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Vector as V
import Numeric.Natural (Natural)

import SAWCore.Name
import SAWCore.OpenTerm (OpenTerm)
import qualified SAWCore.OpenTerm as OT
import qualified SAWCore.Prim as Prim
import SAWCore.Recognizer ((:*:)(..))
import SAWCore.Prim
import qualified SAWCore.Recognizer as R
import SAWCore.SharedTerm (Term, unwrapTermF)
import qualified SAWCore.TermNet as Net
import SAWCore.Term.Functor

-- | A hack to allow storage of conversions in a term net.
instance Eq Conversion where
    x == y = conversionPat x == conversionPat y

instance Show Conversion where
    show x = show (conversionPat x)

----------------------------------------------------------------------
-- TermNet Patterns

termPat :: Term -> Net.Pat
termPat t = termFPat (unwrapTermF t)

termFPat :: TermF Term -> Net.Pat
termFPat tf =
  case tf of
    Constant nm               -> Net.Atom (toShortName (nameInfo nm))
    App t1 t2                 -> Net.App (termPat t1) (termPat t2)
    FTermF (Sort s _)         -> Net.Atom (Text.pack ('*' : show s))
    _                         -> Net.Var

----------------------------------------------------------------------
-- Matchers for terms

data Matcher a = Matcher { matcherPat :: Net.Pat, runMatcher :: Term -> Maybe a }

instance Functor Matcher where
  fmap f (Matcher p m) = Matcher p (fmap f . m)

-- | @thenMatcher
thenMatcher :: Matcher a -> (a -> Maybe b) -> Matcher b
thenMatcher (Matcher pat match) f = Matcher pat (f <=< match)

asVar :: (Term -> Maybe a) -> Matcher a
asVar = Matcher Net.Var

asAny :: Matcher Term
asAny = asVar pure

-- | Match a list of terms as arguments to a term.
-- Note that the pats and arguments are in reverse order.
data ArgsMatcher a = ArgsMatcher [Net.Pat] ([Term] -> Maybe (a, [Term]))

class ArgsMatchable v a where
  defaultArgsMatcher :: v a -> ArgsMatcher a

instance ArgsMatchable Matcher a where
  defaultArgsMatcher (Matcher p f) = ArgsMatcher [p] match
    where match (h:r) = do v <- f h; return (v,r)
          match [] = Nothing

instance ArgsMatchable ArgsMatcher a where
  defaultArgsMatcher = id

consArgsMatcher :: ArgsMatcher a -> Matcher b -> ArgsMatcher (a :*: b)
consArgsMatcher (ArgsMatcher pl f) (Matcher p g) = ArgsMatcher (pl ++ [p]) match
  where match l = do
          (a,l1) <- f l
          case l1 of
            (h:l2) -> do b <- g h; return (a :*: b, l2)
            [] -> Nothing

asEmpty :: ArgsMatcher ()
asEmpty = ArgsMatcher [] (\l -> return ((),l))

infixl 9 >:

-- | @x >: y@ appends @y@ to the list of arguments to match.
(>:) :: (ArgsMatchable v a) => v a -> Matcher b -> ArgsMatcher (a :*: b)
(>:) = consArgsMatcher . defaultArgsMatcher

runArgsMatcher :: ArgsMatcher a -> [Term] -> Maybe a
runArgsMatcher (ArgsMatcher _ f) l = do
  (v,[]) <- f l
  return v

-- | Produces a matcher from an ArgsMatcher and a matcher that yields
-- subterms.
resolveArgs :: (ArgsMatchable v a)
               -- Given a term, matches arguments to term.
            => Matcher [Term]
            -> v a
            -> Matcher a
resolveArgs (Matcher p m) (defaultArgsMatcher -> args@(ArgsMatcher pl _)) =
  Matcher (foldl Net.App p pl) (m >=> runArgsMatcher args)

----------------------------------------------------------------------
-- Term matchers

-- | Match a global definition.
asGlobalDef :: Ident -> Matcher ()
asGlobalDef ident = Matcher (Net.Atom (identBaseName ident)) f
  where f (R.asGlobalDef -> Just o) | ident == o = return ()
        f _ = Nothing

infixl 8 <:>

-- | Match an application
(<:>) :: Matcher a -> Matcher b -> Matcher (a :*: b)
(<:>) (Matcher p1 f1) (Matcher p2 f2) = Matcher (Net.App p1 p2) match
    where
      match (unwrapTermF -> App t1 t2) = liftM2 (:*:) (f1 t1) (f2 t2)
      match _ = Nothing

-- | Match an application and return second term.
(<:>>) :: Matcher a -> Matcher b -> Matcher b
x <:>> y = fmap (view _2) $ x <:> y


-- | Matches any tuple.
asAnyTupleValue :: Matcher [Term]
asAnyTupleValue = asVar R.asTupleValue

-- | Matches a tuple with arguments matching constraints.
asTupleValue :: ArgsMatchable v a => v a -> Matcher a
asTupleValue (defaultArgsMatcher -> m) = asVar $ \t -> do
  l <- R.asTupleValue t
  runArgsMatcher m l

-- | Matches the type of any tuple.
asAnyTupleType :: Matcher [Term]
asAnyTupleType = asVar R.asTupleType

-- | Matches a tuple type with arguments matching constraints.
asTupleType :: ArgsMatchable v a => v a -> Matcher a
asTupleType (defaultArgsMatcher -> m) = asVar $ \t -> do
  l <- R.asTupleType t
  runArgsMatcher m l

asTupleSelector :: Matcher a -> Matcher (a, Int)
asTupleSelector m = asVar $ \t -> _1 (runMatcher m) =<< R.asTupleSelector t

-- | Matches record values, and returns fields.
asAnyRecordValue :: Matcher (Map FieldName Term)
asAnyRecordValue = asVar R.asRecordValue

-- | Matches record types, and returns fields.
asAnyRecordType :: Matcher (Map FieldName Term)
asAnyRecordType = asVar R.asRecordType

-- | Matches
asRecordSelector :: Matcher a -> Matcher (a, FieldName)
asRecordSelector m = asVar $ \t -> _1 (runMatcher m) =<< R.asRecordSelector t

--TODO: RecordSelector

-- | Match a constructor
asCtor :: ArgsMatchable v a => Ident -> v a -> Matcher a
asCtor o = resolveArgs $ Matcher (Net.Atom (identBaseName o)) match
  where match t = R.asGlobalApply o t

-- | Match any sort.
asAnySort :: Matcher Sort
asAnySort = asVar $ \t -> do Sort v _ <- R.asFTermF t; return v

-- | Match a specific sort.
asSort :: Sort -> Matcher ()
asSort s = Matcher (termFPat (FTermF (Sort s noFlags))) fn
  where fn t = do s' <- R.asSort t
                  guard (s == s')

-- | Match a Nat literal
asAnyNatLit :: Matcher Natural
asAnyNatLit = asVar $ \t -> R.asNat t

-- | Match a Vec literal
asAnyVecLit :: Matcher (Term, V.Vector Term)
asAnyVecLit = asVar $ \t -> do ArrayValue u xs <- R.asFTermF t; return (u,xs)

-- | Match any named variable.
asVariable :: Matcher (VarName, Term)
asVariable = asVar R.asVariable

----------------------------------------------------------------------
-- Prelude matchers

asBoolType :: Matcher ()
asBoolType = asGlobalDef "Prelude.Bool"

asSuccLit :: Matcher Natural
asSuccLit = asCtor "Prelude.Succ" asAnyNatLit

asBvNatLit :: Matcher Prim.BitVector
asBvNatLit =
  (\(_ :*: n :*: x) -> Prim.bv (fromIntegral n) (toInteger x)) <$>
    (asGlobalDef "Prelude.bvNat" <:> asAnyNatLit <:> asAnyNatLit)

checkedIntegerToNonNegInt :: Integer -> Maybe Int
checkedIntegerToNonNegInt x
  | 0 <= x && x <= toInteger (maxBound :: Int) = return (fromInteger x)
  | otherwise = Nothing

----------------------------------------------------------------------
-- Matchable

class Matchable a where
    defaultMatcher :: Matcher a

instance Matchable () where
    defaultMatcher = asVar (const (pure ()))

instance Matchable Term where
    defaultMatcher = asAny

instance Matchable Natural where
    defaultMatcher = asAnyNatLit

instance Matchable Integer where
    defaultMatcher = toInteger <$> asAnyNatLit

instance Matchable Int where
    defaultMatcher = thenMatcher asAnyNatLit (checkedIntegerToNonNegInt . toInteger)

instance Matchable Prim.BitVector where
    defaultMatcher = asBvNatLit

instance Matchable (Prim.Vec Term Term) where
    defaultMatcher = uncurry Prim.Vec <$> asAnyVecLit

----------------------------------------------------------------------
-- Term builders

mkBvNat :: Natural -> Integer -> OpenTerm
mkBvNat n x = do
  OT.applyGlobal "Prelude.bvNat"
    [OT.nat n, OT.nat $ fromInteger $ x .&. bitMask (fromIntegral n)]

class Buildable a where
  defaultBuilder :: a -> OpenTerm

instance Buildable Term where
  defaultBuilder = OT.term

instance Buildable Bool where
  defaultBuilder = OT.bool

instance Buildable Natural where
  defaultBuilder = OT.nat

instance Buildable Integer where
  defaultBuilder = OT.nat . fromInteger

instance Buildable Int where
  defaultBuilder = OT.nat . fromIntegral

instance (Buildable a, Buildable b) => Buildable (a, b) where
  defaultBuilder (x, y) = OT.pair (defaultBuilder x) (defaultBuilder y)

instance (Buildable a, Buildable b) => Buildable (Prim.Vec a b) where
  defaultBuilder (Prim.Vec t v) =
    OT.arrayValue (defaultBuilder t) (V.toList (fmap defaultBuilder v))

instance Buildable Prim.BitVector where
  defaultBuilder (Prim.BV w x) = mkBvNat (fromIntegral w) x

----------------------------------------------------------------------
-- Conversions

-- | These are conversions in the LCF-style term-rewriting sense: A
-- conversion is a function that takes a term and returns (possibly) a
-- rewritten term. We use conversions to model the behavior of
-- primitive operations in SAWCore.
-- The Bool field is true if the terms before and after the conversion
-- is executed are convertible in the SAWCore type system and false
-- otherwise.

data Conversion = Conversion Bool (Matcher OpenTerm)

runConversion :: Conversion -> Term -> Maybe OpenTerm
runConversion (Conversion _ m) = runMatcher m

conversionPat :: Conversion -> Net.Pat
conversionPat (Conversion _ m) = matcherPat m

-- | Constructs a 'Conversion' from a @Matcher OpenTerm@.
-- This assumes the default case that the Conversion is
-- non-convertible; if the Conversion is convertible with regard
-- to the SAW type system, it should be constructed using
-- the data constructor.
newConversion :: Matcher OpenTerm -> Conversion
newConversion = Conversion False

-- | This class is meant to include n-ary function types whose
-- arguments are all in class @Matchable@ and whose result type is
-- in class @Buildable@. Given a matcher for the global constant
-- itself, we can construct a conversion that applies the function to
-- its arguments and builds the result.

class Conversionable a where
    convOfMatcher :: Matcher a -> Conversion

instance (Matchable a, Conversionable b) => Conversionable (a -> b) where
    convOfMatcher m = convOfMatcher
        (thenMatcher (m <:> defaultMatcher) (\(f :*: x) -> Just (f x)))

instance Buildable a => Conversionable (Maybe a) where
    convOfMatcher m = newConversion (thenMatcher m (fmap defaultBuilder))

defaultConvOfMatcher :: Buildable a => Matcher a -> Conversion
defaultConvOfMatcher m = newConversion (thenMatcher m (Just . defaultBuilder))

instance Conversionable Term where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Bool where
    convOfMatcher = defaultConvOfMatcher

instance Conversionable Natural where
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

-- | Conversions for operations on Nat literals
natConversions :: [Conversion]
natConversions = [ succ_NatLit, addNat_NatLit, subNat_NatLit
                 , mulNat_NatLit, expNat_NatLit, divNat_NatLit, remNat_NatLit
                 , equalNat_NatLit
                 ]

succ_NatLit :: Conversion
succ_NatLit =
    Conversion True $ thenMatcher asSuccLit (\n -> pure $ OT.nat (n + 1))

addNat_NatLit :: Conversion
addNat_NatLit = globalConv "Prelude.addNat" ((+) :: Natural -> Natural -> Natural)

subNat_NatLit :: Conversion
subNat_NatLit = Conversion True $
  thenMatcher (asGlobalDef "Prelude.subNat" <:> asAnyNatLit <:> asAnyNatLit)
    (\(_ :*: x :*: y) -> if x >= y then Just (OT.nat (x - y)) else Nothing)

mulNat_NatLit :: Conversion
mulNat_NatLit = globalConv "Prelude.mulNat" ((*) :: Natural -> Natural -> Natural)

expNat_NatLit :: Conversion
expNat_NatLit = globalConv "Prelude.expNat" ((^) :: Natural -> Natural -> Natural)

divNat_NatLit :: Conversion
divNat_NatLit = Conversion True $
  thenMatcher (asGlobalDef "Prelude.divNat" <:> asAnyNatLit <:> asAnyNatLit)
    (\(_ :*: x :*: y) ->
         if y /= 0 then Just (OT.nat (x `div` y)) else Nothing)

remNat_NatLit :: Conversion
remNat_NatLit = Conversion True $
  thenMatcher (asGlobalDef "Prelude.remNat" <:> asAnyNatLit <:> asAnyNatLit)
    (\(_ :*: x :*: y) ->
         if y /= 0 then Just (OT.nat (x `rem` y)) else Nothing)

equalNat_NatLit :: Conversion
equalNat_NatLit = globalConv "Prelude.equalNat" ((==) :: Natural -> Natural -> Bool)

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
  Conversion False $
  (\(_ :*: n :*: a :*: d :*: x :*: i) ->
    if fromIntegral i < width x then OT.bool (Prim.at_bv n a x i) else OT.term d) <$>
  (asGlobalDef "Prelude.atWithDefault" <:>
   defaultMatcher <:> defaultMatcher <:> asAny <:> asBvNatLit <:> asAnyNatLit)

take_bvNat :: Conversion
take_bvNat = globalConv "Prelude.take" Prim.take_bv

drop_bvNat :: Conversion
drop_bvNat = globalConv "Prelude.drop" Prim.drop_bv

slice_bvNat :: Conversion
slice_bvNat = globalConv "Prelude.slice" Prim.slice_bv
