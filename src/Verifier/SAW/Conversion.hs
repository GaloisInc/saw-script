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

mkAny :: t -> TermBuilder t t
mkAny t = TermBuilder $ \_ -> return t

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

----------------------------------------------------------------------
-- Conversions for Prelude operations

-- | Conversions for operations on Nat literals
natConversions :: Termlike t => [Conversion t]
natConversions = [succ_NatLit, addNat_NatLit]

succ_NatLit :: Termlike t => Conversion t
succ_NatLit =
    Conversion $ thenMatcher asSuccLit (\n -> return $ mkNatLit (n + 1))

addNat_NatLit :: Termlike t => Conversion t
addNat_NatLit =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.addNat" <:> asNatLit <:> asNatLit)
    (\(((), m), n) -> return $ mkNatLit (m + n))

-- | Conversions for operations on Fin literals
finConversions :: Termlike t => [Conversion t]
finConversions = [finInc_FinVal, finIncLim_FinVal]

finInc_FinVal :: Termlike t => Conversion t
finInc_FinVal =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.finInc" <:> asNatLit <:> asNatLit <:> asFinValLit)
    (\((((), m), n), (i, j)) ->
         guard (n == i + j + 1) >> return (mkFinVal (m + i) j))

finIncLim_FinVal :: Termlike t => Conversion t
finIncLim_FinVal =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.finIncLim" <:> asNatLit <:> asNatLit <:> asFinValLit)
    (\((((), m), n), (i, j)) ->
         guard (n == i + j + 1) >> return (mkFinVal i (m + j)))

-- | Conversions for operations on vector literals
vecConversions :: Termlike t => [Conversion t]
vecConversions = [get_VecLit, append_VecLit]

get_VecLit :: Termlike t => Conversion t
get_VecLit =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.get" <:> asNatLit <:> asAny <:> asVecLit <:> asFinValLit)
    (\(((((), _n), _e), (_, xs)), (i, _j)) ->
         return $ mkAny (xs V.! fromIntegral i))

append_VecLit :: Termlike t => Conversion t
append_VecLit =
    Conversion $
    thenMatcher (matchGlobalDef append <:> asNatLit <:> asNatLit <:> asAny <:> asVecLit <:> asVecLit)
    (\((((((), _m), _n), e), (_, xs)), (_, ys)) ->
         return $ mkVecLit e ((V.++) xs ys))
    where append = "Prelude.append"


-- | Conversions for operations on bitvector literals
bvConversions :: Termlike t => [Conversion t]
bvConversions =
    [ bvToNat_bvNat
    , append_bvNat
    , bvAdd_bvNat
    , bvAddWithCarry_bvNat
    , bvSub_bvNat
    , bvMul_bvNat
    , bvUDiv_bvNat
    , bvURem_bvNat
    , bvSDiv_bvNat
    , bvSRem_bvNat
    , bvShl_bvNat
    , bvShr_bvNat
    , bvSShr_bvNat
    , bvNot_bvNat
    , bvAnd_bvNat
    , bvOr_bvNat
    , bvXor_bvNat
    , bvMbit_bvNat
    , bvEq_bvNat

    , bvugt_bvNat, bvuge_bvNat, bvult_bvNat, bvule_bvNat
    , bvsgt_bvNat, bvsge_bvNat, bvsle_bvNat, bvslt_bvNat

    , bvTrunc_bvNat, bvUExt_bvNat, bvSExt_bvNat

    , get_bvNat, slice_bvNat
    , vTake_bvNat, vDrop_bvNat
    ]

append_bvNat :: Termlike t => Conversion t
append_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef append <:> asNatLit <:> asNatLit <:>
                 asBoolType <:> asBvNatLit <:> asBvNatLit)
    (\((((((), m), n), _), (_, x)), (_, y)) ->
--         return $ mkBvNat (m + n) (shiftL x (fromIntegral n) .|. y)) -- ^ Assuming big-endian order
         return $ mkBvNat (m + n) (x .|. shiftL y (fromIntegral m))) -- ^ Assuming little-endian order
    where
      append = "Prelude.append"

bitMask :: Integer -> Integer
bitMask n = bit (fromInteger n) - 1

preludeBinBVGroundSimplifier :: Termlike t
                             => Ident
                             -> (Integer -> Integer -> Integer -> Integer)  
                             -> Conversion t
preludeBinBVGroundSimplifier symId fn =
    Conversion $
    thenMatcher (matchGlobalDef symId <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\( (((), n), (_, x)), (_, y)) ->
      return $ mkBvNat n (fn n x y))

bvToNat_bvNat :: Termlike t => Conversion t
bvToNat_bvNat =
  Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvToNat" <:> asNatLit <:> asBvNatLit)
    (\( (((), n), (_, x))) ->
      return $ mkNatLit (x .&. bitMask n))

bvAdd_bvNat :: Termlike t => Conversion t
bvAdd_bvNat = preludeBinBVGroundSimplifier "Prelude.bvAdd" (const (+))

bvAddWithCarry_bvNat :: Termlike t => Conversion t
bvAddWithCarry_bvNat = Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvAddWithCarry" <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\( (((), n), (_, x)), (_, y)) -> Just $ do
      let r = x + y
      o <- mkBool $ r `testBit` fromInteger n
      v <- mkBvNat n r
      mkTuple [o, v])

bvSub_bvNat :: Termlike t => Conversion t
bvSub_bvNat = preludeBinBVGroundSimplifier "Prelude.bvSub" (const (-))

bvMul_bvNat :: Termlike t => Conversion t
bvMul_bvNat = preludeBinBVGroundSimplifier "Prelude.bvMul" (const (*))

bvUDiv_bvNat :: Termlike t => Conversion t
bvUDiv_bvNat = Conversion $
   thenMatcher (matchGlobalDef "Prelude.bvUDiv" <:> asNatLit <:> asBvNatLit <:> asBvNatLit) fn
 where fn ((((), n), (_,x)), (_,y))
         | y == 0 = Nothing
         | otherwise = return $ mkBvNat n (x `quot` y)

bvURem_bvNat :: Termlike t => Conversion t
bvURem_bvNat = Conversion $
   thenMatcher (matchGlobalDef "Prelude.bvURem" <:> asNatLit <:> asBvNatLit <:> asBvNatLit) fn
 where fn ((((), n), (_,x)), (_,y))
         | y == 0 = Nothing
         | otherwise = return $ mkBvNat n (x `rem` y)

bvSDiv_bvNat :: Termlike t => Conversion t
bvSDiv_bvNat = Conversion $
   thenMatcher (matchGlobalDef "Prelude.bvSDiv" <:> asNatLit
                                             <:> asSignedBvNatLit
                                             <:> asSignedBvNatLit)
               fn
 where fn ((((), n), x), y)
         | y == 0 = Nothing
         | otherwise = return $ mkBvNat n (x `quot` y)

bvSRem_bvNat :: Termlike t => Conversion t
bvSRem_bvNat = Conversion $
   thenMatcher (matchGlobalDef "Prelude.bvSRem" <:> asNatLit
                                             <:> asSignedBvNatLit
                                             <:> asSignedBvNatLit)
               fn
 where fn ((((), n), x), y)
         | y == 0 = Nothing
         | otherwise = return $ mkBvNat n (x `rem` y)

bvShl_bvNat :: Termlike t => Conversion t
bvShl_bvNat =
   Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvShl" <:> asNatLit <:> asBvNatLit <:> asNatLit)
    (\((((), n), (_,x)), i) ->
      return $ mkBvNat n (x `shiftL` fromInteger i))

bvShr_bvNat :: Termlike t => Conversion t
bvShr_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvShr" <:> asNatLit <:> asBvNatLit <:> asNatLit)
    (\((((), n), (_,x)), i) ->
      return $ mkBvNat n (x `shiftR` fromInteger i))

bvSShr_bvNat :: Termlike t => Conversion t
bvSShr_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvSShr" <:> asNatLit <:> asSignedBvNatLit <:> asNatLit)
    (\((((), n), x), i) ->
      return $ mkBvNat (n+1) (x `shiftR` fromInteger i))

bvNot_bvNat :: Termlike t => Conversion t
bvNot_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvNot" <:> asNatLit <:> asBvNatLit)
    (\(((), n), (_, x)) ->
      return $ mkBvNat n (x `xor` bitMask n))

bvAnd_bvNat :: Termlike t => Conversion t
bvAnd_bvNat = preludeBinBVGroundSimplifier "Prelude.bvAnd" (const (.&.))

bvOr_bvNat  :: Termlike t => Conversion t
bvOr_bvNat  = preludeBinBVGroundSimplifier "Prelude.bvOr" (const (.|.))

bvXor_bvNat :: Termlike t => Conversion t
bvXor_bvNat = preludeBinBVGroundSimplifier "Prelude.bvXor" (const xor)

bvMbit_bvNat :: Termlike t => Conversion t
bvMbit_bvNat =
  Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvMbit" <:> asNatLit <:> asBvNatLit <:> asFinValLit)
    (\( (((), _n), (_, v)), (_, y)) ->
      return $ mkBool (testBit v (fromInteger y)))

bvEq_bvNat :: Termlike t => Conversion t
bvEq_bvNat =
  Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvEq" <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\( (((), n), (_, x)), (_, y)) ->
      return $ mkBool (x .&. bitMask n == y .&. bitMask n))

bvugt_bvNat :: Termlike t => Conversion t
bvugt_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvugt" <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), _), (_, x)), (_, y)) -> return $ mkBool (x > y))

bvuge_bvNat :: Termlike t => Conversion t
bvuge_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvuge" <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), _), (_, x)), (_, y)) -> return $ mkBool (x >= y))

bvult_bvNat :: Termlike t => Conversion t
bvult_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvult" <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), _), (_, x)), (_, y)) -> return $ mkBool (x < y))

bvule_bvNat :: Termlike t => Conversion t
bvule_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvule" <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), _), (_, x)), (_, y)) -> return $ mkBool (x <= y))

bvsgt_bvNat :: Termlike t => Conversion t
bvsgt_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvsgt" <:> asNatLit <:> asSignedBvNatLit <:> asSignedBvNatLit)
    (\((((), _), x), y) -> return $ mkBool (x > y))

bvsge_bvNat :: Termlike t => Conversion t
bvsge_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvsge" 
                                 <:> asNatLit <:> asSignedBvNatLit <:> asSignedBvNatLit)
    (\((((), _), x), y) -> return $ mkBool (x >= y))

bvslt_bvNat :: Termlike t => Conversion t
bvslt_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvslt" <:> asNatLit <:> asSignedBvNatLit <:> asSignedBvNatLit)
    (\((((), _), x), y) -> return $ mkBool (x < y))

bvsle_bvNat :: Termlike t => Conversion t
bvsle_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvsle" 
                                 <:> asNatLit <:> asSignedBvNatLit <:> asSignedBvNatLit)
    (\((((), _), x), y) -> return $ mkBool (x <= y))

bvTrunc_bvNat :: Termlike t => Conversion t
bvTrunc_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvTrunc" <:> asNatLit <:> asNatLit <:> asBvNatLit)
    (\((((), _), y), (_, a)) -> return $ mkBvNat y a)

bvUExt_bvNat :: Termlike t => Conversion t
bvUExt_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvUExt" <:> asNatLit <:> asNatLit <:> asBvNatLit)
    (\((((), x), y), (_, a)) -> return $ mkBvNat (x+y) a)

bvSExt_bvNat :: Termlike t => Conversion t
bvSExt_bvNat =
    Conversion $
    thenMatcher (matchGlobalDef "Prelude.bvSExt" <:> asNatLit <:> asNatLit <:> asSignedBvNatLit)
    (\((((), x), y), a) -> return $ mkBvNat (x+y) a)

get_bvNat :: Termlike t => Conversion t
get_bvNat =
    Conversion $
    thenMatcher
    (matchGlobalDef "Prelude.get" <:> asNatLit <:> asBoolType <:> asBvNatLit <:> asFinValLit)
    (\(((((), _n), ()), (_n', x)), (i, _j)) ->
--         return $ mkBool (testBit x (fromIntegral j))) -- ^ Assuming big-endian order
         return $ mkBool (testBit x (fromIntegral i))) -- ^ Assuming little-endian order

vTake_bvNat :: Termlike t => Conversion t
vTake_bvNat =
    Conversion $
    thenMatcher
    (matchGlobalDef "Prelude.vTake" <:> asBoolType <:> asNatLit <:> asNatLit <:> asBvNatLit)
    (\(((((), ()), m), _n), (_, x)) ->
         return $ mkBvNat m x) -- Assumes little-endian order

vDrop_bvNat :: Termlike t => Conversion t
vDrop_bvNat =
    Conversion $
    thenMatcher
    (matchGlobalDef "Prelude.vDrop" <:> asBoolType <:> asNatLit <:> asNatLit <:> asBvNatLit)
    (\(((((), ()), m), n), (_, x)) ->
         return $ mkBvNat n (x `shiftR` fromInteger m)) -- Assumes little-endian order

slice_bvNat :: Termlike t => Conversion t
slice_bvNat =
    Conversion $
    thenMatcher
    (matchGlobalDef "Prelude.slice" <:> asBoolType <:>
     asNatLit <:> asNatLit <:> asNatLit <:> asBvNatLit)
    (\((((((), _), i), n), j), (m, x)) ->
         guard (i + n + j == m) >>
         let mask = bit (fromIntegral n) - 1
--         in return $ mkBvNat n (shiftR x (fromIntegral j) .&. mask)) -- ^ Assuming big-endian order
         in return $ mkBvNat n (shiftR x (fromIntegral i) .&. mask)) -- ^ Assuming little-endian order