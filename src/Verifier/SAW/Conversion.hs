{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Conversion
  ( isGlobalDef
  , Matcher
  , (<:>)
  , asAny
  , asFinValLit
  , asGlobalDef
  , thenMatcher
  , TermBuilder
  , mkAny
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

import Control.Applicative ((<$>), pure, (<*>))
import Control.Exception (assert)
import Control.Monad (guard, (>=>))
import Data.Bits
import Data.Map (Map)
import qualified Data.Vector as V

import Verifier.SAW.SharedTerm (Termlike(..))
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

destNatLit :: Termlike t => t -> Maybe Integer
destNatLit (unwrapTermF -> FTermF (NatLit i)) = Just i
destNatLit _ = Nothing

asNatLit :: Termlike t => Matcher t Integer
asNatLit = Matcher Net.Var match
    where
      match (unwrapTermF -> FTermF (NatLit i)) = Just i
      match _ = Nothing

asVecLit :: Termlike t => Matcher t (t, V.Vector t)
asVecLit = Matcher Net.Var match
    where
      match (unwrapTermF -> FTermF (ArrayValue t xs)) = Just (t, xs)
      match _ = Nothing

isGlobalDef :: Termlike t => Ident -> t -> Maybe () 
isGlobalDef i (unwrapTermF -> FTermF (GlobalDef i')) | i == i' = Just ()
isGlobalDef _ _ = Nothing

asGlobalDef :: Termlike t => Ident -> Matcher t ()
asGlobalDef ident = Matcher (Net.Atom (identName ident)) (isGlobalDef ident)

asBoolType :: Termlike t => Matcher t ()
asBoolType = Matcher (Net.Atom (identName bool)) match
    where
      match (unwrapTermF -> FTermF (DataTypeApp ident [])) | ident == bool = Just ()
      match _ = Nothing
      bool = "Prelude.Bool"

asFinValLit :: Termlike t => Matcher t (Integer, Integer)
asFinValLit = Matcher pat match
    where
      pat = Net.App (Net.App (Net.Atom (identName finval)) Net.Var) Net.Var
      match (unwrapTermF -> FTermF (CtorApp ident [x, y]))
          | ident == finval = (,) <$> destNatLit x <*> destNatLit y
      match _ = Nothing
      finval = "Prelude.FinVal"

asSuccLit :: Termlike t => Matcher t Integer
asSuccLit = Matcher pat match
    where
      pat = Net.App (Net.Atom (identName succ)) Net.Var
      match (unwrapTermF -> FTermF (CtorApp ident [x]))
          | ident == succ = destNatLit x
      match _ = Nothing
      succ = "Prelude.Succ"

asBvNatLit :: Termlike t => Matcher t (Integer, Integer)
asBvNatLit =
    thenMatcher (asGlobalDef "Prelude.bvNat" <:> asNatLit <:> asNatLit) $
        \(((), n), x) -> return (n, x .&. bitMask n)


normSignedBV :: Int -> Integer -> Integer
normSignedBV n x | testBit x n = x' - bit (n+1)
                 | otherwise   = x'
  where mask = bit (n+1) - 1
        x' = x .&. mask


asSignedBvNatLit :: Termlike t => Matcher t Integer
asSignedBvNatLit =
    thenMatcher (asGlobalDef "Prelude.bvNat" <:> asNatLit <:> asNatLit) $
        \(((), n), x) -> return (normSignedBV (fromInteger n) x)

----------------------------------------------------------------------
-- Term builders

newtype TermBuilder t =
    TermBuilder { runTermBuilder :: forall m. Monad m => (TermF t -> m t) -> m t }

mkAny :: t -> TermBuilder t
mkAny t = TermBuilder $ \mk -> return t

mkBool :: Bool -> TermBuilder t
mkBool b = TermBuilder $ \mk -> mk (FTermF (CtorApp idSym []))
  where idSym | b = "Prelude.True" 
              | otherwise = "Prelude.False"

mkNatLit :: Integer -> TermBuilder t
mkNatLit n = TermBuilder $ \mk -> mk (FTermF (NatLit n))

mkVecLit :: t -> V.Vector t -> TermBuilder t
mkVecLit t xs = TermBuilder $ \mk -> mk (FTermF (ArrayValue t xs))

mkFinVal :: Integer -> Integer -> TermBuilder t
mkFinVal i j = TermBuilder $ \mk ->
    do i' <- mk (FTermF (NatLit i))
       j' <- mk (FTermF (NatLit j))
       mk (FTermF (CtorApp "Prelude.FinVal" [i', j']))

mkBvNat :: Integer -> Integer -> TermBuilder t
mkBvNat n x = TermBuilder $ \mk -> assert (n >= 0) $ 
    do n' <- mk (FTermF (NatLit n))
       x' <- mk $ FTermF $ NatLit $ x .&. bitMask n 
       t0 <- mk (FTermF (GlobalDef "Prelude.bvNat"))
       t1 <- mk (FTermF (App t0 n'))
       t2 <- mk (FTermF (App t1 x'))
       return t2

----------------------------------------------------------------------
-- Conversions

-- | These are conversions in the LCF-style term-rewriting sense: A
-- conversion is a function that takes a term and returns (possibly) a
-- rewritten term. We use conversions to model the behavior of
-- primitive operations in SAWCore.

newtype Conversion t = Conversion (Matcher t (TermBuilder t))

runConversion :: Conversion t -> t -> Maybe (TermBuilder t)
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
    thenMatcher (asGlobalDef addNat <:> asNatLit <:> asNatLit)
    (\(((), m), n) -> return $ mkNatLit (m + n))
    where addNat = "Prelude.addNat"

-- | Conversions for operations on Fin literals
finConversions :: Termlike t => [Conversion t]
finConversions = [finInc_FinVal, finIncLim_FinVal]

finInc_FinVal :: Termlike t => Conversion t
finInc_FinVal =
    Conversion $
    thenMatcher (asGlobalDef "Prelude.finInc" <:> asNatLit <:> asNatLit <:> asFinValLit)
    (\((((), m), n), (i, j)) ->
         guard (n == i + j + 1) >> return (mkFinVal (m + i) j))

finIncLim_FinVal :: Termlike t => Conversion t
finIncLim_FinVal =
    Conversion $
    thenMatcher (asGlobalDef finIncLim <:> asNatLit <:> asNatLit <:> asFinValLit)
    (\((((), m), n), (i, j)) ->
         guard (n == i + j + 1) >> return (mkFinVal i (m + j)))
    where
      finIncLim = "Prelude.finIncLim"

-- | Conversions for operations on vector literals
vecConversions :: Termlike t => [Conversion t]
vecConversions = [get_VecLit, append_VecLit]

get_VecLit :: Termlike t => Conversion t
get_VecLit =
    Conversion $
    thenMatcher (asGlobalDef get <:> asNatLit <:> asAny <:> asVecLit <:> asFinValLit)
    (\(((((), n), e), (_, xs)), (i, j)) ->
         return $ mkAny (xs V.! fromIntegral i))
    where
      get = "Prelude.get"

append_VecLit :: Termlike t => Conversion t
append_VecLit =
    Conversion $
    thenMatcher (asGlobalDef append <:> asNatLit <:> asNatLit <:> asAny <:> asVecLit <:> asVecLit)
    (\((((((), m), n), e), (_, xs)), (_, ys)) ->
         return $ mkVecLit e ((V.++) xs ys))
    where append = "Prelude.append"


-- | Conversions for operations on bitvector literals
bvConversions :: Termlike t => [Conversion t]
bvConversions =
    [ bvToNat_bvNat
    , bvEq_bvNat
    , append_bvNat
    , bvAdd_bvNat, bvSub_bvNat, bvMul_bvNat, bvNot_bvNat
    , bvule_bvNat, bvult_bvNat, bvsle_bvNat, bvslt_bvNat
    , bvUExt_bvNat, bvSExt_bvNat
    , get_bvNat, slice_bvNat
    ]

append_bvNat :: Termlike t => Conversion t
append_bvNat =
    Conversion $
    thenMatcher (asGlobalDef append <:> asNatLit <:> asNatLit <:>
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
    thenMatcher (asGlobalDef symId <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\( (((), n), (_, x)), (_, y)) ->
      return $ mkBvNat n (fn n x y .&. bitMask n))

bvToNat_bvNat :: Termlike t => Conversion t
bvToNat_bvNat =
  Conversion $
    thenMatcher (asGlobalDef "Prelude.bvToNat" <:> asNatLit <:> asBvNatLit)
    (\( (((), n), (_, x))) ->
      return $ mkNatLit (x .&. bitMask n))

bvEq_bvNat :: Termlike t => Conversion t
bvEq_bvNat =
  Conversion $
    thenMatcher (asGlobalDef "Prelude.bvEq" <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\( (((), n), (_, x)), (_, y)) ->
      return $ mkBool (x .&. bitMask n == y .&. bitMask n))

bvAdd_bvNat :: Termlike t => Conversion t
bvAdd_bvNat = preludeBinBVGroundSimplifier "Prelude.bvAdd" (const (+))

bvSub_bvNat :: Termlike t => Conversion t
bvSub_bvNat = preludeBinBVGroundSimplifier "Prelude.bvSub" (const (-))

bvMul_bvNat :: Termlike t => Conversion t
bvMul_bvNat = preludeBinBVGroundSimplifier "Prelude.bvMul" (const (*))

bvNot_bvNat :: Termlike t => Conversion t
bvNot_bvNat =
    Conversion $
    thenMatcher (asGlobalDef "Prelude.bvNot" <:> asNatLit <:> asBvNatLit)
    (\(((), n), (_, x)) ->
      return $ mkBvNat n (x `xor` bitMask n))

bvule_bvNat :: Termlike t => Conversion t
bvule_bvNat =
    Conversion $
    thenMatcher (asGlobalDef "Prelude.bvule" <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), _), (_, x)), (_, y)) -> return $ mkBool (x <= y))

bvult_bvNat :: Termlike t => Conversion t
bvult_bvNat =
    Conversion $
    thenMatcher (asGlobalDef "Prelude.bvult" <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), _), (_, x)), (_, y)) -> return $ mkBool (x < y))

bvsle_bvNat :: Termlike t => Conversion t
bvsle_bvNat =
    Conversion $
    thenMatcher (asGlobalDef "Prelude.bvsle" 
                                 <:> asNatLit <:> asSignedBvNatLit <:> asSignedBvNatLit)
    (\((((), _), x), y) -> return $ mkBool (x <= y))

bvslt_bvNat :: Termlike t => Conversion t
bvslt_bvNat =
    Conversion $
    thenMatcher (asGlobalDef "Prelude.bvslt" <:> asNatLit <:> asSignedBvNatLit <:> asSignedBvNatLit)
    (\((((), _), x), y) -> return $ mkBool (x < y))

bvUExt_bvNat :: Termlike t => Conversion t
bvUExt_bvNat =
    Conversion $
    thenMatcher (asGlobalDef "Prelude.bvUExt" <:> asNatLit <:> asNatLit <:> asBvNatLit)
    (\((((), x), y), (_, a)) -> return $ mkBvNat (x+y) a)

bvSExt_bvNat :: Termlike t => Conversion t
bvSExt_bvNat =
    Conversion $
    thenMatcher (asGlobalDef "Prelude.bvSExt" <:> asNatLit <:> asNatLit <:> asSignedBvNatLit)
    (\((((), x), y), a) -> return $ mkBvNat (x+y) a)

get_bvNat :: Termlike t => Conversion t
get_bvNat =
    Conversion $
    thenMatcher
    (asGlobalDef "Prelude.get" <:> asNatLit <:> asBoolType <:> asBvNatLit <:> asFinValLit)
    (\(((((), n), ()), (n', x)), (i, j)) ->
--         return $ mkBool (testBit x (fromIntegral j))) -- ^ Assuming big-endian order
         return $ mkBool (testBit x (fromIntegral i))) -- ^ Assuming little-endian order

slice_bvNat :: Termlike t => Conversion t
slice_bvNat =
    Conversion $
    thenMatcher
    (asGlobalDef "Prelude.slice" <:> asBoolType <:>
     asNatLit <:> asNatLit <:> asNatLit <:> asBvNatLit)
    (\((((((), _), i), n), j), (m, x)) ->
         guard (i + n + j == m) >>
         let mask = bit (fromIntegral n) - 1
--         in return $ mkBvNat n (shiftR x (fromIntegral j) .&. mask)) -- ^ Assuming big-endian order
         in return $ mkBvNat n (shiftR x (fromIntegral i) .&. mask)) -- ^ Assuming little-endian order