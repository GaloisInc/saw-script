{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.Simulator.BitBlast where

import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable
import qualified Data.Vector as V
import qualified Data.Vector.Storable as LV

import Verifier.SAW.Prim (Nat)
import Verifier.SAW.Simulator
import Verifier.SAW.TypedAST (Ident)

import Verinf.Symbolic.Lit

------------------------------------------------------------
-- Values

type BValue l = Value IO (BExtra l)

data BExtra l
  = BBool l
  | BWord (LitVector l) -- ^ Bits in LSB order
  | BToNat Nat (LitVector l)

-- | Swap from big-endian to little-endian
lvFromV :: LV.Storable l => V.Vector l -> LV.Vector l
lvFromV v = LV.generate (V.length v) ((V.!) (V.reverse v))

-- | Swap from little-endian to big-endian
vFromLV :: LV.Storable l => LV.Vector l -> V.Vector l
vFromLV lv = V.generate (LV.length lv) ((LV.!) (LV.reverse lv))

vBool :: l -> BValue l
vBool l = VExtra (BBool l)

toBool :: BValue l -> l
toBool (VExtra (BBool l)) = l
toBool _ = error "toBool"

vWord :: LitVector l -> BValue l
vWord lv = VExtra (BWord lv)

toWord :: LV.Storable l => BValue l -> IO (LitVector l)
toWord (VExtra (BWord lv)) = return lv
toWord (VVector vv) = lvFromV <$> traverse (fmap toBool . force) vv
toWord _ = fail "toWord"

wordFun :: LV.Storable l => (LitVector l -> IO (BValue l)) -> BValue l
wordFun f = strictFun (\x -> toWord x >>= f)

-- | op :: Bool -> Bool -> Bool
boolBinOp :: (l -> l -> IO l) -> BValue l
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> vBool <$> op (toBool x) (toBool y)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n
binOp :: LV.Storable l => (LitVector l -> LitVector l -> IO (LitVector l)) -> BValue l
binOp op =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> Bool
binRel :: LV.Storable l => (LitVector l -> LitVector l -> IO l) -> BValue l
binRel op =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vBool <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
shiftOp :: LV.Storable l =>
           (LitVector l -> LitVector l -> IO (LitVector l))
        -> (LitVector l -> Nat -> LitVector l)
        -> BValue l
shiftOp bvOp natOp =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  strictFun $ \y ->
    case y of
      VExtra (BToNat _ lv) -> vWord <$> bvOp x lv
      VNat n               -> return (vWord (natOp x (fromInteger n)))
      _                    -> error "shiftOp"

------------------------------------------------------------

lvShl :: LV.Storable l => l -> LV.Vector l -> Nat -> LV.Vector l
lvShl l v i = LV.replicate j l LV.++ LV.take (n-j) v
  where n = LV.length v
        j = fromIntegral i `min` n

lvShr :: LV.Storable l => l -> LV.Vector l -> Nat -> LV.Vector l
lvShr l v i = LV.drop j v LV.++ LV.replicate j l
  where j = fromIntegral i `min` LV.length v

lvSShr :: LV.Storable l => LV.Vector l -> Nat -> LV.Vector l
lvSShr v i = LV.drop j v LV.++ LV.replicate j l
  where j = fromIntegral i `min` LV.length v
        l = LV.last v

------------------------------------------------------------

beConstMap :: LV.Storable l => BitEngine l -> Map Ident (BValue l)
beConstMap be = Map.fromList
  -- Boolean
  [ ("Prelude.True"  , vBool (beTrue be))
  , ("Prelude.False" , vBool (beFalse be))
  , ("Prelude.not"   , strictFun (return . vBool . beNeg be . toBool))
  , ("Prelude.and"   , boolBinOp (beAnd be))
  , ("Prelude.or"    , boolBinOp (beOr be))
  , ("Prelude.xor"   , boolBinOp (beXor be))
  , ("Prelude.boolEq", boolBinOp (beEq be))
  , ("Prelude.ite"   , iteOp be)
  -- Arithmetic
  , ("Prelude.bvAdd" , binOp (beAddInt be))
  , ("Prelude.bvSub" , binOp (beSubInt be))
  , ("Prelude.bvMul" , binOp (beMulInt be))
  , ("Prelude.bvAnd" , binOp (beAndInt be))
  , ("Prelude.bvOr"  , binOp (beOrInt be))
  , ("Prelude.bvXor" , binOp (beXorInt be))
  , ("Prelude.bvUDiv", binOp (beQuotUnsigned be))
  , ("Prelude.bvURem", binOp (beRemUnsigned be))
  , ("Prelude.bvSDiv", binOp (beQuot be))
  , ("Prelude.bvSRem", binOp (beRem be))
  -- Relations
  , ("Prelude.bvEq"  , binRel (beEqVector be))
  , ("Prelude.bvsle" , binRel (beSignedLeq be))
  , ("Prelude.bvslt" , binRel (beSignedLt be))
  , ("Prelude.bvule" , binRel (beUnsignedLeq be))
  , ("Prelude.bvult" , binRel (beUnsignedLt be))
  , ("Prelude.bvsge" , binRel (flip (beSignedLeq be)))
  , ("Prelude.bvsgt" , binRel (flip (beSignedLt be)))
  , ("Prelude.bvuge" , binRel (flip (beUnsignedLeq be)))
  , ("Prelude.bvugt" , binRel (flip (beUnsignedLt be)))
  -- Shifts
  , ("Prelude.bvShl" , shiftOp (beShl be) (lvShl (beFalse be)))
  , ("Prelude.bvShr" , shiftOp (beUnsignedShr be) (lvShr (beFalse be)))
  , ("Prelude.bvSShr", shiftOp (beSignedShr be) lvSShr)
  ]

-- | ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
iteOp :: forall l. (LV.Storable l) => BitEngine l -> BValue l
iteOp be =
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> beLazyMux be muxFn (toBool b) (force x) (force y)
  where
    muxFn :: l -> BValue l -> BValue l -> IO (BValue l)
    muxFn b (VExtra x) (VExtra y) = VExtra <$> extraFn b x y
    muxFn _ _ _ = fail "iteOp: unimplemented"

    extraFn :: l -> BExtra l -> BExtra l -> IO (BExtra l)
    extraFn b (BBool x) (BBool y) = BBool <$> beMux be b x y
    extraFn b (BWord x) (BWord y) | LV.length x == LV.length y = BWord <$> LV.zipWithM (beMux be b) x y
    extraFn b (BToNat m x) (BToNat n y) | m == n && LV.length x == LV.length y = BToNat m <$> LV.zipWithM (beMux be b) x y
    extraFn _ _ _ = fail "iteOp: malformed arguments"
{-
  | BWord (LitVector l) -- ^ Bits in LSB order
  | BToNat Nat (LitVector l)

                iteFn (BVector x) (BVector y)
                  | V.length x == V.length y
                  = BVector <$> V.zipWithM iteFn x y
                iteFn (BTuple x) (BTuple y)
                  | length x == length y
                  = BTuple <$> zipWithM iteFn x y
                iteFn (BRecord x) (BRecord y)
                  | Map.keys x == Map.keys y
                  = fmap BRecord $ sequenceOf traverse 
                                 $ Map.intersectionWith iteFn x y
                iteFn _ _ = fail "malformed arguments."
-}
