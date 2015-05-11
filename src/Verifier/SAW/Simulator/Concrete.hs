{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Verifier.SAW.Simulator.Concrete
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.Concrete
       ( evalSharedTerm
       , CValue, Value(..)
       , CExtra(..)
       , toBool
       , runIdentity
       ) where

--import Control.Applicative
--import Control.Monad (zipWithM, (<=<))
import Control.Monad.Identity
import Data.Bits
import Data.IntTrie (IntTrie)
import qualified Data.IntTrie as IntTrie
import Data.Map (Map)
import qualified Data.Map as Map
--import Data.Traversable
import Data.Vector (Vector)
import qualified Data.Vector as V

import Verifier.SAW.Prim (BitVector(..))
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST (Module)
import Verifier.SAW.SharedTerm

------------------------------------------------------------

-- type ExtCnsEnv = VarIndex -> String -> CValue

-- | Evaluator for shared terms.
evalSharedTerm :: Module -> SharedTerm s -> CValue
evalSharedTerm m t =
  runIdentity $ do
    cfg <- Sim.evalGlobal m constMap (const (const Nothing))
    Sim.evalSharedTerm cfg t

------------------------------------------------------------
-- BitVector operations

bvRotateL :: BitVector -> Int -> BitVector
bvRotateL (BV w x) i = Prim.bv w ((x `shiftL` j) .|. (x `shiftR` (w - j)))
  where j = i `mod` w

bvRotateR :: BitVector -> Int -> BitVector
bvRotateR w i = bvRotateL w (- i)

bvShiftL :: Bool -> BitVector -> Int -> BitVector
bvShiftL c (BV w x) i = Prim.bv w ((x `shiftL` i) .|. c')
  where c' = if c then (1 `shiftL` i) - 1 else 0

bvShiftR :: Bool -> BitVector -> Int -> BitVector
bvShiftR c (BV w x) i = Prim.bv w (c' .|. (x `shiftR` i))
  where c' = if c then (full `shiftL` (w - j)) .&. full else 0
        full = (1 `shiftL` w) - 1
        j  = min w i

------------------------------------------------------------
-- Vector operations

vRotateL :: V.Vector a -> Int -> V.Vector a
vRotateL xs i
  | V.null xs = xs
  | otherwise = (V.++) (V.drop j xs) (V.take j xs)
  where j = i `mod` V.length xs

vRotateR :: V.Vector a -> Int -> V.Vector a
vRotateR xs i = vRotateL xs (- i)

vShiftL :: a -> V.Vector a -> Int -> V.Vector a
vShiftL x xs i = (V.++) (V.drop j xs) (V.replicate j x)
  where j = min i (V.length xs)

vShiftR :: a -> V.Vector a -> Int -> V.Vector a
vShiftR x xs i = (V.++) (V.replicate j x) (V.take (V.length xs - j) xs)
  where j = min i (V.length xs)

------------------------------------------------------------
-- Values

type CValue = Value Identity Bool BitVector CExtra

data CExtra
  = CStream (IntTrie CValue)

instance Show CExtra where
  show (CStream _) = "<stream>"

vBool :: Bool -> CValue
vBool b = VBool b

toBool :: CValue -> Bool
toBool (VBool b) = b
toBool x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toBool", show x]

vWord :: BitVector -> CValue
vWord x = VWord x

-- | Conversion from list of bits to integer (big-endian)
bvToInteger :: Vector Bool -> Integer
bvToInteger = V.foldl' (\x b -> if b then 2*x+1 else 2*x) 0

explodeBitVector :: BitVector -> Vector Bool
explodeBitVector (BV w x) = V.reverse (V.generate w (testBit x))

toWord :: CValue -> BitVector
toWord (VWord x) = x
toWord (VVector vv) = BV (V.length vv) (bvToInteger (fmap (toBool . runIdentity . force) vv))
toWord x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toWord", show x]

vStream :: IntTrie CValue -> CValue
vStream x = VExtra (CStream x)

toStream :: CValue -> IntTrie CValue
toStream (VExtra (CStream x)) = x
toStream x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toStream", show x]

toVector :: CValue -> V.Vector CValue
toVector (VVector xv) = fmap (runIdentity . force) xv
toVector (VWord w) = fmap vBool (explodeBitVector w)
toVector x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toVector", show x]

{-
flattenBValue :: CValue -> BitVector
flattenBValue (VExtra (BBool l)) = return (AIG.replicate 1 l)
flattenBValue (VWord lv) = return lv
flattenBValue (VExtra (CStream _ _)) = error "Verifier.SAW.Simulator.Concrete.flattenBValue: CStream"
flattenBValue (VVector vv) =
  AIG.concat <$> traverse (flattenBValue <=< force) (V.toList vv)
flattenBValue (VTuple vv) =
  AIG.concat <$> traverse (flattenBValue <=< force) (V.toList vv)
flattenBValue (VRecord m) =
  AIG.concat <$> traverse (flattenBValue <=< force) (Map.elems m)
flattenBValue _ = error $ unwords ["Verifier.SAW.Simulator.Concrete.flattenBValue: unsupported value"]
-}

wordFun :: (BitVector -> CValue) -> CValue
wordFun f = pureFun (\x -> f (toWord x))

-- | op :: Bool -> Bool -> Bool
boolBinOp :: (Bool -> Bool -> Bool) -> CValue
boolBinOp op =
  pureFun $ \x ->
  pureFun $ \y -> vBool (op (toBool x) (toBool y))

-- | op :: (n :: Nat) -> bitvector n -> bitvector n
unOp :: (BitVector -> BitVector) -> CValue
unOp op =
  constFun $
  wordFun $ \x -> vWord (op x)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n
binOp :: (BitVector -> BitVector -> BitVector) -> CValue
binOp op =
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vWord (op x y)

binOp' :: (BitVector -> BitVector -> Maybe BitVector) -> CValue
binOp' op =
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> maybe Prim.divideByZero vWord (op x y)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> Bool
binRel :: (BitVector -> BitVector -> Bool) -> CValue
binRel op =
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vBool (op x y)

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
shiftOp :: (BitVector -> BitVector -> BitVector)
        -> (BitVector -> Int -> BitVector)
        -> CValue
shiftOp _bvOp natOp =
  constFun $
  wordFun $ \x ->
  pureFun $ \y ->
    case y of
      VNat n           -> vWord (natOp x (fromInteger n))
      _                -> error $ unwords ["Verifier.SAW.Simulator.Concrete.shiftOp", show y]

------------------------------------------------------------

constMap :: Map Ident CValue
constMap = Map.fromList
  -- Boolean
  [ ("Prelude.True"  , vBool True)
  , ("Prelude.False" , vBool False)
  , ("Prelude.not"   , pureFun (vBool . not . toBool))
  , ("Prelude.and"   , boolBinOp (&&))
  , ("Prelude.or"    , boolBinOp (||))
  , ("Prelude.xor"   , boolBinOp (/=))
  , ("Prelude.boolEq", boolBinOp (==))
  , ("Prelude.ite"   , iteOp)
  -- Arithmetic
  , ("Prelude.bvNeg" , unOp (Prim.bvNeg undefined))
  , ("Prelude.bvAdd" , binOp (Prim.bvAdd undefined))
  , ("Prelude.bvSub" , binOp (Prim.bvSub undefined))
  , ("Prelude.bvMul" , binOp (Prim.bvMul undefined))
  , ("Prelude.bvAnd" , binOp (Prim.bvAnd undefined))
  , ("Prelude.bvOr"  , binOp (Prim.bvOr undefined))
  , ("Prelude.bvXor" , binOp (Prim.bvXor undefined))
  , ("Prelude.bvUDiv", binOp' (Prim.bvUDiv undefined))
  , ("Prelude.bvURem", binOp' (Prim.bvURem undefined))
  , ("Prelude.bvSDiv", binOp' (Prim.bvSDiv undefined))
  , ("Prelude.bvSRem", binOp' (Prim.bvSRem undefined))
  , ("Prelude.bvPMul", binOp (Prim.bvPMul undefined undefined))
  , ("Prelude.bvPMod", binOp (Prim.bvPDiv undefined undefined))
  -- Relations
  , ("Prelude.bvEq"  , binRel (Prim.bvEq undefined))
  , ("Prelude.bvsle" , binRel (Prim.bvsle undefined))
  , ("Prelude.bvslt" , binRel (Prim.bvslt undefined))
  , ("Prelude.bvule" , binRel (Prim.bvule undefined))
  , ("Prelude.bvult" , binRel (Prim.bvult undefined))
  , ("Prelude.bvsge" , binRel (Prim.bvsge undefined))
  , ("Prelude.bvsgt" , binRel (Prim.bvsgt undefined))
  , ("Prelude.bvuge" , binRel (Prim.bvuge undefined))
  , ("Prelude.bvugt" , binRel (Prim.bvugt undefined))
  -- Shifts
  , ("Prelude.bvShl" , shiftOp undefined (Prim.bvShl undefined))
  , ("Prelude.bvShr" , shiftOp undefined (Prim.bvShr undefined))
  , ("Prelude.bvSShr", shiftOp undefined (Prim.bvSShr undefined))
  -- Nat
  , ("Prelude.Succ", Prims.succOp)
  , ("Prelude.addNat", Prims.addNatOp)
  , ("Prelude.subNat", Prims.subNatOp)
  , ("Prelude.mulNat", Prims.mulNatOp)
  , ("Prelude.minNat", Prims.minNatOp)
  , ("Prelude.maxNat", Prims.maxNatOp)
  , ("Prelude.divModNat", Prims.divModNatOp)
  , ("Prelude.expNat", Prims.expNatOp)
  , ("Prelude.widthNat", Prims.widthNatOp)
  , ("Prelude.natCase", Prims.natCaseOp)
  -- Fin
  , ("Prelude.finDivMod", Prims.finDivModOp)
  , ("Prelude.finMax", Prims.finMaxOp)
  , ("Prelude.finPred", Prims.finPredOp)
  , ("Prelude.natSplitFin", Prims.natSplitFinOp)
  -- Vectors
  , ("Prelude.generate", Prims.generateOp)
  , ("Prelude.get", getOp)
  , ("Prelude.set", setOp)
  , ("Prelude.at", Prims.atOp bvUnpack Prim.bvAt ite)
  , ("Prelude.upd", Prims.updOp bvUnpack (\x y -> return (Prim.bvEq undefined x y)) Prim.bv Prim.width ite)
  , ("Prelude.append", appendOp)
  , ("Prelude.vZip", vZipOp)
  , ("Prelude.foldr", foldrOp)
  , ("Prelude.bvRotateL", bvRotateLOp)
  , ("Prelude.bvRotateR", bvRotateROp)
  , ("Prelude.bvShiftL", bvShiftLOp)
  , ("Prelude.bvShiftR", bvShiftROp)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  , ("Prelude.bvNat", bvNatOp)
  , ("Prelude.bvToNat", bvToNatOp)
  -- Overloaded
  , ("Prelude.zero", zeroOp)
  , ("Prelude.unary", Prims.unaryOp mkStreamOp streamGetOp)
  , ("Prelude.binary", Prims.binaryOp mkStreamOp streamGetOp)
  , ("Prelude.eq", eqOp)
  , ("Prelude.comparison", Prims.comparisonOp)
  ]

bvToNatOp :: CValue
bvToNatOp = constFun $ wordFun $ VNat . unsigned

-- | ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
iteOp :: CValue
iteOp =
  constFun $
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> if toBool b then force x else force y

-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
getOp :: CValue
getOp =
  constFun $
  constFun $
  pureFun $ \v ->
  Prims.finFun $ \i ->
    case v of
      VVector xv -> force $ (V.!) xv (fromEnum (Prim.finVal i))
      VWord w -> return $ vBool (Prim.get_bv undefined undefined w i)
      _ -> fail $ "Verifier.SAW.Simulator.Concrete.getOp: expected vector, got " ++ show v

-- set :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a -> Vec n a;
setOp :: CValue
setOp =
  constFun $
  constFun $
  pureFun $ \v ->
  Prims.finFun $ \i -> return $
  VFun $ \y -> return $
    case v of
      VVector xv -> VVector ((V.//) xv [(fromEnum (Prim.finVal i), y)])
      _ -> error $ "Verifier.SAW.Simulator.Concrete.setOp: expected vector, got " ++ show v

bvUnpack :: BitVector -> V.Vector Bool
bvUnpack x = V.generate (Prim.width x) (Prim.bvAt x)

ite :: Bool -> a -> a -> a
ite b x y = if b then x else y

-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: CValue
appendOp =
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  pureFun $ \ys ->
  case (xs, ys) of
    (VVector xv, VVector yv)         -> VVector ((V.++) xv yv)
    (VVector xv, VWord yw) -> VVector ((V.++) xv (fmap (ready . vBool) (explodeBitVector yw)))
    (VWord xw, VVector yv) -> VVector ((V.++) (fmap (ready . vBool) (explodeBitVector xw)) yv)
    (VWord xw, VWord yw) -> vWord (Prim.append_bv undefined undefined undefined xw yw)
    _ -> error "Verifier.SAW.Simulator.Concrete.appendOp"

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: CValue
vZipOp =
  constFun $
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  pureFun $ \ys ->
  VVector (V.zipWith (\x y -> ready (VTuple (V.fromList [ready x, ready y]))) (toVector xs) (toVector ys))

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: CValue
foldrOp =
  constFun $
  constFun $
  constFun $
  strictFun $ \f -> return $
  VFun $ \z -> return $
  strictFun $ \xs -> do
    let g x m = do fx <- apply f x
                   y <- delay m
                   apply fx y
    case xs of
      VVector xv -> V.foldr g (force z) xv
      _ -> fail "Verifier.SAW.Simulator.Concrete.foldrOp"

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNatOp :: CValue
bvNatOp =
  Prims.natFun'' "bvNatOp1" $ \w -> return $
  Prims.natFun'' "bvNatOp2"  $ \x -> return $
  VWord (Prim.bv (fromIntegral w) (toInteger x))

-- bvRotateL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateLOp :: CValue
bvRotateLOp =
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  wordFun $ \i ->
    case xs of
      VVector xv -> VVector (vRotateL xv (fromInteger (unsigned i)))
      VWord w -> vWord (bvRotateL w (fromInteger (unsigned i)))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.bvRotateLOp: " ++ show xs

-- bvRotateR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateROp :: CValue
bvRotateROp =
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  wordFun $ \i ->
    case xs of
      VVector xv -> VVector (vRotateR xv (fromInteger (unsigned i)))
      VWord w -> vWord (bvRotateR w (fromInteger (unsigned i)))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.bvRotateROp: " ++ show xs

-- bvShiftL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftLOp :: CValue
bvShiftLOp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  pureFun $ \xs ->
  wordFun $ \i ->
    case xs of
      VVector xv -> VVector (vShiftL x xv (fromInteger (unsigned i)))
      VWord w -> vWord (bvShiftL c w (fromInteger (unsigned i)))
        where c = toBool (runIdentity (force x))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.bvShiftLOp: " ++ show xs

-- bvShiftR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftROp :: CValue
bvShiftROp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  pureFun $ \xs ->
  wordFun $ \i ->
    case xs of
      VVector xv -> VVector (vShiftR x xv (fromInteger (unsigned i)))
      VWord w -> vWord (bvShiftR c w (fromInteger (unsigned i)))
        where c = toBool (runIdentity (force x))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.bvShiftROp: " ++ show xs

zeroOp :: CValue
zeroOp = Prims.zeroOp bvZ boolZ mkStreamOp
  where bvZ n = return (vWord (Prim.bv (fromInteger n) 0))
        boolZ = return (vBool False)

eqOp :: CValue
eqOp = Prims.eqOp trueOp andOp boolOp bvOp
  where trueOp = vBool True
        andOp x y = return (vBool (toBool x && toBool y))
        boolOp x y = return (vBool (toBool x == toBool y))
        bvOp _ x y = return (vBool (Prim.bvEq undefined (toWord x) (toWord y)))

----------------------------------------

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: CValue
mkStreamOp =
  constFun $
  pureFun $ \f ->
  vStream (fmap (\n -> runIdentity (apply f (ready (VNat n)))) IntTrie.identity)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: CValue
streamGetOp =
  constFun $
  pureFun $ \xs ->
  Prims.natFun'' "streamGetOp" $ \n -> return $
  IntTrie.apply (toStream xs) n

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: CValue
bvStreamGetOp =
  constFun $
  constFun $
  pureFun $ \xs ->
  wordFun $ \i ->
  IntTrie.apply (toStream xs) (Prim.unsigned i)
