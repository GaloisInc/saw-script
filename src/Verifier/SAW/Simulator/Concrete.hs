{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Verifier.SAW.Simulator.Concrete
Copyright   : Galois, Inc. 2012-2015
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
       , toWord
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

import Verifier.SAW.Prim (BitVector(..), signed, bv, bvNeg)
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST (Module)
import Verifier.SAW.SharedTerm

------------------------------------------------------------

-- type ExtCnsEnv = VarIndex -> String -> CValue

-- | Evaluator for shared terms.
evalSharedTerm :: Module -> Map Ident CValue -> Term -> CValue
evalSharedTerm m addlPrims t =
  runIdentity $ do
    cfg <- Sim.evalGlobal m (Map.union constMap addlPrims)
           Sim.noExtCns (const (const Nothing))
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
bvShiftOp :: (BitVector -> BitVector -> BitVector)
          -> (BitVector -> Int -> BitVector)
          -> CValue
bvShiftOp _bvOp natOp =
  constFun $
  wordFun $ \x ->
  pureFun $ \y ->
    case y of
      VNat n -> vWord (natOp x (fromInteger n))
      _      -> error $ unwords ["Verifier.SAW.Simulator.Concrete.shiftOp", show y]

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
  , ("Prelude.bvPMul", constFun $ binOp (Prim.bvPMul undefined undefined))
  , ("Prelude.bvPMod", constFun $ binOp (Prim.bvPMod undefined undefined))
  , ("Prelude.bvLg2" , Prims.bvLg2Op (return . toWord) (return . Prim.bvLg2))
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
  , ("Prelude.bvShl" , bvShiftOp undefined (Prim.bvShl undefined))
  , ("Prelude.bvShr" , bvShiftOp undefined (Prim.bvShr undefined))
  , ("Prelude.bvSShr", bvShiftOp undefined (Prim.bvSShr undefined))
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
  , ("Prelude.equalNat", Prims.equalNat return)
  , ("Prelude.ltNat", Prims.ltNat return)
  -- Integers
  , ("Prelude.intAdd", Prims.intAddOp)
  , ("Prelude.intSub", Prims.intSubOp)
  , ("Prelude.intMul", Prims.intMulOp)
  , ("Prelude.intDiv", Prims.intDivOp)
  , ("Prelude.intMod", Prims.intModOp)
  , ("Prelude.intNeg", Prims.intNegOp)
  , ("Prelude.intEq" , Prims.intEqOp id)
  , ("Prelude.intLe" , Prims.intLeOp id)
  , ("Prelude.intLt" , Prims.intLtOp id)
  , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", Prims.natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  , ("Prelude.intMin"  , Prims.intMinOp)
  , ("Prelude.intMax"  , Prims.intMaxOp)
  -- Vectors
  , ("Prelude.gen", Prims.genOp)
  , ("Prelude.atWithDefault", Prims.atWithDefaultOp bvUnpack Prim.bvAt ite)
  , ("Prelude.upd", Prims.updOp bvUnpack (\x y -> return (Prim.bvEq undefined x y)) Prim.bv Prim.width ite)
  , ("Prelude.append", Prims.appendOp bvUnpack (Prim.append_bv undefined undefined undefined))
  , ("Prelude.join", Prims.joinOp bvUnpack (Prim.append_bv undefined undefined undefined))
  , ("Prelude.zip", vZipOp)
  , ("Prelude.foldr", foldrOp)
  , ("Prelude.rotateL", rotateLOp)
  , ("Prelude.rotateR", rotateROp)
  , ("Prelude.shiftL", shiftLOp)
  , ("Prelude.shiftR", shiftROp)
  , ("Prelude.EmptyVec", Prims.emptyVec)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  , ("Prelude.bvNat", bvNatOp)
  , ("Prelude.bvToNat", bvToNatOp)
  , ("Prelude.error", Prims.errorOp)
  -- Overloaded
  , ("Prelude.eq", eqOp)
  ]

bvToNatOp :: CValue
bvToNatOp = constFun $ wordFun $ VNat . unsigned

-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
bvToIntOp :: CValue
bvToIntOp = constFun $ wordFun $ VInt . unsigned

-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
sbvToIntOp :: CValue
sbvToIntOp = constFun $ wordFun $ VInt . signed

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
intToBvOp :: CValue
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x -> return $
    VWord $
     if n >= 0 then bv (fromIntegral n) x
               else bvNeg n $ bv (fromIntegral n) $ negate x

-- | ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
iteOp :: CValue
iteOp =
  constFun $
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> if toBool b then force x else force y

bvUnpack :: BitVector -> V.Vector Bool
bvUnpack x = V.generate (Prim.width x) (Prim.bvAt x)

ite :: Bool -> a -> a -> a
ite b x y = if b then x else y

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: CValue
vZipOp =
  constFun $
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  pureFun $ \ys ->
  VVector (V.zipWith (\x y -> ready (vTuple [ready x, ready y])) (toVector xs) (toVector ys))

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

-- rotateL :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateLOp :: CValue
rotateLOp =
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  Prims.natFun $ \i -> return $
    case xs of
      VVector xv -> VVector (vRotateL xv (fromIntegral i))
      VWord w -> vWord (bvRotateL w (fromIntegral i))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.rotateLOp: " ++ show xs

-- rotateR :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateROp :: CValue
rotateROp =
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  Prims.natFun $ \i -> return $
    case xs of
      VVector xv -> VVector (vRotateR xv (fromIntegral i))
      VWord w -> vWord (bvRotateR w (fromIntegral i))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.rotateROp: " ++ show xs

-- shiftL :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftLOp :: CValue
shiftLOp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  pureFun $ \xs ->
  Prims.natFun $ \i -> return $
    case xs of
      VVector xv -> VVector (vShiftL x xv (fromIntegral i))
      VWord w -> vWord (bvShiftL c w (fromIntegral i))
        where c = toBool (runIdentity (force x))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.shiftLOp: " ++ show xs

-- shiftR :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftROp :: CValue
shiftROp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  pureFun $ \xs ->
  Prims.natFun $ \i -> return $
    case xs of
      VVector xv -> VVector (vShiftR x xv (fromIntegral i))
      VWord w -> vWord (bvShiftR c w (fromIntegral i))
        where c = toBool (runIdentity (force x))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.shiftROp: " ++ show xs

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
