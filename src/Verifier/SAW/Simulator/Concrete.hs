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

------------------------------------------------------------
-- Vector operations

vRotateL :: V.Vector a -> Int -> V.Vector a
vRotateL xs i
  | V.null xs = xs
  | otherwise = (V.++) (V.drop j xs) (V.take j xs)
  where j = i `mod` V.length xs

vRotateR :: V.Vector a -> Int -> V.Vector a
vRotateR xs i = vRotateL xs (- i)

_vShiftL :: a -> V.Vector a -> Int -> V.Vector a
_vShiftL x xs i = (V.++) (V.drop j xs) (V.replicate j x)
  where j = min i (V.length xs)

_vShiftR :: a -> V.Vector a -> Int -> V.Vector a
_vShiftR x xs i = (V.++) (V.replicate j x) (V.take (V.length xs - j) xs)
  where j = min i (V.length xs)

------------------------------------------------------------
-- Values

type CValue = Value Identity CExtra

data CExtra
  = CBool Bool
  | CWord BitVector
  | CStream (IntTrie CValue)

instance Show CExtra where
  show (CBool b) = show b
  show (CWord (BV w x)) = show x ++ "::[" ++ show w ++ "]"
  show (CStream _) = "<stream>"

vBool :: Bool -> CValue
vBool b = VExtra (CBool b)

toBool :: CValue -> Bool
toBool (VExtra (CBool b)) = b
toBool x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toBool", show x]

vWord :: BitVector -> CValue
vWord x = VExtra (CWord x)

-- | Conversion from list of bits to integer (big-endian)
bvToInteger :: Vector Bool -> Integer
bvToInteger = V.foldl' (\x b -> if b then 2*x+1 else 2*x) 0

explodeBitVector :: BitVector -> Vector Bool
explodeBitVector (BV w x) = V.reverse (V.generate w (testBit x))

toWord :: CValue -> BitVector
toWord (VExtra (CWord x)) = x
toWord (VVector vv) = BV (V.length vv) (bvToInteger (fmap (toBool . runIdentity . force) vv))
toWord x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toWord", show x]

vStream :: IntTrie CValue -> CValue
vStream x = VExtra (CStream x)

toStream :: CValue -> IntTrie CValue
toStream (VExtra (CStream x)) = x
toStream x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toStream", show x]

toVector :: CValue -> V.Vector CValue
toVector (VVector xv) = fmap (runIdentity . force) xv
toVector (VExtra (CWord w)) = fmap vBool (explodeBitVector w)
toVector x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toVector", show x]

{-
flattenBValue :: CValue -> BitVector
flattenBValue (VExtra (BBool l)) = return (AIG.replicate 1 l)
flattenBValue (VExtra (CWord lv)) = return lv
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
  , ("Prelude.at", atOp)
  , ("Prelude.upd", updOp)
  , ("Prelude.append", appendOp)
  , ("Prelude.vZip", vZipOp)
  , ("Prelude.foldr", foldrOp)
  , ("Prelude.bvAt", bvAtOp)
  --TODO, ("Prelude.bvUpd", bvUpdOp)
  , ("Prelude.bvRotateL", bvRotateLOp)
  , ("Prelude.bvRotateR", bvRotateROp)
  --TODO, ("Prelude.bvShiftL", bvShiftLOp)
  --TODO, ("Prelude.bvShiftR", bvShiftROp)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  , ("Prelude.bvNat", bvNatOp)
  --, ("Prelude.bvToNat", bvToNatOp)
  -- Overloaded
  , ("Prelude.zero", zeroOp)
  , ("Prelude.unary", Prims.unaryOp mkStreamOp streamGetOp)
  , ("Prelude.binary", Prims.binaryOp mkStreamOp streamGetOp)
  , ("Prelude.eq", eqOp)
  , ("Prelude.comparison", Prims.comparisonOp)
  ]

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
      VExtra (CWord w) -> return $ vBool (Prim.get_bv undefined undefined w i)
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

-- at :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a;
atOp :: CValue
atOp =
  constFun $
  constFun $
  pureFun $ \v ->
  Prims.natFun $ \n ->
    case v of
      VVector xv -> force $ (V.!) xv (fromIntegral n)
      VExtra (CWord w) -> return $ vBool (Prim.get_bv undefined undefined w (Prim.finFromBound n (fromIntegral (width w))))
      _ -> fail $ "Verifier.SAW.Simulator.Concrete.atOp: expected vector, got " ++ show v

-- bvAt :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> a;
bvAtOp :: CValue
bvAtOp =
  constFun $
  constFun $
  constFun $
  pureFun $ \v ->
  wordFun $ \i ->
    case v of
      VVector xv -> runIdentity $ force $ (V.!) xv (fromInteger (unsigned i))
      VExtra (CWord w) -> vBool (Prim.get_bv undefined undefined w (Prim.finFromBound (fromInteger (unsigned i)) (fromIntegral (width w))))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.bvAtOp: expected vector, got " ++ show v

-- upd :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a -> Vec n a;
updOp :: CValue
updOp =
  constFun $
  constFun $
  strictFun $ \v -> return $
  Prims.natFun $ \i -> return $
  VFun $ \y ->
    case v of
      VVector xv -> return $ VVector ((V.//) xv [(fromIntegral i, y)])
      _ -> fail $ "Verifier.SAW.Simulator.Concrete.updOp: expected vector, got " ++ show v

{-
-- bvUpd :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> a -> Vec n a;
-- NB: this isn't necessarily the most efficient possible implementation.
bvUpdOp :: CValue
bvUpdOp =
  constFun $
  constFun $
  constFun $
  strictFun $ \v -> return $
  wordFun $ \ilv -> return $
  strictFun $ \y ->
    case v of
      VVector xv -> do
        y' <- delay (return y)
        let update i = return (VVector (xv V.// [(i, y')]))
        AIG.muxInteger (lazyMux be (muxBVal be)) (V.length xv - 1) ilv update
      VExtra (CWord lv) -> do
        AIG.muxInteger (lazyMux be (muxBVal be)) (l - 1) ilv (\i -> return (vWord (AIG.generate_msb0 l (update i))))
          where update i j | i == j    = toBool y
                           | otherwise = AIG.at lv j
                l = AIG.length lv
      _ -> fail $ "Verifier.SAW.Simulator.Concrete.bvUpdOp: expected vector, got " ++ show v
-}

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
    (VVector xv, VExtra (CWord yw)) -> VVector ((V.++) xv (fmap (ready . vBool) (explodeBitVector yw)))
    (VExtra (CWord xw), VVector yv) -> VVector ((V.++) (fmap (ready . vBool) (explodeBitVector xw)) yv)
    (VExtra (CWord xw), VExtra (CWord yw)) -> vWord (Prim.append_bv undefined undefined undefined xw yw)
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
  Prims.natFun $ \w -> return $
  Prims.natFun $ \x -> return $
  VExtra (CWord (Prim.bv (fromIntegral w) (toInteger x)))

-- bvRotateL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateLOp :: CValue
bvRotateLOp =
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  wordFun $ \i ->
    case xs of
      VVector xv       -> VVector (vRotateL xv (fromInteger (unsigned i)))
      VExtra (CWord w) -> vWord (bvRotateL w (fromInteger (unsigned i)))
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
      VVector xv       -> VVector (vRotateR xv (fromInteger (unsigned i)))
      VExtra (CWord w) -> vWord (bvRotateR w (fromInteger (unsigned i)))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.bvRotateROp: " ++ show xs

{-
-- bvShiftL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftLOp :: CValue
bvShiftLOp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    (n, f) <- case xs of
                VVector xv         -> return (V.length xv, VVector . vShiftL x xv)
                VExtra (CWord xlv) -> do l <- toBool <$> force x
                                         return (AIG.length xlv, VExtra . CWord . lvShiftL l xlv)
                _ -> fail $ "Verifier.SAW.Simulator.Concrete.bvShiftLOp: " ++ show xs
    AIG.muxInteger (lazyMux be (muxBVal be)) n ilv (return . f)

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
      VVector xv       -> VVector (vShiftR x xv (fromInteger (unsigned i)))
      VExtra (CWord w) -> vWord (lvShiftR x w (fromInteger (unsigned i)))
      _ -> error $ "Verifier.SAW.Simulator.Concrete.bvShiftROp: " ++ show xs
-}

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
  Prims.natFun $ \n -> return $
  IntTrie.apply (toStream xs) n

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: CValue
bvStreamGetOp =
  constFun $
  constFun $
  pureFun $ \xs ->
  wordFun $ \i ->
  IntTrie.apply (toStream xs) (Prim.unsigned i)
