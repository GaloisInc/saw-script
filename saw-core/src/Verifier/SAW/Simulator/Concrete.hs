{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}

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
       , CValue, Concrete, Value(..), TValue(..)
       , CExtra(..)
       , toBool
       , toWord
       , runIdentity
       ) where

import Control.Monad.Identity
import Data.IntTrie (IntTrie)
import qualified Data.IntTrie as IntTrie
import Data.Map (Map)
import qualified Data.Map as Map

import Verifier.SAW.Prim (BitVector(..), signed, bv, bvNeg)
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST (ModuleMap)
import Verifier.SAW.SharedTerm

------------------------------------------------------------

-- | Evaluator for shared terms.
evalSharedTerm :: ModuleMap -> Map Ident CValue -> Map VarIndex CValue -> Term -> CValue
evalSharedTerm m addlPrims ecVals t =
  runIdentity $ do
    cfg <- Sim.evalGlobal m (Map.union constMap addlPrims) extcns (const Nothing) neutral
    Sim.evalSharedTerm cfg t
  where
    neutral _env nt = return $ Prim.userError $ "Cannot evaluate neutral term\n" ++ show nt
    extcns ec =
      case Map.lookup (ecVarIndex ec) ecVals of
        Just v  -> return v
        Nothing -> return $ Prim.userError $ "Unimplemented: external constant " ++ show (ecName ec)

------------------------------------------------------------
-- Values

data Concrete

type instance EvalM Concrete = Identity
type instance VBool Concrete = Bool
type instance VWord Concrete = BitVector
type instance VInt  Concrete = Integer
type instance VArray Concrete = ()
type instance Extra Concrete = CExtra

type CValue = Value Concrete -- (WithM Identity Concrete)

data CExtra
  = CStream (IntTrie CValue)

instance Show CExtra where
  show (CStream _) = "<stream>"

toBool :: CValue -> Bool
toBool (VBool b) = b
toBool x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toBool", show x]

vWord :: BitVector -> CValue
vWord x = VWord x

toWord :: CValue -> BitVector
toWord (VWord x) = x
toWord (VVector vv) = Prim.packBitVector (fmap (toBool . runIdentity . force) vv)
toWord x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toWord", show x]

vStream :: IntTrie CValue -> CValue
vStream x = VExtra (CStream x)

toStream :: CValue -> IntTrie CValue
toStream (VExtra (CStream x)) = x
toStream x = error $ unwords ["Verifier.SAW.Simulator.Concrete.toStream", show x]

wordFun :: (BitVector -> CValue) -> CValue
wordFun f = pureFun (\x -> f (toWord x))

-- | op : (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool
bvShiftOp :: (BitVector -> Int -> BitVector) -> CValue
bvShiftOp natOp =
  constFun $
  wordFun $ \x ->
  pureFun $ \y ->
    case y of
      VNat n | toInteger n < toInteger (maxBound :: Int) -> vWord (natOp x (fromIntegral n))
      _      -> error $ unwords ["Verifier.SAW.Simulator.Concrete.shiftOp", show y]

------------------------------------------------------------

pure1 :: Applicative f => (a -> b) -> a -> f b
pure1 f x = pure (f x)

pure2 :: Applicative f => (a -> b -> c) -> a -> b -> f c
pure2 f x y = pure (f x y)

pure3 :: Applicative f => (a -> b -> c -> d) -> a -> b -> c -> f d
pure3 f x y z = pure (f x y z)

divOp :: (a -> b -> Maybe c) -> a -> b -> Identity c
divOp f x y = maybe Prim.divideByZero pure (f x y)

ite :: Bool -> a -> a -> a
ite b x y = if b then x else y

prims :: Prims.BasePrims Concrete
prims =
  Prims.BasePrims
  { Prims.bpAsBool  = Just
  , Prims.bpUnpack  = pure1 Prim.unpackBitVector
  , Prims.bpPack    = pure1 Prim.packBitVector
  , Prims.bpBvAt    = pure2 Prim.bvAt
  , Prims.bpBvLit   = pure2 Prim.bv
  , Prims.bpBvSize  = Prim.width
  , Prims.bpBvJoin  = pure2 (Prim.append_bv undefined undefined undefined)
  , Prims.bpBvSlice = pure3 (\m n x -> Prim.slice_bv () m n (Prim.width x - m - n) x)
    -- Conditionals
  , Prims.bpMuxBool  = pure3 ite
  , Prims.bpMuxWord  = pure3 ite
  , Prims.bpMuxInt   = pure3 ite
  , Prims.bpMuxExtra = \_tp -> pure3 ite
    -- Booleans
  , Prims.bpTrue   = True
  , Prims.bpFalse  = False
  , Prims.bpNot    = pure1 not
  , Prims.bpAnd    = pure2 (&&)
  , Prims.bpOr     = pure2 (||)
  , Prims.bpXor    = pure2 (/=)
  , Prims.bpBoolEq = pure2 (==)
    -- Bitvector logical
  , Prims.bpBvNot  = pure1 (Prim.bvNot undefined)
  , Prims.bpBvAnd  = pure2 (Prim.bvAnd undefined)
  , Prims.bpBvOr   = pure2 (Prim.bvOr  undefined)
  , Prims.bpBvXor  = pure2 (Prim.bvXor undefined)
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = pure1 (Prim.bvNeg undefined)
  , Prims.bpBvAdd  = pure2 (Prim.bvAdd undefined)
  , Prims.bpBvSub  = pure2 (Prim.bvSub undefined)
  , Prims.bpBvMul  = pure2 (Prim.bvMul undefined)
  , Prims.bpBvUDiv = divOp (Prim.bvUDiv undefined)
  , Prims.bpBvURem = divOp (Prim.bvURem undefined)
  , Prims.bpBvSDiv = divOp (Prim.bvSDiv undefined)
  , Prims.bpBvSRem = divOp (Prim.bvSRem undefined)
  , Prims.bpBvLg2  = pure1 Prim.bvLg2
    -- Bitvector comparisons
  , Prims.bpBvEq   = pure2 (Prim.bvEq  undefined)
  , Prims.bpBvsle  = pure2 (Prim.bvsle undefined)
  , Prims.bpBvslt  = pure2 (Prim.bvslt undefined)
  , Prims.bpBvule  = pure2 (Prim.bvule undefined)
  , Prims.bpBvult  = pure2 (Prim.bvult undefined)
  , Prims.bpBvsge  = pure2 (Prim.bvsge undefined)
  , Prims.bpBvsgt  = pure2 (Prim.bvsgt undefined)
  , Prims.bpBvuge  = pure2 (Prim.bvuge undefined)
  , Prims.bpBvugt  = pure2 (Prim.bvugt undefined)
    -- Bitvector shift/rotate
  , Prims.bpBvRolInt = pure2 Prim.bvRotateL
  , Prims.bpBvRorInt = pure2 Prim.bvRotateR
  , Prims.bpBvShlInt = pure3 Prim.bvShiftL
  , Prims.bpBvShrInt = pure3 Prim.bvShiftR
  , Prims.bpBvRol    = pure2 (\x y -> Prim.bvRotateL x (unsigned y))
  , Prims.bpBvRor    = pure2 (\x y -> Prim.bvRotateR x (unsigned y))
  , Prims.bpBvShl    = pure3 (\b x y -> Prim.bvShiftL b x (unsigned y))
  , Prims.bpBvShr    = pure3 (\b x y -> Prim.bvShiftR b x (unsigned y))
    -- Bitvector misc
  , Prims.bpBvPopcount = pure1 (Prim.bvPopcount undefined)
  , Prims.bpBvCountLeadingZeros = pure1 (Prim.bvCountLeadingZeros undefined)
  , Prims.bpBvCountTrailingZeros = pure1 (Prim.bvCountTrailingZeros undefined)
  , Prims.bpBvForall = unsupportedConcretePrimitive "bvForall"

    -- Integer operations
  , Prims.bpIntAdd = pure2 (+)
  , Prims.bpIntSub = pure2 (-)
  , Prims.bpIntMul = pure2 (*)
  , Prims.bpIntDiv = pure2 div
  , Prims.bpIntMod = pure2 mod
  , Prims.bpIntNeg = pure1 negate
  , Prims.bpIntAbs = pure1 abs
  , Prims.bpIntEq  = pure2 (==)
  , Prims.bpIntLe  = pure2 (<=)
  , Prims.bpIntLt  = pure2 (<)
  , Prims.bpIntMin = pure2 min
  , Prims.bpIntMax = pure2 max

    -- Array operations
  , Prims.bpArrayConstant = unsupportedConcretePrimitive "bpArrayConstant"
  , Prims.bpArrayLookup = unsupportedConcretePrimitive "bpArrayLookup"
  , Prims.bpArrayUpdate = unsupportedConcretePrimitive "bpArrayUpdate"
  , Prims.bpArrayEq = unsupportedConcretePrimitive "bpArrayEq"
  }

unsupportedConcretePrimitive :: String -> a
unsupportedConcretePrimitive = Prim.unsupportedPrimitive "concrete"

constMap :: Map Ident CValue
constMap =
  flip Map.union (Prims.constMap prims) $
  Map.fromList
  -- Shifts
  [ ("Prelude.bvShl" , bvShiftOp (Prim.bvShl undefined))
  , ("Prelude.bvShr" , bvShiftOp (Prim.bvShr undefined))
  , ("Prelude.bvSShr", bvShiftOp (Prim.bvSShr undefined))
  -- Integers
  , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", Prims.natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  -- Integers mod n
  , ("Prelude.toIntMod"  , toIntModOp)
  , ("Prelude.fromIntMod", fromIntModOp)
  , ("Prelude.intModEq"  , intModEqOp)
  , ("Prelude.intModAdd" , intModBinOp (+))
  , ("Prelude.intModSub" , intModBinOp (-))
  , ("Prelude.intModMul" , intModBinOp (*))
  , ("Prelude.intModNeg" , intModUnOp negate)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  -- Miscellaneous
  , ("Prelude.bvToNat", bvToNatOp) -- override Prims.constMap
  , ("Prelude.expByNat", Prims.expByNatOp prims)
  ]

------------------------------------------------------------

-- primitive bvToNat : (n : Nat) -> Vec n Bool -> Nat;
bvToNatOp :: CValue
bvToNatOp = constFun $ wordFun $ VNat . fromInteger . unsigned

-- primitive bvToInt : (n : Nat) -> Vec n Bool -> Integer;
bvToIntOp :: CValue
bvToIntOp = constFun $ wordFun $ VInt . unsigned

-- primitive sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: CValue
sbvToIntOp = constFun $ wordFun $ VInt . signed

-- primitive intToBv : (n : Nat) -> Integer -> Vec n Bool;
intToBvOp :: CValue
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x -> return $
    VWord $
     if n >= 0 then bv (fromIntegral n) x
               else bvNeg n $ bv (fromIntegral n) $ negate x

------------------------------------------------------------

toIntModOp :: CValue
toIntModOp =
  Prims.natFun $ \n -> return $
  Prims.intFun "toIntModOp" $ \x -> return $
  VIntMod n (x `mod` toInteger n)

fromIntModOp :: CValue
fromIntModOp =
  constFun $
  Prims.intModFun "fromIntModOp" $ \x -> pure $
  VInt x

intModEqOp :: CValue
intModEqOp =
  constFun $
  Prims.intModFun "intModEqOp" $ \x -> return $
  Prims.intModFun "intModEqOp" $ \y -> return $
  VBool (x == y)

intModBinOp :: (Integer -> Integer -> Integer) -> CValue
intModBinOp f =
  Prims.natFun $ \n -> return $
  Prims.intModFun "intModBinOp x" $ \x -> return $
  Prims.intModFun "intModBinOp y" $ \y -> return $
  VIntMod n (f x y `mod` toInteger n)

intModUnOp :: (Integer -> Integer) -> CValue
intModUnOp f =
  Prims.natFun $ \n -> return $
  Prims.intModFun "intModUnOp" $ \x -> return $
  VIntMod n (f x `mod` toInteger n)

------------------------------------------------------------

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
  strictFun $ \case
    VNat n -> return $ IntTrie.apply (toStream xs) (toInteger n)
    VIntToNat (VInt i) -> return $ IntTrie.apply (toStream xs) i
    VBVToNat _ w -> return $ IntTrie.apply (toStream xs) (unsigned (toWord w))
    n -> Prims.panic "Verifier.SAW.Simulator.Concrete.streamGetOp"
               ["Expected Nat value", show n]
