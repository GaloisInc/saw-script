{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Verifier.SAW.Simulator.RME
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.RME
  ( evalSharedTerm
  , RValue, Value(..)
  , RExtra(..)
  , toBool
  , toWord
  , runIdentity
  , withBitBlastedPred
  ) where

import Control.Monad.Identity
import Control.Monad.State
import Data.Bits
import Data.IntTrie (IntTrie)
import qualified Data.IntTrie as IntTrie
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V

import Verifier.SAW.Simulator.RME.Base (RME)
import qualified Verifier.SAW.Simulator.RME.Base as RME
import qualified Verifier.SAW.Simulator.RME.Vector as RMEV

import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.FiniteValue
import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST (Module)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable
#endif

------------------------------------------------------------

-- | Evaluator for shared terms.
evalSharedTerm :: Module -> Map Ident RValue -> Term -> RValue
evalSharedTerm m addlPrims t =
  runIdentity $ do
    cfg <- Sim.evalGlobal m (Map.union constMap addlPrims)
           Sim.noExtCns (const (const Nothing))
    Sim.evalSharedTerm cfg t

------------------------------------------------------------
-- BitVector operations
{-
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
-}
------------------------------------------------------------
-- Vector operations

vRotateL :: V.Vector a -> Integer -> V.Vector a
vRotateL xs i
  | V.null xs = xs
  | otherwise = (V.++) (V.drop j xs) (V.take j xs)
  where j = fromInteger (i `mod` toInteger (V.length xs))

vRotateR :: V.Vector a -> Integer -> V.Vector a
vRotateR xs i = vRotateL xs (- i)

vShiftL :: a -> V.Vector a -> Integer -> V.Vector a
vShiftL x xs i = (V.++) (V.drop j xs) (V.replicate j x)
  where j = fromInteger (min i (toInteger (V.length xs)))

vShiftR :: a -> V.Vector a -> Integer -> V.Vector a
vShiftR x xs i = (V.++) (V.replicate j x) (V.take (V.length xs - j) xs)
  where j = fromInteger (min i (toInteger (V.length xs)))

------------------------------------------------------------
-- Values

type RValue = Value Identity RME (Vector RME) RExtra
type RThunk = Thunk Identity RME (Vector RME) RExtra

data RExtra = AStream (IntTrie RValue)

instance Show RExtra where
  show (AStream _) = "<stream>"

vBool :: RME -> RValue
vBool b = VBool b

toBool :: RValue -> RME
toBool (VBool b) = b
toBool x = error $ unwords ["Verifier.SAW.Simulator.RME.toBool", show x]

vWord :: Vector RME -> RValue
vWord x = VWord x

toWord :: RValue -> Vector RME
toWord (VWord x) = x
toWord (VVector vv) = fmap (toBool . runIdentity . force) vv
toWord x = error $ unwords ["Verifier.SAW.Simulator.RME.toWord", show x]

vStream :: IntTrie RValue -> RValue
vStream x = VExtra (AStream x)

toStream :: RValue -> IntTrie RValue
toStream (VExtra (AStream x)) = x
toStream x = error $ unwords ["Verifier.SAW.Simulator.RME.toStream", show x]

vVector :: V.Vector RValue -> RValue
vVector xv = VVector (fmap ready xv)

toVector :: RValue -> V.Vector RValue
toVector (VVector xv) = fmap (runIdentity . force) xv
toVector (VWord w) = fmap vBool w
toVector x = error $ unwords ["Verifier.SAW.Simulator.RME.toVector", show x]

wordFun :: (Vector RME -> RValue) -> RValue
wordFun f = pureFun (\x -> f (toWord x))

-- | op :: Bool -> Bool -> Bool
boolBinOp :: (RME -> RME -> RME) -> RValue
boolBinOp op =
  pureFun $ \x ->
  pureFun $ \y -> VBool (op (toBool x) (toBool y))

-- | op :: (n :: Nat) -> bitvector n -> bitvector n
unOp :: (Vector RME -> Vector RME) -> RValue
unOp op =
  constFun $
  wordFun $ \x -> vWord (op x)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n
binOp :: (Vector RME -> Vector RME -> Vector RME) -> RValue
binOp op =
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vWord (op x y)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> Bool
binRel :: (Vector RME -> Vector RME -> RME) -> RValue
binRel op =
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vBool (op x y)

genShift :: (a -> b -> b -> b) -> (b -> Integer -> b) -> b -> Vector a -> b
genShift cond f x0 v = go x0 (V.toList v)
  where
    go x [] = x
    go x (y : ys) = go (cond y (f x (2 ^ length ys)) x) ys

-- | op :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
shiftOp :: (Vector RME -> Integer -> Vector RME) -> RValue
shiftOp op =
  constFun $
  wordFun $ \x ->
  pureFun $ \y ->
    case y of
      VNat n   -> vWord (op x n)
      VToNat v -> vWord (genShift muxRMEV op x (toWord v))
      _        -> error $ unwords ["Verifier.SAW.Simulator.RME.shiftOp", show y]

-- | op :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateOp :: (Vector RValue -> Integer -> Vector RValue) -> RValue
bvRotateOp op =
  constFun $
  constFun $
  constFun $
  pureFun $ \(toVector -> x) ->
  wordFun $ \y ->
  vVector (genShift (V.zipWith . muxRValue) op x y)

-- | op :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftOp :: (RValue -> Vector RValue -> Integer -> Vector RValue) -> RValue
bvShiftOp op =
  constFun $
  constFun $
  constFun $
  pureFun $ \z ->
  pureFun $ \(toVector -> x) ->
  wordFun $ \y ->
  vVector (genShift (V.zipWith . muxRValue) (op z) x y)

------------------------------------------------------------

constMap :: Map Ident RValue
constMap = Map.fromList
  -- Boolean
  [ ("Prelude.True"  , VBool RME.true)
  , ("Prelude.False" , VBool RME.false)
  , ("Prelude.not"   , pureFun (VBool . RME.compl . toBool))
  , ("Prelude.and"   , boolBinOp RME.conj)
  , ("Prelude.or"    , boolBinOp RME.disj)
  , ("Prelude.xor"   , boolBinOp RME.xor)
  , ("Prelude.boolEq", boolBinOp RME.iff)
  , ("Prelude.ite"   , iteOp)
  -- Arithmetic
  , ("Prelude.bvNeg" , unOp RMEV.neg)
  , ("Prelude.bvAdd" , binOp RMEV.add)
  , ("Prelude.bvSub" , binOp RMEV.sub)
  , ("Prelude.bvMul" , binOp RMEV.mul)
  , ("Prelude.bvAnd" , binOp (V.zipWith RME.conj))
  , ("Prelude.bvOr"  , binOp (V.zipWith RME.disj))
  , ("Prelude.bvXor" , binOp (V.zipWith RME.xor))
  , ("Prelude.bvUDiv", binOp RMEV.udiv)
  , ("Prelude.bvURem", binOp RMEV.urem)
  , ("Prelude.bvSDiv", binOp RMEV.sdiv)
  , ("Prelude.bvSRem", binOp RMEV.srem)
  , ("Prelude.bvPMul", bvPMulOp)
  , ("Prelude.bvPMod", bvPModOp)
  , ("Prelude.bvPDiv", bvPDivOp)
  -- Relations
  , ("Prelude.bvEq"  , binRel RMEV.eq)
  , ("Prelude.bvsle" , binRel RMEV.sle)
  , ("Prelude.bvslt" , binRel RMEV.slt)
  , ("Prelude.bvule" , binRel RMEV.ule)
  , ("Prelude.bvult" , binRel RMEV.ult)
  , ("Prelude.bvsge" , binRel (flip RMEV.sle))
  , ("Prelude.bvsgt" , binRel (flip RMEV.slt))
  , ("Prelude.bvuge" , binRel (flip RMEV.ule))
  , ("Prelude.bvugt" , binRel (flip RMEV.ult))
  -- Shifts
  , ("Prelude.bvShl" , shiftOp (vShiftL RME.false))
  , ("Prelude.bvShr" , shiftOp (vShiftR RME.false))
  --, ("Prelude.bvSShr", shiftOp RMEV.sshr lvSShr)
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
  , ("Prelude.equalNat", Prims.equalNat (return . RME.constant))
  , ("Prelude.ltNat", Prims.ltNat (return . RME.constant))
  -- Integers
  , ("Prelude.intAdd", Prims.intAddOp)
  , ("Prelude.intSub", Prims.intSubOp)
  , ("Prelude.intMul", Prims.intMulOp)
  , ("Prelude.intDiv", Prims.intDivOp)
  , ("Prelude.intMod", Prims.intModOp)
  , ("Prelude.intNeg", Prims.intNegOp)
  , ("Prelude.intEq" , Prims.intEqOp RME.constant)
  , ("Prelude.intLe" , Prims.intLeOp RME.constant)
  , ("Prelude.intLt" , Prims.intLtOp RME.constant)
  , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", Prims.natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  , ("Prelude.intMin"  , Prims.intMinOp)
  , ("Prelude.intMax"  , Prims.intMaxOp)
  -- Vectors
  , ("Prelude.gen", Prims.genOp)
  , ("Prelude.atWithDefault", Prims.atWithDefaultOp id (V.!) ite)
  , ("Prelude.upd", Prims.updOp id (\x y -> return (RMEV.eq x y)) RMEV.integer V.length ite)
  , ("Prelude.append", Prims.appendOp id (V.++))
  , ("Prelude.join", Prims.joinOp id (V.++))
  , ("Prelude.zip", vZipOp)
  , ("Prelude.foldr", foldrOp)
  , ("Prelude.bvRotateL", bvRotateOp vRotateL)
  , ("Prelude.bvRotateR", bvRotateOp vRotateR)
  , ("Prelude.bvShiftL", bvShiftOp vShiftL)
  , ("Prelude.bvShiftR", bvShiftOp vShiftR)
  , ("Prelude.EmptyVec", Prims.emptyVec)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  , ("Prelude.bvNat", bvNatOp)
  , ("Prelude.bvToNat", Prims.bvToNatOp)
  , ("Prelude.error", Prims.errorOp)
  -- Overloaded
  , ("Prelude.eq", eqOp)
  ]

-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
bvToIntOp :: RValue
bvToIntOp = undefined -- constFun $ wordFun $ VInt . unsigned

-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
sbvToIntOp :: RValue
sbvToIntOp = undefined -- constFun $ wordFun $ VInt . signed

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
intToBvOp :: RValue
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x -> return $
    VWord (V.reverse (V.generate (fromIntegral n) (RME.constant . testBit x)))

-- | ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
iteOp :: RValue
iteOp =
  constFun $
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> ite (toBool b) (force x) (force y)

ite :: RME -> Identity RValue -> Identity RValue -> Identity RValue
ite b x y
  | b == RME.true = x
  | b == RME.false = y
  | otherwise = return $ muxRValue b (runIdentity x) (runIdentity y)

muxRMEV :: RME -> Vector RME -> Vector RME -> Vector RME
muxRMEV b = V.zipWith (RME.mux b)

muxRValue :: RME -> RValue -> RValue -> RValue
muxRValue b0 x0 y0 = runIdentity $ Prims.muxValue id bool word extra b0 x0 y0
  where
    bool b x y = return (RME.mux b x y)
    word b x y = return (muxRMEV b x y)
    extra b (AStream xs) (AStream ys) = return (AStream (muxRValue b <$> xs <*> ys))

----------------------------------------
-- Polynomial operations

-- bvPMul :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector _;
bvPMulOp :: RValue
bvPMulOp =
  constFun $
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vWord (RMEV.pmul x y)

-- bvPMod :: (m n :: Nat) -> bitvector m -> bitvector (Succ n) -> bitvector n;
bvPModOp :: RValue
bvPModOp =
  constFun $
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vWord (RMEV.pmod x y)

-- primitive bvPDiv :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector m;
bvPDivOp :: RValue
bvPDivOp =
  constFun $
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vWord (RMEV.pdiv x y)

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: RValue
vZipOp =
  constFun $
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  pureFun $ \ys ->
  VVector (V.zipWith (\x y -> ready (vTuple [ready x, ready y])) (toVector xs) (toVector ys))

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: RValue
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
      _ -> fail "Verifier.SAW.Simulator.RME.foldrOp"

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNatOp :: RValue
bvNatOp =
  Prims.natFun'' "bvNatOp1" $ \w -> return $
  Prims.natFun'' "bvNatOp2"  $ \x -> return $
  VWord (RMEV.integer (fromIntegral w) (toInteger x))

eqOp :: RValue
eqOp = Prims.eqOp trueOp andOp boolOp bvOp
  where
    trueOp = vBool RME.true
    andOp x y = return (vBool (RME.conj (toBool x) (toBool y)))
    boolOp x y = return (vBool (RME.iff (toBool x) (toBool y)))
    bvOp _ x y = return (vBool (RMEV.eq (toWord x) (toWord y)))

----------------------------------------

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: RValue
mkStreamOp =
  constFun $
  pureFun $ \f ->
  vStream (fmap (\n -> runIdentity (apply f (ready (VNat n)))) IntTrie.identity)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: RValue
streamGetOp =
  constFun $
  pureFun $ \xs ->
  Prims.natFun'' "streamGetOp" $ \n -> return $
  IntTrie.apply (toStream xs) n

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: RValue
bvStreamGetOp =
  constFun $
  constFun $
  pureFun $ \_xs ->
  wordFun $ \_i ->
  error "bvStreamGetOp"
  --IntTrie.apply (toStream xs) (Prim.unsigned i)

------------------------------------------------------------
-- Generating variables for arguments

newVars :: FiniteType -> State Int RValue
newVars FTBit = do
  i <- get
  put (i + 1)
  return (vBool (RME.lit i))
newVars (FTVec n t) = VVector <$> V.replicateM (fromIntegral n) (newVars' t)
newVars (FTTuple ts) = vTuple <$> traverse newVars' ts
newVars (FTRec tm) = vRecord <$> traverse newVars' tm

newVars' :: FiniteType -> State Int RThunk
newVars' shape = ready <$> newVars shape

------------------------------------------------------------
-- Bit-blasting primitives.

bitBlastBasic :: Module
              -> Map Ident RValue
              -> Term
              -> RValue
bitBlastBasic m addlPrims t = runIdentity $ do
  cfg <- Sim.evalGlobal m (Map.union constMap addlPrims)
         (\_varidx name _ty -> error ("RME: unsupported ExtCns: " ++ name))
         (const (const Nothing))
  Sim.evalSharedTerm cfg t

asPredType :: SharedContext -> Term -> IO [Term]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "Verifier.SAW.Simulator.BitBlast.asPredType: non-boolean result type: " ++ show t'

withBitBlastedPred ::
  SharedContext ->
  Map Ident RValue ->
  Term ->
  (RME -> [FiniteType] -> IO a) -> IO a
withBitBlastedPred sc addlPrims t c = do
  ty <- scTypeOf sc t
  argTs <- asPredType sc ty
  shapes <- traverse (asFiniteType sc) argTs
  let vars = evalState (traverse newVars' shapes) 0
  let bval = bitBlastBasic (scModule sc) addlPrims t
  let bval' = runIdentity $ applyAll bval vars
  case bval' of
    VBool anf -> c anf shapes
    _ -> fail "Verifier.SAW.Simulator.RME.bitBlast: non-boolean result type."
