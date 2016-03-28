{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Verifier.SAW.Simulator.ANF
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.ANF
  ( evalSharedTerm
  , AValue, Value(..)
  , AExtra(..)
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

import Verifier.SAW.Simulator.ANF.Base (ANF)
import qualified Verifier.SAW.Simulator.ANF.Base as ANF
import qualified Verifier.SAW.Simulator.ANF.Vector as ANFV

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
evalSharedTerm :: Module -> Map Ident AValue -> SharedTerm s -> AValue
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

type AValue = Value Identity ANF (Vector ANF) AExtra
type AThunk = Thunk Identity ANF (Vector ANF) AExtra

data AExtra = AStream (IntTrie AValue)

instance Show AExtra where
  show (AStream _) = "<stream>"

vBool :: ANF -> AValue
vBool b = VBool b

toBool :: AValue -> ANF
toBool (VBool b) = b
toBool x = error $ unwords ["Verifier.SAW.Simulator.ANF.toBool", show x]

vWord :: Vector ANF -> AValue
vWord x = VWord x

toWord :: AValue -> Vector ANF
toWord (VWord x) = x
toWord (VVector vv) = fmap (toBool . runIdentity . force) vv
toWord x = error $ unwords ["Verifier.SAW.Simulator.ANF.toWord", show x]

vStream :: IntTrie AValue -> AValue
vStream x = VExtra (AStream x)

toStream :: AValue -> IntTrie AValue
toStream (VExtra (AStream x)) = x
toStream x = error $ unwords ["Verifier.SAW.Simulator.ANF.toStream", show x]

vVector :: V.Vector AValue -> AValue
vVector xv = VVector (fmap ready xv)

toVector :: AValue -> V.Vector AValue
toVector (VVector xv) = fmap (runIdentity . force) xv
toVector (VWord w) = fmap vBool w
toVector x = error $ unwords ["Verifier.SAW.Simulator.ANF.toVector", show x]

wordFun :: (Vector ANF -> AValue) -> AValue
wordFun f = pureFun (\x -> f (toWord x))

-- | op :: Bool -> Bool -> Bool
boolBinOp :: (ANF -> ANF -> ANF) -> AValue
boolBinOp op =
  pureFun $ \x ->
  pureFun $ \y -> VBool (op (toBool x) (toBool y))

-- | op :: (n :: Nat) -> bitvector n -> bitvector n
unOp :: (Vector ANF -> Vector ANF) -> AValue
unOp op =
  constFun $
  wordFun $ \x -> vWord (op x)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n
binOp :: (Vector ANF -> Vector ANF -> Vector ANF) -> AValue
binOp op =
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vWord (op x y)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> Bool
binRel :: (Vector ANF -> Vector ANF -> ANF) -> AValue
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
shiftOp :: (Vector ANF -> Integer -> Vector ANF) -> AValue
shiftOp op =
  constFun $
  wordFun $ \x ->
  pureFun $ \y ->
    case y of
      VNat n   -> vWord (op x n)
      VToNat v -> vWord (genShift muxANFV op x (toWord v))
      _        -> error $ unwords ["Verifier.SAW.Simulator.ANF.shiftOp", show y]

-- | op :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateOp :: (Vector AValue -> Integer -> Vector AValue) -> AValue
bvRotateOp op =
  constFun $
  constFun $
  constFun $
  pureFun $ \(toVector -> x) ->
  wordFun $ \y ->
  vVector (genShift (V.zipWith . muxAValue) op x y)

-- | op :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftOp :: (AValue -> Vector AValue -> Integer -> Vector AValue) -> AValue
bvShiftOp op =
  constFun $
  constFun $
  constFun $
  pureFun $ \z ->
  pureFun $ \(toVector -> x) ->
  wordFun $ \y ->
  vVector (genShift (V.zipWith . muxAValue) (op z) x y)

------------------------------------------------------------

constMap :: Map Ident AValue
constMap = Map.fromList
  -- Boolean
  [ ("Prelude.True"  , VBool ANF.true)
  , ("Prelude.False" , VBool ANF.false)
  , ("Prelude.not"   , pureFun (VBool . ANF.compl . toBool))
  , ("Prelude.and"   , boolBinOp ANF.conj)
  , ("Prelude.or"    , boolBinOp ANF.disj)
  , ("Prelude.xor"   , boolBinOp ANF.xor)
  , ("Prelude.boolEq", boolBinOp ANF.iff)
  , ("Prelude.ite"   , iteOp)
  -- Arithmetic
  , ("Prelude.bvNeg" , unOp ANFV.neg)
  , ("Prelude.bvAdd" , binOp ANFV.add)
  , ("Prelude.bvSub" , binOp ANFV.sub)
  , ("Prelude.bvMul" , binOp ANFV.mul)
  , ("Prelude.bvAnd" , binOp (V.zipWith ANF.conj))
  , ("Prelude.bvOr"  , binOp (V.zipWith ANF.disj))
  , ("Prelude.bvXor" , binOp (V.zipWith ANF.xor))
  , ("Prelude.bvUDiv", binOp ANFV.udiv)
  , ("Prelude.bvURem", binOp ANFV.urem)
  , ("Prelude.bvSDiv", binOp ANFV.sdiv)
  , ("Prelude.bvSRem", binOp ANFV.srem)
  , ("Prelude.bvPMul", bvPMulOp)
  , ("Prelude.bvPMod", bvPModOp)
  , ("Prelude.bvPDiv", bvPDivOp)
  -- Relations
  , ("Prelude.bvEq"  , binRel ANFV.eq)
  , ("Prelude.bvsle" , binRel ANFV.sle)
  , ("Prelude.bvslt" , binRel ANFV.slt)
  , ("Prelude.bvule" , binRel ANFV.ule)
  , ("Prelude.bvult" , binRel ANFV.ult)
  , ("Prelude.bvsge" , binRel (flip ANFV.sle))
  , ("Prelude.bvsgt" , binRel (flip ANFV.slt))
  , ("Prelude.bvuge" , binRel (flip ANFV.ule))
  , ("Prelude.bvugt" , binRel (flip ANFV.ult))
  -- Shifts
  , ("Prelude.bvShl" , shiftOp (vShiftL ANF.false))
  , ("Prelude.bvShr" , shiftOp (vShiftR ANF.false))
  --, ("Prelude.bvSShr", shiftOp ANFV.sshr lvSShr)
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
  , ("Prelude.equalNat", Prims.equalNat (return . ANF.constant))
  , ("Prelude.ltNat", Prims.ltNat (return . ANF.constant))
  -- Integers
  , ("Prelude.intAdd", Prims.intAddOp)
  , ("Prelude.intSub", Prims.intSubOp)
  , ("Prelude.intMul", Prims.intMulOp)
  , ("Prelude.intDiv", Prims.intDivOp)
  , ("Prelude.intMod", Prims.intModOp)
  , ("Prelude.intNeg", Prims.intNegOp)
  , ("Prelude.intEq" , Prims.intEqOp ANF.constant)
  , ("Prelude.intLe" , Prims.intLeOp ANF.constant)
  , ("Prelude.intLt" , Prims.intLtOp ANF.constant)
  , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", Prims.natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  , ("Prelude.intMin"  , Prims.intMinOp)
  , ("Prelude.intMax"  , Prims.intMaxOp)
  -- Vectors
  , ("Prelude.gen", Prims.genOp)
  , ("Prelude.at", Prims.atOp id (V.!) ite)
  , ("Prelude.upd", Prims.updOp id (\x y -> return (ANFV.eq x y)) ANFV.integer V.length ite)
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
  -- Overloaded
  , ("Prelude.eq", eqOp)
  ]

-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
bvToIntOp :: AValue
bvToIntOp = undefined -- constFun $ wordFun $ VInt . unsigned

-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
sbvToIntOp :: AValue
sbvToIntOp = undefined -- constFun $ wordFun $ VInt . signed

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
intToBvOp :: AValue
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x -> return $
    VWord (V.reverse (V.generate (fromIntegral n) (ANF.constant . testBit x)))

-- | ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
iteOp :: AValue
iteOp =
  constFun $
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> ite (toBool b) (force x) (force y)

ite :: ANF -> Identity AValue -> Identity AValue -> Identity AValue
ite b x y
  | b == ANF.true = x
  | b == ANF.false = y
  | otherwise = return $ muxAValue b (runIdentity x) (runIdentity y)

muxANFV :: ANF -> Vector ANF -> Vector ANF -> Vector ANF
muxANFV b = V.zipWith (ANF.mux b)

muxAValue :: ANF -> AValue -> AValue -> AValue
muxAValue b0 x0 y0 = runIdentity $ Prims.muxValue id bool word extra b0 x0 y0
  where
    bool b x y = return (ANF.mux b x y)
    word b x y = return (muxANFV b x y)
    extra b (AStream xs) (AStream ys) = return (AStream (muxAValue b <$> xs <*> ys))

----------------------------------------
-- Polynomial operations

-- bvPMul :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector _;
bvPMulOp :: AValue
bvPMulOp =
  constFun $
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vWord (ANFV.pmul x y)

-- bvPMod :: (m n :: Nat) -> bitvector m -> bitvector (Succ n) -> bitvector n;
bvPModOp :: AValue
bvPModOp =
  constFun $
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vWord (ANFV.pmod x y)

-- primitive bvPDiv :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector m;
bvPDivOp :: AValue
bvPDivOp =
  constFun $
  constFun $
  wordFun $ \x ->
  wordFun $ \y -> vWord (ANFV.pdiv x y)

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: AValue
vZipOp =
  constFun $
  constFun $
  constFun $
  constFun $
  pureFun $ \xs ->
  pureFun $ \ys ->
  VVector (V.zipWith (\x y -> ready (vTuple [ready x, ready y])) (toVector xs) (toVector ys))

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: AValue
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
      _ -> fail "Verifier.SAW.Simulator.ANF.foldrOp"

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNatOp :: AValue
bvNatOp =
  Prims.natFun'' "bvNatOp1" $ \w -> return $
  Prims.natFun'' "bvNatOp2"  $ \x -> return $
  VWord (ANFV.integer (fromIntegral w) (toInteger x))

eqOp :: AValue
eqOp = Prims.eqOp trueOp andOp boolOp bvOp
  where
    trueOp = vBool ANF.true
    andOp x y = return (vBool (ANF.conj (toBool x) (toBool y)))
    boolOp x y = return (vBool (ANF.iff (toBool x) (toBool y)))
    bvOp _ x y = return (vBool (ANFV.eq (toWord x) (toWord y)))

----------------------------------------

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: AValue
mkStreamOp =
  constFun $
  pureFun $ \f ->
  vStream (fmap (\n -> runIdentity (apply f (ready (VNat n)))) IntTrie.identity)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: AValue
streamGetOp =
  constFun $
  pureFun $ \xs ->
  Prims.natFun'' "streamGetOp" $ \n -> return $
  IntTrie.apply (toStream xs) n

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: AValue
bvStreamGetOp =
  constFun $
  constFun $
  pureFun $ \_xs ->
  wordFun $ \_i ->
  error "bvStreamGetOp"
  --IntTrie.apply (toStream xs) (Prim.unsigned i)

------------------------------------------------------------
-- Generating variables for arguments

newVars :: FiniteType -> State Int AValue
newVars FTBit = do
  i <- get
  put (i + 1)
  return (vBool (ANF.lit i))
newVars (FTVec n t) = VVector <$> V.replicateM (fromIntegral n) (newVars' t)
newVars (FTTuple ts) = vTuple <$> traverse newVars' ts
newVars (FTRec tm) = vRecord <$> traverse newVars' tm

newVars' :: FiniteType -> State Int AThunk
newVars' shape = ready <$> newVars shape

------------------------------------------------------------
-- Bit-blasting primitives.

bitBlastBasic :: Module
              -> Map Ident AValue
              -> SharedTerm s
              -> AValue
bitBlastBasic m addlPrims t = runIdentity $ do
  cfg <- Sim.evalGlobal m (Map.union constMap addlPrims)
         (\_varidx name _ty -> error ("ANF: unsupported ExtCns: " ++ name))
         (const (const Nothing))
  Sim.evalSharedTerm cfg t

asPredType :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "Verifier.SAW.Simulator.BitBlast.asPredType: non-boolean result type: " ++ show t'

withBitBlastedPred ::
  SharedContext s ->
  Map Ident AValue ->
  SharedTerm s ->
  (ANF -> [FiniteType] -> IO a) -> IO a
withBitBlastedPred sc addlPrims t c = do
  ty <- scTypeOf sc t
  argTs <- asPredType sc ty
  shapes <- traverse (asFiniteType sc) argTs
  let vars = evalState (traverse newVars' shapes) 0
  let bval = bitBlastBasic (scModule sc) addlPrims t
  let bval' = runIdentity $ applyAll bval vars
  case bval' of
    VBool anf -> c anf shapes
    _ -> fail "Verifier.SAW.Simulator.ANF.bitBlast: non-boolean result type."
