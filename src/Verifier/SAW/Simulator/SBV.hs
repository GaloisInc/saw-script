{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
module Verifier.SAW.Simulator.SBV where

import qualified Data.SBV as S
import qualified Data.SBV.Tools.Polynomial as Poly
import Data.SBV (Symbolic, SBool, Predicate)
import Data.SBV.Internals
import Data.SBV.LowLevel as L
import Data.Bits

import Control.Lens
import Control.Arrow

import Data.Map (Map)
import Data.IORef
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Traversable as T
import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.State as ST
import Control.Monad

import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Prim hiding (BV)
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.TypedAST (FieldName, {-Ident,-} Module)
import Verinf.Symbolic.Lit

import Debug.Trace

import Verifier.SAW.BitBlast (BShape(..))

type SValue = Value IO SbvExtra
type SThunk = Thunk IO SbvExtra

data SbvExtra =
  SBool SBool |
  SWord SWord | 
  SZero |
  SStream (Integer -> IO SValue) (IORef (Map Integer SValue))

instance Show SbvExtra where
  show (SBool s) = "SBool " ++ show s
  show (SWord w) = "SWord " ++ show w
  show SZero = "SZero"
  show (SStream _ _) = "<SStream>"
  
constMap :: Map Ident SValue
constMap = Map.fromList [
    -- Boolean
    ("Prelude.True", VExtra (SBool S.true)),
    ("Prelude.False", VExtra (SBool S.false)),
    ("Prelude.not", strictFun (return . vBool . S.bnot . forceBool)),
    ("Prelude.and", boolBinOp (S.&&&)),
    ("Prelude.or", boolBinOp (S.|||)),
    ("Prelude.xor", boolBinOp (S.<+>)) ,
    ("Prelude.boolEq", boolBinOp (S.<=>)),
    ("Prelude.ite", iteOp),
    -- Arithmetic
    ("Prelude.bvAdd" , binOp L.bvAdd),
    ("Prelude.bvSub" , binOp L.bvSub),
    ("Prelude.bvMul" , binOp L.bvMul),
    ("Prelude.bvAnd" , binOp L.bvAnd),
    ("Prelude.bvOr"  , binOp L.bvOr),
    ("Prelude.bvXor" , binOp L.bvXOr),
    ("Prelude.bvUDiv", binOp L.bvUDiv),
    ("Prelude.bvURem", binOp L.bvURem),
    ("Prelude.bvSDiv", binOp L.bvSDiv),
    ("Prelude.bvSRem", binOp L.bvSRem),
    ("Prelude.bvPMul", bvPMulOp),
    ("Prelude.bvPMod", bvPModOp),
    -- Relations 
    ("Prelude.bvEq"  , binRel L.bvEq),
    ("Prelude.bvsle" , binRel L.bvSLe),
    ("Prelude.bvslt" , binRel L.bvSLt),
    ("Prelude.bvule" , binRel L.bvLe),
    ("Prelude.bvult" , binRel L.bvLt),
    ("Prelude.bvsge" , binRel L.bvSGe),
    ("Prelude.bvsgt" , binRel L.bvSGt),
    ("Prelude.bvuge" , binRel L.bvGe),
    ("Prelude.bvugt" , binRel L.bvGt),
    -- Shifts
    ("Prelude.bvShl" , bvShLOp),
    ("Prelude.bvShr" , bvShROp),
    ("Prelude.bvSShr", bvSShROp),
    -- Nat
    ("Prelude.Succ", Prims.succOp),
    ("Prelude.addNat", Prims.addNatOp),
    ("Prelude.subNat", Prims.subNatOp),
    ("Prelude.mulNat", Prims.mulNatOp),
    ("Prelude.minNat", Prims.minNatOp),
    ("Prelude.maxNat", Prims.maxNatOp),
    ("Prelude.widthNat", Prims.widthNatOp),
    ("Prelude.natCase", Prims.natCaseOp),
    -- Fin
    ("Prelude.finDivMod", Prims.finDivModOp),
    ("Prelude.finMax", Prims.finMaxOp),
    ("Prelude.finPred", Prims.finPredOp),
    ("Prelude.natSplitFin", Prims.natSplitFinOp),
    -- Vectors
    ("Prelude.generate", Prims.generateOp),
    ("Prelude.get", getOp),
    ("Prelude.at", atOp),
    ("Prelude.append", appendOp),
    ("Prelude.vZip", vZipOp),
    ("Prelude.foldr", foldrOp),
    ("Prelude.bvAt", bvAtOp),
    ("Prelude.bvUpd", bvUpdOp),
    ("Prelude.bvRotateL", bvRotateLOp),
    ("Prelude.bvRotateR", bvRotateROp),
    ("Prelude.bvShiftR", bvShiftROp),
     -- Streams
    ("Prelude.MkStream", mkStreamOp),
    ("Prelude.streamGet", streamGetOp),
    ("Prelude.bvStreamGet", bvStreamGetOp),
    -- Miscellaneous
    ("Prelude.coerce", Prims.coerceOp),
    ("Prelude.bvNat", bvNatOp)
    -- ("Prelude.bvToNat", bvToNatOp)
  ]

------------------------------------------------------------
-- Coersion functions

symFromBits :: Vector SBool -> SWord
symFromBits v
  = V.foldl (L.bvAdd) (bitVector l 0) $ flip V.imap (V.reverse v) $ \i b->
      S.ite b (symBit l i) (bitVector l 0)
  where
    l = V.length v

symBit :: Int -> Int -> SWord
symBit l i = bitVector l (S.shiftL 1 i)

toBool :: SValue -> Maybe SBool
toBool (VExtra (SBool b)) = Just b
toBool _  = Nothing

forceBool :: SValue -> SBool
forceBool = fromJust . toBool

toWord :: SValue -> IO (Maybe SWord)
toWord (VExtra (SWord w)) = return (Just w)
toWord (VVector vv) = ((symFromBits <$>) . T.sequence) <$> traverse (fmap toBool . force) vv
toWord x = trace ("could not convert " ++ show x) $ return Nothing

toVector :: SValue -> V.Vector SThunk
toVector (VVector xv) = xv
toVector (VExtra SZero) = V.empty
toVector (VExtra (SWord xv@(SBV (KBounded _ k) _))) =
  V.fromList (map (Ready . vBool . symTestBit xv) (enumFromThenTo (k-1) (k-2) 0))
toVector _ = error "this word might be symbolic"

vWord :: SWord -> SValue
vWord lv = VExtra (SWord lv)

vBool :: SBool -> SValue
vBool l = VExtra (SBool l)

------------------------------------------------------------
-- Function constructors

wordFun :: (Maybe SWord -> IO SValue) -> SValue
wordFun f = strictFun (\x -> toWord x >>= f)

------------------------------------------------------------
-- Indexing operations

-- | Lifts a strict mux operation to a lazy mux
lazyMux :: (SBool -> a -> a -> IO a) -> (SBool -> IO a -> IO a -> IO a)
lazyMux muxFn c tm fm
  | c `S.isConcretely` (== True) = tm
  | c `S.isConcretely` (== False) = fm
  | otherwise = do
      t <- tm
      f <- fm
      muxFn c t f

-- selectV merger maxValue valueFn index returns valueFn v when index has value v
-- if index is greater than maxValue, it returns valueFn maxValue. Use the ite op from merger.
selectV :: (Ord a, Num a, Bits a) => (SBool -> b -> b -> b)
  -> a -> (a -> b) -> SWord -> b
selectV merger maxValue valueFn vx@(SBV _ (Left (cwVal -> CWInteger i))) =
  trace "selecting concretely" $ valueFn (fromIntegral i)
selectV merger maxValue valueFn vx@(SBV(KBounded _ s) _) = trace "selecting symbolicly" $
  impl s 0 where
  impl _ y | y >= maxValue = valueFn maxValue
  impl 0 y = valueFn y
  impl i y = merger (symTestBit vx j) (impl j (y `setBit` j)) (impl j y) where j = i - 1

-- `nOfSize word len` pads word with zeros to be size len
nOfSize :: SWord -> Int -> SWord
nOfSize ind@(SBV (KBounded _ k2) s) k
  | k == k2 = ind
  | Left (cwVal -> CWInteger ival) <- s = bitVector k ival
  | k >= k2 = L.bvJoin ((bitVector (k - k2) 0) :: SWord) ind
  | otherwise = error "could not resize index"

-- could use extract instead

-- symTestSym word index gets index ind from vector w
-- it is the equivalent of cryptol-2 indexing; NOT the same as testBit
symTestSym :: SWord -> SWord -> SValue
symTestSym w@(SBV (KBounded _ k) _) (SBV _ (Left (cwVal -> CWInteger i))) = vBool $ symTestBit w (traceIt "conc symtestsym" (k - 1 - fromIntegral i))
symTestSym w@(SBV (KBounded _ k) _) ind =
  vBool $ L.bvNeq (bitVector k 0) $ L.bvAnd w
    (L.bvShL (bitVector k 1)
    (traceIt "sym symtestsym" (L.bvSub (bitVector k (fromIntegral k - 1)) (nOfSize ind k)) ))

traceIt a x = trace (a ++ ": " ++ show x) $ x

-- symTestBit word index gets bit position ind from word w
-- it is the equivalent of testBit; NOT the same as cryptol-2 indexing
symTestBit :: SWord -> Int -> SBool
symTestBit x@(SBV (KBounded _ w) _) i = bvNeq (bitVector w 0) (L.bvAnd x (bitVector w (bit i)))
symTestBit _ _ = error "SWord must be bounded"

-- at :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a;
atOp :: SValue
atOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  Prims.natFun $ \n ->
    case v of
      VVector xv -> force ((V.!) xv (fromIntegral n))
      VExtra (SWord lv@(SBV (KBounded _ k) _)) -> return $ vBool $ symTestBit lv ((k-1) - fromIntegral n)
      _ -> fail "atOp: expected vector"

-- bvAt :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> a;
bvAtOp :: SValue
bvAtOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  wordFun $ \milv -> do
    case (milv, v) of
      (Nothing, VVector xv) -> force (xv V.! 0)
      (Just ilv, VVector xv) ->
        force =<< selectV (lazyMux muxThunk) (V.length xv - 1) (return . (V.!) xv) ilv
      (Just ilv, VExtra (SWord lv)) -> trace "v is a word" $ return $ symTestSym lv ilv
      _ -> fail "getOp: expected vector"

-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
getOp :: SValue
getOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  Prims.finFun $ \i ->
    case v of
      VVector xv -> force ((V.!) xv (fromEnum (finVal i)))
      VExtra (SWord lv@(SBV (KBounded _ k) _)) -> return $ vBool $ symTestBit lv ((k-1) - fromEnum (finVal i))
      _ -> fail "getOp: expected vector"

----------------------------------------
-- Shift operations

-- bvShl :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShLOp :: SValue
bvShLOp = 
  VFun $ \_ -> return $
  wordFun $ \(Just w) -> return $
  Prims.natFun $ \n -> return $ vWord $ L.bvShLC w (fromIntegral n)

-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShROp :: SValue
bvShROp = 
  VFun $ \_ -> return $
  wordFun $ \(Just w) -> return $
  Prims.natFun $ \n -> return $ vWord $ L.bvShRC w (fromIntegral n)

-- bvSShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvSShROp :: SValue
bvSShROp = 
  VFun $ \_ -> return $
  wordFun $ \(Just w) -> return $
  Prims.natFun $ \n -> return $ vWord $ L.bvSShRC w (fromIntegral n)


----------------------------------------
-- Polynomial operations

-- bvPMod :: (m n :: Nat) -> bitvector m -> bitvector (Succ n) -> bitvector n;
bvPModOp :: SValue
bvPModOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  wordFun $ \(Just x@(SBV (KBounded _ a) _)) -> return $
  wordFun $ \(Just y@(SBV (KBounded _ b) _)) ->
    return . vWord . S.fromBitsLE $ take (b-1) (snd (Poly.mdp (S.blastLE x) (S.blastLE y)) ++ repeat S.false)

-- bvPMul :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector (subNat (maxNat 1 (addNat m n)) 1);
bvPMulOp :: SValue
bvPMulOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  wordFun $ \(Just x@(SBV (KBounded _ a) _)) -> return $
  wordFun $ \(Just y@(SBV (KBounded _ b) _)) -> do
    let k = max 1 (a + b) - 1
    let mul _ [] ps = ps
        mul as (b:bs) ps = mul (S.false : as) bs (Poly.ites b (as `Poly.addPoly` ps) ps)
    return . vWord . S.fromBitsLE $ take k $ mul (S.blastLE x) (S.blastLE y) [] ++ repeat S.false

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

-- bvUpd :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> a -> Vec n a;
bvUpdOp :: SValue
bvUpdOp = 
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  wordFun $ \milv -> return $
  strictFun $ \y ->
    case (milv, v) of
      (Nothing, VVector xv) -> do
        y' <- delay (return y)
        return (VVector (xv V.// [(0, y')]))
      (Nothing, VExtra (SWord lv@(SBV (KBounded _ w) _)))-> do
        let (Just b) = toBool y
        return $ vWord $ S.ite b
          (L.bvOr lv (L.bvShLC (bitVector w 1) (fromIntegral w - 1)))
          (L.bvAnd lv (L.bvNot (L.bvShLC (bitVector w 1) (fromIntegral w - 1))))
      (Just ilv, VVector xv) -> do
        y' <- delay (return y)
        let upd i = return (VVector (xv V.// [(i, y')]))
        selectV (lazyMux muxBVal) (V.length xv - 1) upd ilv
      (Just ilv, VExtra (SWord lv@(SBV (KBounded _ w) _))) -> do
        let (Just b) = toBool y
        return $ vWord $ S.ite b
          (L.bvOr lv (L.bvShL (bitVector w 1) (L.bvSub (bitVector w (fromIntegral w - 1)) (nOfSize ilv w))))
          (L.bvAnd lv (L.bvNot (L.bvShL (bitVector w 1) (L.bvSub (bitVector w (fromIntegral w - 1)) (nOfSize ilv w)))))
      _ -> fail "bvUpdOp: expected vector"

------------------------------------------------------------
-- Rotations and shifts

-- bvRotateL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateLOp :: SValue
bvRotateLOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  wordFun $ \milv ->
    case (milv, xs) of
      (Nothing, xv) -> return xv
      (Just ilv, VVector xv) -> selectV (lazyMux muxBVal) (V.length xv -1) (return . VVector . vRotateL xv) ilv
      (Just ilv, VExtra (SWord xlv)) ->
        selectV (lazyMux muxBVal) (L.bvLength xlv -1) (return . vWord . L.bvRotLC xlv) ilv
      _ -> error $ "rotateLOp: " ++ show xs

-- bvRotateR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateROp :: SValue
bvRotateROp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  wordFun $ \milv -> do
    case (milv, xs) of
      (Nothing, xv) -> return xv
      (Just ilv, VVector xv) -> selectV (lazyMux muxBVal) (V.length xv -1) (return . VVector . vRotateR xv) ilv
      (Just ilv, VExtra (SWord xlv)) ->
        selectV (lazyMux muxBVal) (L.bvLength xlv -1) (return . VExtra . SWord . L.bvRotRC xlv) ilv
      _ -> error $ "rotateROp: " ++ show xs

-- bvShiftR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftROp :: SValue
bvShiftROp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \milv -> do
    case (milv, xs) of
      (Nothing, xv) -> return xv
      (Just ilv, VVector xv) -> selectV (lazyMux muxBVal) (V.length xv - 1) (return . VVector . vShiftR x xv) ilv
      (Just ilv, VExtra (SWord xlv)) -> return $ vWord (L.bvShR xlv ilv)
      _ -> fail $ "bvShiftROp: " ++ show xs

------------------------------------------------------------
-- Stream operations

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: SValue
mkStreamOp =
  VFun $ \_ -> return $
  strictFun $ \f -> do
    r <- newIORef Map.empty
    return $ VExtra (SStream (\n -> apply f (Ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: SValue
streamGetOp =
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  Prims.natFun $ \n -> lookupSStream xs (toInteger n)

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: SValue
bvStreamGetOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  wordFun $ \(Just ilv) ->
  selectV (lazyMux muxBVal) ((2 ^ L.bvLength ilv) - 1) (lookupSStream xs) ilv

lookupSStream :: SValue -> Integer -> IO SValue
lookupSStream (VExtra (SStream f r)) n = do
   m <- readIORef r
   case Map.lookup n m of
     Just v  -> return v
     Nothing -> do v <- f n
                   writeIORef r (Map.insert n v m)
                   return v
lookupSStream _ _ = fail "expected Stream"

------------------------------------------------------------
-- Misc operations

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNatOp :: SValue
bvNatOp = 
  Prims.natFun $ \w -> return $
  Prims.natFun $ \x -> return $
  if w == 0 then VExtra SZero
    else vWord (bitVector (fromIntegral w) (toInteger x))

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: SValue
foldrOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \f -> return $
  VFun $ \z -> return $
  strictFun $ \xs -> do
    let g x m = do fx <- apply f x
                   y <- delay m
                   apply fx y
    case xs of
      VVector xv -> V.foldr g (force z) xv
      _ -> fail "foldrOp"

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: SValue
vZipOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  VVector (V.zipWith (\x y -> Ready (VTuple (V.fromList [x, y]))) (toVector xs) (toVector ys))

-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: SValue
appendOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \ys ->
  case (xs, ys) of
    (VVector xv, VVector yv) -> return $ VVector ((V.++) xv yv)
    (VExtra SZero, w) -> return w
    (v, VExtra SZero) -> return v
    (v, w) -> do
      (Just v') <- toWord v
      (Just w') <- toWord w
      return $ vWord $ traceIt "appending" $ bvJoin (traceIt "v" v') (traceIt "w" w')
    _ -> error "appendOp"

------------------------------------------------------------
-- Helpers for marshalling into SValues

binOp :: (SWord -> SWord -> SWord) -> SValue
binOp op = VFun $ \_-> return $
          strictFun $ \mx-> return $
          strictFun $ \my->
            case (mx, my) of
               (VExtra SZero, VExtra SZero) -> return (VExtra SZero)
               _ -> do
                 (Just x) <- toWord mx
                 (Just y) <- toWord my
                 return $ vWord $ op x y

binRel :: (SWord -> SWord -> SBool) -> SValue
binRel op = VFun $ \_-> return $
            strictFun $ \mx-> return $
            strictFun $ \my-> do
              (Just x) <- toWord mx
              (Just y) <- toWord my
              return $ vBool $ op x y

boolBinOp :: (SBool -> SBool -> SBool) -> SValue
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> return $ vBool $ op (forceBool x) (forceBool y)

------------------------------------------------------------
-- Ite ops

iteOp :: SValue
iteOp = 
    VFun $ \_ -> return $
    strictFun $ \b-> return $
    strictFun $ \x-> return $
    strictFun $ \y-> muxBVal (forceBool b) x y

muxBVal :: SBool -> SValue -> SValue -> IO SValue
muxBVal b (VFun f) (VFun g) = return $ VFun (\a -> do x <- f a; y <- g a; muxBVal b x y)
muxBVal b (VCtorApp i xv) (VCtorApp j yv) | i == j = VCtorApp i <$> muxThunks b xv yv
muxBVal b (VVector xv)    (VVector yv)    = VVector <$> muxThunks b xv yv
muxBVal _ (VNat m)        (VNat n)        | m == n = return $ VNat m
muxBVal _ (VString x)     (VString y)     | x == y = return $ VString x
muxBVal _ (VFloat x)      (VFloat y)      | x == y = return $ VFloat x
muxBVal _ (VDouble x)     (VDouble y)     | x == y = return $ VDouble y
muxBVal _ VType           VType           = return VType
muxBVal b (VExtra x)      (VExtra y)      = return $ VExtra $ extraFn b x y
muxBVal _ _ _ = fail "iteOp: malformed arguments"

muxThunks :: SBool -> V.Vector SThunk -> V.Vector SThunk -> IO (V.Vector SThunk)
muxThunks b xv yv
  | V.length xv == V.length yv = V.zipWithM (muxThunk b) xv yv
  | otherwise                  = fail "iteOp: malformed arguments"

muxThunk :: SBool -> SThunk -> SThunk -> IO SThunk
muxThunk b x y = delay $ do x' <- force x; y' <- force y; muxBVal b x' y'

extraFn :: SBool -> SbvExtra -> SbvExtra -> SbvExtra
extraFn b (SBool x) (SBool y) = SBool $ S.ite b x y
extraFn b (SWord x) (SWord y) = SWord $ S.ite b x y
extraFn _ _ _ = error "iteOp: malformed arguments"

------------------------------------------------------------
-- External interface

sbvSolveBasic :: Module -> SharedTerm s -> IO SValue
sbvSolveBasic m = Sim.evalSharedTerm cfg
  where cfg = Sim.evalGlobal m constMap

asPredType :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "non-boolean result type: " ++ show t'

sbvSolve :: SharedContext s -> SharedTerm s -> IO ([Labeler], Predicate)
sbvSolve sc t = do
  ty <- scTypeOf sc t
  argTs <- asPredType sc ty
  shapes <- traverse (parseShape sc) argTs
  bval <- sbvSolveBasic (scModule sc) t
  let (labels, vars) = flip evalState 0 $ unzip <$> traverse newVars shapes
  let pred = do
              bval' <- traverse (fmap Ready) vars >>= (liftIO . applyAll bval)
              case bval' of
                VExtra (SBool b) -> return b
                _ -> fail "bitBlast: non-boolean result type."
  return (labels, pred)

parseShape :: SharedContext s -> SharedTerm s -> IO BShape
parseShape sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asBoolType -> Just ())
      -> return BoolShape
    (R.isVecType return -> Just (n R.:*: tp))
      -> VecShape n <$> parseShape sc tp
    (R.asTupleType -> Just ts)
      -> TupleShape <$> traverse (parseShape sc) ts
    (R.asRecordType -> Just tm)
       -> RecShape <$> traverse (parseShape sc) tm
    _ -> fail $ "bitBlast: unsupported argument type: " ++ show t'

data Labeler
   = BoolLabel String
   | WordLabel String
   | VecLabel (Vector Labeler)
   | TupleLabel (Vector Labeler)
   | RecLabel (Map FieldName Labeler)
     deriving (Show)

nextId :: State Int String
nextId = ST.get >>= (\s-> modify (+1) >> return ("x" ++ show s))

myfun ::(Map String (Labeler, Symbolic SValue)) -> (Map String Labeler, Map String (Symbolic SValue))
myfun = fmap fst &&& fmap snd

newVars :: BShape -> State Int (Labeler, Symbolic SValue)
newVars BoolShape = nextId <&> \s-> (BoolLabel s, vBool <$> S.exists s)
newVars (VecShape n BoolShape) =
  if n == 0
    then nextId <&> \s-> (WordLabel s, return (VExtra SZero))
    else nextId <&> \s-> (WordLabel s, vWord <$> symBitVector (fromIntegral n) EX (Just s))
newVars (VecShape n tp) = do
  (labels, vals) <- V.unzip <$> V.replicateM (fromIntegral n) (newVars tp)
  return (VecLabel labels, VVector <$> traverse (fmap Ready) vals)
newVars (TupleShape ts) = do
  (labels, vals) <- V.unzip <$> traverse newVars (V.fromList ts)
  return (TupleLabel labels, VTuple <$> traverse (fmap Ready) vals)
newVars (RecShape tm) = do
  (labels, vals) <- myfun <$> (traverse newVars tm :: State Int (Map String (Labeler, Symbolic SValue)))
  return (RecLabel labels, VRecord <$> traverse (fmap Ready) (vals :: (Map String (Symbolic SValue))))
