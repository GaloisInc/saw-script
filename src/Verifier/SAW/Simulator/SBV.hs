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
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
module Verifier.SAW.Simulator.SBV where

import Data.SBV
import Data.SBV.Internals
import Verifier.SAW.Simulator.SBV.SWord

import Control.Lens ((<&>))
import qualified Control.Arrow as A

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

import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Prim hiding (BV, ite, bv)
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.TypedAST (FieldName, Ident(..), Module, Termlike)

import Verifier.SAW.FiniteValue ( FiniteType(..), sizeFiniteType, asFiniteType
                                , asFiniteTypePure)

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

-- no, we need shape information
uninterpreted :: (Show t, Termlike t) => Ident -> t -> Maybe (IO SValue)
uninterpreted ident t = Just $ parseUninterpreted [] [] t (identName ident)

-- actually...
-- rewriteSharedTerm

constMap :: Map Ident SValue
constMap = Map.fromList [
    -- Boolean
    ("Prelude.True", VExtra (SBool true)),
    ("Prelude.False", VExtra (SBool false)),
    ("Prelude.not", strictFun (return . vBool . bnot . forceBool)),
    ("Prelude.and", boolBinOp (&&&)),
    ("Prelude.or", boolBinOp (|||)),
    ("Prelude.xor", boolBinOp (<+>)) ,
    ("Prelude.boolEq", boolBinOp (<=>)),
    ("Prelude.ite", iteOp),
    -- Arithmetic
    ("Prelude.bvAdd" , binOp (+)),
    ("Prelude.bvSub" , binOp (-)),
    ("Prelude.bvMul" , binOp (*)),
    ("Prelude.bvAnd" , binOp (.&.)),
    ("Prelude.bvOr"  , binOp (.|.)),
    ("Prelude.bvXor" , binOp xor),
    ("Prelude.bvUDiv", binOp sDiv),
    ("Prelude.bvURem", binOp sRem),
    ("Prelude.bvSDiv", sbinOp sDiv),
    ("Prelude.bvSRem", sbinOp sRem),
    ("Prelude.bvPMul", bvPMulOp),
    ("Prelude.bvPMod", bvPModOp),
    -- Relations
    ("Prelude.bvEq"  , binRel (.==)),
    ("Prelude.bvsle" , sbinRel (.<=)),
    ("Prelude.bvslt" , sbinRel (.<)),
    ("Prelude.bvule" , binRel (.<=)),
    ("Prelude.bvult" , binRel (.<)),
    ("Prelude.bvsge" , sbinRel (.>=)),
    ("Prelude.bvsgt" , sbinRel (.>)),
    ("Prelude.bvuge" , binRel (.>=)),
    ("Prelude.bvugt" , binRel (.>)),
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
    ("Prelude.divModNat", Prims.divModNatOp),
    ("Prelude.expNat", Prims.expNatOp),
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
    ("Prelude.set", setOp),
    ("Prelude.at", atOp),
    ("Prelude.upd", updOp),
    ("Prelude.append", appendOp),
    ("Prelude.vZip", vZipOp),
    ("Prelude.foldr", foldrOp),
    ("Prelude.bvAt", bvAtOp),
    ("Prelude.bvUpd", bvUpdOp),
    ("Prelude.bvRotateL", bvRotateLOp),
    ("Prelude.bvRotateR", bvRotateROp),
    ("Prelude.bvShiftL", bvShiftLOp),
    ("Prelude.bvShiftR", bvShiftROp),
     -- Streams
    ("Prelude.MkStream", mkStreamOp),
    ("Prelude.streamGet", streamGetOp),
    ("Prelude.bvStreamGet", bvStreamGetOp),
    -- Miscellaneous
    ("Prelude.coerce", Prims.coerceOp),
    ("Prelude.bvNat", bvNatOp)
  ]

------------------------------------------------------------
-- Coersion functions
--

bitVector :: Int -> Integer -> SWord
bitVector w i = literalSWord w i

symFromBits :: Vector SBool -> SWord
symFromBits v
  = V.foldl (+) (bitVector l 0) $ flip V.imap (V.reverse v) $ \i b->
      ite b (symBit l i) (bitVector l 0)
  where
    l = V.length v

symBit :: Int -> Int -> SWord
symBit l i = bitVector l (shiftL 1 i)

toBool :: SValue -> Maybe SBool
toBool (VExtra (SBool b)) = Just b
toBool _  = Nothing

forceBool :: SValue -> SBool
forceBool = fromJust . toBool

toWord :: SValue -> IO (Maybe SWord)
toWord (VExtra (SWord w)) = return (Just w)
toWord (VVector vv) = ((symFromBits <$>) . T.sequence) <$> traverse (fmap toBool . force) vv
toWord _ = return Nothing

toVector :: SValue -> V.Vector SThunk
toVector (VVector xv) = xv
toVector (VExtra SZero) = V.empty
toVector (VExtra (SWord xv@(SBV (KBounded _ k) _))) =
  V.fromList (map (ready . vBool . symTestBit xv) (enumFromThenTo (k-1) (k-2) 0))
toVector _ = error "this word might be symbolic"

toTuple :: SValue -> IO (Maybe [SBV ()])
toTuple (VTuple xv) = (fmap concat . T.sequence . V.toList . V.reverse) <$> traverse (force >=> toSBV) xv
toTuple _ = return Nothing

toSBV :: SValue -> IO (Maybe [SBV ()])
toSBV v = do
  t <- toTuple v
  w <- toWord v
  return $ (untype <$> toBool v) `mplus` (untype <$> w) `mplus` t

untype :: SBV a -> [SBV ()]
untype (SBV k e) = [SBV k e]


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
  | c `isConcretely` (== True) = tm
  | c `isConcretely` (== False) = fm
  | otherwise = do
      t <- tm
      f <- fm
      muxFn c t f

-- selectV merger maxValue valueFn index returns valueFn v when index has value v
-- if index is greater than maxValue, it returns valueFn maxValue. Use the ite op from merger.
selectV :: (Ord a, Num a, Bits a) => (SBool -> b -> b -> b)
  -> a -> (a -> b) -> SWord -> b
selectV _merger _maxValue valueFn _vx@(SBV _ (Left (cwVal -> CWInteger i))) =
  valueFn (fromIntegral i)
selectV merger maxValue valueFn vx@(SBV(KBounded _ s) _) =
  impl s 0 where
  impl _ y | y >= maxValue = valueFn maxValue
  impl 0 y = valueFn y
  impl i y = merger (symTestBit vx j) (impl j (y `setBit` j)) (impl j y) where j = i - 1
selectV _ _ _ _ = error "selectV: invalid argument"

-- `nOfSize word len` pads word with zeros to be size len
nOfSize :: SWord -> Int -> SWord
nOfSize ind@(SBV (KBounded _ k2) s) k
  | k == k2 = ind
  | Left (cwVal -> CWInteger ival) <- s = bitVector k ival
  | k >= k2 = cat ((bitVector (k - k2) 0) :: SWord) ind
  | otherwise = error "could not resize index"
nOfSize _ _ = error "nOfSize: invalid argument"

-- could use extract instead

-- symTestSym word index gets index ind from vector w
-- it is the equivalent of cryptol-2 indexing; NOT the same as testBit
symTestSym :: SWord -> SWord -> SValue
symTestSym w@(SBV (KBounded _ k) _) (SBV _ (Left (cwVal -> CWInteger i))) = vBool $ symTestBit w (k - 1 - fromIntegral i)
symTestSym w@(SBV (KBounded _ k) _) ind =
  vBool $ bitVector k 0 ./= (w .&.
    (sbvShiftLeft (bitVector k 1)
    ((bitVector k (fromIntegral k - 1)) - (nOfSize ind k)) ))
symTestSym _ _ = error "symTestSym: invalid argument"

-- symTestBit word index gets bit position ind from word w
-- it is the equivalent of testBit; NOT the same as cryptol-2 indexing
symTestBit :: SWord -> Int -> SBool
symTestBit x@(SBV (KBounded _ w) _) i = (bitVector w 0) ./= (x .&. (bitVector w (bit i)))
symTestBit _ _ = error "SWord must be bounded"

-- at :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a;
atOp :: SValue
atOp =
  constFun $
  constFun $
  strictFun $ \v -> return $
  Prims.natFun $ \n ->
    case v of
      VVector xv -> force ((V.!) xv (fromIntegral n))
      VExtra (SWord lv@(SBV (KBounded _ k) _)) -> return $ vBool $ symTestBit lv ((k-1) - fromIntegral n)
      _ -> fail "atOp: expected vector"

-- upd :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a -> Vec n a;
updOp :: SValue
updOp =
  constFun $
  constFun $
  strictFun $ \v -> return $
  Prims.natFun $ \n -> return $
  VFun $ \y ->
    case v of
      VVector xv -> return $ VVector ((V.//) xv [(fromIntegral n, y)])
      _ -> fail "updOp: expected vector"

-- bvAt :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> a;
bvAtOp :: SValue
bvAtOp =
  constFun $
  constFun $
  constFun $
  strictFun $ \v -> return $
  wordFun $ \milv -> do
    case (milv, v) of
      (Nothing, VVector xv) -> force (xv V.! 0)
      (Just ilv, VVector xv) ->
        force =<< selectV (lazyMux muxThunk) (V.length xv - 1) (return . (V.!) xv) ilv
      (Just ilv, VExtra (SWord lv)) -> return $ symTestSym lv ilv
      _ -> fail "getOp: expected vector"

-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
getOp :: SValue
getOp =
  constFun $
  constFun $
  strictFun $ \v -> return $
  Prims.finFun $ \i ->
    case v of
      VVector xv -> force ((V.!) xv (fromEnum (finVal i)))
      VExtra (SWord lv@(SBV (KBounded _ k) _)) -> return $ vBool $ symTestBit lv ((k-1) - fromEnum (finVal i))
      _ -> fail "getOp: expected vector"

-- set :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a -> Vec n a;
setOp :: SValue
setOp =
  constFun $
  constFun $
  strictFun $ \v -> return $
  Prims.finFun $ \i -> return $
  VFun $ \y ->
    case v of
      VVector xv -> return $ VVector ((V.//) xv [(fromEnum (finVal i), y)])
      _ -> fail "setOp: expected vector"

----------------------------------------
-- Shift operations

-- bvShl :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShLOp :: SValue
bvShLOp =
  constFun $
  wordFun $ \(Just w) -> return $
  Prims.natFun $ \n -> return $ vWord $ shiftL w (fromIntegral n)

-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShROp :: SValue
bvShROp =
  constFun $
  wordFun $ \(Just w) -> return $
  Prims.natFun $ \n -> return $ vWord $ shiftR w (fromIntegral n)

-- bvSShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvSShROp :: SValue
bvSShROp =
  constFun $
  wordFun $ \(Just w) -> return $
  Prims.natFun $ \n -> return $ vWord $ unsignCast $ shiftR (signCast w) (fromIntegral n)


----------------------------------------
-- Polynomial operations

-- bvPMod :: (m n :: Nat) -> bitvector m -> bitvector (Succ n) -> bitvector n;
bvPModOp :: SValue
bvPModOp =
  constFun $
  constFun $
  wordFun $ \(Just x@(SBV (KBounded _ _k1) _)) -> return $
  wordFun $ \(Just y@(SBV (KBounded _ k2) _)) ->
    return . vWord . fromBitsLE $ take (k2-1) (snd (mdp (blastLE x) (blastLE y)) ++ repeat false)

-- bvPMul :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector (subNat (maxNat 1 (addNat m n)) 1);
bvPMulOp :: SValue
bvPMulOp =
  constFun $
  constFun $
  wordFun $ \(Just x@(SBV (KBounded _ k1) _)) -> return $
  wordFun $ \(Just y@(SBV (KBounded _ k2) _)) -> do
    let k = max 1 (k1 + k2) - 1
    let mul _ [] ps = ps
        mul as (b:bs) ps = mul (false : as) bs (ites b (as `addPoly` ps) ps)
    return . vWord . fromBitsLE $ take k $ mul (blastLE x) (blastLE y) [] ++ repeat false

-- TODO: Data.SBV.BitVectors.Polynomials should export ites, addPoly,
-- and mdp (the following definitions are copied from that module)

-- | Add two polynomials
addPoly :: [SBool] -> [SBool] -> [SBool]
addPoly xs    []      = xs
addPoly []    ys      = ys
addPoly (x:xs) (y:ys) = x <+> y : addPoly xs ys

ites :: SBool -> [SBool] -> [SBool] -> [SBool]
ites s xs ys
 | Just t <- unliteral s
 = if t then xs else ys
 | True
 = go xs ys
 where go [] []         = []
       go []     (b:bs) = ite s false b : go [] bs
       go (a:as) []     = ite s a false : go as []
       go (a:as) (b:bs) = ite s a b : go as bs

-- conservative over-approximation of the degree
degree :: [SBool] -> Int
degree xs = walk (length xs - 1) $ reverse xs
  where walk n []     = n
        walk n (b:bs)
         | Just t <- unliteral b
         = if t then n else walk (n-1) bs
         | True
         = n -- over-estimate

mdp :: [SBool] -> [SBool] -> ([SBool], [SBool])
mdp xs ys = go (length ys - 1) (reverse ys)
  where degTop  = degree xs
        go _ []     = error "SBV.Polynomial.mdp: Impossible happened; exhausted ys before hitting 0"
        go n (b:bs)
         | n == 0   = (reverse qs, rs)
         | True     = let (rqs, rrs) = go (n-1) bs
                      in (ites b (reverse qs) rqs, ites b rs rrs)
         where degQuot = degTop - n
               ys' = replicate degQuot false ++ ys
               (qs, rs) = divx (degQuot+1) degTop xs ys'

-- return the element at index i; if not enough elements, return false
-- N.B. equivalent to '(xs ++ repeat false) !! i', but more efficient
idx :: [SBool] -> Int -> SBool
idx []     _ = false
idx (x:_)  0 = x
idx (_:xs) i = idx xs (i-1)

divx :: Int -> Int -> [SBool] -> [SBool] -> ([SBool], [SBool])
divx n _ xs _ | n <= 0 = ([], xs)
divx n i xs ys'        = (q:qs, rs)
  where q        = xs `idx` i
        xs'      = ites q (xs `addPoly` ys') xs
        (qs, rs) = divx (n-1) (i-1) xs' (tail ys')

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
  constFun $
  constFun $
  constFun $
  strictFun $ \v -> return $
  wordFun $ \milv -> return $
  strictFun $ \y ->
    case (milv, v) of
      (Nothing, VVector xv) -> do
        y' <- delay (return y)
        return (VVector (xv V.// [(0, y')]))
      (Nothing, VExtra (SWord lv@(SBV (KBounded _ w) _)))-> do
        let (Just b) = toBool y
        return $ vWord $ ite b
          (lv .|. (shiftL (bitVector w 1) (fromIntegral w - 1)))
          (lv .&. (complement (shiftL (bitVector w 1) (fromIntegral w - 1))))
      (Just ilv, VVector xv) -> do
        y' <- delay (return y)
        let update i = return (VVector (xv V.// [(i, y')]))
        selectV (lazyMux muxBVal) (V.length xv - 1) update ilv
      (Just ilv, VExtra (SWord lv@(SBV (KBounded _ w) _))) -> do
        let (Just b) = toBool y
        return $ vWord $ ite b
          (lv .|. (sbvShiftLeft (bitVector w 1) ((bitVector w (fromIntegral w - 1)) - (nOfSize ilv w))))
          (lv .&. (complement (sbvShiftLeft (bitVector w 1) ((bitVector w (fromIntegral w - 1)) - (nOfSize ilv w)))))
      _ -> fail "bvUpdOp: expected vector"

------------------------------------------------------------
-- Rotations and shifts

-- bvRotateL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateLOp :: SValue
bvRotateLOp =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \milv ->
    case (milv, xs) of
      (Nothing, xv) -> return xv
      (Just ilv, VVector xv) -> selectV (lazyMux muxBVal) (V.length xv -1) (return . VVector . vRotateL xv) ilv
      (Just ilv, VExtra (SWord xlv)) ->
        selectV (lazyMux muxBVal) (intSizeOf xlv - 1) (return . vWord . rotateL xlv) ilv
      _ -> error $ "rotateLOp: " ++ show xs

-- bvRotateR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateROp :: SValue
bvRotateROp =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \milv -> do
    case (milv, xs) of
      (Nothing, xv) -> return xv
      (Just ilv, VVector xv) -> selectV (lazyMux muxBVal) (V.length xv -1) (return . VVector . vRotateR xv) ilv
      (Just ilv, VExtra (SWord xlv)) -> return $ vWord (sbvRotateRight xlv ilv)
      _ -> error $ "rotateROp: " ++ show xs

-- bvShiftR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftLOp :: SValue
bvShiftLOp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \milv -> do
    case (milv, xs) of
      (Nothing, xv) -> return xv
      (Just ilv, VVector xv) -> selectV (lazyMux muxBVal) (V.length xv - 1) (return . VVector . vShiftL x xv) ilv
      (Just ilv, VExtra (SWord xlv)) -> return $ vWord (sbvShiftLeft xlv ilv)
      _ -> fail $ "bvShiftROp: " ++ show xs

-- bvShiftR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftROp :: SValue
bvShiftROp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \milv -> do
    case (milv, xs) of
      (Nothing, xv) -> return xv
      (Just ilv, VVector xv) -> selectV (lazyMux muxBVal) (V.length xv - 1) (return . VVector . vShiftR x xv) ilv
      (Just ilv, VExtra (SWord xlv)) -> return $ vWord (sbvShiftRight xlv ilv)
      _ -> fail $ "bvShiftROp: " ++ show xs

------------------------------------------------------------
-- Stream operations

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: SValue
mkStreamOp =
  constFun $
  strictFun $ \f -> do
    r <- newIORef Map.empty
    return $ VExtra (SStream (\n -> apply f (ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: SValue
streamGetOp =
  constFun $
  strictFun $ \xs -> return $
  Prims.natFun $ \n -> lookupSStream xs (toInteger n)

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: SValue
bvStreamGetOp =
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \(Just ilv) ->
  selectV (lazyMux muxBVal) ((2 ^ intSizeOf ilv) - 1) (lookupSStream xs) ilv

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
      _ -> fail "foldrOp"

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: SValue
vZipOp =
  constFun $
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  VVector (V.zipWith (\x y -> ready (VTuple (V.fromList [x, y]))) (toVector xs) (toVector ys))

-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: SValue
appendOp =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  strictFun $ \ys ->
  case (xs, ys) of
    (VVector xv, VVector yv) -> return $ VVector ((V.++) xv yv)
    (VExtra SZero, w) -> return w
    (v, VExtra SZero) -> return v
    (v, w) -> do
      (Just v') <- toWord v
      (Just w') <- toWord w
      return $ vWord $ cat v' w'


------------------------------------------------------------
-- Helpers for marshalling into SValues

binOp :: (SWord -> SWord -> SWord) -> SValue
binOp op = constFun $
          strictFun $ \mx-> return $
          strictFun $ \my->
            case (mx, my) of
               (VExtra SZero, VExtra SZero) -> return (VExtra SZero)
               _ -> do
                 (Just x) <- toWord mx
                 (Just y) <- toWord my
                 return $ vWord $ op x y

sbinOp :: (SWord -> SWord -> SWord) -> SValue
sbinOp f = binOp (\x y -> f (signCast x) y)

binRel :: (SWord -> SWord -> SBool) -> SValue
binRel op = constFun $
            strictFun $ \mx-> return $
            strictFun $ \my-> do
              (Just x) <- toWord mx
              (Just y) <- toWord my
              return $ vBool $ op x y

sbinRel :: (SWord -> SWord -> SBool) -> SValue
sbinRel f = binRel (\x y-> signCast x `f` signCast y)

boolBinOp :: (SBool -> SBool -> SBool) -> SValue
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> return $ vBool $ op (forceBool x) (forceBool y)

------------------------------------------------------------
-- Ite ops

iteOp :: SValue
iteOp =
    constFun $
    strictFun $ \b-> return $
    strictFun $ \x-> return $
    strictFun $ \y-> muxBVal (forceBool b) x y

muxBVal :: SBool -> SValue -> SValue -> IO SValue
muxBVal b (VFun f) (VFun g) = return $ VFun (\a -> do x <- f a; y <- g a; muxBVal b x y)
muxBVal b (VCtorApp i xv) (VCtorApp j yv) | i == j = VCtorApp i <$> muxThunks b xv yv
muxBVal b (VVector xv)    y               = VVector <$> muxThunks b xv (toVector y)
muxBVal b x               (VVector yv)    = VVector <$> muxThunks b (toVector x) yv
muxBVal _ (VNat m)        (VNat n)        | m == n = return $ VNat m
muxBVal _ (VString x)     (VString y)     | x == y = return $ VString x
muxBVal _ (VFloat x)      (VFloat y)      | x == y = return $ VFloat x
muxBVal _ (VDouble x)     (VDouble y)     | x == y = return $ VDouble y
muxBVal _ VType           VType           = return VType
muxBVal b (VExtra x)      (VExtra y)      = return $ VExtra $ extraFn b x y
muxBVal _ x y = fail $ "iteOp: malformed arguments (muxBVal): " ++ show x ++ " and " ++ show y

muxThunks :: SBool -> V.Vector SThunk -> V.Vector SThunk -> IO (V.Vector SThunk)
muxThunks b xv yv
  | V.length xv == V.length yv = V.zipWithM (muxThunk b) xv yv
  | otherwise                  = fail "iteOp: malformed arguments (muxThunks)"

muxThunk :: SBool -> SThunk -> SThunk -> IO SThunk
muxThunk b x y = delay $ do x' <- force x; y' <- force y; muxBVal b x' y'

extraFn :: SBool -> SbvExtra -> SbvExtra -> SbvExtra
extraFn b (SBool x) (SBool y) = SBool $ ite b x y
extraFn b (SWord x) (SWord y) = SWord $ ite b x y
extraFn _ _ _ = error "iteOp: malformed arguments (extraFn)"

------------------------------------------------------------
-- External interface

sbvSolveBasic :: Module -> SharedTerm s -> IO SValue
sbvSolveBasic m t = do
  cfg <- Sim.evalGlobal m constMap uninterpreted
  Sim.evalSharedTerm cfg t

kindFromType :: (Show t, Termlike t) => t -> Kind
kindFromType (R.asBoolType -> Just ()) = KBool
kindFromType (R.asBitvectorType -> Just n) = KBounded False (fromIntegral n)
kindFromType (R.asVecType -> Just (n R.:*: ety)) =
  case kindFromType ety of
    KBounded False m -> KBounded False (fromIntegral n * m)
    k -> error $ "Unsupported vector element kind: " ++ show k
kindFromType (R.asTupleType -> Just []) = KBounded False 0
kindFromType (R.asTupleType -> Just tys) =
  foldr1 combineKind (map kindFromType tys)
    where combineKind (KBounded False m) (KBounded False n) = KBounded False (m + n)
          combineKind k k' = error $ "Can't combine kinds " ++ show k ++ " and " ++ show k'
kindFromType ty = error $ "Unsupported type: " ++ show ty

parseUninterpreted :: (Show t, Termlike t) => [Kind] -> [SBV ()] -> t -> String -> IO SValue
parseUninterpreted ks cws (R.asBoolType -> Just ()) =
  return . vBool . mkUninterpreted (reverse (KBool : ks)) (reverse cws)
parseUninterpreted ks cws (R.asPi -> Just (_, _, t2)) =
  \s -> return $
  strictFun $ \x -> do
    m <- toSBV x
    case m of
      Nothing -> fail $ "Could not create sbv argument for " ++ show x
      Just l -> parseUninterpreted (map (\(SBV k _)-> k) l ++ ks) (l ++ cws) t2 s
parseUninterpreted ks cws ty =
  reconstitute ty . vWord . mkUninterpreted (reverse (kindFromType ty : ks)) (reverse cws)
    where reconstitute (R.asBitvectorType -> (Just _)) v = return v
          reconstitute (R.asVecType -> (Just (n R.:*: ety))) v = do
            let xs = toVector v
            vs <- (reverse . fst) <$> foldM parseTy ([], xs) (replicate (fromIntegral n) ety)
            return . VVector . V.fromList . map ready $ vs
          reconstitute (R.asTupleType -> (Just [])) v = return v
          reconstitute (R.asTupleType -> (Just tys)) v = do
            vs <- (reverse . fst) <$> foldM parseTy ([], toVector v) tys
            return . VTuple . V.fromList . map ready $ vs
          reconstitute t _ = fail $ "could not create uninterpreted type for " ++ show t
          parseTy (vs, bs) ty' =
            case typeSize ty' of
              Just n -> do
                let vbs = V.take n bs
                    bs' = V.drop n bs
                mw <- toWord (VVector vbs)
                case mw of
                  Just w -> do
                    v' <- reconstitute ty' (vWord w)
                    return (v' : vs, bs')
                  Nothing -> do vbs' <- traverse force vbs
                                fail $ "Can't convert to word: " ++ show vbs'
              Nothing -> fail $ "Could not calculate the size of type: " ++ show ty'

mkUninterpreted :: [Kind] -> [SBV ()] -> String -> SBV a
mkUninterpreted = error "FIXME: mkUninterpreted"
{- FIXME: export enough from SBV to make this implementable
mkUninterpreted ks args nm = SBV ka $ Right $ cache result where
  ka = last ks
  result st = do
    newUninterpreted st nm (SBVType ks) Nothing
    sws <- traverse (sbvToSW st) args
    mapM_ forceSWArg sws
    newExpr st ka $ SBVApp (Uninterpreted nm) sws
-}

typeSize :: (Termlike t) => t -> Maybe Int
typeSize t = sizeFiniteType <$> asFiniteTypePure t

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
  shapes <- traverse (asFiniteType sc) argTs
  bval <- sbvSolveBasic (scModule sc) t
  let (labels, vars) = flip evalState 0 $ unzip <$> traverse newVars shapes
  let prd = do
              bval' <- traverse (fmap ready) vars >>= (liftIO . applyAll bval)
              case bval' of
                VExtra (SBool b) -> return b
                _ -> fail "bitBlast: non-boolean result type."
  return (labels, prd)

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
myfun = fmap fst A.&&& fmap snd

newVars :: FiniteType -> State Int (Labeler, Symbolic SValue)
newVars FTBit = nextId <&> \s-> (BoolLabel s, vBool <$> exists s)
newVars (FTVec n FTBit) =
  if n == 0
    then nextId <&> \s-> (WordLabel s, return (VExtra SZero))
    else nextId <&> \s-> (WordLabel s, vWord <$> existsSWord s (fromIntegral n))
newVars (FTVec n tp) = do
  (labels, vals) <- V.unzip <$> V.replicateM (fromIntegral n) (newVars tp)
  return (VecLabel labels, VVector <$> traverse (fmap ready) vals)
newVars (FTTuple ts) = do
  (labels, vals) <- V.unzip <$> traverse newVars (V.fromList ts)
  return (TupleLabel labels, VTuple <$> traverse (fmap ready) vals)
newVars (FTRec tm) = do
  (labels, vals) <- myfun <$> (traverse newVars tm :: State Int (Map String (Labeler, Symbolic SValue)))
  return (RecLabel labels, VRecord <$> traverse (fmap ready) (vals :: (Map String (Symbolic SValue))))
