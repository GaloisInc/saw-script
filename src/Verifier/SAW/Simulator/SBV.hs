{-# LANGUAGE CPP #-}
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

{- |
Module      : Verifier.SAW.Simulator.SBV
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module Verifier.SAW.Simulator.SBV
  ( sbvSolve
  , SValue
  , Labeler(..)
  , sbvCodeGen_definition
  , sbvCodeGen
  , toWord
  , toBool
  , module Verifier.SAW.Simulator.SBV.SWord
  ) where

import Data.SBV.Dynamic

import Verifier.SAW.Simulator.SBV.SWord

import Control.Lens ((<&>))
import qualified Control.Arrow as A

import Data.Bits
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Traversable as T
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad.IO.Class
import Control.Monad.State as ST

import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.Simulator as Sim
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.TypedAST (FieldName, Module, identName)
import Verifier.SAW.FiniteValue (FirstOrderType(..), asFirstOrderType)

type SValue = Value IO SBool SWord SInteger SbvExtra
type SThunk = Thunk IO SBool SWord SInteger SbvExtra

data SbvExtra =
  SStream (Integer -> IO SValue) (IORef (Map Integer SValue))

instance Show SbvExtra where
  show (SStream _ _) = "<SStream>"

constMap :: Map Ident SValue
constMap = Map.fromList
  -- Boolean
  [ ("Prelude.True", VBool svTrue)
  , ("Prelude.False", VBool svFalse)
  , ("Prelude.not", strictFun (return . vBool . svNot . toBool))
  , ("Prelude.and", boolBinOp svAnd)
  , ("Prelude.or", boolBinOp svOr)
  , ("Prelude.xor", boolBinOp svXOr)
  , ("Prelude.boolEq", boolBinOp svEqual)
  , ("Prelude.ite", iteOp)
  -- Arithmetic
  , ("Prelude.bvNeg" , unOp svUNeg)
  , ("Prelude.bvAdd" , binOp svPlus)
  , ("Prelude.bvSub" , binOp svMinus)
  , ("Prelude.bvMul" , binOp svTimes)
  , ("Prelude.bvAnd" , binOp svAnd)
  , ("Prelude.bvOr"  , binOp svOr)
  , ("Prelude.bvXor" , binOp svXOr)
  , ("Prelude.bvNot" , unOp svNot)
  , ("Prelude.bvUDiv", binOp svQuot)
  , ("Prelude.bvURem", binOp svRem)
  , ("Prelude.bvSDiv", sbinOp svQuot)
  , ("Prelude.bvSRem", sbinOp svRem)
  , ("Prelude.bvPMul", bvPMulOp)
  , ("Prelude.bvPDiv", bvPDivOp)
  , ("Prelude.bvPMod", bvPModOp)
  , ("Prelude.bvLg2" , Prims.bvLg2Op toWord (return . sLg2))
  -- Relations
  , ("Prelude.bvEq"  , binRel svEqual)
  , ("Prelude.bvsle" , sbinRel svLessEq)
  , ("Prelude.bvslt" , sbinRel svLessThan)
  , ("Prelude.bvule" , binRel svLessEq)
  , ("Prelude.bvult" , binRel svLessThan)
  , ("Prelude.bvsge" , sbinRel svGreaterEq)
  , ("Prelude.bvsgt" , sbinRel svGreaterThan)
  , ("Prelude.bvuge" , binRel svGreaterEq)
  , ("Prelude.bvugt" , binRel svGreaterThan)
  -- Shifts
  , ("Prelude.bvShl" , bvShLOp)
  , ("Prelude.bvShr" , bvShROp)
  , ("Prelude.bvSShr", bvSShROp)
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
  , ("Prelude.equalNat", Prims.equalNat (return . svBool))
  , ("Prelude.ltNat", Prims.ltNat (return . svBool))
  -- Integers
  , ("Prelude.intAdd", Prims.intBinOp "intAdd" svPlus)
  , ("Prelude.intSub", Prims.intBinOp "intSub" svMinus)
  , ("Prelude.intMul", Prims.intBinOp "intMul" svTimes)
  , ("Prelude.intDiv", Prims.intBinOp "intDiv" svQuot)
  , ("Prelude.intMod", Prims.intBinOp "intMod" svRem)
  , ("Prelude.intNeg", Prims.intUnOp "intNeg" svUNeg)
  , ("Prelude.intEq" , Prims.intBinCmp "intEq" svEqual id)
  , ("Prelude.intLe" , Prims.intBinCmp "intLe" svLessEq id)
  , ("Prelude.intLt" , Prims.intBinCmp "intLt" svLessThan id)
  --XXX , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  --XXX , ("Prelude.intMin"  , Prims.intMinOp)
  --XXX , ("Prelude.intMax"  , Prims.intMaxOp)
  -- Vectors
  , ("Prelude.gen", Prims.genOp)
  , ("Prelude.atWithDefault", atWithDefaultOp)
  , ("Prelude.upd", Prims.updOp svUnpack (\x y -> return (svEqual x y)) literalSWord intSizeOf (lazyMux muxBVal))
  , ("Prelude.take", takeOp)
  , ("Prelude.drop", dropOp)
  , ("Prelude.append", Prims.appendOp svUnpack svJoin)
  , ("Prelude.join", Prims.joinOp svUnpack svJoin)
  , ("Prelude.split", splitOp)
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
  , ("Prelude.bvToNat", Prims.bvToNatOp)
  , ("Prelude.error", Prims.errorOp)
  -- Overloaded
  , ("Prelude.eq", eqOp)
  ]

------------------------------------------------------------
-- Coercion functions
--

bitVector :: Int -> Integer -> SWord
bitVector w i = literalSWord w i

symFromBits :: Vector SBool -> SWord
symFromBits v = V.foldl svJoin (bitVector 0 0) (V.map svToWord1 v)

toMaybeBool :: SValue -> Maybe SBool
toMaybeBool (VBool b) = Just b
toMaybeBool _  = Nothing

toBool :: SValue -> SBool
toBool (VBool b) = b
toBool sv = error $ unwords ["toBool failed:", show sv]

toWord :: SValue -> IO SWord
toWord (VWord w) = return w
toWord (VVector vv) = symFromBits <$> traverse (fmap toBool . force) vv
toWord x = fail $ unwords ["Verifier.SAW.Simulator.SBV.toWord", show x]

fromVInt :: SValue -> SInteger
fromVInt (VInt i) = i
fromVInt sv = error $ unwords ["fromVInt failed:", show sv]

toMaybeWord :: SValue -> IO (Maybe SWord)
toMaybeWord (VWord w) = return (Just w)
toMaybeWord (VVector vv) = ((symFromBits <$>) . T.sequence) <$> traverse (fmap toMaybeBool . force) vv
toMaybeWord _ = return Nothing

toVector :: SValue -> Vector SThunk
toVector (VVector xv) = xv
toVector (VWord xv) =
  V.fromList (map (ready . vBool . svTestBit xv) (enumFromThenTo (k-1) (k-2) 0))
  where k = intSizeOf xv
toVector _ = error "Verifier.SAW.Simulator.SBV.toVector"

-- | Flatten an SValue to a sequence of components, each of which is
-- either a symbolic word or a symbolic boolean. If the SValue
-- contains any values built from data constructors, then return them
-- encoded as a String.
flattenSValue :: SValue -> IO ([SVal], String)
flattenSValue v = do
  mw <- toMaybeWord v
  case mw of
    Just w -> return ([w], "")
    Nothing ->
      case v of
        VUnit                     -> return ([], "")
        VPair x y                 -> do (xs, sx) <- flattenSValue =<< force x
                                        (ys, sy) <- flattenSValue =<< force y
                                        return (xs ++ ys, sx ++ sy)
        VEmpty                    -> return ([], "")
        VField _ x y              -> do (xs, sx) <- flattenSValue =<< force x
                                        (ys, sy) <- flattenSValue y
                                        return (xs ++ ys, sx ++ sy)
        VVector (V.toList -> ts)  -> do (xss, ss) <- unzip <$> traverse (force >=> flattenSValue) ts
                                        return (concat xss, concat ss)
        VBool sb                  -> return ([sb], "")
        VWord sw                  -> return (if intSizeOf sw > 0 then [sw] else [], "")
        VCtorApp i (V.toList->ts) -> do (xss, ss) <- unzip <$> traverse (force >=> flattenSValue) ts
                                        return (concat xss, "_" ++ identName i ++ concat ss)
        VNat n                    -> return ([], "_" ++ show n)
        _ -> fail $ "Could not create sbv argument for " ++ show v

vWord :: SWord -> SValue
vWord lv = VWord lv

vBool :: SBool -> SValue
vBool l = VBool l

vInteger :: SInteger -> SValue
vInteger x = VInt x

------------------------------------------------------------
-- Function constructors

wordFun :: (SWord -> IO SValue) -> SValue
wordFun f = strictFun (\x -> toWord x >>= f)

------------------------------------------------------------
-- Indexing operations

-- | Lifts a strict mux operation to a lazy mux
lazyMux :: (SBool -> a -> a -> IO a) -> (SBool -> IO a -> IO a -> IO a)
lazyMux muxFn c tm fm =
  case svAsBool c of
    Just True  -> tm
    Just False -> fm
    Nothing    -> do
      t <- tm
      f <- fm
      muxFn c t f

-- selectV merger maxValue valueFn index returns valueFn v when index has value v
-- if index is greater than maxValue, it returns valueFn maxValue. Use the ite op from merger.
selectV :: (Ord a, Num a, Bits a) => (SBool -> b -> b -> b) -> a -> (a -> b) -> SWord -> b
selectV merger maxValue valueFn vx =
  case svAsInteger vx of
    Just i  -> valueFn (fromIntegral i)
    Nothing -> impl (intSizeOf vx) 0
  where
    impl _ y | y >= maxValue = valueFn maxValue
    impl 0 y = valueFn y
    impl i y = merger (svTestBit vx j) (impl j (y `setBit` j)) (impl j y) where j = i - 1

-- | Barrel-shifter algorithm. Takes a list of bits in big-endian order.
shifter :: (SBool -> a -> a -> IO a) -> (a -> Integer -> a) -> a -> [SBool] -> IO a
shifter mux op = go
  where
    go x [] = return x
    go x (b : bs) = do
      x' <- mux b (op x (2 ^ length bs)) x
      go x' bs

-- Big-endian version of svTestBit
svAt :: SWord -> Int -> SBool
svAt x i = svTestBit x (intSizeOf x - 1 - i)

svUnpack :: SWord -> Vector SBool
svUnpack x = V.generate (intSizeOf x) (svAt x)

-- atWithDefault :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> a;
atWithDefaultOp :: SValue
atWithDefaultOp =
  Prims.natFun $ \n -> return $
  constFun $
  VFun $ \d -> return $
  strictFun $ \x -> return $
  strictFun $ \index ->
    case index of
      VNat i ->
        case x of
          VVector xv -> force (Prims.vecIdx d xv (fromIntegral i))
          VWord xw -> return $ VBool $ svAt xw (fromIntegral i)
          _ -> fail "atOp: expected vector"
      VToNat i -> do
        case x of
          VVector xv ->
            case i of
              VWord iw -> do
                selectV (lazyMux muxBVal) (fromIntegral n - 1) (force . Prims.vecIdx d xv) iw
              _ -> do
                iv <- Prims.toBits svUnpack i
                Prims.selectV (lazyMux muxBVal) (fromIntegral n - 1) (force . Prims.vecIdx d xv) iv
{-
            case i of
              VWord iw -> do
                xs <- T.mapM force $ V.toList xv
                case asWordList xs of
                  Just (w:ws) -> return $ VWord $ svSelect (w:ws) w iw
                  _ -> do
                    selectV (lazyMux muxBVal) (fromIntegral n - 1) (force . Prims.vecIdx d xv) iw
              _ -> do
                iv <- Prims.toBits svUnpack i
                Prims.selectV (lazyMux muxBVal) (fromIntegral n - 1) (force . Prims.vecIdx d xv) iv
-}
          VWord xw -> do
            case i of
              VWord iw ->
                selectV (lazyMux muxBVal) (fromIntegral n - 1) (return . VBool . svAt xw) iw
              _ -> do
                iv <- Prims.toBits svUnpack i
                Prims.selectV (lazyMux muxBVal) (fromIntegral n - 1) (return . VBool . svAt xw) iv
          _ -> fail "atOp: expected vector"
      _ -> fail $ "atOp: expected Nat, got " ++ show index

asWordList :: [SValue] -> Maybe [SWord]
asWordList = go id
 where
  go f [] = Just (f [])
  go f (VWord x : xs) = go (f . (x:)) xs
  go _ _ = Nothing

-- take :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec m a;
takeOp :: SValue
takeOp =
  constFun $
  Prims.natFun $ \(fromIntegral -> m) -> return $
  Prims.natFun $ \(fromIntegral -> n) -> return $
  strictFun $ \v -> return $
    case v of
      VVector vv -> VVector (V.take m vv)
      VWord vw -> VWord (svExtract (m + n - 1) n vw)
      _ -> error $ "takeOp: " ++ show v

-- drop :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec n a;
dropOp :: SValue
dropOp =
  constFun $
  Prims.natFun $ \(fromIntegral -> m) -> return $
  Prims.natFun $ \(fromIntegral -> n) -> return $
  strictFun $ \v -> return $
    case v of
      VVector vv -> VVector (V.drop m vv)
      VWord vw -> VWord (svExtract (n - 1) 0 vw)
      _ -> error $ "dropOp: " ++ show v

-- split :: (m n :: Nat) -> (a :: sort 0) -> Vec (mulNat m n) a -> Vec m (Vec n a);
splitOp :: SValue
splitOp =
  Prims.natFun $ \(fromIntegral -> m) -> return $
  Prims.natFun $ \(fromIntegral -> n) -> return $
  constFun $
  strictFun $ \x -> return $
  case x of
    VVector xv ->
      let f i = ready (VVector (V.slice (i*n) n xv))
      in VVector (V.generate m f)
    VWord xw ->
      let f i = ready (VWord (svExtract ((m-i)*n-1) ((m-i-1)*n) xw))
      in VVector (V.generate m f)
    _ -> error "Verifier.SAW.Simulator.SBV.splitOp"

----------------------------------------
-- Shift operations

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
bvShiftOp :: (SWord -> SWord -> SWord) -> (SWord -> Int -> SWord) -> SValue
bvShiftOp bvOp natOp =
  constFun $
  wordFun $ \x -> return $
  strictFun $ \y ->
    case y of
      VNat i   -> return (vWord (natOp x j))
        where j = fromInteger (i `min` toInteger (intSizeOf x))
      VToNat v -> fmap (vWord . bvOp x) (toWord v)
      _        -> error $ unwords ["Verifier.SAW.Simulator.SBV.bvShiftOp", show y]

-- bvShl :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShLOp :: SValue
bvShLOp = bvShiftOp svShiftLeft svShl

-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShROp :: SValue
bvShROp = bvShiftOp svShiftRight svShr

-- bvSShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvSShROp :: SValue
bvSShROp = bvShiftOp bvOp natOp
  where
    bvOp w x = svUnsign (svShiftRight (svSign w) x)
    natOp w i = svUnsign (svShr (svSign w) i)

eqOp :: SValue
eqOp = Prims.eqOp trueOp andOp boolEqOp bvEqOp intEqOp
  where trueOp       = VBool svTrue
        andOp    x y = return $ vBool (svAnd (toBool x) (toBool y))
        boolEqOp x y = return $ vBool (svEqual (toBool x) (toBool y))
        intEqOp  x y = return $ vBool (svEqual (fromVInt x) (fromVInt y))
        bvEqOp _ x y = do x' <- toWord x
                          y' <- toWord y
                          return $ vBool (svEqual x' y')

-----------------------------------------
-- Integer/bitvector conversions

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: SValue
natToIntOp =
  Prims.natFun' "natToInt" $ \n -> return $
    VInt (literalSInteger (toInteger n))

-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
bvToIntOp :: SValue
bvToIntOp = constFun $ wordFun $ \v ->
   case svAsInteger v of
      Just i -> return $ VInt (literalSInteger i)
      Nothing -> fail "Cannot convert symbolic bitvector to integer"

-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
sbvToIntOp :: SValue
sbvToIntOp = constFun $ wordFun $ \v ->
   case svAsInteger (svSign v) of
      Just i -> return $ VInt (literalSInteger i)
      Nothing -> fail "Cannot convert symbolic bitvector to integer"

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
intToBvOp :: SValue
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x ->
    case svAsInteger x of
      Just i -> return $ VWord $ literalSWord (fromIntegral n) i
      Nothing -> fail "intToBv: Cannot convert symbolic integer to bitvector"

----------------------------------------
-- Polynomial operations

-- bvPMod :: (m n :: Nat) -> bitvector m -> bitvector (Succ n) -> bitvector n;
bvPModOp :: SValue
bvPModOp =
  constFun $
  constFun $
  wordFun $ \x -> return $
  wordFun $ \y -> do
      let j  = intSizeOf y
          xs = svBlastLE x
          ys = svBlastLE y
          zs = take (j-1) $ snd (mdp xs ys) ++ repeat svFalse
       in return $ vWord $ svWordFromLE zs

-- primitive bvPDiv :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector m;
bvPDivOp :: SValue
bvPDivOp =
  constFun $
  constFun $
  wordFun $ \x -> return $
  wordFun $ \y -> do
      let i  = intSizeOf x
          xs = svBlastLE x
          ys = svBlastLE y
          zs = take i $ fst (mdp xs ys) ++ repeat svFalse
       in return $ vWord $ svWordFromLE $ zs

-- bvPMul :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector (subNat (maxNat 1 (addNat m n)) 1);
bvPMulOp :: SValue
bvPMulOp =
  constFun $
  constFun $
  wordFun $ \x -> return $
  wordFun $ \y -> do
      let i = intSizeOf x
          j = intSizeOf y
          k = max 1 (i + j) - 1
          mul _  []     ps = ps
          mul as (b:bs) ps = mul (svFalse : as) bs (ites b (as `addPoly` ps) ps)
          xs = svBlastLE x
          ys = svBlastLE y
          zs = take k (mul xs ys [] ++ repeat svFalse)
       in return $ vWord $ svWordFromLE $ zs

-- | Add two polynomials
addPoly :: [SBool] -> [SBool] -> [SBool]
addPoly xs    []      = xs
addPoly []    ys      = ys
addPoly (x:xs) (y:ys) = svXOr x y : addPoly xs ys

ites :: SBool -> [SBool] -> [SBool] -> [SBool]
ites s xs ys
 | Just t <- svAsBool s
 = if t then xs else ys
 | True
 = go xs ys
 where go [] []         = []
       go []     (b:bs) = svIte s svFalse b : go [] bs
       go (a:as) []     = svIte s a svFalse : go as []
       go (a:as) (b:bs) = svIte s a b : go as bs

-- conservative over-approximation of the degree
degree :: [SBool] -> Int
degree xs = walk (length xs - 1) $ reverse xs
  where walk n []     = n
        walk n (b:bs)
         | Just t <- svAsBool b
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
               ys' = replicate degQuot svFalse ++ ys
               (qs, rs) = divx (degQuot+1) degTop xs ys'

-- return the element at index i; if not enough elements, return false
-- N.B. equivalent to '(xs ++ repeat false) !! i', but more efficient
idx :: [SBool] -> Int -> SBool
idx []     _ = svFalse
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

vRotateL :: Vector a -> Integer -> Vector a
vRotateL xs i
  | V.null xs = xs
  | otherwise = (V.++) (V.drop j xs) (V.take j xs)
  where j = fromInteger (i `mod` toInteger (V.length xs))

vRotateR :: Vector a -> Integer -> Vector a
vRotateR xs i = vRotateL xs (- i)

vShiftL :: a -> Vector a -> Integer -> Vector a
vShiftL x xs i = (V.++) (V.drop j xs) (V.replicate j x)
  where j = fromInteger (i `min` toInteger (V.length xs))

vShiftR :: a -> Vector a -> Integer -> Vector a
vShiftR x xs i = (V.++) (V.replicate j x) (V.take (V.length xs - j) xs)
  where j = fromInteger (i `min` toInteger (V.length xs))

------------------------------------------------------------
-- Rotations and shifts

-- rotate{L,R} :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateOp :: (Vector SThunk -> Integer -> Vector SThunk)
         -> (SWord -> Integer -> SWord)
         -> (SWord -> SWord -> SWord)
         -> SValue
rotateOp vecOp wordOp svOp =
  constFun $
  constFun $
  strictFun $ \xs -> return $
  strictFun $ \y ->
    case y of
      VNat i -> return $
        case xs of
          VVector xv -> VVector (vecOp xv i)
          VWord xw -> vWord (wordOp xw (fromInteger (i `mod` toInteger (intSizeOf xw))))
          _ -> error $ "rotateOp: " ++ show xs
      VToNat (VVector iv) -> do
        bs <- V.toList <$> traverse (fmap toBool . force) iv
        case xs of
          VVector xv -> VVector <$> shifter muxVector vecOp xv bs
          VWord xw -> vWord <$> shifter muxWord wordOp xw bs
          _ -> error $ "rotateOp: " ++ show xs
      VToNat (VWord iw) -> do
        case xs of
          VVector xv -> do
            let bs = V.toList (svUnpack iw)
            VVector <$> shifter muxVector vecOp xv bs
          VWord xw -> return $ vWord (svOp xw iw)
          _ -> error $ "rotateOp: " ++ show xs
      _ -> error $ "rotateOp: " ++ show y

-- rotateL :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateLOp :: SValue
rotateLOp = rotateOp vRotateL rol svRotateLeft
  where rol x i = svRol x (fromInteger (i `mod` toInteger (intSizeOf x)))

-- rotateR :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateROp :: SValue
rotateROp = rotateOp vRotateR ror svRotateRight
  where ror x i = svRol x (fromInteger (i `mod` toInteger (intSizeOf x)))

-- shift{L,R} :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftOp :: (SThunk -> Vector SThunk -> Integer -> Vector SThunk)
        -> (SBool -> SWord -> Integer -> SWord)
        -> (SBool -> SWord -> SWord -> SWord)
        -> SValue
shiftOp vecOp wordOp svOp =
  constFun $
  constFun $
  VFun $ \z -> return $
  strictFun $ \xs -> return $
  strictFun $ \y ->
    case y of
      VNat i ->
        case xs of
          VVector xv -> return $ VVector (vecOp z xv i)
          VWord xw -> do
            zv <- toBool <$> force z
            let i' = fromInteger (i `min` toInteger (intSizeOf xw))
            return $ vWord (wordOp zv xw i')
          _ -> error $ "shiftOp: " ++ show xs
      VToNat (VVector iv) -> do
        bs <- V.toList <$> traverse (fmap toBool . force) iv
        case xs of
          VVector xv -> VVector <$> shifter muxVector (vecOp z) xv bs
          VWord xw -> do
            zv <- toBool <$> force z
            vWord <$> shifter muxWord (wordOp zv) xw bs
          _ -> error $ "shiftOp: " ++ show xs
      VToNat (VWord iw) ->
        case xs of
          VVector xv -> do
            let bs = V.toList (svUnpack iw)
            VVector <$> shifter muxVector (vecOp z) xv bs
          VWord xw -> do
            zv <- toBool <$> force z
            return $ vWord (svOp zv xw iw)
          _ -> error $ "shiftOp: " ++ show xs
      _ -> error $ "shiftOp: " ++ show y

-- shiftL :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
shiftLOp :: SValue
shiftLOp = shiftOp vShiftL undefined shl
  where shl b x i = svIte b (svNot (svShiftLeft (svNot x) i)) (svShiftLeft x i)

-- shiftR :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
shiftROp :: SValue
shiftROp = shiftOp vShiftR undefined shr
  where shr b x i = svIte b (svNot (svShiftRight (svNot x) i)) (svShiftRight x i)

muxWord :: SBool -> SWord -> SWord -> IO SWord
muxWord b w1 w2 = return (svIte b w1 w2)

muxVector :: SBool -> Vector SThunk -> Vector SThunk -> IO (Vector SThunk)
muxVector b v1 v2 = toVector <$> muxBVal b (VVector v1) (VVector v2)

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
  Prims.natFun'' "streamGetOp" $ \n -> lookupSStream xs (toInteger n)

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: SValue
bvStreamGetOp =
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \ilv ->
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
  Prims.natFun'' "bvNatOp(1)" $ \w -> return $
  Prims.natFun'' "bvNatOp(2)" $ \x -> return $
  vWord (bitVector (fromIntegral w) (toInteger x))

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
  VVector (V.zipWith (\x y -> ready (vTuple [x, y])) (toVector xs) (toVector ys))

-- | Ceiling (log_2 x)
sLg2 :: SWord -> SWord
sLg2 x = go 0
  where
    lit n = literalSWord (intSizeOf x) n
    go i | i < intSizeOf x = svIte (svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise       = lit (toInteger i)

------------------------------------------------------------
-- Helpers for marshalling into SValues

unOp :: (SWord -> SWord) -> SValue
unOp op = constFun $
          strictFun $ \mx -> do
            x <- toWord mx
            return $ vWord $ op x

binOp :: (SWord -> SWord -> SWord) -> SValue
binOp op = constFun $
          strictFun $ \mx -> return $
          strictFun $ \my -> do
            x <- toWord mx
            y <- toWord my
            return $ vWord $ op x y

sbinOp :: (SWord -> SWord -> SWord) -> SValue
sbinOp f = binOp (\x y -> svUnsign (f (svSign x) (svSign y)))

binRel :: (SWord -> SWord -> SBool) -> SValue
binRel op = constFun $
            strictFun $ \mx-> return $
            strictFun $ \my-> do
              x <- toWord mx
              y <- toWord my
              return $ vBool $ op x y

sbinRel :: (SWord -> SWord -> SBool) -> SValue
sbinRel f = binRel (\x y -> svSign x `f` svSign y)

boolBinOp :: (SBool -> SBool -> SBool) -> SValue
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> return $ vBool $ op (toBool x) (toBool y)

------------------------------------------------------------
-- Ite ops

iteOp :: SValue
iteOp =
    constFun $
    strictFun $ \b -> return $
    VFun $ \x -> return $
    VFun $ \y ->
      lazyMux muxBVal (toBool b) (force x) (force y)

muxBVal :: SBool -> SValue -> SValue -> IO SValue
muxBVal = Prims.muxValue svUnpack bool word extra
  where
    bool b x y = return (svIte b x y)
    word b x y = return (svIte b x y)
    extra b x y = return (extraFn b x y)

extraFn :: SBool -> SbvExtra -> SbvExtra -> SbvExtra
extraFn _ _ _ = error "iteOp: malformed arguments (extraFn)"

------------------------------------------------------------
-- External interface

-- | Abstract constants with names in the list 'unints' are kept as
-- uninterpreted constants; all others are unfolded.
sbvSolveBasic :: Module -> Map Ident SValue -> [String] -> Term -> IO SValue
sbvSolveBasic m addlPrims unints t = do
  let unintSet = Set.fromList unints
  let uninterpreted nm ty
        | Set.member nm unintSet = Just $ parseUninterpreted [] nm ty
        | otherwise              = Nothing
  cfg <- Sim.evalGlobal m (Map.union constMap addlPrims)
         (const (parseUninterpreted []))
         uninterpreted
  Sim.evalSharedTerm cfg t

-- | SBV Kind corresponding to the result of concatenating all the
-- bitvector components of the given type value.
kindFromType :: SValue -> Kind
kindFromType (VDataType "Prelude.Bool" []) = KBool
kindFromType (VDataType "Prelude.Vec" [VNat n, VDataType "Prelude.Bool" []]) =
  KBounded False (fromIntegral n)
kindFromType (VDataType "Prelude.Vec" [VNat n, ety]) =
  case kindFromType ety of
    KBounded False m -> KBounded False (fromIntegral n * m)
    k -> error $ "Unsupported vector element kind: " ++ show k
kindFromType VUnitType = KBounded False 0
kindFromType (VPairType ty1 ty2) = combineKind (kindFromType ty1) (kindFromType ty2)
kindFromType VEmptyType = KBounded False 0
kindFromType (VFieldType _ ty1 ty2) = combineKind (kindFromType ty1) (kindFromType ty2)
kindFromType ty = error $ "Unsupported type: " ++ show ty

combineKind :: Kind -> Kind -> Kind
combineKind (KBounded False m) (KBounded False n) = KBounded False (m + n)
combineKind k k' = error $ "Can't combine kinds " ++ show k ++ " and " ++ show k'

parseUninterpreted :: [SVal] -> String -> SValue -> IO SValue
parseUninterpreted cws nm (VDataType "Prelude.Bool" []) =
  return $ vBool $ mkUninterpreted KBool cws nm

parseUninterpreted cws nm (VPiType _ f) =
  return $
  strictFun $ \x -> do
    (cws', suffix) <- flattenSValue x
    t2 <- f (ready x)
    parseUninterpreted (cws ++ cws') (nm ++ suffix) t2

parseUninterpreted cws nm ty =
  ST.evalStateT (parseTy ty) (mkUninterpreted (kindFromType ty) cws nm)
  where
    parseTy :: SValue -> ST.StateT SWord IO SValue
    parseTy (VDataType "Prelude.Vec" [VNat n, VDataType "Prelude.Bool" []]) = do
      v <- ST.get
      let w = intSizeOf v
      let v1 = svExtract (w - 1) (w - fromInteger n) v
      let v2 = svExtract (w - fromInteger n - 1) 0 v
      ST.put v2
      return (vWord v1)
    parseTy (VDataType "Prelude.Vec" [VNat n, ety]) = do
      xs <- traverse parseTy (replicate (fromIntegral n) ety)
      return (VVector (V.fromList (map ready xs)))
    parseTy VUnitType = return VUnit
    parseTy (VPairType ty1 ty2) = do
      x1 <- parseTy ty1
      x2 <- parseTy ty2
      return (VPair (ready x1) (ready x2))
    parseTy VEmptyType = return VEmpty
    parseTy (VFieldType f ty1 ty2) = do
      x1 <- parseTy ty1
      x2 <- parseTy ty2
      return (VField f (ready x1) x2)
    parseTy t = fail $ "could not create uninterpreted type for " ++ show t

mkUninterpreted :: Kind -> [SVal] -> String -> SVal
mkUninterpreted k args nm = svUninterpreted k nm' Nothing args
  where nm' = "|" ++ nm ++ "|" -- enclose name to allow primes and other non-alphanum chars

asPredType :: SharedContext -> Term -> IO [Term]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "non-boolean result type: " ++ show t'

sbvSolve :: SharedContext
         -> Map Ident SValue
         -> [String]
         -> Term
         -> IO ([Labeler], Symbolic SBool)
sbvSolve sc addlPrims unints t = do
  ty <- scTypeOf sc t
  argTs <- asPredType sc ty
  shapes <- traverse (asFirstOrderType sc) argTs
  bval <- sbvSolveBasic (scModule sc) addlPrims unints t
  (labels, vars) <- flip evalStateT 0 $ unzip <$> traverse newVars shapes
  let prd = do
              bval' <- traverse (fmap ready) vars >>= (liftIO . applyAll bval)
              case bval' of
                VBool b -> return b
                _ -> fail $ "sbvSolve: non-boolean result type. " ++ show bval'
  return (labels, prd)

data Labeler
   = BoolLabel String
   | IntegerLabel String
   | WordLabel String
   | VecLabel (Vector Labeler)
   | TupleLabel (Vector Labeler)
   | RecLabel (Map FieldName Labeler)
     deriving (Show)

nextId :: StateT Int IO String
nextId = ST.get >>= (\s-> modify (+1) >> return ("x" ++ show s))

--unzipMap :: Map k (a, b) -> (Map k a, Map k b)
--unzipMap m = (fmap fst m, fmap snd m)

myfun ::(Map String (Labeler, Symbolic SValue)) -> (Map String Labeler, Map String (Symbolic SValue))
myfun = fmap fst A.&&& fmap snd

newVars :: FirstOrderType -> StateT Int IO (Labeler, Symbolic SValue)
newVars FOTBit = nextId <&> \s-> (BoolLabel s, vBool <$> existsSBool s)
newVars FOTInt = nextId <&> \s-> (IntegerLabel s, vInteger <$> existsSInteger s)
newVars (FOTVec n FOTBit) =
  if n == 0
    then nextId <&> \s-> (WordLabel s, return (vWord (literalSWord 0 0)))
    else nextId <&> \s-> (WordLabel s, vWord <$> existsSWord s (fromIntegral n))
newVars (FOTVec n tp) = do
  (labels, vals) <- V.unzip <$> V.replicateM (fromIntegral n) (newVars tp)
  return (VecLabel labels, VVector <$> traverse (fmap ready) vals)
newVars (FOTTuple ts) = do
  (labels, vals) <- V.unzip <$> traverse newVars (V.fromList ts)
  return (TupleLabel labels, vTuple <$> traverse (fmap ready) (V.toList vals))
newVars (FOTRec tm) = do
  (labels, vals) <- myfun <$> (traverse newVars tm :: StateT Int IO (Map String (Labeler, Symbolic SValue)))
  return (RecLabel labels, vRecord <$> traverse (fmap ready) (vals :: (Map String (Symbolic SValue))))

------------------------------------------------------------
-- Code Generation

newCodeGenVars :: (Nat -> Bool) -> FirstOrderType -> StateT Int IO (SBVCodeGen SValue)
newCodeGenVars _checkSz FOTBit = nextId <&> \s -> (vBool <$> svCgInput KBool s)
newCodeGenVars _checkSz FOTInt = nextId <&> \s -> (vInteger <$> svCgInput KUnbounded s)
newCodeGenVars checkSz (FOTVec n FOTBit)
  | n == 0    = nextId <&> \_ -> return (vWord (literalSWord 0 0))
  | checkSz n = nextId <&> \s -> vWord <$> cgInputSWord s (fromIntegral n)
  | otherwise = nextId <&> \s -> fail $ "Invalid codegen bit width for input variable \'" ++ s ++ "\': " ++ show n
newCodeGenVars checkSz (FOTVec n (FOTVec m FOTBit))
  | m == 0    = nextId <&> \_ -> return (VVector $ V.fromList $ replicate (fromIntegral n) (ready $ vWord (literalSWord 0 0)))
  | checkSz m = do
      let k = KBounded False (fromIntegral m)
      vals <- nextId <&> \s -> svCgInputArr k (fromIntegral n) s
      return (VVector . V.fromList . fmap (ready . vWord) <$> vals)
  | otherwise = nextId <&> \s -> fail $ "Invalid codegen bit width for input variable array \'" ++ s ++ "\': " ++ show n
newCodeGenVars checkSz (FOTVec n tp) = do
  vals <- V.replicateM (fromIntegral n) (newCodeGenVars checkSz tp)
  return (VVector <$> traverse (fmap ready) vals)
newCodeGenVars checkSz (FOTTuple ts) = do
  vals <- traverse (newCodeGenVars checkSz) ts
  return (vTuple <$> traverse (fmap ready) vals)
newCodeGenVars checkSz (FOTRec tm) = do
  vals <- traverse (newCodeGenVars checkSz) tm
  return (vRecord <$> traverse (fmap ready) vals)

cgInputSWord :: String -> Int -> SBVCodeGen SWord
cgInputSWord s n = svCgInput (KBounded False n) s

argTypes :: SharedContext -> Term -> IO ([Term], Term)
argTypes sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> do
       (ts,res) <- argTypes sc t2
       return (t1:ts, res)
    _ -> return ([], t')

sbvCodeGen_definition
  :: SharedContext
  -> Map Ident SValue
  -> [String]
  -> Term
  -> (Nat -> Bool) -- ^ Allowed word sizes
  -> IO (SBVCodeGen (), [FirstOrderType], FirstOrderType)
sbvCodeGen_definition sc addlPrims unints t checkSz = do
  ty <- scTypeOf sc t
  (argTs,resTy) <- argTypes sc ty
  shapes <- traverse (asFirstOrderType sc) argTs
  resultShape <- asFirstOrderType sc resTy
  bval <- sbvSolveBasic (scModule sc) addlPrims unints t
  vars <- evalStateT (traverse (newCodeGenVars checkSz) shapes) 0
  let codegen = do
        args <- traverse (fmap ready) vars
        bval' <- liftIO (applyAll bval args)
        sbvSetResult checkSz resultShape bval'
  return (codegen, shapes, resultShape)


sbvSetResult :: (Nat -> Bool)
             -> FirstOrderType
             -> SValue
             -> SBVCodeGen ()
sbvSetResult _checkSz FOTBit (VBool b) = do
   svCgReturn b
sbvSetResult checkSz (FOTVec n FOTBit) v
   | n == 0    = return ()
   | checkSz n = do
      w <- liftIO $ toWord v
      svCgReturn w
   | otherwise =
      fail $ "Invalid word size in result: " ++ show n
sbvSetResult checkSz ft v = do
   void $ sbvSetOutput checkSz ft v 0


sbvSetOutput :: (Nat -> Bool)
             -> FirstOrderType
             -> SValue
             -> Int
             -> SBVCodeGen Int
sbvSetOutput _checkSz FOTBit (VBool b) i = do
   svCgOutput ("out_"++show i) b
   return $! i+1
sbvSetOutput checkSz (FOTVec n FOTBit) v i
   | n == 0    = return i
   | checkSz n = do
       w <- liftIO $ toWord v
       svCgOutput ("out_"++show i) w
       return $! i+1
   | otherwise =
       fail $ "Invalid word size in output " ++ show i ++ ": " ++ show n

sbvSetOutput checkSz (FOTVec n t) (VVector xv) i = do
   xs <- liftIO $ traverse force $ V.toList xv
   unless (toInteger n == toInteger (length xs)) $
     fail "sbvCodeGen: vector length mismatch when setting output values"
   case asWordList xs of
     Just ws -> do svCgOutputArr ("out_"++show i) ws
                   return $! i+1
     Nothing -> foldM (\i' x -> sbvSetOutput checkSz t x i') i xs
sbvSetOutput _checkSz (FOTTuple []) VUnit i =
   return i
sbvSetOutput checkSz (FOTTuple (t:ts)) (VPair l r) i = do
   l' <- liftIO $ force l
   r' <- liftIO $ force r
   sbvSetOutput checkSz t l' i >>= sbvSetOutput checkSz (FOTTuple ts) r'

sbvSetOutput _checkSz (FOTRec fs) VUnit i | Map.null fs = do
   return i
sbvSetOutput checkSz (FOTRec fs) (VField fn x rec) i = do
   x' <- liftIO $ force x
   case Map.lookup fn fs of
     Just t -> do
       let fs' = Map.delete fn fs
       sbvSetOutput checkSz t x' i >>= sbvSetOutput checkSz (FOTRec fs') rec
     Nothing -> fail "sbvCodeGen: type mismatch when setting record output value"
sbvSetOutput _checkSz _ft _v _i = do
   fail "sbvCode gen: type mismatch when setting output values"


sbvCodeGen :: SharedContext
           -> Map Ident SValue
           -> [String]
           -> Maybe FilePath
           -> String
           -> Term
           -> IO ()
sbvCodeGen sc addlPrims unints path fname t = do
  -- The SBV C code generator expects only these word sizes
  let checkSz n = n `elem` [8,16,32,64]

  (codegen,_,_) <- sbvCodeGen_definition sc addlPrims unints t checkSz
  compileToC path fname codegen
