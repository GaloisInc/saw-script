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
import Verifier.SAW.FiniteValue (FiniteType(..), asFiniteType)

type SValue = Value IO SBool SWord SbvExtra
type SThunk = Thunk IO SBool SWord SbvExtra

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
  , ("Prelude.intAdd", Prims.intAddOp)
  , ("Prelude.intSub", Prims.intSubOp)
  , ("Prelude.intMul", Prims.intMulOp)
  , ("Prelude.intDiv", Prims.intDivOp)
  , ("Prelude.intMod", Prims.intModOp)
  , ("Prelude.intNeg", Prims.intNegOp)
  , ("Prelude.intEq" , Prims.intEqOp svBool)
  , ("Prelude.intLe" , Prims.intLeOp svBool)
  , ("Prelude.intLt" , Prims.intLtOp svBool)
  , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", Prims.natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  , ("Prelude.intMin"  , Prims.intMinOp)
  , ("Prelude.intMax"  , Prims.intMaxOp)
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
  , ("Prelude.bvRotateL", bvRotateLOp)
  , ("Prelude.bvRotateR", bvRotateROp)
  , ("Prelude.bvShiftL", bvShiftLOp)
  , ("Prelude.bvShiftR", bvShiftROp)
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

toMaybeWord :: SValue -> IO (Maybe SWord)
toMaybeWord (VWord w) = return (Just w)
toMaybeWord (VVector vv) = ((symFromBits <$>) . T.sequence) <$> traverse (fmap toMaybeBool . force) vv
toMaybeWord _ = return Nothing

toVector :: SValue -> V.Vector SThunk
toVector (VVector xv) = xv
toVector (VWord xv) =
  V.fromList (map (ready . vBool . svTestBit xv) (enumFromThenTo (k-1) (k-2) 0))
  where k = intSizeOf xv
toVector _ = error "this word might be symbolic"

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
shiftOp :: (SWord -> SWord -> SWord) -> (SWord -> Int -> SWord) -> SValue
shiftOp bvOp natOp =
  constFun $
  wordFun $ \x -> return $
  strictFun $ \y ->
    case y of
      VNat n   -> return (vWord (natOp x (fromInteger n)))
      VToNat v -> fmap (vWord . bvOp x) (toWord v)
      _        -> error $ unwords ["Verifier.SAW.Simulator.SBV.shiftOp", show y]

-- bvShl :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShLOp :: SValue
bvShLOp = shiftOp svShiftLeft svShl

-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShROp :: SValue
bvShROp = shiftOp svShiftRight svShr

-- bvSShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvSShROp :: SValue
bvSShROp =
  constFun $
  wordFun $ \w -> return $
  Prims.natFun'' "bvSShrOp" $ \n -> return $ vWord $ svUnsign (svShr (svSign w) (fromIntegral n))
-- FIXME: make this work for bvToNat arguments

eqOp :: SValue
eqOp = Prims.eqOp trueOp andOp boolEqOp bvEqOp
  where trueOp       = VBool svTrue
        andOp    x y = return $ vBool (svAnd (toBool x) (toBool y))
        boolEqOp x y = return $ vBool (svEqual (toBool x) (toBool y))
        bvEqOp _ x y = do x' <- toWord x
                          y' <- toWord y
                          return $ vBool (svEqual x' y')

-----------------------------------------
-- Integer/bitvector conversions

-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
bvToIntOp :: SValue
bvToIntOp = constFun $ wordFun $ \v ->
   case svAsInteger v of
      Just i -> return $ VInt i
      Nothing -> fail "Cannot convert symbolic bitvector to integer"

-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
sbvToIntOp :: SValue
sbvToIntOp = constFun $ wordFun $ \v ->
   case svAsInteger (svSign v) of
      Just i -> return $ VInt i
      Nothing -> fail "Cannot convert symbolic bitvector to integer"

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
intToBvOp :: SValue
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x -> return $
    VWord $
     if n >= 0 then svInteger (KBounded False (fromIntegral n)) x
               else svUnsign $ svUNeg $ svInteger (KBounded True (fromIntegral n)) (negate x)

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
-- Rotations and shifts

-- bvRotateL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateLOp :: SValue
bvRotateLOp =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \ilv ->
    case xs of
      VVector xv -> selectV (lazyMux muxBVal) (V.length xv -1) (return . VVector . vRotateL xv) ilv
      VWord xlv -> return $ vWord (svRotateLeft xlv ilv)
      _ -> error $ "bvRotateLOp: " ++ show xs

-- bvRotateR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateROp :: SValue
bvRotateROp =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    case xs of
      VVector xv -> selectV (lazyMux muxBVal) (V.length xv -1) (return . VVector . vRotateR xv) ilv
      VWord xlv -> return $ vWord (svRotateRight xlv ilv)
      _ -> error $ "bvRotateROp: " ++ show xs

-- bvShiftR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftLOp :: SValue
bvShiftLOp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    let xv = toVector xs
    selectV (lazyMux muxBVal) (V.length xv - 1) (return . VVector . vShiftL x xv) ilv

-- bvShiftR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftROp :: SValue
bvShiftROp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    let xv = toVector xs
    selectV (lazyMux muxBVal) (V.length xv - 1) (return . VVector . vShiftR x xv) ilv

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
  shapes <- traverse (asFiniteType sc) argTs
  bval <- sbvSolveBasic (scModule sc) addlPrims unints t
  (labels, vars) <- flip evalStateT 0 $ unzip <$> traverse newVars shapes
  let prd = do
              bval' <- traverse (fmap ready) vars >>= (liftIO . applyAll bval)
              case bval' of
                VBool b -> return b
                _ -> fail "bitBlast: non-boolean result type."
  return (labels, prd)

data Labeler
   = BoolLabel String
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

newVars :: FiniteType -> StateT Int IO (Labeler, Symbolic SValue)
newVars FTBit = nextId <&> \s-> (BoolLabel s, vBool <$> existsSBool s)
newVars (FTVec n FTBit) =
  if n == 0
    then nextId <&> \s-> (WordLabel s, return (vWord (literalSWord 0 0)))
    else nextId <&> \s-> (WordLabel s, vWord <$> existsSWord s (fromIntegral n))
newVars (FTVec n tp) = do
  (labels, vals) <- V.unzip <$> V.replicateM (fromIntegral n) (newVars tp)
  return (VecLabel labels, VVector <$> traverse (fmap ready) vals)
newVars (FTTuple ts) = do
  (labels, vals) <- V.unzip <$> traverse newVars (V.fromList ts)
  return (TupleLabel labels, vTuple <$> traverse (fmap ready) (V.toList vals))
newVars (FTRec tm) = do
  (labels, vals) <- myfun <$> (traverse newVars tm :: StateT Int IO (Map String (Labeler, Symbolic SValue)))
  return (RecLabel labels, vRecord <$> traverse (fmap ready) (vals :: (Map String (Symbolic SValue))))

------------------------------------------------------------
-- Code Generation

newCodeGenVars :: (Nat -> Bool) -> FiniteType -> StateT Int IO (SBVCodeGen SValue)
newCodeGenVars _checkSz FTBit = nextId <&> \s -> (vBool <$> svCgInput KBool s)
newCodeGenVars checkSz (FTVec n FTBit)
  | n == 0    = nextId <&> \_ -> return (vWord (literalSWord 0 0))
  | checkSz n = nextId <&> \s -> vWord <$> cgInputSWord s (fromIntegral n)
  | otherwise = nextId <&> \s -> fail $ "Invalid codegen bit width for input variable \'" ++ s ++ "\': " ++ show n
newCodeGenVars checkSz (FTVec n (FTVec m FTBit))
  | m == 0    = nextId <&> \_ -> return (VVector $ V.fromList $ replicate (fromIntegral n) (ready $ vWord (literalSWord 0 0)))
  | checkSz m = do
      let k = KBounded False (fromIntegral m)
      vals <- nextId <&> \s -> svCgInputArr k (fromIntegral n) s
      return (VVector . V.fromList . fmap (ready . vWord) <$> vals)
  | otherwise = nextId <&> \s -> fail $ "Invalid codegen bit width for input variable array \'" ++ s ++ "\': " ++ show n
newCodeGenVars checkSz (FTVec n tp) = do
  vals <- V.replicateM (fromIntegral n) (newCodeGenVars checkSz tp)
  return (VVector <$> traverse (fmap ready) vals)
newCodeGenVars checkSz (FTTuple ts) = do
  vals <- traverse (newCodeGenVars checkSz) ts
  return (vTuple <$> traverse (fmap ready) vals)
newCodeGenVars checkSz (FTRec tm) = do
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
  -> IO (SBVCodeGen (), [FiniteType], FiniteType)
sbvCodeGen_definition sc addlPrims unints t checkSz = do
  ty <- scTypeOf sc t
  (argTs,resTy) <- argTypes sc ty
  shapes <- traverse (asFiniteType sc) argTs
  resultShape <- asFiniteType sc resTy
  bval <- sbvSolveBasic (scModule sc) addlPrims unints t
  vars <- evalStateT (traverse (newCodeGenVars checkSz) shapes) 0
  let codegen = do
        args <- traverse (fmap ready) vars
        bval' <- liftIO (applyAll bval args)
        sbvSetResult checkSz resultShape bval'
  return (codegen, shapes, resultShape)


sbvSetResult :: (Nat -> Bool)
             -> FiniteType
             -> SValue
             -> SBVCodeGen ()
sbvSetResult _checkSz FTBit (VBool b) = do
   svCgReturn b
sbvSetResult checkSz (FTVec n FTBit) v
   | n == 0    = return ()
   | checkSz n = do
      w <- liftIO $ toWord v
      svCgReturn w
   | otherwise =
      fail $ "Invalid word size in result: " ++ show n
sbvSetResult checkSz ft v = do
   void $ sbvSetOutput checkSz ft v 0


sbvSetOutput :: (Nat -> Bool)
             -> FiniteType
             -> SValue
             -> Int
             -> SBVCodeGen Int
sbvSetOutput _checkSz FTBit (VBool b) i = do
   svCgOutput ("out_"++show i) b
   return $! i+1
sbvSetOutput checkSz (FTVec n FTBit) v i
   | n == 0    = return i
   | checkSz n = do
       w <- liftIO $ toWord v
       svCgOutput ("out_"++show i) w
       return $! i+1
   | otherwise =
       fail $ "Invalid word size in output " ++ show i ++ ": " ++ show n

sbvSetOutput checkSz (FTVec n t) (VVector xv) i = do
   xs <- liftIO $ traverse force $ V.toList xv
   unless (toInteger n == toInteger (length xs)) $
     fail "sbvCodeGen: vector length mismatch when setting output values"
   case asWordList xs of
     Just ws -> do svCgOutputArr ("out_"++show i) ws
                   return $! i+1
     Nothing -> foldM (\i' x -> sbvSetOutput checkSz t x i') i xs
sbvSetOutput _checkSz (FTTuple []) VUnit i =
   return i
sbvSetOutput checkSz (FTTuple (t:ts)) (VPair l r) i = do
   l' <- liftIO $ force l
   r' <- liftIO $ force r
   sbvSetOutput checkSz t l' i >>= sbvSetOutput checkSz (FTTuple ts) r'

sbvSetOutput _checkSz (FTRec fs) VUnit i | Map.null fs = do
   return i
sbvSetOutput checkSz (FTRec fs) (VField fn x rec) i = do
   x' <- liftIO $ force x
   case Map.lookup fn fs of
     Just t -> do
       let fs' = Map.delete fn fs
       sbvSetOutput checkSz t x' i >>= sbvSetOutput checkSz (FTRec fs') rec
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
