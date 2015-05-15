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
module Verifier.SAW.Simulator.SBV
  ( sbvSolve
  , Labeler(..)
  , sbvCodeGen
  ) where

import Data.SBV.Dynamic

import Verifier.SAW.Simulator.SBV.SWord

import Control.Lens ((<&>))
import qualified Control.Arrow as A

import Data.Bits
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
import Verifier.SAW.TypedAST (FieldName, Ident(..), Module)

import Verifier.SAW.FiniteValue (FiniteType(..), asFiniteType)

type SValue = Value IO SBool SWord SbvExtra
type SThunk = Thunk IO SBool SWord SbvExtra

data SbvExtra =
  SStream (Integer -> IO SValue) (IORef (Map Integer SValue))

instance Show SbvExtra where
  show (SStream _ _) = "<SStream>"

-- no, we need shape information
uninterpreted :: Ident -> SValue -> Maybe (IO SValue)
uninterpreted ident t = Just $ parseUninterpreted [] (identName ident) t

-- actually...
-- rewriteSharedTerm

constMap :: Map Ident SValue
constMap = Map.fromList
  -- Boolean
  [ ("Prelude.True", VBool svTrue)
  , ("Prelude.False", VBool svFalse)
  , ("Prelude.not", strictFun (return . vBool . svNot . forceBool))
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
  , ("Prelude.bvPMod", bvPModOp)
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
  -- Fin
  , ("Prelude.finDivMod", Prims.finDivModOp)
  , ("Prelude.finMax", Prims.finMaxOp)
  , ("Prelude.finPred", Prims.finPredOp)
  , ("Prelude.natSplitFin", Prims.natSplitFinOp)
  -- Vectors
  , ("Prelude.generate", Prims.generateOp)
  , ("Prelude.get", getOp)
  , ("Prelude.set", setOp)
  , ("Prelude.at", Prims.atOp svUnpack svAt (lazyMux muxBVal))
  , ("Prelude.upd", Prims.updOp svUnpack (\x y -> return (svEqual x y)) literalSWord svBitSize (lazyMux muxBVal))
  , ("Prelude.append", Prims.appendOp svUnpack svJoin)
  , ("Prelude.join", Prims.joinOp svUnpack svJoin)
  , ("Prelude.split", splitOp)
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
  , ("Prelude.bvToNat", Prims.bvToNatOp)
  -- Overloaded
  , ("Prelude.zero", zeroOp)
  , ("Prelude.unary", Prims.unaryOp mkStreamOp streamGetOp)
  , ("Prelude.binary", Prims.binaryOp mkStreamOp streamGetOp)
  , ("Prelude.eq", eqOp)
  , ("Prelude.comparison", Prims.comparisonOp)
  ]

------------------------------------------------------------
-- Coercion functions
--

bitVector :: Int -> Integer -> SWord
bitVector w i = literalSWord w i

symFromBits :: Vector SBool -> SWord
symFromBits v = V.foldl svJoin (bitVector 0 0) (V.map svToWord1 v)

toBool :: SValue -> Maybe SBool
toBool (VBool b) = Just b
toBool _  = Nothing

forceBool :: SValue -> SBool
forceBool = fromJust . toBool

toWord :: SValue -> IO (Maybe SWord)
toWord (VWord w) = return (Just w)
toWord (VVector vv) = ((symFromBits <$>) . T.sequence) <$> traverse (fmap toBool . force) vv
toWord _ = return Nothing

toVector :: SValue -> V.Vector SThunk
toVector (VVector xv) = xv
toVector (VWord xv) =
  V.fromList (map (ready . vBool . svTestBit xv) (enumFromThenTo (k-1) (k-2) 0))
  where k = svBitSize xv
toVector _ = error "this word might be symbolic"

-- | Flatten an SValue to a sequence of components, each of which is
-- either a symbolic word or a symbolic boolean.
flattenSValue :: SValue -> IO [SVal]
flattenSValue v = do
  mw <- toWord v
  case mw of
    Just w -> return [w]
    Nothing ->
      case v of
        VTuple (V.toList -> ts)   -> concat <$> traverse (force >=> flattenSValue) ts
        VRecord (Map.elems -> ts) -> concat <$> traverse (force >=> flattenSValue) ts
        VVector (V.toList -> ts)  -> concat <$> traverse (force >=> flattenSValue) ts
        VBool sb                  -> return [sb]
        VWord sw                  -> return (if svBitSize sw > 0 then [sw] else [])
        _ -> fail $ "Could not create sbv argument for " ++ show v

vWord :: SWord -> SValue
vWord lv = VWord lv

vBool :: SBool -> SValue
vBool l = VBool l

------------------------------------------------------------
-- Function constructors

wordFun :: (Maybe SWord -> IO SValue) -> SValue
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
    Nothing -> impl (svBitSize vx) 0
  where
    impl _ y | y >= maxValue = valueFn maxValue
    impl 0 y = valueFn y
    impl i y = merger (svTestBit vx j) (impl j (y `setBit` j)) (impl j y) where j = i - 1

-- Big-endian version of svTestBit
svAt :: SWord -> Int -> SBool
svAt x i = svTestBit x (svBitSize x - 1 - i)

svUnpack :: SWord -> Vector SBool
svUnpack x = V.generate (svBitSize x) (svAt x)

-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
getOp :: SValue
getOp =
  constFun $
  constFun $
  strictFun $ \v -> return $
  Prims.finFun $ \i ->
    case v of
      VVector xv -> force ((V.!) xv (fromEnum (finVal i)))
      VWord lv -> return $ vBool $ svTestBit lv ((svBitSize lv - 1) - fromEnum (finVal i))
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

-- bvShl :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShLOp :: SValue
bvShLOp =
  constFun $
  wordFun $ \(Just w) -> return $
  Prims.natFun'' "bvShlOp" $ \n -> return $ vWord $ svShl w (fromIntegral n)

-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShROp :: SValue
bvShROp =
  constFun $
  wordFun $ \(Just w) -> return $
  Prims.natFun'' "bvShrOp" $ \n -> return $ vWord $ svShr w (fromIntegral n)

-- bvSShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvSShROp :: SValue
bvSShROp =
  constFun $
  wordFun $ \(Just w) -> return $
  Prims.natFun'' "bvSShrOp" $ \n -> return $ vWord $ svUnsign (svShr (svSign w) (fromIntegral n))

zeroOp :: SValue
zeroOp = Prims.zeroOp bvZ boolZ mkStreamOp
  where bvZ n = return (vWord (bitVector (fromInteger n) 0))
        boolZ = return (VBool svFalse)

eqOp :: SValue
eqOp = Prims.eqOp trueOp andOp boolEqOp bvEqOp
  where trueOp       = VBool svTrue
        andOp    x y = return $ vBool (svAnd (forceBool x) (forceBool y))
        boolEqOp x y = return $ vBool (svEqual (forceBool x) (forceBool y))
        bvEqOp _ x y = do Just x' <- toWord x
                          Just y' <- toWord y
                          return $ vBool (svEqual x' y')

----------------------------------------
-- Polynomial operations

-- bvPMod :: (m n :: Nat) -> bitvector m -> bitvector (Succ n) -> bitvector n;
bvPModOp :: SValue
bvPModOp =
  constFun $
  constFun $
  wordFun $ \ (Just x) -> return $
  wordFun $ \ (Just y) ->
    return . vWord . fromBitsLE $ take (svBitSize y - 1) (snd (mdp (blastLE x) (blastLE y)) ++ repeat svFalse)

-- bvPMul :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector (subNat (maxNat 1 (addNat m n)) 1);
bvPMulOp :: SValue
bvPMulOp =
  constFun $
  constFun $
  wordFun $ \(Just x) -> return $
  wordFun $ \(Just y) -> do
    let k1 = svBitSize x
    let k2 = svBitSize y
    let k = max 1 (k1 + k2) - 1
    let mul _ [] ps = ps
        mul as (b:bs) ps = mul (svFalse : as) bs (ites b (as `addPoly` ps) ps)
    return . vWord . fromBitsLE $ take k $ mul (blastLE x) (blastLE y) [] ++ repeat svFalse

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
  wordFun $ \milv ->
    case (milv, xs) of
      (Nothing, xv) -> return xv -- FIXME: this case should be an error
      (Just ilv, VVector xv) -> selectV (lazyMux muxBVal) (V.length xv -1) (return . VVector . vRotateL xv) ilv
      (Just ilv, VWord xlv) -> return $ vWord (svRotateLeft xlv ilv)
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
      (Nothing, xv) -> return xv -- FIXME: this case should be an error
      (Just ilv, VVector xv) -> selectV (lazyMux muxBVal) (V.length xv -1) (return . VVector . vRotateR xv) ilv
      (Just ilv, VWord xlv) -> return $ vWord (svRotateRight xlv ilv)
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
    let xv = toVector xs
    case milv of
      Just ilv -> selectV (lazyMux muxBVal) (V.length xv - 1) (return . VVector . vShiftL x xv) ilv
      Nothing -> fail $ "bvShiftLOp: " ++ show xs

-- bvShiftR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftROp :: SValue
bvShiftROp =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \milv -> do
    let xv = toVector xs
    case milv of
      Just ilv -> selectV (lazyMux muxBVal) (V.length xv - 1) (return . VVector . vShiftR x xv) ilv
      Nothing -> fail $ "bvShiftROp: " ++ show xs

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
  wordFun $ \(Just ilv) ->
  selectV (lazyMux muxBVal) ((2 ^ svBitSize ilv) - 1) (lookupSStream xs) ilv

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
  VVector (V.zipWith (\x y -> ready (VTuple (V.fromList [x, y]))) (toVector xs) (toVector ys))

------------------------------------------------------------
-- Helpers for marshalling into SValues

unOp :: (SWord -> SWord) -> SValue
unOp op = constFun $
          strictFun $ \mx -> do
            (Just x) <- toWord mx
            return $ vWord $ op x

binOp :: (SWord -> SWord -> SWord) -> SValue
binOp op = constFun $
          strictFun $ \mx -> return $
          strictFun $ \my -> do
            (Just x) <- toWord mx
            (Just y) <- toWord my
            return $ vWord $ op x y

sbinOp :: (SWord -> SWord -> SWord) -> SValue
sbinOp f = binOp (\x y -> svUnsign (f (svSign x) (svSign y)))

binRel :: (SWord -> SWord -> SBool) -> SValue
binRel op = constFun $
            strictFun $ \mx-> return $
            strictFun $ \my-> do
              (Just x) <- toWord mx
              (Just y) <- toWord my
              return $ vBool $ op x y

sbinRel :: (SWord -> SWord -> SBool) -> SValue
sbinRel f = binRel (\x y -> svSign x `f` svSign y)

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
muxBVal b (VBool x)       (VBool y)       = return $ VBool $ svIte b x y
muxBVal b (VWord x)       (VWord y)       = return $ VWord $ svIte b x y
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
extraFn _ _ _ = error "iteOp: malformed arguments (extraFn)"

------------------------------------------------------------
-- External interface

sbvSolveBasic :: Module -> SharedTerm s -> IO SValue
sbvSolveBasic m t = do
  cfg <- Sim.evalGlobal m constMap uninterpreted
  let cfg' = cfg { Sim.simExtCns = const (parseUninterpreted []) }
  Sim.evalSharedTerm cfg' t

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
kindFromType (VTupleType []) = KBounded False 0
kindFromType (VTupleType tys) =
  foldr1 combineKind (map kindFromType tys)
    where combineKind (KBounded False m) (KBounded False n) = KBounded False (m + n)
          combineKind k k' = error $ "Can't combine kinds " ++ show k ++ " and " ++ show k'
kindFromType (VRecordType m) = kindFromType (VTupleType (Map.elems m))
kindFromType ty = error $ "Unsupported type: " ++ show ty

parseUninterpreted :: [SVal] -> String -> SValue -> IO SValue
parseUninterpreted cws nm (VDataType "Prelude.Bool" []) =
  return $ vBool $ mkUninterpreted KBool cws nm
parseUninterpreted cws nm (VPiType _ f) =
  return $
  strictFun $ \x -> do
    cws' <- flattenSValue x
    t2 <- f (ready x)
    parseUninterpreted (cws ++ cws') nm t2
parseUninterpreted cws nm ty =
  ST.evalStateT (parseTy ty) (mkUninterpreted (kindFromType ty) cws nm)
  where
    parseTy :: SValue -> ST.StateT SWord IO SValue
    parseTy (VDataType "Prelude.Vec" [VNat n, VDataType "Prelude.Bool" []]) = do
      v <- ST.get
      let w = svBitSize v
      let v1 = svExtract (w - 1) (w - fromInteger n) v
      let v2 = svExtract (w - fromInteger n - 1) 0 v
      ST.put v2
      return (vWord v1)
    parseTy (VDataType "Prelude.Vec" [VNat n, ety]) = do
      xs <- traverse parseTy (replicate (fromIntegral n) ety)
      return (VVector (V.fromList (map ready xs)))
    parseTy (VTupleType tys) = do
      xs <- traverse parseTy tys
      return (VTuple (V.fromList (map ready xs)))
    parseTy (VRecordType tm) = do
      xm <- traverse parseTy tm
      return (VRecord (fmap ready xm))
    parseTy t = fail $ "could not create uninterpreted type for " ++ show t

mkUninterpreted :: Kind -> [SVal] -> String -> SVal
mkUninterpreted k args nm = svUninterpreted k nm Nothing args

asPredType :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "non-boolean result type: " ++ show t'

sbvSolve :: SharedContext s -> SharedTerm s -> IO ([Labeler], Symbolic SBool)
sbvSolve sc t = do
  ty <- scTypeOf sc t
  argTs <- asPredType sc ty
  shapes <- traverse (asFiniteType sc) argTs
  bval <- sbvSolveBasic (scModule sc) t
  let (labels, vars) = flip evalState 0 $ unzip <$> traverse newVars shapes
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

nextId :: State Int String
nextId = ST.get >>= (\s-> modify (+1) >> return ("x" ++ show s))

--unzipMap :: Map k (a, b) -> (Map k a, Map k b)
--unzipMap m = (fmap fst m, fmap snd m)

myfun ::(Map String (Labeler, Symbolic SValue)) -> (Map String Labeler, Map String (Symbolic SValue))
myfun = fmap fst A.&&& fmap snd

newVars :: FiniteType -> State Int (Labeler, Symbolic SValue)
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
  return (TupleLabel labels, VTuple <$> traverse (fmap ready) vals)
newVars (FTRec tm) = do
  (labels, vals) <- myfun <$> (traverse newVars tm :: State Int (Map String (Labeler, Symbolic SValue)))
  return (RecLabel labels, VRecord <$> traverse (fmap ready) (vals :: (Map String (Symbolic SValue))))

------------------------------------------------------------
-- C Code Generation

newCodeGenVars :: FiniteType -> State Int (SBVCodeGen SValue)
newCodeGenVars FTBit = nextId <&> \s -> (vBool <$> svCgInput KBool s)
newCodeGenVars (FTVec n FTBit) =
  if n == 0
    then nextId <&> \_ -> return (vWord (literalSWord 0 0))
    else nextId <&> \s -> vWord <$> cgInputSWord s (fromIntegral n)
newCodeGenVars (FTVec n tp) = do
  vals <- V.replicateM (fromIntegral n) (newCodeGenVars tp)
  return (VVector <$> traverse (fmap ready) vals)
newCodeGenVars (FTTuple ts) = do
  vals <- traverse newCodeGenVars (V.fromList ts)
  return (VTuple <$> traverse (fmap ready) vals)
newCodeGenVars (FTRec tm) = do
  vals <- traverse newCodeGenVars tm
  return (VRecord <$> traverse (fmap ready) vals)

cgInputSWord :: String -> Int -> SBVCodeGen SWord
cgInputSWord s n
  | n `elem` [8,16,32,64] = svCgInput (KBounded False n) s
  | otherwise =
  fail $ "Invalid codegen bit width for input variable \'" ++ s ++ "\': " ++ show n

argTypes :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
argTypes sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> argTypes sc t2
    _                            -> return []

sbvCodeGen :: SharedContext s -> Maybe FilePath -> String -> SharedTerm s -> IO ()
sbvCodeGen sc path fname t = do
  ty <- scTypeOf sc t
  argTs <- argTypes sc ty
  shapes <- traverse (asFiniteType sc) argTs
  bval <- sbvSolveBasic (scModule sc) t
  let vars = evalState (traverse newCodeGenVars shapes) 0
  let codegen = do
        args <- traverse (fmap ready) vars
        bval' <- liftIO (applyAll bval args)
        case bval' of
          VBool b -> svCgReturn b
          VWord w
            | n `elem` [8,16,32,64] -> svCgReturn w
            | otherwise -> fail $ "sbvCodeGen: unsupported bitvector size: " ++ show n
            where n = svBitSize w
          _ -> fail "sbvCodeGen: invalid result type: not boolean or bitvector"
  compileToC path fname codegen
