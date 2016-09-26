{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Simulator.BitBlast
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.BitBlast where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable
#endif
import Control.Monad ((<=<))
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

import Verifier.SAW.FiniteValue (FiniteType(..), asFiniteType)
import Verifier.SAW.Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST (Module)
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Recognizer as R

import qualified Data.AIG as AIG

type LitVector l = AIG.BV l

------------------------------------------------------------
-- Vector operations

lvFromV :: V.Vector l -> LitVector l
lvFromV v = AIG.generate_msb0 (V.length v) ((V.!) v)

vFromLV :: LitVector l -> V.Vector l
vFromLV lv = V.generate (AIG.length lv) (AIG.at lv)

vRotateL :: V.Vector a -> Integer -> V.Vector a
vRotateL xs i
  | V.null xs = xs
  | otherwise = (V.++) (V.drop j xs) (V.take j xs)
  where j = fromInteger (i `mod` toInteger (V.length xs))

vRotateR :: V.Vector a -> Integer -> V.Vector a
vRotateR xs i = vRotateL xs (- i)

vShiftL :: a -> V.Vector a -> Int -> V.Vector a
vShiftL x xs i = (V.++) (V.drop j xs) (V.replicate j x)
  where j = min i (V.length xs)

vShiftR :: a -> V.Vector a -> Int -> V.Vector a
vShiftR x xs i = (V.++) (V.replicate j x) (V.take (V.length xs - j) xs)
  where j = min i (V.length xs)

lvRotateL :: LitVector l -> Integer -> LitVector l
lvRotateL xs i
  | AIG.length xs == 0 = xs
  | otherwise = (AIG.++) (AIG.drop j xs) (AIG.take j xs)
  where j = fromInteger (i `mod` toInteger (AIG.length xs))

lvRotateR :: LitVector l -> Integer -> LitVector l
lvRotateR xs i = lvRotateL xs (- i)

lvShiftL :: l -> LitVector l -> Int -> LitVector l
lvShiftL x xs i = (AIG.++) (AIG.drop j xs) (AIG.replicate j x)
  where j = min i (AIG.length xs)

lvShiftR :: l -> LitVector l -> Int -> LitVector l
lvShiftR x xs i = (AIG.++) (AIG.replicate j x) (AIG.take (AIG.length xs - j) xs)
  where j = min i (AIG.length xs)

------------------------------------------------------------
-- Values

type BValue l = Value IO l (LitVector l) Integer (BExtra l)
type BThunk l = Thunk IO l (LitVector l) Integer (BExtra l)

data BExtra l
  = BStream (Integer -> IO (BValue l)) (IORef (Map Integer (BValue l)))

instance Show (BExtra l) where
  show (BStream _ _) = "BStream"

vBool :: l -> BValue l
vBool l = VBool l

toBool :: BValue l -> l
toBool (VBool l) = l
toBool x = error $ unwords ["Verifier.SAW.Simulator.BitBlast.toBool", show x]

vWord :: LitVector l -> BValue l
vWord lv = VWord lv

toWord :: BValue l -> IO (LitVector l)
toWord (VWord lv) = return lv
toWord (VVector vv) = lvFromV <$> traverse (fmap toBool . force) vv
toWord x = fail $ unwords ["Verifier.SAW.Simulator.BitBlast.toWord", show x]

fromVInt :: BValue l -> Integer
fromVInt (VInt i) = i
fromVInt sv = error $ unwords ["fromVInt failed:", show sv]

flattenBValue :: BValue l -> IO (LitVector l)
flattenBValue (VBool l) = return (AIG.replicate 1 l)
flattenBValue (VWord lv) = return lv
flattenBValue (VExtra (BStream _ _)) = error "Verifier.SAW.Simulator.BitBlast.flattenBValue: BStream"
flattenBValue (VVector vv) =
  AIG.concat <$> traverse (flattenBValue <=< force) (V.toList vv)
flattenBValue VUnit = return $ AIG.concat []
flattenBValue (VPair x y) = do
  vx <- flattenBValue =<< force x
  vy <- flattenBValue =<< force y
  return $ AIG.concat [vx, vy]
flattenBValue VEmpty = return $ AIG.concat []
flattenBValue (VField _ x y) = do
  vx <- flattenBValue =<< force x
  vy <- flattenBValue y
  return $ AIG.concat [vx, vy]
flattenBValue _ = error $ unwords ["Verifier.SAW.Simulator.BitBlast.flattenBValue: unsupported value"]

wordFun :: (LitVector l -> IO (BValue l)) -> BValue l
wordFun f = strictFun (\x -> toWord x >>= f)

-- | op :: Bool -> Bool -> Bool
boolBinOp :: (l -> l -> IO l) -> BValue l
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> vBool <$> op (toBool x) (toBool y)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n
unOp :: (LitVector l -> IO (LitVector l)) -> BValue l
unOp op =
  constFun $
  wordFun $ \x -> vWord <$> op x

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n
binOp :: (LitVector l -> LitVector l -> IO (LitVector l)) -> BValue l
binOp op =
  constFun $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> Bool
binRel :: (LitVector l -> LitVector l -> IO l) -> BValue l
binRel op =
  constFun $
  wordFun $ \x -> return $
  wordFun $ \y -> vBool <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
bvShiftOp :: (LitVector l -> LitVector l -> IO (LitVector l))
          -> (LitVector l -> Nat -> LitVector l)
          -> BValue l
bvShiftOp bvOp natOp =
  constFun $
  wordFun $ \x -> return $
  strictFun $ \y ->
    case y of
      VNat n   -> return (vWord (natOp x (fromInteger n)))
      VToNat v -> fmap vWord (bvOp x =<< toWord v)
      _        -> error $ unwords ["Verifier.SAW.Simulator.BitBlast.shiftOp", show y]

rol :: BValue l -> Integer -> BValue l
rol x i =
  case x of
    VVector xv -> VVector (vRotateL xv i)
    VWord xlv -> VWord (lvRotateL xlv i)
    _ -> error $ "Verifier.SAW.Simulator.BitBlast.rol: " ++ show x

ror :: BValue l -> Integer -> BValue l
ror x i =
  case x of
    VVector xv -> VVector (vRotateR xv i)
    VWord xlv -> VWord (lvRotateR xlv i)
    _ -> error $ "Verifier.SAW.Simulator.BitBlast.ror: " ++ show x

------------------------------------------------------------

lvShl :: l -> LitVector l -> Nat -> LitVector l
lvShl l v i = AIG.slice v j (n-j) AIG.++ AIG.replicate j l
  where n = AIG.length v
        j = fromIntegral i `min` n

lvShr :: l -> LitVector l -> Nat -> LitVector l
lvShr l v i = AIG.replicate j l AIG.++ AIG.slice v 0 (n-j)
  where n = AIG.length v
        j = fromIntegral i `min` n

lvSShr :: LitVector l -> Nat -> LitVector l
lvSShr v i = lvShr (AIG.msb v) v i

------------------------------------------------------------

beConstMap :: AIG.IsAIG l g => g s -> Map Ident (BValue (l s))
beConstMap be = Map.fromList
  -- Boolean
  [ ("Prelude.True"  , vBool (AIG.trueLit be))
  , ("Prelude.False" , vBool (AIG.falseLit be))
  , ("Prelude.not"   , strictFun (return . vBool . AIG.not . toBool))
  , ("Prelude.and"   , boolBinOp (AIG.and be))
  , ("Prelude.or"    , boolBinOp (AIG.or be))
  , ("Prelude.xor"   , boolBinOp (AIG.xor be))
  , ("Prelude.boolEq", boolBinOp (AIG.eq be))
  , ("Prelude.ite"   , iteOp be)
  -- Arithmetic
  , ("Prelude.bvNeg" , unOp (AIG.neg be))
  , ("Prelude.bvAdd" , binOp (AIG.add be))
  , ("Prelude.bvSub" , binOp (AIG.sub be))
  , ("Prelude.bvMul" , binOp (AIG.mul be))
  , ("Prelude.bvAnd" , binOp (AIG.zipWithM (AIG.and be)))
  , ("Prelude.bvOr"  , binOp (AIG.zipWithM (AIG.or be)))
  , ("Prelude.bvXor" , binOp (AIG.zipWithM (AIG.xor be)))
  , ("Prelude.bvUDiv", binOp (AIG.uquot be))
  , ("Prelude.bvURem", binOp (AIG.urem be))
  , ("Prelude.bvSDiv", binOp (AIG.squot be))
  , ("Prelude.bvSRem", binOp (AIG.srem be))
  , ("Prelude.bvPMul", bvPMulOp be)
  , ("Prelude.bvPMod", bvPModOp be)
  , ("Prelude.bvPDiv", bvPDivOp be)
  , ("Prelude.bvLg2" , Prims.bvLg2Op toWord (bitblastLogBase2 be) )
  -- Relations
  , ("Prelude.bvEq"  , binRel (AIG.bvEq be))
  , ("Prelude.bvsle" , binRel (AIG.sle be))
  , ("Prelude.bvslt" , binRel (AIG.slt be))
  , ("Prelude.bvule" , binRel (AIG.ule be))
  , ("Prelude.bvult" , binRel (AIG.ult be))
  , ("Prelude.bvsge" , binRel (flip (AIG.sle be)))
  , ("Prelude.bvsgt" , binRel (flip (AIG.slt be)))
  , ("Prelude.bvuge" , binRel (flip (AIG.ule be)))
  , ("Prelude.bvugt" , binRel (flip (AIG.ult be)))
  -- Shifts
  , ("Prelude.bvShl" , bvShiftOp (AIG.shl be) (lvShl (AIG.falseLit be)))
  , ("Prelude.bvShr" , bvShiftOp (AIG.ushr be) (lvShr (AIG.falseLit be)))
  , ("Prelude.bvSShr", bvShiftOp (AIG.sshr be) lvSShr)
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
  , ("Prelude.equalNat", Prims.equalNat (return . AIG.constant be))
  , ("Prelude.ltNat", Prims.ltNat (return . AIG.constant be))
  -- Integers
  , ("Prelude.intAdd", Prims.intAddOp)
  , ("Prelude.intSub", Prims.intSubOp)
  , ("Prelude.intMul", Prims.intMulOp)
  , ("Prelude.intDiv", Prims.intDivOp)
  , ("Prelude.intMod", Prims.intModOp)
  , ("Prelude.intNeg", Prims.intNegOp)
  , ("Prelude.intEq" , Prims.intEqOp (AIG.constant be))
  , ("Prelude.intLe" , Prims.intLeOp (AIG.constant be))
  , ("Prelude.intLt" , Prims.intLtOp (AIG.constant be))
  , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", Prims.natToIntOp)
  , ("Prelude.intToBv" , intToBvOp be)
  , ("Prelude.bvToInt" , bvToIntOp be)
  , ("Prelude.sbvToInt", sbvToIntOp be)
  , ("Prelude.intMin"  , Prims.intMinOp)
  , ("Prelude.intMax"  , Prims.intMaxOp)
  -- Vectors
  , ("Prelude.gen", Prims.genOp)
  , ("Prelude.atWithDefault", Prims.atWithDefaultOp vFromLV AIG.at (lazyMux be (muxBVal be)))
  , ("Prelude.upd", Prims.updOp vFromLV (AIG.bvEq be) (AIG.bvFromInteger be) AIG.length (lazyMux be (muxBVal be)))
  , ("Prelude.append", Prims.appendOp vFromLV (AIG.++))
  , ("Prelude.join", Prims.joinOp vFromLV (AIG.++))
  , ("Prelude.zip", vZipOp)
  , ("Prelude.foldr", foldrOp)
  , ("Prelude.rotateL", rotateOp be rol)
  , ("Prelude.rotateR", rotateOp be ror)
  , ("Prelude.shiftL", shiftLOp be)
  , ("Prelude.shiftR", shiftROp be)
  , ("Prelude.EmptyVec", Prims.emptyVec)
-- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp be)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  , ("Prelude.bvNat", bvNatOp be)
  , ("Prelude.bvToNat", Prims.bvToNatOp)
  , ("Prelude.error", Prims.errorOp)
  -- Overloaded
  , ("Prelude.eq", eqOp be)
  ]

-- | Lifts a strict mux operation to a lazy mux
lazyMux :: AIG.IsAIG l g => g s -> (l s -> a -> a -> IO a) -> l s -> IO a -> IO a -> IO a
lazyMux be muxFn c tm fm
  | (AIG.===) c (AIG.trueLit be) = tm
  | (AIG.===) c (AIG.falseLit be) = fm
  | otherwise = do
      t <- tm
      f <- fm
      muxFn c t f

-- | ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
iteOp :: AIG.IsAIG l g => g s -> BValue (l s)
iteOp be =
  constFun $
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> lazyMux be (muxBVal be) (toBool b) (force x) (force y)

muxBVal :: AIG.IsAIG l g => g s -> l s -> BValue (l s) -> BValue (l s) -> IO (BValue (l s))
muxBVal be = Prims.muxValue vFromLV bool word int (muxBExtra be)
  where
    bool b = AIG.mux be b
    word b = AIG.zipWithM (bool b)
    int _ x y = if x == y then return x else fail $ "muxBVal: VInt " ++ show (x, y)

muxBExtra :: AIG.IsAIG l g => g s -> l s -> BExtra (l s) -> BExtra (l s) -> IO (BExtra (l s))
muxBExtra _ _ _ _ = fail "Verifier.SAW.Simulator.BitBlast.iteOp: malformed arguments"

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: BValue l
vZipOp =
  constFun $
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  VVector (V.zipWith (\x y -> ready (vTuple [x, y])) (vectorOfBValue xs) (vectorOfBValue ys))

vectorOfBValue :: BValue l -> V.Vector (BThunk l)
vectorOfBValue (VVector xv) = xv
vectorOfBValue (VWord lv) = fmap (ready . vBool) (vFromLV lv)
vectorOfBValue _ = error "Verifier.SAW.Simulator.BitBlast.vectorOfBValue"

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: BValue l
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
      _ -> fail "Verifier.SAW.Simulator.BitBlast.foldrOp"

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNatOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvNatOp be =
  Prims.natFun'' "bvNat(1)" $ \w -> return $
  Prims.natFun'' "bvNat(2)" $ \x -> return $
  VWord (AIG.bvFromInteger be (fromIntegral w) (toInteger x))

-- rotate{L,R} :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateOp :: AIG.IsAIG l g =>
  g s -> (BValue (l s) -> Integer -> BValue (l s)) -> BValue (l s)
rotateOp be op =
  constFun $
  constFun $
  strictFun $ \x0 -> return $
  strictFun $ \i ->
    case i of
      VNat n   -> return (op x0 n)
      VToNat v -> toWord v >>= \ilv -> go x0 (AIG.bvToList ilv)
      _        -> fail $ "Verifier.SAW.Simulator.BitBlast.rotateOp: " ++ show i
  where
    go x [] = return x
    go x (y : ys) = do
      x' <- lazyMux be (muxBVal be) y (return (op x (2 ^ length ys))) (return x)
      go x' ys

-- shift{L,R} :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftOp :: AIG.IsAIG l g => g s
        -> (BThunk (l s) -> V.Vector (BThunk (l s)) -> Int -> V.Vector (BThunk (l s)))
        -> (l s -> AIG.BV (l s) -> Int -> LitVector (l s))
        -> BValue (l s)
shiftOp be vecOp wordOp =
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  strictFun $ \y -> do
    (n, f) <- case xs of
                VVector xv -> return (V.length xv, VVector . vecOp x xv)
                VWord xlv -> do l <- toBool <$> force x
                                return (AIG.length xlv, VWord . wordOp l xlv)
                _ -> fail $ "Verifier.SAW.Simulator.BitBlast.shiftOp: " ++ show xs
    case y of
      VNat i   -> return (f (fromInteger (i `min` toInteger n)))
      VToNat v -> do
        ilv <- toWord v
        AIG.muxInteger (lazyMux be (muxBVal be)) n ilv (return . f)
      _        -> fail $ "Verifier.SAW.Simulator.BitBlast.shiftOp: " ++ show y

-- shiftL :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftLOp :: AIG.IsAIG l g => g s -> BValue (l s)
shiftLOp be = shiftOp be vShiftL lvShiftL

-- shiftR :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftROp :: AIG.IsAIG l g => g s -> BValue (l s)
shiftROp be = shiftOp be vShiftR lvShiftR

eqOp :: AIG.IsAIG l g => g s -> BValue (l s)
eqOp be = Prims.eqOp trueOp andOp boolEqOp bvEqOp intEqOp
  where trueOp       = vBool (AIG.trueLit be)
        andOp    x y = vBool <$> AIG.and be (toBool x) (toBool y)
        boolEqOp x y = vBool <$> AIG.eq be (toBool x) (toBool y)
        bvEqOp _ x y = do x' <- toWord x
                          y' <- toWord y
                          vBool <$> AIG.bvEq be x' y'
        intEqOp  x y = return $ vBool (AIG.constant be (fromVInt x == fromVInt y))

-- | rounded-up log base 2, where we complete the function by setting:
--   lg2 0 = 0
bitblastLogBase2 :: AIG.IsAIG l g => g s -> LitVector (l s) -> IO (LitVector (l s))
bitblastLogBase2 g x = do
  z <- AIG.isZero g x
  AIG.iteM g z (return x) (AIG.logBase2_up g x)

-----------------------------------------
-- Integer/bitvector conversions

-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
bvToIntOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvToIntOp g = constFun $ wordFun $ \v ->
   case AIG.asUnsigned g v of
      Just i -> return $ VInt i
      Nothing -> fail "Cannot convert symbolic bitvector to integer"

-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
sbvToIntOp :: AIG.IsAIG l g => g s -> BValue (l s)
sbvToIntOp g = constFun $ wordFun $ \v ->
   case AIG.asSigned g v of
      Just i -> return $ VInt i
      Nothing -> fail "Cannot convert symbolic bitvector to integer"

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
intToBvOp :: AIG.IsAIG l g => g s -> BValue (l s)
intToBvOp g =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x ->
    VWord <$>
     if n >= 0 then return (AIG.bvFromInteger g (fromIntegral n) x)
               else AIG.neg g (AIG.bvFromInteger g (fromIntegral n) (negate x))

----------------------------------------
-- Polynomial operations

-- bvPMod :: (m n :: Nat) -> bitvector m -> bitvector (Succ n) -> bitvector n;
bvPModOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvPModOp g =
  constFun $
  constFun $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> AIG.pmod g x y

-- bvPMul :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector _;
bvPMulOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvPMulOp g =
  constFun $
  constFun $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> AIG.pmul g x y

-- primitive bvPDiv :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector m;
bvPDivOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvPDivOp g =
  constFun $
  constFun $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> AIG.pdiv g x y

----------------------------------------

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: BValue l
mkStreamOp =
  constFun $
  strictFun $ \f -> do
    r <- newIORef Map.empty
    return $ VExtra (BStream (\n -> apply f (ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: BValue l
streamGetOp =
  constFun $
  strictFun $ \xs -> return $
  Prims.natFun'' "streamGet" $ \n -> lookupBStream xs (toInteger n)

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvStreamGetOp be =
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \ilv ->
  AIG.muxInteger (lazyMux be (muxBVal be)) ((2 ^ AIG.length ilv) - 1) ilv (lookupBStream xs)

lookupBStream :: BValue l -> Integer -> IO (BValue l)
lookupBStream (VExtra (BStream f r)) n = do
   m <- readIORef r
   case Map.lookup n m of
     Just v  -> return v
     Nothing -> do v <- f n
                   writeIORef r (Map.insert n v m)
                   return v
lookupBStream _ _ = fail "Verifier.SAW.Simulator.BitBlast.lookupBStream: expected Stream"

------------------------------------------------------------
-- Generating variables for arguments

newVars :: AIG.IsAIG l g => g s -> FiniteType -> IO (BValue (l s))
newVars be FTBit = vBool <$> AIG.newInput be
newVars be (FTVec n tp) = VVector <$> V.replicateM (fromIntegral n) (newVars' be tp)
newVars be (FTTuple ts) = vTuple <$> traverse (newVars' be) ts
newVars be (FTRec tm) = vRecord <$> traverse (newVars' be) tm

newVars' :: AIG.IsAIG l g => g s -> FiniteType -> IO (BThunk (l s))
newVars' be shape = ready <$> newVars be shape

------------------------------------------------------------
-- Bit-blasting primitives.
--
-- NB: It doesn't make sense to bit blast more than one term using the
-- same bit engine, so the primitives 'withBitBlasted*' create their
-- own bit engine internally, instead of receiving it from the caller,
-- and pass it to the caller-provided continuation.

type PrimMap l g = forall s. g s -> Map Ident (BValue (l s))

bitBlastBasic :: AIG.IsAIG l g
              => g s
              -> Module
              -> PrimMap l g
              -> Term
              -> IO (BValue (l s))
bitBlastBasic be m addlPrims t = do
  cfg <- Sim.evalGlobal m (Map.union (beConstMap be) (addlPrims be))
         (const (bitBlastExtCns be))
         (const (const Nothing))
  Sim.evalSharedTerm cfg t

bitBlastExtCns :: AIG.IsAIG l g => g s -> String -> BValue (l s) -> IO (BValue (l s))
bitBlastExtCns be name v =
  case asFiniteTypeValue v of
    Just ft -> newVars be ft
    Nothing -> fail $ "Verifier.SAW.Simulator.BitBlast: variable " ++ show name
               ++ " has non-finite type " ++ show v

asPredType :: SharedContext -> Term -> IO [Term]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "Verifier.SAW.Simulator.BitBlast.asPredType: non-boolean result type: " ++ show t'

withBitBlastedPred :: AIG.IsAIG l g => AIG.Proxy l g ->
  SharedContext ->
  PrimMap l g ->
  Term ->
  (forall s. g s -> l s -> [FiniteType] -> IO a) -> IO a
withBitBlastedPred proxy sc addlPrims t c = AIG.withNewGraph proxy $ \be -> do
  ty <- scTypeOf sc t
  argTs <- asPredType sc ty
  shapes <- traverse (asFiniteType sc) argTs
  vars <- traverse (newVars' be) shapes
  bval <- bitBlastBasic be (scModule sc) addlPrims t
  bval' <- applyAll bval vars
  case bval' of
    VBool l -> c be l shapes
    _ -> fail "Verifier.SAW.Simulator.BitBlast.bitBlast: non-boolean result type."

asAIGType :: SharedContext -> Term -> IO [Term]
asAIGType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asAIGType sc t2
    (R.asBoolType -> Just ())    -> return []
    (R.asVecType -> Just _)      -> return []
    (R.asTupleType -> Just _)    -> return []
    (R.asRecordType -> Just _)   -> return []
    _                          -> fail $ "Verifier.SAW.Simulator.BitBlast.adAIGType: invalid AIG type: " ++ show t'

withBitBlastedTerm :: AIG.IsAIG l g => AIG.Proxy l g ->
  SharedContext ->
  PrimMap l g ->
  Term ->
  (forall s. g s -> LitVector (l s) -> IO a) -> IO a
withBitBlastedTerm proxy sc addlPrims t c = AIG.withNewGraph proxy $ \be -> do
  ty <- scTypeOf sc t
  argTs <- asAIGType sc ty
  shapes <- traverse (asFiniteType sc) argTs
  vars <- traverse (newVars' be) shapes
  bval <- bitBlastBasic be (scModule sc) addlPrims t
  bval' <- applyAll bval vars
  v <- flattenBValue bval'
  c be v
