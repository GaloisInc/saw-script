{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
import Control.Monad (zipWithM, (<=<))
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

lvRotateL :: LitVector l -> Int -> LitVector l
lvRotateL xs i
  | AIG.length xs == 0 = xs
  | otherwise = (AIG.++) (AIG.drop j xs) (AIG.take j xs)
  where j = i `mod` AIG.length xs

lvRotateR :: LitVector l -> Int -> LitVector l
lvRotateR xs i = lvRotateL xs (- i)

lvShiftL :: l -> LitVector l -> Int -> LitVector l
lvShiftL x xs i = (AIG.++) (AIG.drop j xs) (AIG.replicate j x)
  where j = min i (AIG.length xs)

lvShiftR :: l -> LitVector l -> Int -> LitVector l
lvShiftR x xs i = (AIG.++) (AIG.replicate j x) (AIG.take (AIG.length xs - j) xs)
  where j = min i (AIG.length xs)

------------------------------------------------------------
-- Values

type BValue l = Value IO l (LitVector l) (BExtra l)
type BThunk l = Thunk IO l (LitVector l) (BExtra l)

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

flattenBValue :: BValue l -> IO (LitVector l)
flattenBValue (VBool l) = return (AIG.replicate 1 l)
flattenBValue (VWord lv) = return lv
flattenBValue (VExtra (BStream _ _)) = error "Verifier.SAW.Simulator.BitBlast.flattenBValue: BStream"
flattenBValue (VVector vv) =
  AIG.concat <$> traverse (flattenBValue <=< force) (V.toList vv)
flattenBValue (VTuple vv) =
  AIG.concat <$> traverse (flattenBValue <=< force) (V.toList vv)
flattenBValue (VRecord m) =
  AIG.concat <$> traverse (flattenBValue <=< force) (Map.elems m)
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
shiftOp :: (LitVector l -> LitVector l -> IO (LitVector l))
        -> (LitVector l -> Nat -> LitVector l)
        -> BValue l
shiftOp bvOp natOp =
  constFun $
  wordFun $ \x -> return $
  strictFun $ \y ->
    case y of
      VNat n   -> return (vWord (natOp x (fromInteger n)))
      VToNat v -> fmap vWord (bvOp x =<< toWord v)
      _        -> error $ unwords ["Verifier.SAW.Simulator.BitBlast.shiftOp", show y]

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
  , ("Prelude.bvShl" , shiftOp (AIG.shl be) (lvShl (AIG.falseLit be)))
  , ("Prelude.bvShr" , shiftOp (AIG.ushr be) (lvShr (AIG.falseLit be)))
  , ("Prelude.bvSShr", shiftOp (AIG.sshr be) lvSShr)
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
  -- Vectors
  , ("Prelude.gen", Prims.genOp)
  , ("Prelude.at", Prims.atOp vFromLV AIG.at (lazyMux be (muxBVal be)))
  , ("Prelude.upd", Prims.updOp vFromLV (AIG.bvEq be) (AIG.bvFromInteger be) AIG.length (lazyMux be (muxBVal be)))
  , ("Prelude.append", Prims.appendOp vFromLV (AIG.++))
  , ("Prelude.join", Prims.joinOp vFromLV (AIG.++))
  , ("Prelude.zip", vZipOp)
  , ("Prelude.foldr", foldrOp)
  , ("Prelude.bvRotateL", bvRotateLOp be)
  , ("Prelude.bvRotateR", bvRotateROp be)
  , ("Prelude.bvShiftL", bvShiftLOp be)
  , ("Prelude.bvShiftR", bvShiftROp be)
  , ("Prelude.EmptyVec", Prims.emptyVec)
-- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp be)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  , ("Prelude.bvNat", bvNatOp be)
  , ("Prelude.bvToNat", Prims.bvToNatOp)
  -- Overloaded
  , ("Prelude.zero", zeroOp be)
  , ("Prelude.unary", Prims.unaryOp mkStreamOp streamGetOp)
  , ("Prelude.binary", Prims.binaryOp mkStreamOp streamGetOp)
  , ("Prelude.eq", eqOp be)
  , ("Prelude.comparison", Prims.comparisonOp)
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
muxBVal be b (VFun f)        (VFun g)        = return $ VFun (\a -> do x <- f a; y <- g a; muxBVal be b x y)
muxBVal be b (VTuple xv)     (VTuple yv)     = VTuple <$> muxThunks be b xv yv
muxBVal be b (VRecord xm)    (VRecord ym)
  | Map.keys xm == Map.keys ym               = (VRecord . Map.fromList . zip (Map.keys xm)) <$>
                                                 zipWithM (muxThunk be b) (Map.elems xm) (Map.elems ym)
muxBVal be b (VCtorApp i xv) (VCtorApp j yv) | i == j = VCtorApp i <$> muxThunks be b xv yv
muxBVal be b (VVector xv)    (VVector yv)    = VVector <$> muxThunks be b xv yv
muxBVal be b (VBool x)       (VBool y)       = VBool <$> AIG.mux be b x y
muxBVal be b (VWord x)       (VWord y)       | AIG.length x == AIG.length y
                                             = VWord <$> AIG.zipWithM (AIG.mux be b) x y
muxBVal _  _ (VNat m)        (VNat n)        | m == n = return $ VNat m
muxBVal _  _ (VString x)     (VString y)     | x == y = return $ VString x
muxBVal _  _ (VFloat x)      (VFloat y)      | x == y = return $ VFloat x
muxBVal _  _ (VDouble x)     (VDouble y)     | x == y = return $ VDouble y
muxBVal _  _ VType           VType           = return VType
muxBVal be b (VExtra x)      (VExtra y)      = VExtra <$> muxBExtra be b x y
muxBVal be b x@(VWord _) y         =
  muxBVal be b (VVector (vectorOfBValue x)) y
muxBVal be b x y@(VWord _)         =
  muxBVal be b x (VVector (vectorOfBValue y))
muxBVal _ _ x y =
  fail $ "Verifier.SAW.Simulator.BitBlast.iteOp: malformed arguments: " ++ show x ++ " " ++ show y

muxThunks :: AIG.IsAIG l g => g s -> l s
          -> V.Vector (BThunk (l s)) -> V.Vector (BThunk (l s)) -> IO (V.Vector (BThunk (l s)))
muxThunks be b xv yv
  | V.length xv == V.length yv = V.zipWithM (muxThunk be b) xv yv
  | otherwise                  = fail "Verifier.SAW.Simulator.BitBlast.iteOp: malformed arguments"

muxThunk :: AIG.IsAIG l g => g s -> l s -> BThunk (l s) -> BThunk (l s) -> IO (BThunk (l s))
muxThunk be b x y = delay $ do x' <- force x; y' <- force y; muxBVal be b x' y'

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
  VVector (V.zipWith (\x y -> ready (VTuple (V.fromList [x, y]))) (vectorOfBValue xs) (vectorOfBValue ys))

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

-- bvRotateL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateLOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvRotateLOp be =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    let (n, f) = case xs of
                   VVector xv -> (V.length xv, VVector . vRotateL xv)
                   VWord xlv -> (AIG.length xlv, VWord . lvRotateL xlv)
                   _ -> error $ "Verifier.SAW.Simulator.BitBlast.bvRotateLOp: " ++ show xs
    r <- AIG.urem be ilv (AIG.bvFromInteger be (AIG.length ilv) (toInteger n))
    AIG.muxInteger (lazyMux be (muxBVal be)) (n - 1) r (return . f)

-- bvRotateR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateROp :: AIG.IsAIG l g => g s -> BValue (l s)
bvRotateROp be =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    let (n, f) = case xs of
                   VVector xv -> (V.length xv, VVector . vRotateR xv)
                   VWord xlv -> (AIG.length xlv, VWord . lvRotateR xlv)
                   _ -> error $ "Verifier.SAW.Simulator.BitBlast.bvRotateROp: " ++ show xs
    r <- AIG.urem be ilv (AIG.bvFromInteger be (AIG.length ilv) (toInteger n))
    AIG.muxInteger (lazyMux be (muxBVal be)) (n - 1) r (return . f)

-- bvShiftL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftLOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvShiftLOp be =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    (n, f) <- case xs of
                VVector xv -> return (V.length xv, VVector . vShiftL x xv)
                VWord xlv -> do l <- toBool <$> force x
                                return (AIG.length xlv, VWord . lvShiftL l xlv)
                _ -> fail $ "Verifier.SAW.Simulator.BitBlast.bvShiftLOp: " ++ show xs
    AIG.muxInteger (lazyMux be (muxBVal be)) n ilv (return . f)

-- bvShiftR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftROp :: AIG.IsAIG l g => g s -> BValue (l s)
bvShiftROp be =
  constFun $
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    (n, f) <- case xs of
                VVector xv -> return (V.length xv, VVector . vShiftR x xv)
                VWord xlv -> do l <- toBool <$> force x
                                return (AIG.length xlv, VWord . lvShiftR l xlv)
                _ -> fail $ "Verifier.SAW.Simulator.BitBlast.bvShiftROp: " ++ show xs
    AIG.muxInteger (lazyMux be (muxBVal be)) n ilv (return . f)

zeroOp :: AIG.IsAIG l g => g s -> BValue (l s)
zeroOp be = Prims.zeroOp bvZ boolZ mkStreamOp
  where bvZ n = return (VWord (AIG.bvFromInteger be (fromInteger n) 0))
        boolZ = return (vBool (AIG.falseLit be))

eqOp :: AIG.IsAIG l g => g s -> BValue (l s)
eqOp be = Prims.eqOp trueOp andOp boolEqOp bvEqOp
  where trueOp       = vBool (AIG.trueLit be)
        andOp    x y = vBool <$> AIG.and be (toBool x) (toBool y)
        boolEqOp x y = vBool <$> AIG.eq be (toBool x) (toBool y)
        bvEqOp _ x y = do x' <- toWord x
                          y' <- toWord y
                          vBool <$> AIG.bvEq be x' y'

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
newVars be (FTTuple ts) = VTuple <$> traverse (newVars' be) (V.fromList ts)
newVars be (FTRec tm) = VRecord <$> traverse (newVars' be) tm

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
              -> SharedTerm t
              -> IO (BValue (l s))
bitBlastBasic be m addlPrims t = do
  cfg <- Sim.evalGlobal m (Map.union (beConstMap be) (addlPrims be)) (const (const Nothing))
  Sim.evalSharedTerm cfg t

asPredType :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "Verifier.SAW.Simulator.BitBlast.asPredType: non-boolean result type: " ++ show t'

withBitBlastedPred :: AIG.IsAIG l g => AIG.Proxy l g ->
  SharedContext t ->
  PrimMap l g ->
  SharedTerm t ->
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

asAIGType :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
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
  SharedContext t ->
  PrimMap l g ->
  SharedTerm t ->
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
