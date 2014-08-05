{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.Simulator.BitBlast where

import Control.Applicative
import Control.Monad (zipWithM, (<=<))
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable
import qualified Data.Vector as V

import Verifier.SAW.Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST (FieldName, {-Ident,-} Module)
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Recognizer as R

import Data.AIG (BV)
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

type BValue l = Value IO (BExtra l)
type BThunk l = Thunk IO (BExtra l)

data BExtra l
  = BBool l
  | BWord (LitVector l) -- ^ Bits in LSB order
  | BStream (Integer -> IO (BValue l)) (IORef (Map Integer (BValue l)))

instance Show (BExtra l) where
  show (BBool _) = "BBool"
  show (BWord _) = "BWord"
  show (BStream _ _) = "BStream"

vBool :: l -> BValue l
vBool l = VExtra (BBool l)

toBool :: BValue l -> l
toBool (VExtra (BBool l)) = l
toBool _ = error "toBool"

vWord :: LitVector l -> BValue l
vWord lv = VExtra (BWord lv)

toWord :: BValue l -> IO (LitVector l)
toWord (VExtra (BWord lv)) = return lv
toWord (VVector vv) = lvFromV <$> traverse (fmap toBool . force) vv
toWord _ = fail "toWord"

flattenBValue :: BValue l -> IO (LitVector l)
flattenBValue (VExtra (BBool l)) = return (AIG.replicate 1 l)
flattenBValue (VExtra (BWord lv)) = return lv
flattenBValue (VExtra (BStream _ _)) = error "flattenBValue: BStream"
flattenBValue (VVector vv) =
  AIG.concat <$> traverse (flattenBValue <=< force) (V.toList vv)
flattenBValue (VTuple vv) =
  AIG.concat <$> traverse (flattenBValue <=< force) (V.toList vv)
flattenBValue (VRecord m) =
  AIG.concat <$> traverse (flattenBValue <=< force) (Map.elems m)
flattenBValue _ = error "flattenBValue: unsupported value"

wordFun :: (LitVector l -> IO (BValue l)) -> BValue l
wordFun f = strictFun (\x -> toWord x >>= f)

-- | op :: Bool -> Bool -> Bool
boolBinOp :: (l -> l -> IO l) -> BValue l
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> vBool <$> op (toBool x) (toBool y)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n
binOp :: (LitVector l -> LitVector l -> IO (LitVector l)) -> BValue l
binOp op =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> Bool
binRel :: (LitVector l -> LitVector l -> IO l) -> BValue l
binRel op =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vBool <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
shiftOp :: (LitVector l -> LitVector l -> IO (LitVector l))
        -> (LitVector l -> Nat -> LitVector l)
        -> BValue l
shiftOp _bvOp natOp =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  strictFun $ \y ->
    case y of
      VNat n           -> return (vWord (natOp x (fromInteger n)))
      _                -> error "shiftOp"

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
  , ("Prelude.at", atOp)
  , ("Prelude.append", appendOp)
  , ("Prelude.vZip", vZipOp)
  , ("Prelude.foldr", foldrOp)
  , ("Prelude.bvAt", bvAtOp be)
  , ("Prelude.bvUpd", bvUpdOp be)
  , ("Prelude.bvRotateL", bvRotateLOp be)
  , ("Prelude.bvRotateR", bvRotateROp be)
  , ("Prelude.bvShiftL", bvShiftLOp be)
  , ("Prelude.bvShiftR", bvShiftROp be)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp be)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  , ("Prelude.bvNat", bvNatOp be)
  --, ("Prelude.bvToNat", bvToNatOp)
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
  VFun $ \_ -> return $
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
muxBVal _  _ (VNat m)        (VNat n)        | m == n = return $ VNat m
muxBVal _  _ (VString x)     (VString y)     | x == y = return $ VString x
muxBVal _  _ (VFloat x)      (VFloat y)      | x == y = return $ VFloat x
muxBVal _  _ (VDouble x)     (VDouble y)     | x == y = return $ VDouble y
muxBVal _  _ VType           VType           = return VType
muxBVal be b (VExtra x)      (VExtra y)      = VExtra <$> muxBExtra be b x y
muxBVal be b x@(VExtra (BWord _)) y         =
  muxBVal be b (VVector (vectorOfBValue x)) y
muxBVal be b x y@(VExtra (BWord _))         =
  muxBVal be b x (VVector (vectorOfBValue y))
muxBVal _ _ x y =
  fail $ "iteOp: malformed arguments: " ++ show x ++ " " ++ show y

muxThunks :: AIG.IsAIG l g => g s -> l s
          -> V.Vector (BThunk (l s)) -> V.Vector (BThunk (l s)) -> IO (V.Vector (BThunk (l s)))
muxThunks be b xv yv
  | V.length xv == V.length yv = V.zipWithM (muxThunk be b) xv yv
  | otherwise                  = fail "iteOp: malformed arguments"

muxThunk :: AIG.IsAIG l g => g s -> l s -> BThunk (l s) -> BThunk (l s) -> IO (BThunk (l s))
muxThunk be b x y = delay $ do x' <- force x; y' <- force y; muxBVal be b x' y'

muxBExtra :: AIG.IsAIG l g => g s -> l s -> BExtra (l s) -> BExtra (l s) -> IO (BExtra (l s))
muxBExtra be b (BBool x) (BBool y) = BBool <$> AIG.mux be b x y
muxBExtra be b (BWord x) (BWord y) | AIG.length x == AIG.length y = BWord <$> AIG.zipWithM (AIG.mux be b) x y
muxBExtra _ _ _ _ = fail "iteOp: malformed arguments"

-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
getOp :: BValue l
getOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  Prims.finFun $ \i ->
    case v of
      VVector xv -> force ((V.!) xv (fromEnum (finVal i)))
      VExtra (BWord lv) -> return (vBool (AIG.at lv (fromEnum (finVal i))))
      _ -> fail "getOp: expected vector"

-- at :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a;
atOp :: BValue l
atOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  Prims.natFun $ \n ->
    case v of
      VVector xv -> force ((V.!) xv (fromIntegral n))
      VExtra (BWord lv) -> return $ vBool $ AIG.at lv (fromIntegral n)
      _ -> fail "atOp: expected vector"

-- bvAt :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> a;
bvAtOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvAtOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  wordFun $ \ilv ->
    case v of
      VVector xv ->
          force =<< AIG.muxInteger (lazyMux be (muxThunk be)) (V.length xv - 1) ilv (return . (V.!) xv)
      VExtra (BWord lv) ->
          vBool <$> AIG.muxInteger (lazyMux be (AIG.mux be)) (AIG.length lv - 1) ilv (return . AIG.at lv)
      _ -> fail "bvAtOp: expected vector"

-- bvUpd :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> a -> Vec n a;
-- NB: this isn't necessarily the most efficient possible implementation.
bvUpdOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvUpdOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  wordFun $ \ilv -> return $
  strictFun $ \y ->
    case v of
      VVector xv -> do
        y' <- delay (return y)
        let upd i = return (VVector (xv V.// [(i, y')]))
        AIG.muxInteger (lazyMux be (muxBVal be)) (V.length xv - 1) ilv upd
      VExtra (BWord lv) -> do
        AIG.muxInteger (lazyMux be (muxBVal be)) (l - 1) ilv (\i -> return (vWord (AIG.generate_msb0 l (upd i))))
          where upd i j | i == j    = toBool y
                        | otherwise = AIG.at lv j
                l = AIG.length lv
      _ -> fail "bvUpdOp: expected vector"

-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: BValue l
appendOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  case (xs, ys) of
    (VVector xv, VVector yv)         -> VVector ((V.++) xv yv)
    (VVector xv, VExtra (BWord ylv)) -> VVector ((V.++) xv (fmap (Ready . vBool) (vFromLV ylv)))
    (VExtra (BWord xlv), VVector yv) -> VVector ((V.++) (fmap (Ready . vBool) (vFromLV xlv)) yv)
    (VExtra (BWord xlv), VExtra (BWord ylv)) -> vWord ((AIG.++) xlv ylv)
    _ -> error "appendOp"

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: BValue l
vZipOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  VVector (V.zipWith (\x y -> Ready (VTuple (V.fromList [x, y]))) (vectorOfBValue xs) (vectorOfBValue ys))

vectorOfBValue :: BValue l -> V.Vector (BThunk l)
vectorOfBValue (VVector xv) = xv
vectorOfBValue (VExtra (BWord lv)) = fmap (Ready . vBool) (vFromLV lv)
vectorOfBValue _ = error "vectorOfBValue"

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: BValue l
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

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNatOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvNatOp be =
  Prims.natFun $ \w -> return $
  Prims.natFun $ \x -> return $
  VExtra (BWord (AIG.bvFromInteger be (fromIntegral w) (toInteger x)))

-- bvRotateL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateLOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvRotateLOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    let (n, f) = case xs of
                   VVector xv         -> (V.length xv, VVector . vRotateL xv)
                   VExtra (BWord xlv) -> (AIG.length xlv, VExtra . BWord . lvRotateL xlv)
                   _ -> error $ "rotateROp: " ++ show xs
    r <- AIG.urem be ilv (AIG.bvFromInteger be (AIG.length ilv) (toInteger n))
    AIG.muxInteger (lazyMux be (muxBVal be)) (n - 1) r (return . f)

-- bvRotateR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> Vec n a -> bitvector w -> Vec n a;
bvRotateROp :: AIG.IsAIG l g => g s -> BValue (l s)
bvRotateROp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    let (n, f) = case xs of
                   VVector xv         -> (V.length xv, VVector . vRotateR xv)
                   VExtra (BWord xlv) -> (AIG.length xlv, VExtra . BWord . lvRotateR xlv)
                   _ -> error $ "rotateROp: " ++ show xs
    r <- AIG.urem be ilv (AIG.bvFromInteger be (AIG.length ilv) (toInteger n))
    AIG.muxInteger (lazyMux be (muxBVal be)) (n - 1) r (return . f)

-- bvShiftL :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftLOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvShiftLOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    (n, f) <- case xs of
                VVector xv         -> return (V.length xv, VVector . vShiftL x xv)
                VExtra (BWord xlv) -> do l <- toBool <$> force x
                                         return (AIG.length xlv, VExtra . BWord . lvShiftL l xlv)
                _ -> fail $ "bvShiftLOp: " ++ show xs
    AIG.muxInteger (lazyMux be (muxBVal be)) n ilv (return . f)

-- bvShiftR :: (n :: Nat) -> (a :: sort 0) -> (w :: Nat) -> a -> Vec n a -> bitvector w -> Vec n a;
bvShiftROp :: AIG.IsAIG l g => g s -> BValue (l s)
bvShiftROp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  wordFun $ \ilv -> do
    (n, f) <- case xs of
                VVector xv         -> return (V.length xv, VVector . vShiftR x xv)
                VExtra (BWord xlv) -> do l <- toBool <$> force x
                                         return (AIG.length xlv, VExtra . BWord . lvShiftR l xlv)
                _ -> fail $ "bvShiftROp: " ++ show xs
    AIG.muxInteger (lazyMux be (muxBVal be)) n ilv (return . f)

----------------------------------------
-- Polynomial operations

-- bvPMod :: (m n :: Nat) -> bitvector m -> bitvector (Succ n) -> bitvector n;
bvPModOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvPModOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> AIG.pmod be x y

-- bvPMul :: (m n :: Nat) -> bitvector m -> bitvector n -> bitvector _;
bvPMulOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvPMulOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> AIG.pmul be x y

-- TODO: Move polynomial operations to aig package.

-- Polynomial div/mod: resulting lengths are as in Cryptol.
pdivmod :: forall l g s. AIG.IsAIG l g => g s -> BV (l s) -> BV (l s) -> IO (BV (l s), BV (l s))
pdivmod g x y = findmsb (AIG.bvToList y)
  where
    findmsb :: [l s] -> IO (BV (l s), BV (l s))
    findmsb (c : cs) = lazyMux g muxPair c (usemask cs) (findmsb cs)
    findmsb [] = return (x, AIG.replicate (AIG.length y - 1) (AIG.falseLit g)) -- division by zero

    usemask :: [l s] -> IO (BV (l s), BV (l s))
    usemask mask = do
      (qs, rs) <- pdivmod_helper g (AIG.bvToList x) mask
      let z = AIG.falseLit g
      let qs' = map (const z) rs ++ qs
      let rs' = replicate (AIG.length y - 1 - length rs) z ++ rs
      let q = AIG.concat (map (AIG.replicate 1) qs')
      let r = AIG.concat (map (AIG.replicate 1) rs')
      return (q, r)

    muxPair :: l s -> (BV (l s), BV (l s)) -> (BV (l s), BV (l s)) -> IO (BV (l s), BV (l s))
    muxPair c (x1, y1) (x2, y2) = (,) <$> AIG.zipWithM (AIG.mux g c) x1 x2 <*> AIG.zipWithM (AIG.mux g c) y1 y2

-- Divide ds by (1 : mask), giving quotient and remainder. All
-- arguments and results are big-endian. Remainder has the same length
-- as mask (but limited by length ds); total length of quotient ++
-- remainder = length ds.
pdivmod_helper :: forall l g s. AIG.IsAIG l g => g s -> [l s] -> [l s] -> IO ([l s], [l s])
pdivmod_helper g ds mask = go (length ds - length mask) ds
  where
    go :: Int -> [l s] -> IO ([l s], [l s])
    go n cs | n <= 0 = return ([], cs)
    go _ []          = fail "pdivmod: impossible"
    go n (c : cs)    = do cs' <- mux_add c cs mask
                          (qs, rs) <- go (n - 1) cs'
                          return (c : qs, rs)

    mux_add :: l s -> [l s] -> [l s] -> IO [l s]
    mux_add c (x : xs) (y : ys) = do z <- lazyMux g (AIG.mux g) c (AIG.xor g x y) (return x)
                                     zs <- mux_add c xs ys
                                     return (z : zs)
    mux_add _ []       (_ : _ ) = fail "pdivmod: impossible"
    mux_add _ xs       []       = return xs

----------------------------------------

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: BValue l
mkStreamOp =
  VFun $ \_ -> return $
  strictFun $ \f -> do
    r <- newIORef Map.empty
    return $ VExtra (BStream (\n -> apply f (Ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: BValue l
streamGetOp =
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  Prims.natFun $ \n -> lookupBStream xs (toInteger n)

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvStreamGetOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
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
lookupBStream _ _ = fail "expected Stream"

------------------------------------------------------------
-- Generating variables for arguments

data BShape
  = BoolShape
  | VecShape Nat BShape
  | TupleShape [BShape]
  | RecShape (Map FieldName BShape)

shapeSize :: BShape -> Int
shapeSize x =
  case x of
    BoolShape     -> 1
    VecShape n x1 -> fromIntegral n * shapeSize x1
    TupleShape xs -> sum (map shapeSize xs)
    RecShape xm   -> sum (map shapeSize (Map.elems xm))

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

newVars :: AIG.IsAIG l g => g s -> BShape -> IO (BValue (l s))
newVars be BoolShape = vBool <$> AIG.newInput be
newVars be (VecShape n tp) = VVector <$> V.replicateM (fromIntegral n) (newVars' be tp)
newVars be (TupleShape ts) = VTuple <$> traverse (newVars' be) (V.fromList ts)
newVars be (RecShape tm) = VRecord <$> traverse (newVars' be) tm

newVars' :: AIG.IsAIG l g => g s -> BShape -> IO (BThunk (l s))
newVars' be shape = Ready <$> newVars be shape

------------------------------------------------------------
-- Bit-blasting predicates

bitBlastBasic :: AIG.IsAIG l g => g s -> Module -> SharedTerm t -> IO (BValue (l s))
bitBlastBasic be m = Sim.evalSharedTerm cfg
  where cfg = Sim.evalGlobal m (beConstMap be) (const Nothing)

asPredType :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "non-boolean result type: " ++ show t'

bitBlast :: AIG.IsAIG l g =>
            g s -> SharedContext t -> SharedTerm t -> IO ([BShape], l s)
bitBlast be sc t = do
  ty <- scTypeOf sc t
  argTs <- asPredType sc ty
  shapes <- traverse (parseShape sc) argTs
  vars <- traverse (newVars' be) shapes
  bval <- bitBlastBasic be (scModule sc) t
  bval' <- applyAll bval vars
  case bval' of
    VExtra (BBool l) -> return (shapes, l)
    _ -> fail "bitBlast: non-boolean result type."
