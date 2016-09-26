{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Verifier.SAW.Simulator.Prims
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.Prims where

import Prelude hiding (sequence, mapM)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad (foldM, liftM)
import Data.Bits
import Data.Traversable
import qualified Data.Vector as V

import Verifier.SAW.Simulator.Value
import Verifier.SAW.Prim

------------------------------------------------------------
-- Value accessors and constructors

vNat :: Nat -> Value m b w i e
vNat n = VNat (fromIntegral n)

natFromValue :: Num a => Value m b w i e -> a
natFromValue (VNat n) = fromInteger n
natFromValue _ = error "natFromValue"

natFun'' :: (Monad m, Show e) => String -> (Nat -> m (Value m b w i e)) -> Value m b w i e
natFun'' s f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g v = fail $ "expected Nat (" ++ s ++ "): " ++ show v

natFun' :: Monad m => String -> (Nat -> m (Value m b w i e)) -> Value m b w i e
natFun' s f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g _ = fail $ "expected Nat: " ++ s

natFun :: Monad m => (Nat -> m (Value m b w i e)) -> Value m b w i e
natFun f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g _ = fail "expected Nat"

intFun :: Monad m => String -> (i -> m (Value m b w i e)) -> Value m b w i e
intFun msg f = strictFun g
  where g (VInt i) = f i
        g _ = fail $ "expected Integer "++ msg

toBool :: Show e => Value m b w i e -> b
toBool (VBool b) = b
toBool x = error $ unwords ["Verifier.SAW.Simulator.toBool", show x]

toWord :: (Monad m, Show e) => (V.Vector b -> w) -> Value m b w i e -> m w
toWord _ (VWord w) = return w
toWord pack (VVector vv) = liftM pack $ V.mapM (liftM toBool . force) vv
toWord _ x = fail $ unwords ["Verifier.SAW.Simulator.toWord", show x]

toBits :: (Monad m, Show e) => (w -> V.Vector b) -> Value m b w i e -> m (V.Vector b)
toBits unpack (VWord w) = return (unpack w)
toBits _ (VVector v) = V.mapM (liftM toBool . force) v
toBits _ x = fail $ unwords ["Verifier.SAW.Simulator.toBits", show x]

toVector :: (Monad m, Show e) => (w -> V.Vector b)
         -> Value m b w i e -> V.Vector (Thunk m b w i e)
toVector _ (VVector v) = v
toVector unpack (VWord w) = fmap (ready . VBool) (unpack w)
toVector _ x = fail $ unwords ["Verifier.SAW.Simulator.toVector", show x]

wordFun :: (Monad m, Show e) => (V.Vector b -> w) -> (w -> m (Value m b w i e)) -> Value m b w i e
wordFun pack f = strictFun (\x -> toWord pack x >>= f)

bitsFun :: (Monad m, Show e) => (w -> V.Vector b)
        -> (V.Vector b -> m (Value m b w i e)) -> Value m b w i e
bitsFun unpack f = strictFun (\x -> toBits unpack x >>= f)

vectorFun :: (Monad m, Show e) => (w -> V.Vector b)
          -> (V.Vector (Thunk m b w i e) -> m (Value m b w i e)) -> Value m b w i e
vectorFun unpack f = strictFun (\x -> f (toVector unpack x))

vecIdx :: a -> V.Vector a -> Int -> a
vecIdx err v n =
  case (V.!?) v n of
    Just a -> a
    Nothing -> err

------------------------------------------------------------
-- Utility functions

-- @selectV mux maxValue valueFn v@ treats the vector @v@ as an
-- index, represented as a big-endian list of bits. It does a binary
-- lookup, using @mux@ as an if-then-else operator. If the index is
-- greater than @maxValue@, then it returns @valueFn maxValue@.
selectV :: (b -> a -> a -> a) -> Int -> (Int -> a) -> V.Vector b -> a
selectV mux maxValue valueFn v = impl len 0
  where
    len = V.length v
    err = error "selectV: impossible"
    impl _ x | x >= maxValue || x < 0 = valueFn maxValue
    impl 0 x = valueFn x
    impl i x = mux (vecIdx err v (len - i)) (impl j (x `setBit` j)) (impl j x) where j = i - 1

------------------------------------------------------------
-- Values for common primitives

-- bvToNat :: (n :: Nat) -> bitvector n -> Nat;
bvToNatOp :: Monad m => Value m b w i e
bvToNatOp = constFun $ pureFun VToNat

-- coerce :: (a b :: sort 0) -> Eq (sort 0) a b -> a -> b;
coerceOp :: Monad m => Value m b w i e
coerceOp =
  constFun $
  constFun $
  constFun $
  VFun force

-- Succ :: Nat -> Nat;
succOp :: Monad m => Value m b w i e
succOp =
  natFun' "Succ" $ \n -> return $
  vNat (succ n)

-- addNat :: Nat -> Nat -> Nat;
addNatOp :: Monad m => Value m b w i e
addNatOp =
  natFun' "addNat1" $ \m -> return $
  natFun' "addNat2" $ \n -> return $
  vNat (m + n)

-- subNat :: Nat -> Nat -> Nat;
subNatOp :: Monad m => Value m b w i e
subNatOp =
  natFun' "subNat1" $ \m -> return $
  natFun' "subNat2" $ \n -> return $
  vNat (if m < n then 0 else m - n)

-- mulNat :: Nat -> Nat -> Nat;
mulNatOp :: Monad m => Value m b w i e
mulNatOp =
  natFun' "mulNat1" $ \m -> return $
  natFun' "mulNat2" $ \n -> return $
  vNat (m * n)

-- minNat :: Nat -> Nat -> Nat;
minNatOp :: Monad m => Value m b w i e
minNatOp =
  natFun' "minNat1" $ \m -> return $
  natFun' "minNat2" $ \n -> return $
  vNat (min m n)

-- maxNat :: Nat -> Nat -> Nat;
maxNatOp :: Monad m => Value m b w i e
maxNatOp =
  natFun' "maxNat1" $ \m -> return $
  natFun' "maxNat2" $ \n -> return $
  vNat (max m n)

-- equalNat :: Nat -> Nat -> Bool;
equalNat :: Monad m => (Bool -> m b) -> Value m b w i e
equalNat lit =
  natFun' "equalNat1" $ \m -> return $
  natFun' "equalNat2" $ \n ->
  lit (m == n) >>= return . VBool

-- equalNat :: Nat -> Nat -> Bool;
ltNat :: Monad m => (Bool -> m b) -> Value m b w i e
ltNat lit =
  natFun' "ltNat1" $ \m -> return $
  natFun' "ltNat2" $ \n ->
  lit (m < n) >>= return . VBool

-- divModNat :: Nat -> Nat -> #(Nat, Nat);
divModNatOp :: Monad m => Value m b w i e
divModNatOp =
  natFun' "divModNat1" $ \m -> return $
  natFun' "divModNat2" $ \n -> return $
    let (q,r) = divMod m n in
    vTuple [ready $ vNat q, ready $ vNat r]

-- expNat :: Nat -> Nat -> Nat;
expNatOp :: Monad m => Value m b w i e
expNatOp =
  natFun' "expNat1" $ \m -> return $
  natFun' "expNat2" $ \n -> return $
  vNat (m ^ n)

-- widthNat :: Nat -> Nat;
widthNatOp :: Monad m => Value m b w i e
widthNatOp =
  natFun' "widthNat1" $ \n -> return $
  vNat (widthNat n)

-- natCase :: (p :: Nat -> sort 0) -> p Zero -> ((n :: Nat) -> p (Succ n)) -> (n :: Nat) -> p n;
natCaseOp :: Monad m => Value m b w i e
natCaseOp =
  constFun $
  VFun $ \z -> return $
  VFun $ \s -> return $
  natFun' "natCase" $ \n ->
    if n == 0
    then force z
    else do s' <- force s
            apply s' (ready (VNat (fromIntegral n - 1)))

-- gen :: (n :: Nat) -> (a :: sort 0) -> (Nat -> a) -> Vec n a;
genOp :: MonadLazy m => Value m b w i e
genOp =
  natFun' "gen1" $ \n -> return $
  constFun $
  strictFun $ \f -> do
    let g i = delay $ apply f (ready (VNat (fromIntegral i)))
    liftM VVector $ V.generateM (fromIntegral n) g

-- eq :: (a :: sort 0) -> a -> a -> Bool
eqOp :: (MonadLazy m, Show e) => Value m b w i e
     -> (Value m b w i e -> Value m b w i e -> m (Value m b w i e))
     -> (Value m b w i e -> Value m b w i e -> m (Value m b w i e))
     -> (Integer -> Value m b w i e -> Value m b w i e -> m (Value m b w i e))
     -> (Value m b w i e -> Value m b w i e -> m (Value m b w i e))
     -> Value m b w i e
eqOp trueOp andOp boolOp bvOp intOp =
  pureFun $ \t -> pureFun $ \v1 -> strictFun $ \v2 -> go t v1 v2
  where
    go VUnitType VUnit VUnit = return trueOp
    go (VPairType t1 t2) (VPair x1 x2) (VPair y1 y2) = do
      b1 <- go' t1 x1 y1
      b2 <- go' t2 x2 y2
      andOp b1 b2
    go VEmptyType VEmpty VEmpty = return trueOp
    go (VFieldType f t1 t2) (VField xf x1 x2) (VField yf y1 y2)
      | f == xf && f == yf = do
        b1 <- go' t1 x1 y1
        b2 <- go t2 x2 y2
        andOp b1 b2
    go (VDataType "Prelude.Vec" [VNat n, VDataType "Prelude.Bool" []]) v1 v2 = bvOp n v1 v2
    go (VDataType "Prelude.Vec" [_, t']) (VVector vv1) (VVector vv2) = do
      bs <- sequence $ zipWith (go' t') (V.toList vv1) (V.toList vv2)
      foldM andOp trueOp bs
    go (VDataType "Prelude.Bool" []) v1 v2 = boolOp v1 v2
    go (VDataType "Prelude.Integer" []) v1 v2 = intOp v1 v2
    go t _ _ = fail $ "binary: invalid arguments: " ++ show t

    go' t thunk1 thunk2 = do
      v1 <- force thunk1
      v2 <- force thunk2
      go t v1 v2

-- atWithDefault :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> a;
atWithDefaultOp :: (Monad m, Show e) => (w -> V.Vector b) -> (w -> Int -> b)
     -> (b -> m (Value m b w i e) -> m (Value m b w i e) -> m (Value m b w i e))
     -> Value m b w i e
atWithDefaultOp unpack bvOp mux =
  natFun $ \n -> return $
  constFun $
  VFun $ \d -> return $
  strictFun $ \x -> return $
  strictFun $ \idx ->
    case idx of
      VNat i ->
        case x of
          VVector xv -> force (vecIdx d xv (fromIntegral i))
          VWord xw -> return $ VBool $ bvOp xw (fromIntegral i)
          _ -> fail "atOp: expected vector"
      VToNat i -> do
        iv <- toBits unpack i
        case x of
          VVector xv ->
            selectV mux (fromIntegral n - 1) (force . vecIdx d xv) iv
          VWord xw ->
            selectV mux (fromIntegral n - 1) (return . VBool . bvOp xw) iv
          _ -> fail "atOp: expected vector"
      _ -> fail $ "atOp: expected Nat, got " ++ show idx

-- upd :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a -> Vec n a;
updOp :: (MonadLazy m, Show e) => (w -> V.Vector b)
      -> (w -> w -> m b) -> (Int -> Integer -> w) -> (w -> Int)
      -> (b -> m (Value m b w i e) -> m (Value m b w i e) -> m (Value m b w i e))
      -> Value m b w i e
updOp unpack eq lit bitsize mux =
  natFun $ \n -> return $
  constFun $
  vectorFun unpack $ \xv -> return $
  strictFun $ \idx -> return $
  VFun $ \y ->
    case idx of
      VNat i -> return (VVector (xv V.// [(fromIntegral i, y)]))
      VToNat (VWord w) -> do
        let f i = do b <- eq w (lit (bitsize w) (toInteger i))
                     err <- delay (fail "updOp")
                     delay (mux b (force y) (force (vecIdx err xv i)))
        yv <- V.generateM (V.length xv) f
        return (VVector yv)
      VToNat val -> do
        let update i = return (VVector (xv V.// [(i, y)]))
        iv <- toBits unpack val
        selectV mux (fromIntegral n - 1) update iv
      _ -> fail $ "updOp: expected Nat, got " ++ show idx



-- primitive EmptyVec :: (a :: sort 0) -> Vec 0 a;
emptyVec :: Monad m => Value m b w i e
emptyVec = constFun $ VVector V.empty


-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: Monad m => (w -> V.Vector b) -> (w -> w -> w) -> Value m b w i e
appendOp unpack app =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  appV unpack app xs ys

appV :: Monad m => (w -> V.Vector b) -> (w -> w -> w)
     -> Value m b w i e -> Value m b w i e -> Value m b w i e
appV unpack app xs ys =
  case (xs, ys) of
    (VVector xv, _) | V.null xv -> ys
    (_, VVector yv) | V.null yv -> xs
    (VVector xv, VVector yv) -> VVector ((V.++) xv yv)
    (VVector xv, VWord yw) -> VVector ((V.++) xv (fmap (ready . VBool) (unpack yw)))
    (VWord xw, VVector yv) -> VVector ((V.++) (fmap (ready . VBool) (unpack xw)) yv)
    (VWord xw, VWord yw) -> VWord (app xw yw)
    _ -> error "Verifier.SAW.Simulator.Prims.appendOp"

-- join  :: (m n :: Nat) -> (a :: sort 0) -> Vec m (Vec n a) -> Vec (mulNat m n) a;
joinOp :: Monad m => (w -> V.Vector b) -> (w -> w -> w) -> Value m b w i e
joinOp unpack app =
  constFun $
  constFun $
  constFun $
  strictFun $ \x ->
  case x of
    VVector xv -> do
      vv <- V.mapM force xv
      return (V.foldr (appV unpack app) (VVector V.empty) vv)
    _ -> error "Verifier.SAW.Simulator.Prims.joinOp"


intUnOp :: Monad m => String -> (i -> i) -> Value m b w i e
intUnOp nm f =
  intFun nm $ \x -> return $
    VInt (f x)

intBinOp :: Monad m => String -> (i -> i -> i) -> Value m b w i e
intBinOp nm f =
  intFun (nm++" x") $ \x -> return $
  intFun (nm++" y") $ \y -> return $
    VInt (f x y)

intBinCmp :: Monad m => String -> (i -> i -> a) -> (a -> b) -> Value m b w i e
intBinCmp nm f boolLit =
  intFun (nm++" x") $ \x -> return $
  intFun (nm++" y") $ \y -> return $
    VBool $ boolLit (f x y)

-- primitive intAdd :: Integer -> Integer -> Integer;
intAddOp :: Monad m => Value m b w Integer e
intAddOp = intBinOp "intAdd" (+)

-- primitive intSub :: Integer -> Integer -> Integer;
intSubOp :: Monad m => Value m b w Integer e
intSubOp = intBinOp "intSub" (-)

-- primitive intMul :: Integer -> Integer -> Integer;
intMulOp :: Monad m => Value m b w Integer e
intMulOp = intBinOp "intMul" (*)

-- primitive intDiv :: Integer -> Integer -> Integer;
intDivOp :: Monad m => Value m b w Integer e
intDivOp = intBinOp "intDiv" div

-- primitive intMod :: Integer -> Integer -> Integer;
intModOp :: Monad m => Value m b w Integer e
intModOp = intBinOp "intMod" mod

-- primitive intMin :: Integer -> Integer -> Integer;
intMinOp :: Monad m => Value m b w Integer e
intMinOp = intBinOp "intMin" min

-- primitive intMax :: Integer -> Integer -> Integer;
intMaxOp :: Monad m => Value m b w Integer e
intMaxOp = intBinOp "intMax" max

-- primitive intNeg :: Integer -> Integer;
intNegOp :: Monad m => Value m b w Integer e
intNegOp = intUnOp "intNeg x" negate

-- primitive intEq  :: Integer -> Integer -> Bool;
intEqOp :: Monad m => (Bool -> b) -> Value m b w Integer e
intEqOp = intBinCmp "intEq" (==)

-- primitive intLe  :: Integer -> Integer -> Bool;
intLeOp :: Monad m => (Bool -> b) -> Value m b w Integer e
intLeOp = intBinCmp "intLe" (<=)

-- primitive intLt  :: Integer -> Integer -> Bool;
intLtOp :: Monad m => (Bool -> b) -> Value m b w Integer e
intLtOp = intBinCmp "intLt" (<)

-- primitive intToNat :: Integer -> Nat;
intToNatOp :: Monad m => Value m b w Integer e
intToNatOp =
  intFun "intToNat" $ \x -> return $!
    if x >= 0 then VNat x else VNat 0

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: Monad m => Value m b w Integer e
natToIntOp = natFun' "natToInt" $ \x -> return $ VInt (fromIntegral x)

-- primitive bvLg2 :: (n :: Nat) -> bitvector n -> bitvector n;
bvLg2Op :: Monad m => (Value m b w i e -> m w) -> (w -> m w) -> Value m b w i e
bvLg2Op asWord wordLg2 =
  natFun' "bvLg2 1" $ \_n -> return $
  strictFun $ \w -> (return . VWord) =<< (wordLg2 =<< asWord w)

-- primitive error :: (a :: sort 0) -> String -> a;
errorOp :: Monad m => Value m b w i e
errorOp =
  constFun $
  strictFun $ \x ->
  case x of
    VString s -> fail s
    _ -> fail "unknown error"

muxValue :: forall m b w i e. (MonadLazy m, Applicative m, Show e) =>
            (w -> V.Vector b)
         -> (b -> b -> b -> m b)
         -> (b -> w -> w -> m w)
         -> (b -> i -> i -> m i)
         -> (b -> e -> e -> m e)
         -> b -> Value m b w i e -> Value m b w i e -> m (Value m b w i e)
muxValue unpack bool word int extra b = value
  where
    value :: Value m b w i e -> Value m b w i e -> m (Value m b w i e)
    value (VFun f)          (VFun g)          = return $ VFun $ \a -> do
                                                  x <- f a
                                                  y <- g a
                                                  value x y
    value VUnit             VUnit             = return VUnit
    value (VPair x1 x2)     (VPair y1 y2)     = VPair <$> thunk x1 y1 <*> thunk x2 y2
    value VEmpty            VEmpty            = return VEmpty
    value (VField xf x1 x2) (VField yf y1 y2) | xf == yf
                                              = VField xf <$> thunk x1 y1 <*> value x2 y2
    value (VCtorApp i xv)   (VCtorApp j yv)   | i == j = VCtorApp i <$> thunks xv yv
    value (VVector xv)      (VVector yv)      = VVector <$> thunks xv yv
    value (VBool x)         (VBool y)         = VBool <$> bool b x y
    value (VWord x)         (VWord y)         = VWord <$> word b x y
    value (VInt x)          (VInt y)          = VInt <$> int b x y
    value (VNat m)          (VNat n)          | m == n = return $ VNat m
    value (VString x)       (VString y)       | x == y = return $ VString x
    value (VFloat x)        (VFloat y)        | x == y = return $ VFloat x
    value (VDouble x)       (VDouble y)       | x == y = return $ VDouble y
    value VType             VType             = return VType
    value (VExtra x)        (VExtra y)        = VExtra <$> extra b x y
    value x@(VWord _)       y                 = value (VVector (toVector unpack x)) y
    value x                 y@(VWord _)       = value x (VVector (toVector unpack y))
    value x                 y                 =
      fail $ "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments: "
      ++ show x ++ " " ++ show y

    thunks :: V.Vector (Thunk m b w i e) -> V.Vector (Thunk m b w i e) -> m (V.Vector (Thunk m b w i e))
    thunks xv yv
      | V.length xv == V.length yv = V.zipWithM thunk xv yv
      | otherwise                  = fail "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments"

    thunk :: Thunk m b w i e -> Thunk m b w i e -> m (Thunk m b w i e)
    thunk x y = delay $ do x' <- force x; y' <- force y; value x' y'
