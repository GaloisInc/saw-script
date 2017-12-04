{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

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
import Control.Monad.Fix (MonadFix(mfix))
import Data.Bits
import Data.Traversable
import qualified Data.Vector as V

import Verifier.SAW.Simulator.Value
import Verifier.SAW.Prim

------------------------------------------------------------
-- Value accessors and constructors

vNat :: Nat -> Value l
vNat n = VNat (fromIntegral n)

natFromValue :: Num a => Value l -> a
natFromValue (VNat n) = fromInteger n
natFromValue _ = error "natFromValue"

natFun'' :: (VMonad l, Show (Extra l)) => String -> (Nat -> MValue l) -> Value l
natFun'' s f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g v = fail $ "expected Nat (" ++ s ++ "): " ++ show v

natFun' :: VMonad l => String -> (Nat -> MValue l) -> Value l
natFun' s f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g _ = fail $ "expected Nat: " ++ s

natFun :: VMonad l => (Nat -> MValue l) -> Value l
natFun f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g _ = fail "expected Nat"

intFun :: VMonad l => String -> (VInt l -> MValue l) -> Value l
intFun msg f = strictFun g
  where g (VInt i) = f i
        g _ = fail $ "expected Integer "++ msg

toBool :: Show (Extra l) => Value l -> VBool l
toBool (VBool b) = b
toBool x = error $ unwords ["Verifier.SAW.Simulator.toBool", show x]

type Pack l   = V.Vector (VBool l) -> MWord l
type Unpack l = VWord l -> EvalM l (V.Vector (VBool l))

toWord :: (VMonad l, Show (Extra l)) => Pack l -> Value l -> MWord l
toWord _ (VWord w) = return w
toWord pack (VVector vv) = pack =<< V.mapM (liftM toBool . force) vv
toWord _ x = fail $ unwords ["Verifier.SAW.Simulator.toWord", show x]

toBits :: (VMonad l, Show (Extra l)) => Unpack l -> Value l ->
                                                  EvalM l (V.Vector (VBool l))
toBits unpack (VWord w) = unpack w
toBits _ (VVector v) = V.mapM (liftM toBool . force) v
toBits _ x = fail $ unwords ["Verifier.SAW.Simulator.toBits", show x]

toVector :: (VMonad l, Show (Extra l)) => Unpack l
         -> Value l -> EvalM l (V.Vector (Thunk l))
toVector _ (VVector v) = return v
toVector unpack (VWord w) = liftM (fmap (ready . VBool)) (unpack w)
toVector _ x = fail $ unwords ["Verifier.SAW.Simulator.toVector", show x]

wordFun :: (VMonad l, Show (Extra l)) => Pack l -> (VWord l -> MValue l) -> Value l
wordFun pack f = strictFun (\x -> toWord pack x >>= f)

bitsFun :: (VMonad l, Show (Extra l)) =>
  Unpack l -> (V.Vector (VBool l) -> MValue l) -> Value l
bitsFun unpack f = strictFun (\x -> toBits unpack x >>= f)

vectorFun :: (VMonad l, Show (Extra l)) =>
  Unpack l -> (V.Vector (Thunk l) -> MValue l) -> Value l
vectorFun unpack f = strictFun (\x -> toVector unpack x >>= f)

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
    impl _ x | x > maxValue || x < 0 = valueFn maxValue
    impl 0 x = valueFn x
    impl i x = mux (vecIdx err v (len - i)) (impl j (x `setBit` j)) (impl j x) where j = i - 1

------------------------------------------------------------
-- Values for common primitives

-- bvToNat :: (n :: Nat) -> bitvector n -> Nat;
bvToNatOp :: VMonad l => Value l
bvToNatOp = constFun $ pureFun VToNat

-- coerce :: (a b :: sort 0) -> Eq (sort 0) a b -> a -> b;
coerceOp :: VMonad l => Value l
coerceOp =
  constFun $
  constFun $
  constFun $
  VFun force

-- Succ :: Nat -> Nat;
succOp :: VMonad l => Value l
succOp =
  natFun' "Succ" $ \n -> return $
  vNat (succ n)

-- addNat :: Nat -> Nat -> Nat;
addNatOp :: VMonad l => Value l
addNatOp =
  natFun' "addNat1" $ \m -> return $
  natFun' "addNat2" $ \n -> return $
  vNat (m + n)

-- subNat :: Nat -> Nat -> Nat;
subNatOp :: VMonad l => Value l
subNatOp =
  natFun' "subNat1" $ \m -> return $
  natFun' "subNat2" $ \n -> return $
  vNat (if m < n then 0 else m - n)

-- mulNat :: Nat -> Nat -> Nat;
mulNatOp :: VMonad l => Value l
mulNatOp =
  natFun' "mulNat1" $ \m -> return $
  natFun' "mulNat2" $ \n -> return $
  vNat (m * n)

-- minNat :: Nat -> Nat -> Nat;
minNatOp :: VMonad l => Value l
minNatOp =
  natFun' "minNat1" $ \m -> return $
  natFun' "minNat2" $ \n -> return $
  vNat (min m n)

-- maxNat :: Nat -> Nat -> Nat;
maxNatOp :: VMonad l => Value l
maxNatOp =
  natFun' "maxNat1" $ \m -> return $
  natFun' "maxNat2" $ \n -> return $
  vNat (max m n)

-- equalNat :: Nat -> Nat -> Bool;
equalNat :: VMonad l => (Bool -> MBool l) -> Value l
equalNat lit =
  natFun' "equalNat1" $ \m -> return $
  natFun' "equalNat2" $ \n ->
  lit (m == n) >>= return . VBool

-- equalNat :: Nat -> Nat -> Bool;
ltNat :: VMonad l => (Bool -> MBool l) -> Value l
ltNat lit =
  natFun' "ltNat1" $ \m -> return $
  natFun' "ltNat2" $ \n ->
  lit (m < n) >>= return . VBool

-- divModNat :: Nat -> Nat -> #(Nat, Nat);
divModNatOp :: VMonad l => Value l
divModNatOp =
  natFun' "divModNat1" $ \m -> return $
  natFun' "divModNat2" $ \n -> return $
    let (q,r) = divMod m n in
    vTuple [ready $ vNat q, ready $ vNat r]

-- expNat :: Nat -> Nat -> Nat;
expNatOp :: VMonad l => Value l
expNatOp =
  natFun' "expNat1" $ \m -> return $
  natFun' "expNat2" $ \n -> return $
  vNat (m ^ n)

-- widthNat :: Nat -> Nat;
widthNatOp :: VMonad l => Value l
widthNatOp =
  natFun' "widthNat1" $ \n -> return $
  vNat (widthNat n)

-- natCase :: (p :: Nat -> sort 0) -> p Zero -> ((n :: Nat) -> p (Succ n)) -> (n :: Nat) -> p n;
natCaseOp :: VMonad l => Value l
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
genOp :: VMonadLazy l => Value l
genOp =
  natFun' "gen1" $ \n -> return $
  constFun $
  strictFun $ \f -> do
    let g i = delay $ apply f (ready (VNat (fromIntegral i)))
    liftM VVector $ V.generateM (fromIntegral n) g

-- eq :: (a :: sort 0) -> a -> a -> Bool
eqOp :: (VMonadLazy l, Show (Extra l)) => Value l
     -> (Value l -> Value l -> MValue l)
     -> (Value l -> Value l -> MValue l)
     -> (Integer -> Value l -> Value l -> MValue l)
     -> (Value l -> Value l -> MValue l)
     -> Value l
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
atWithDefaultOp :: (VMonad l, Show (Extra l)) =>
  Unpack l ->
  (VWord l -> Int -> MBool l) ->
  (VBool l -> MValue l -> MValue l -> MValue l) ->
  Value l
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
          VWord xw -> VBool <$> bvOp xw (fromIntegral i)
          _ -> fail "atOp: expected vector"
      VToNat i -> do
        iv <- toBits unpack i
        case x of
          VVector xv ->
            selectV mux (fromIntegral n - 1) (force . vecIdx d xv) iv
          VWord xw ->
            selectV mux (fromIntegral n - 1) (liftM VBool . bvOp xw) iv
          _ -> fail "atOp: expected vector"
      _ -> fail $ "atOp: expected Nat, got " ++ show idx

-- upd :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a -> Vec n a;
updOp :: (VMonadLazy l, Show (Extra l)) =>
  Unpack l ->
  (VWord l -> VWord l -> MBool l) ->
  (Int -> Integer -> VWord l) ->
  (VWord l -> Int) ->
  (VBool l -> MValue l -> MValue l -> MValue l) ->
  Value l
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
emptyVec :: VMonad l => Value l
emptyVec = constFun $ VVector V.empty


-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: VMonad l =>
  Unpack l ->
  (VWord l -> VWord l -> VWord l) ->
  Value l
appendOp unpack app =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  strictFun $ \ys ->
  appV unpack app xs ys

appV :: VMonad l =>
  Unpack l ->
  (VWord l -> VWord l -> VWord l) -> -- FIXME: make monadic
  Value l ->
  Value l ->
  MValue l
appV unpack app xs ys =
  case (xs, ys) of
    (VVector xv, _) | V.null xv -> return ys
    (_, VVector yv) | V.null yv -> return xs
    (VWord xw, VWord yw) -> return (VWord (app xw yw))
    (VVector xv, VVector yv) -> return $ VVector ((V.++) xv yv)
    (VVector xv, VWord yw) -> liftM (\yv -> VVector ((V.++) xv (fmap (ready . VBool) yv))) (unpack yw)
    (VWord xw, VVector yv) -> liftM (\xv -> VVector ((V.++) (fmap (ready . VBool) xv) yv)) (unpack xw)
    _ -> fail "Verifier.SAW.Simulator.Prims.appendOp"

-- join  :: (m n :: Nat) -> (a :: sort 0) -> Vec m (Vec n a) -> Vec (mulNat m n) a;
joinOp :: VMonad l =>
  Unpack l ->
  (VWord l -> VWord l -> VWord l) ->
  Value l
joinOp unpack app =
  constFun $
  constFun $
  constFun $
  strictFun $ \x ->
  case x of
    VVector xv -> do
      vv <- V.mapM force xv
      V.foldM (appV unpack app) (VVector V.empty) vv
    _ -> error "Verifier.SAW.Simulator.Prims.joinOp"

intUnOp :: VMonad l => String -> (VInt l -> VInt l) -> Value l
intUnOp nm f =
  intFun nm $ \x -> return $
    VInt (f x)

intBinOp :: VMonad l => String -> (VInt l -> VInt l -> VInt l) -> Value l
intBinOp nm f =
  intFun (nm++" x") $ \x -> return $
  intFun (nm++" y") $ \y -> return $
    VInt (f x y)

intBinCmp :: VMonad l =>
  String -> (VInt l -> VInt l -> a) -> (a -> VBool l) -> Value l
intBinCmp nm f boolLit =
  intFun (nm++" x") $ \x -> return $
  intFun (nm++" y") $ \y -> return $
    VBool $ boolLit (f x y)

-- primitive intAdd :: Integer -> Integer -> Integer;
intAddOp :: (VMonad l, VInt l ~ Integer) => Value l
intAddOp = intBinOp "intAdd" (+)

-- primitive intSub :: Integer -> Integer -> Integer;
intSubOp :: (VMonad l, VInt l ~ Integer) => Value l
intSubOp = intBinOp "intSub" (-)

-- primitive intMul :: Integer -> Integer -> Integer;
intMulOp :: (VMonad l, VInt l ~ Integer) => Value l
intMulOp = intBinOp "intMul" (*)

-- primitive intDiv :: Integer -> Integer -> Integer;
intDivOp :: (VMonad l, VInt l ~ Integer) => Value l
intDivOp = intBinOp "intDiv" div

-- primitive intMod :: Integer -> Integer -> Integer;
intModOp :: (VMonad l, VInt l ~ Integer) => Value l
intModOp = intBinOp "intMod" mod

-- primitive intMin :: Integer -> Integer -> Integer;
intMinOp :: (VMonad l, VInt l ~ Integer) => Value l
intMinOp = intBinOp "intMin" min

-- primitive intMax :: Integer -> Integer -> Integer;
intMaxOp :: (VMonad l, VInt l ~ Integer) => Value l
intMaxOp = intBinOp "intMax" max

-- primitive intNeg :: Integer -> Integer;
intNegOp :: (VMonad l, VInt l ~ Integer) => Value l
intNegOp = intUnOp "intNeg x" negate

-- primitive intEq  :: Integer -> Integer -> Bool;
intEqOp :: (VMonad l, VInt l ~ Integer) => (Bool -> VBool l) -> Value l
intEqOp = intBinCmp "intEq" (==)

-- primitive intLe  :: Integer -> Integer -> Bool;
intLeOp :: (VMonad l, VInt l ~ Integer) => (Bool -> VBool l) -> Value l
intLeOp = intBinCmp "intLe" (<=)

-- primitive intLt  :: Integer -> Integer -> Bool;
intLtOp :: (VMonad l, VInt l ~ Integer) => (Bool -> VBool l) -> Value l
intLtOp = intBinCmp "intLt" (<)

-- primitive intToNat :: Integer -> Nat;
intToNatOp :: (VMonad l, VInt l ~ Integer) => Value l
intToNatOp =
  intFun "intToNat" $ \x -> return $!
    if x >= 0 then VNat x else VNat 0

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: (VMonad l, VInt l ~ Integer) => Value l
natToIntOp = natFun' "natToInt" $ \x -> return $ VInt (fromIntegral x)

-- primitive bvLg2 :: (n :: Nat) -> bitvector n -> bitvector n;
bvLg2Op :: VMonad l => (Value l -> MWord l) -> (VWord l -> MWord l) -> Value l
bvLg2Op asWord wordLg2 =
  natFun' "bvLg2 1" $ \_n -> return $
  strictFun $ \w -> (return . VWord) =<< (wordLg2 =<< asWord w)

-- primitive error :: (a :: sort 0) -> String -> a;
errorOp :: VMonad l => Value l
errorOp =
  constFun $
  strictFun $ \x ->
  case x of
    VString s -> fail s
    _ -> fail "unknown error"

muxValue :: forall b l. (VMonadLazy l, Show (Extra l)) =>
  Unpack l ->
  (b -> VBool l -> VBool l -> MBool l) ->
  (b -> VWord l -> VWord l -> MWord l) ->
  (b -> VInt  l -> VInt  l -> MInt  l) ->
  (b -> Extra l -> Extra l -> EvalM l (Extra l)) ->
  b -> Value l -> Value l -> MValue l
muxValue unpack bool word int extra b = value
  where
    value :: Value l -> Value l -> MValue l
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
    value x@(VWord _)       y                 = toVector unpack x >>= \xv -> value (VVector xv) y
    value x                 y@(VWord _)       = toVector unpack y >>= \yv -> value x (VVector yv)
    value x                 y                 =
      fail $ "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments: "
      ++ show x ++ " " ++ show y

    thunks :: V.Vector (Thunk l) ->
              V.Vector (Thunk l) ->
              EvalM l (V.Vector (Thunk l))
    thunks xv yv
      | V.length xv == V.length yv = V.zipWithM thunk xv yv
      | otherwise                  = fail "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments"

    thunk :: Thunk l -> Thunk l -> EvalM l (Thunk l)
    thunk x y = delay $ do x' <- force x; y' <- force y; value x' y'

-- fix :: (a :: sort 0) -> (a -> a) -> a;
fixOp :: (VMonadLazy l, MonadFix (EvalM l)) => Value l
fixOp =
  constFun $
  strictFun $ \f ->
  force =<< mfix (\x -> delay (apply f x))
