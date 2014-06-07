{-# LANGUAGE OverloadedStrings #-}

module Verifier.SAW.Simulator.Prims where

import Control.Monad (liftM)
import qualified Data.Vector as V

import Verifier.SAW.Simulator.Value
import Verifier.SAW.Prim

import Control.Monad.IO.Class

------------------------------------------------------------
-- Value accessors and constructors

vNat :: Nat -> Value m e
vNat n = VNat (fromIntegral n)

natFromValue :: Num a => Value m e -> a
natFromValue (VNat n) = fromInteger n
natFromValue _ = error "natFromValue"

natFun'' :: (MonadIO m, Show e) => String -> (Nat -> m (Value m e)) -> Value m e
natFun'' s f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g v = fail $ "expected Nat (" ++ s ++ "): " ++ show v

natFun' :: MonadIO m => String -> (Nat -> m (Value m e)) -> Value m e
natFun' s f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g _ = fail $ "expected Nat: " ++ s

natFun :: MonadIO m => (Nat -> m (Value m e)) -> Value m e
natFun f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g _ = fail "expected Nat"

vFin :: Fin -> Value m e
vFin (FinVal i j) = VCtorApp "Prelude.FinVal" $ V.fromList $ map (Ready . vNat) [i, j]

finFromValue :: MonadIO m => Value m e -> m Fin
finFromValue (VCtorApp "Prelude.FinVal" (V.toList -> [x, y])) = do
  i <- liftM natFromValue $ force x
  j <- liftM natFromValue $ force y
  return $ FinVal i j
finFromValue _ = fail "finFromValue"

finFun :: MonadIO m => (Fin -> m (Value m e)) -> Value m e
finFun f = strictFun g
  where g v = finFromValue v >>= f

------------------------------------------------------------
-- Values for common primitives

-- coerce :: (a b :: sort 0) -> Eq (sort 0) a b -> a -> b;
coerceOp :: MonadIO m => Value m e
coerceOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun force

-- Succ :: Nat -> Nat;
succOp :: MonadIO m => Value m e
succOp =
  natFun $ \n -> return $
  vNat (succ n)

-- addNat :: Nat -> Nat -> Nat;
addNatOp :: MonadIO m => Value m e
addNatOp =
  natFun' "addNat1" $ \m -> return $
  natFun' "addNat2" $ \n -> return $
  vNat (m + n)

-- subNat :: Nat -> Nat -> Nat;
subNatOp :: MonadIO m => Value m e
subNatOp =
  natFun' "subNat1" $ \m -> return $
  natFun' "subNat2" $ \n -> return $
  vNat (m - n)

-- mulNat :: Nat -> Nat -> Nat;
mulNatOp :: MonadIO m => Value m e
mulNatOp =
  natFun' "mulNat1" $ \m -> return $
  natFun' "mulNat2" $ \n -> return $
  vNat (m * n)

-- minNat :: Nat -> Nat -> Nat;
minNatOp :: MonadIO m => Value m e
minNatOp =
  natFun' "minNat1" $ \m -> return $
  natFun' "minNat2" $ \n -> return $
  vNat (min m n)

-- maxNat :: Nat -> Nat -> Nat;
maxNatOp :: MonadIO m => Value m e
maxNatOp =
  natFun' "maxNat1" $ \m -> return $
  natFun' "maxNat2" $ \n -> return $
  vNat (max m n)

-- widthNat :: Nat -> Nat;
widthNatOp :: MonadIO m => Value m e
widthNatOp =
  natFun' "widthNat1" $ \n -> return $
  vNat (widthNat n)

-- finOfNat :: (n :: Nat) -> Nat -> Fin n;
finOfNatOp :: MonadIO m => Value m e
finOfNatOp =
  natFun' "finOfNat1" $ \n -> return $
  natFun' "finOfNat2" $ \i -> return $
  vFin (finFromBound i n)

--finDivMod :: (m n :: Nat) -> Fin (mulNat m n) -> #(Fin m, Fin n);
finDivModOp :: MonadIO m => Value m e
finDivModOp =
  natFun $ \m -> return $
  natFun $ \n -> return $
  finFun $ \i -> return $
  let (q, r) = finDivMod m n i
  in VTuple $ V.fromList $ map (Ready . vFin) [q, r]

-- finMax :: (n :: Nat) -> Maybe (Fin n);
finMaxOp :: MonadIO m => Value m e
finMaxOp =
  natFun $ \n -> return $
  if n == 0
    then VCtorApp "Prelude.Nothing" (V.fromList [Ready VType])
    else VCtorApp "Prelude.Just" (V.fromList [Ready VType, Ready (vFin (FinVal (n - 1) 0))])

-- finPred :: (n :: Nat) -> Fin n -> Maybe (Fin n);
finPredOp :: MonadIO m => Value m e
finPredOp =
  VFun $ \_ -> return $
  finFun $ \i -> return $
  if finVal i == 0
    then VCtorApp "Prelude.Nothing" (V.fromList [Ready VType])
    else VCtorApp "Prelude.Just" (V.fromList [Ready VType, Ready (vFin (FinVal (finVal i - 1) (finRem i + 1)))])

-- generate :: (n :: Nat) -> (e :: sort 0) -> (Fin n -> e) -> Vec n e;
generateOp :: MonadIO m => Value m e
generateOp =
  natFun' "generate1" $ \n -> return $
  VFun $ \_ -> return $
  strictFun $ \f -> do
    let g i = delay $ apply f (Ready (vFin (finFromBound (fromIntegral i) n)))
    liftM VVector $ V.generateM (fromIntegral n) g
