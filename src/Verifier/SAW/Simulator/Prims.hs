{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Verifier.SAW.Simulator.Prims
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.Prims where

import Prelude hiding (sequence, mapM)

import Control.Monad (foldM, liftM)
import qualified Data.Map as Map
import Data.Traversable
import qualified Data.Vector as V

import Verifier.SAW.Simulator.Value
import Verifier.SAW.Prim

------------------------------------------------------------
-- Value accessors and constructors

vNat :: Nat -> Value m e
vNat n = VNat (fromIntegral n)

natFromValue :: Num a => Value m e -> a
natFromValue (VNat n) = fromInteger n
natFromValue _ = error "natFromValue"

natFun'' :: (Monad m, Show e) => String -> (Nat -> m (Value m e)) -> Value m e
natFun'' s f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g v = fail $ "expected Nat (" ++ s ++ "): " ++ show v

natFun' :: Monad m => String -> (Nat -> m (Value m e)) -> Value m e
natFun' s f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g _ = fail $ "expected Nat: " ++ s

natFun :: Monad m => (Nat -> m (Value m e)) -> Value m e
natFun f = strictFun g
  where g (VNat n) = f (fromInteger n)
        g _ = fail "expected Nat"

vFin :: Monad m => Fin -> Value m e
vFin (FinVal i j) = VCtorApp "Prelude.FinVal" $ V.fromList $ map (ready . vNat) [i, j]

finFromValue :: Monad m => Value m e -> m Fin
finFromValue (VCtorApp "Prelude.FinVal" (V.toList -> [x, y])) = do
  i <- liftM natFromValue $ force x
  j <- liftM natFromValue $ force y
  return $ FinVal i j
finFromValue _ = fail "finFromValue"

finFun :: Monad m => (Fin -> m (Value m e)) -> Value m e
finFun f = strictFun g
  where g v = finFromValue v >>= f

------------------------------------------------------------
-- Values for common primitives

-- coerce :: (a b :: sort 0) -> Eq (sort 0) a b -> a -> b;
coerceOp :: Monad m => Value m e
coerceOp =
  constFun $
  constFun $
  constFun $
  VFun force

-- Succ :: Nat -> Nat;
succOp :: Monad m => Value m e
succOp =
  natFun $ \n -> return $
  vNat (succ n)

-- addNat :: Nat -> Nat -> Nat;
addNatOp :: Monad m => Value m e
addNatOp =
  natFun' "addNat1" $ \m -> return $
  natFun' "addNat2" $ \n -> return $
  vNat (m + n)

-- subNat :: Nat -> Nat -> Nat;
subNatOp :: Monad m => Value m e
subNatOp =
  natFun' "subNat1" $ \m -> return $
  natFun' "subNat2" $ \n -> return $
  vNat (m - n)

-- mulNat :: Nat -> Nat -> Nat;
mulNatOp :: Monad m => Value m e
mulNatOp =
  natFun' "mulNat1" $ \m -> return $
  natFun' "mulNat2" $ \n -> return $
  vNat (m * n)

-- minNat :: Nat -> Nat -> Nat;
minNatOp :: Monad m => Value m e
minNatOp =
  natFun' "minNat1" $ \m -> return $
  natFun' "minNat2" $ \n -> return $
  vNat (min m n)

-- maxNat :: Nat -> Nat -> Nat;
maxNatOp :: Monad m => Value m e
maxNatOp =
  natFun' "maxNat1" $ \m -> return $
  natFun' "maxNat2" $ \n -> return $
  vNat (max m n)

-- divModNat :: Nat -> Nat -> #(Nat, Nat);
divModNatOp :: Monad m => Value m e
divModNatOp =
  natFun' "divModNat1" $ \m -> return $
  natFun' "divModNat2" $ \n -> return $
    let (q,r) = divMod m n in
    VTuple $ V.fromList [ready $ vNat q, ready $ vNat r]

-- expNat :: Nat -> Nat -> Nat;
expNatOp :: Monad m => Value m e
expNatOp =
  natFun' "expNat1" $ \m -> return $
  natFun' "expNat2" $ \n -> return $
  vNat (m ^ n)

-- widthNat :: Nat -> Nat;
widthNatOp :: Monad m => Value m e
widthNatOp =
  natFun' "widthNat1" $ \n -> return $
  vNat (widthNat n)

-- natCase :: (p :: Nat -> sort 0) -> p Zero -> ((n :: Nat) -> p (Succ n)) -> (n :: Nat) -> p n;
natCaseOp :: Monad m => Value m e
natCaseOp =
  constFun $
  VFun $ \z -> return $
  VFun $ \s -> return $
  natFun $ \n ->
    if n == 0
    then force z
    else do s' <- force s
            apply s' (ready (VNat (fromIntegral n - 1)))

-- finOfNat :: (n :: Nat) -> Nat -> Fin n;
finOfNatOp :: Monad m => Value m e
finOfNatOp =
  natFun' "finOfNat1" $ \n -> return $
  natFun' "finOfNat2" $ \i -> return $
  vFin (finFromBound i n)

--finDivMod :: (m n :: Nat) -> Fin (mulNat m n) -> #(Fin m, Fin n);
finDivModOp :: Monad m => Value m e
finDivModOp =
  natFun $ \m -> return $
  natFun $ \n -> return $
  finFun $ \i -> return $
  let (q, r) = finDivMod m n i
  in VTuple $ V.fromList $ map (ready . vFin) [q, r]

-- finMax :: (n :: Nat) -> Maybe (Fin n);
finMaxOp :: Monad m => Value m e
finMaxOp =
  natFun $ \n -> return $
  if n == 0
    then VCtorApp "Prelude.Nothing" (V.fromList [ready VType])
    else VCtorApp "Prelude.Just" (V.fromList [ready VType, ready (vFin (FinVal (n - 1) 0))])

-- finPred :: (n :: Nat) -> Fin n -> Maybe (Fin n);
finPredOp :: Monad m => Value m e
finPredOp =
  constFun $
  finFun $ \i -> return $
  if finVal i == 0
    then VCtorApp "Prelude.Nothing" (V.fromList [ready VType])
    else VCtorApp "Prelude.Just" (V.fromList [ready VType, ready (vFin (FinVal (finVal i - 1) (finRem i + 1)))])

-- natSplitFin :: (m :: Nat) -> Nat -> Either (Fin m) Nat;
natSplitFinOp :: Monad m => Value m e
natSplitFinOp =
  natFun $ \n -> return $
  natFun $ \i -> return $
  if i < n
    then VCtorApp "Prelude.Left" (V.fromList $ map ready [VType, VType, vFin (FinVal i (pred (n - i)))])
    else VCtorApp "Prelude.Right" (V.fromList $ map ready [VType, VType, vNat (i - n)])

-- generate :: (n :: Nat) -> (e :: sort 0) -> (Fin n -> e) -> Vec n e;
generateOp :: MonadLazy m => Value m e
generateOp =
  natFun' "generate1" $ \n -> return $
  constFun $
  strictFun $ \f -> do
    let g i = delay $ apply f (ready (vFin (finFromBound (fromIntegral i) n)))
    liftM VVector $ V.generateM (fromIntegral n) g

-- zero :: (a :: sort 0) -> a;
zeroOp :: (MonadLazy m, Show e) => (Integer -> m (Value m e)) -> m (Value m e)
       -> Value m e -> Value m e
zeroOp bvZ boolZ mkStream = strictFun go
  where
    go t =
      case t of
        VPiType _ f -> return $ VFun $ \x -> f x >>= go
        VTupleType ts -> liftM VTuple $ mapM (delay . go) (V.fromList ts)
        VRecordType tm -> liftM VRecord $ mapM (delay . go) tm
        VDataType "Prelude.Bool" [] -> boolZ
        VDataType "Prelude.Vec" [VNat n, VDataType "Prelude.Bool" []] -> bvZ n
        VDataType "Prelude.Vec" [VNat n, t'] -> do
          liftM (VVector . V.replicate (fromInteger n)) $ delay (go t')
        VDataType "Prelude.Stream" [t'] -> do
          thunk <- delay (go t')
          applyAll mkStream [ready t', ready (VFun (\_ -> force thunk))]
        _ -> fail $ "zero: invalid type instance: " ++ show t

--unary :: ((n :: Nat) -> bitvector n -> bitvector n)
--       -> (Bool -> Bool)
--       -> (a :: sort 0) -> a -> a;
unaryOp :: (MonadLazy m, Show e) => Value m e -> Value m e -> Value m e
unaryOp mkStream streamGet =
  pureFun $ \bvOp ->
  pureFun $ \boolOp ->
  let go (VPiType _ f) v =
        return $ VFun $ \x -> do
          y <- apply v x
          u <- f x
          go u y
      go (VTupleType ts) (VTuple vs) =
        liftM VTuple $ sequence (V.zipWith go' (V.fromList ts) vs)
      go (VRecordType tm) (VRecord vm)
        | Map.keys tm == Map.keys vm =
          liftM VRecord $ sequence (Map.intersectionWith go' tm vm)
      go (VDataType "Prelude.Vec" [n, VDataType "Prelude.Bool" []]) v =
        applyAll bvOp [ready n, ready v]
      go (VDataType "Prelude.Vec" [_, t']) (VVector vv) =
        liftM VVector $ mapM (go' t') vv
      go (VDataType "Prelude.Bool" []) v =
        apply boolOp (ready v)
      go (VDataType "Prelude.Stream" [t']) v =
        applyAll mkStream [ready t', ready (VFun f)]
        where
          f n = do
            x <- applyAll streamGet [ready t', ready v, n]
            go t' x
      go t _ =
        fail $ "unary: invalid type instance: " ++ show t

      go' t thunk = delay (force thunk >>= go t)

  in pureFun $ \t -> strictFun $ \v -> go t v

--binary :: ((n :: Nat) -> bitvector n -> bitvector n -> bitvector n)
--       -> (Bool -> Bool -> Bool)
--       -> (a :: sort 0) -> a -> a -> a;
binaryOp :: (MonadLazy m, Show e) => Value m e -> Value m e -> Value m e
binaryOp mkStream streamGet =
  VFun $ \bvOp' -> return $
  VFun $ \boolOp' -> return $
  let bin (VPiType _ f) v1 v2 =
        return $ VFun $ \x -> do
          y1 <- apply v1 x
          y2 <- apply v2 x
          u <- f x
          bin u y1 y2
      bin (VTupleType ts) (VTuple vs1) (VTuple vs2) =
        liftM VTuple $ sequence (V.zipWith3 bin' (V.fromList ts) vs1 vs2)
      bin (VRecordType tm) (VRecord vm1) (VRecord vm2)
        | Map.keys tm == Map.keys vm1 && Map.keys tm == Map.keys vm2 =
          liftM VRecord $ sequence
          (Map.intersectionWith ($) (Map.intersectionWith bin' tm vm1) vm2)
      bin (VDataType "Prelude.Bool" []) v1 v2 = do
        boolOp <- force boolOp'
        applyAll boolOp [ready v1, ready v2]
      bin (VDataType "Prelude.Vec" [n, VDataType "Prelude.Bool" []]) v1 v2 = do
        bvOp <- force bvOp'
        applyAll bvOp [ready n, ready v1, ready v2]
      bin (VDataType "Prelude.Vec" [_, t']) (VVector vv1) (VVector vv2) =
        liftM VVector $ sequence (V.zipWith (bin' t') vv1 vv2)
      bin (VDataType "Prelude.Stream" [t']) v1 v2 =
        applyAll mkStream [ready t', ready (VFun f)]
        where
          f n = do
            x1 <- applyAll streamGet [ready t', ready v1, n]
            x2 <- applyAll streamGet [ready t', ready v2, n]
            bin t' x1 x2
      bin t _ _ =
        fail $ "binary: invalid type instance: " ++ show t

      bin' t th1 th2 = delay $ do
        v1 <- force th1
        v2 <- force th2
        bin t v1 v2

  in pureFun $ \t -> pureFun $ \v1 -> strictFun $ \v2 -> bin t v1 v2

-- eq :: (a :: sort 0) -> a -> a -> Bool
eqOp :: (MonadLazy m, Show e) => Value m e
     -> (Value m e -> Value m e -> m (Value m e))
     -> (Value m e -> Value m e -> m (Value m e))
     -> (Integer -> Value m e -> Value m e -> m (Value m e))
     -> Value m e
eqOp trueOp andOp boolOp bvOp =
  pureFun $ \t -> pureFun $ \v1 -> strictFun $ \v2 -> go t v1 v2
  where
    go (VTupleType ts) (VTuple vv1) (VTuple vv2) = do
      bs <- sequence $ zipWith3 go' ts (V.toList vv1) (V.toList vv2)
      foldM andOp trueOp bs
    go (VRecordType tm) (VRecord vm1) (VRecord vm2)
      | Map.keys tm == Map.keys vm1 && Map.keys tm == Map.keys vm2 = do
        bs <- sequence $ zipWith3 go' (Map.elems tm) (Map.elems vm1) (Map.elems vm2)
        foldM andOp trueOp bs
    go (VDataType "Prelude.Vec" [VNat n, VDataType "Prelude.Bool" []]) v1 v2 = bvOp n v1 v2
    go (VDataType "Prelude.Vec" [_, t']) (VVector vv1) (VVector vv2) = do
      bs <- sequence $ zipWith (go' t') (V.toList vv1) (V.toList vv2)
      foldM andOp trueOp bs
    go (VDataType "Prelude.Bool" []) v1 v2 = boolOp v1 v2
    go t _ _ = fail $ "binary: invalid arguments: " ++ show t

    go' t thunk1 thunk2 = do
      v1 <- force thunk1
      v2 <- force thunk2
      go t v1 v2

-- comparison :: (b :: sort 0)
--            -> ((n :: Nat) -> bitvector n -> bitvector n -> b -> b)
--            -> (Bool -> Bool -> b -> b)
--            -> b
--            -> (a :: sort 0) -> a -> a -> b;
comparisonOp :: (MonadLazy m, Show e) => Value m e
comparisonOp =
  constFun $
  pureFun $ \bvOp ->
  pureFun $ \boolOp ->
  let go (VTupleType ts) (VTuple vv1) (VTuple vv2) k =
        foldM (flip ($)) k (zipWith3 go' ts (V.toList vv1) (V.toList vv2))
      go (VRecordType tm) (VRecord vm1) (VRecord vm2) k
        | Map.keys tm == Map.keys vm1 && Map.keys tm == Map.keys vm2 =
          foldM (flip ($)) k (zipWith3 go' (Map.elems tm) (Map.elems vm1) (Map.elems vm2))
      go (VDataType "Prelude.Bool" []) v1 v2 k = do
        applyAll boolOp [ready v1, ready v2, ready k]
      go (VDataType "Prelude.Vec" [n, VDataType "Prelude.Bool" []]) v1 v2 k = do
        applyAll bvOp [ready n, ready v1, ready v2, ready k]
      go (VDataType "Prelude.Vec" [_, t']) (VVector vv1) (VVector vv2) k = do
        foldM (flip ($)) k (zipWith (go' t') (V.toList vv1) (V.toList vv2))
      go t _ _ _ = fail $ "comparison: invalid arguments: " ++ show t

      go' t thunk1 thunk2 k = do
        v1 <- force thunk1
        v2 <- force thunk2
        go t v1 v2 k

  in pureFun $ \k -> pureFun $ \t -> pureFun $ \v1 -> strictFun $ \v2 -> go t v1 v2 k
