{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}

{- |
Module      : Verifier.SAW.Simulator.TermModel
Copyright   : Galois, Inc. 2012-2021
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.TermModel
       ( -- evalTermModel,
         TmValue, TermModel, Value(..), TValue(..)
       , VExtra(..)
       , readBackValue, readBackTValue
       , normalizeSharedTerm
       ) where

import Control.Monad.Fix
import Data.IORef
--import Data.Vector (Vector)
--import qualified Data.Vector as V
import Data.Map (Map)
import qualified Data.Map as Map
import Numeric.Natural

import Verifier.SAW.Prim (BitVector(..))
--import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
--import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST (ModuleMap, DataType(..))
import Verifier.SAW.SharedTerm
import Verifier.SAW.Utils (panic)

------------------------------------------------------------


normalizeSharedTerm ::
  SharedContext ->
  ModuleMap ->
  Map Ident TmValue ->
  Map VarIndex TmValue ->
  Term ->
  IO Term
normalizeSharedTerm sc m addlPrims ecVals t =
  do cfg <- mfix (\cfg -> Sim.evalGlobal m (Map.union constMap addlPrims) (extcns cfg) (const Nothing))
     v <- Sim.evalSharedTerm cfg t
     tv <- evalType cfg =<< scTypeOf sc t
     readBackValue sc cfg tv v
  where
    constMap = error "TermModel TODO: define the constMap!"

    extcns cfg ec =
      case Map.lookup (ecVarIndex ec) ecVals of
        Just v  -> return v
        Nothing ->
          do ec' <- traverse (readBackTValue sc cfg) ec
             tm <- scExtCns sc ec'
             reflectTerm sc cfg (ecType ec) tm

------------------------------------------------------------
-- Values

data TermModel

type TmValue = Value TermModel

type instance EvalM  TermModel = IO
type instance VBool  TermModel = Either Term Bool
type instance VWord  TermModel = Either Term BitVector
type instance VInt   TermModel = Either Term Integer
type instance VArray TermModel = Term
type instance Extra  TermModel = VExtra

data VExtra
  = VStream Term (Natural -> IO TmValue) (IORef (Map Natural TmValue))
  | VExtraTerm (TValue TermModel) Term

instance Show VExtra where
  show (VStream tm _ _) = show tm
  show (VExtraTerm _ tm) = show tm

readBackTValue :: SharedContext -> Sim.SimulatorConfig TermModel -> TValue TermModel -> IO Term
readBackTValue sc cfg = loop
  where
  loop tv =
    case tv of
      VUnitType -> scUnitType sc
      VBoolType -> scBoolType sc
      VIntType -> scIntegerType sc
      VSort s  -> scSort sc s
      VIntModType m ->
        do m' <- scNat sc m
           scIntModType sc m'
      VArrayType t1 t2 ->
        do t1' <- loop t1
           t2' <- loop t2
           scArrayType sc t1' t2'
      VVecType n t ->
        do n' <- scNat sc n
           t' <- loop t
           scVecType sc n' t'
      VPairType t1 t2 ->
        do t1' <- loop t1
           t2' <- loop t2
           scPairType sc t1' t2'
      VRecordType fs ->
        do fs' <- traverse (traverse loop) fs
           scRecordType sc fs'
      VDataType nm vs ->
        do dt <- scRequireDataType sc nm
           dtTy <- evalType cfg (dtType dt)
           vs' <- readBackDataType dtTy vs
           scDataTypeApp sc nm vs'
      VPiType{} ->
        do (ecs, tm) <- readBackPis tv
           scGeneralizeExts sc ecs tm

  readBackDataType (VPiType t f) (v:vs) =
    do v' <- readBackValue sc cfg t v
       t' <- f (ready v)
       vs' <- readBackDataType t' vs
       return (v':vs')
  readBackDataType (VSort _s) [] = return []
  readBackDataType _ _ = panic "readBackTValue" ["Arity mismatch in data type in readback"]

  readBackPis (VPiType t f) =
    do t' <- loop t
       ec <- scFreshEC sc "x" t'
       ecTm <- scExtCns sc ec
       ecVal <- delay (reflectTerm sc cfg t ecTm)
       body <- f ecVal
       (ecs,body') <- readBackPis body
       return (ec:ecs, body')

  readBackPis t =
    do tm <- loop t
       return ([], tm)

evalType :: Sim.SimulatorConfig TermModel -> Term -> IO (TValue TermModel)
evalType cfg tm =
  Sim.evalSharedTerm cfg tm >>= \case
    TValue tv -> pure tv
    _ -> panic "evalType" ["Expected type value"]

reflectTerm :: SharedContext -> Sim.SimulatorConfig TermModel -> TValue TermModel -> Term -> IO (Value TermModel)
reflectTerm sc cfg = loop
  where
  loop tv tm = case tv of
    VUnitType -> pure VUnit
    VBoolType -> return (VBool (Left tm))
    VIntType  -> return (VInt (Left tm))
    VIntModType m -> return (VIntMod m (Left tm))
    VVecType _n VBoolType -> return (VWord (Left tm))
    VArrayType _ _ -> return (VArray tm)
    VSort _s -> TValue <$> evalType cfg tm

    VPiType t tf ->
      return (VFun (\x ->
        do v <- force x
           tbody <- tf x
           xtm <- readBackValue sc cfg t v
           body <- scApply sc tm xtm
           reflectTerm sc cfg tbody body
        ))

    VRecordType{} -> return (VExtra (VExtraTerm tv tm))
    VPairType{} -> return (VExtra (VExtraTerm tv tm))
    -- NB: not a word
    VVecType{} -> return (VExtra (VExtraTerm tv tm))
    VDataType{} -> return (VExtra (VExtraTerm tv tm))


readBackValue :: SharedContext -> Sim.SimulatorConfig TermModel -> TValue TermModel -> Value TermModel -> IO Term
readBackValue sc cfg = loop
  where
    loop _ VUnit = scUnitValue sc

    loop _ (VNat n) = scNat sc n

    loop _ (VBool (Left tm)) = return tm
    loop _ (VBool (Right b)) = scBool sc b
    
    loop _ (VInt (Left tm)) = return tm
    loop _ (VInt (Right i)) = scIntegerConst sc i

    loop _ (VIntMod _ (Left tm)) = return tm
    loop _ (VIntMod m (Right i)) =
      do m' <- scNat sc m
         i' <- scIntegerConst sc i
         scToIntMod sc m' i'

    loop _ (VWord (Left tm)) = return tm
    loop _ (VWord (Right bv)) = scBvConst sc (fromIntegral (width bv)) (unsigned bv)

    loop _ (VArray tm) = return tm
    loop _ (VString s) = scString sc s

    loop _ (TValue tv) = readBackTValue sc cfg tv

    loop _ (VExtra (VExtraTerm _ tm)) = return tm
    loop _ (VExtra (VStream tm _ _))  = return tm

    loop tv@VPiType{} v@VFun{} =
      do (ecs, tm) <- readBackFuns tv v
         scAbstractExts sc ecs tm

    loop (VPairType t1 t2) (VPair v1 v2) =
      do tm1 <- loop t1 =<< force v1
         tm2 <- loop t2 =<< force v2
         scPairValueReduced sc tm1 tm2

    loop (VDataType _nm _ps) (VCtorApp _cnm _vs) =
      fail "readBackValue: ctor app TODO, this is kind of tricky"

    loop (VRecordType fs) (VRecordValue vs) =
      do let fm = Map.fromList fs
         let build (k,v) =
                  case Map.lookup k fm of
                    Nothing -> panic "readBackValue" ["field mismatch in record value"
                                                     , show (map fst fs), show (map snd fs) ]
                    Just t ->
                       do tm <- loop t =<< force v
                          return (k,tm)
         vs' <- Map.fromList <$> traverse build vs
         scRecord sc vs'

    loop tv _v = panic "readBackValue" ["type mismatch", show tv]

    readBackFuns (VPiType tv tf) (VFun f) =
      do t' <- readBackTValue sc cfg tv
         ec <- scFreshEC sc "x" t'
         ecTm <- scExtCns sc ec
         ecVal <- delay (reflectTerm sc cfg tv ecTm)
         tbody <- tf ecVal
         body  <- f ecVal
         (ecs,tm) <- readBackFuns tbody body
         return (ec:ecs, tm)

    readBackFuns tv v =
      do tm <- loop tv v
         return ([], tm)


{-
instance Show TExtra where
  show (TStream{}) = "<stream>"

wordFun :: (BitVector -> CValue) -> CValue
wordFun f = pureFun (\x -> f (toWord x))

-- | op : (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool
bvShiftOp :: (BitVector -> Int -> BitVector) -> CValue
bvShiftOp natOp =
  constFun $
  wordFun $ \x ->
  pureFun $ \y ->
    case y of
      VNat n | toInteger n < toInteger (maxBound :: Int) -> vWord (natOp x (fromIntegral n))
      _      -> error $ unwords ["Verifier.SAW.Simulator.Concrete.shiftOp", show y]

------------------------------------------------------------

pure1 :: Applicative f => (a -> b) -> a -> f b
pure1 f x = pure (f x)

pure2 :: Applicative f => (a -> b -> c) -> a -> b -> f c
pure2 f x y = pure (f x y)

pure3 :: Applicative f => (a -> b -> c -> d) -> a -> b -> c -> f d
pure3 f x y z = pure (f x y z)

divOp :: (a -> b -> Maybe c) -> a -> b -> Identity c
divOp f x y = maybe Prim.divideByZero pure (f x y)

ite :: Bool -> a -> a -> a
ite b x y = if b then x else y

prims :: Prims.BasePrims Concrete
prims =
  Prims.BasePrims
  { Prims.bpAsBool  = Just
  , Prims.bpUnpack  = pure1 unpackBitVector
  , Prims.bpPack    = pure1 packBitVector
  , Prims.bpBvAt    = pure2 Prim.bvAt
  , Prims.bpBvLit   = pure2 Prim.bv
  , Prims.bpBvSize  = Prim.width
  , Prims.bpBvJoin  = pure2 (Prim.append_bv undefined undefined undefined)
  , Prims.bpBvSlice = pure3 (\m n x -> Prim.slice_bv () m n (Prim.width x - m - n) x)
    -- Conditionals
  , Prims.bpMuxBool  = pure3 ite
  , Prims.bpMuxWord  = pure3 ite
  , Prims.bpMuxInt   = pure3 ite
  , Prims.bpMuxExtra = pure3 ite
    -- Booleans
  , Prims.bpTrue   = True
  , Prims.bpFalse  = False
  , Prims.bpNot    = pure1 not
  , Prims.bpAnd    = pure2 (&&)
  , Prims.bpOr     = pure2 (||)
  , Prims.bpXor    = pure2 (/=)
  , Prims.bpBoolEq = pure2 (==)
    -- Bitvector logical
  , Prims.bpBvNot  = pure1 (Prim.bvNot undefined)
  , Prims.bpBvAnd  = pure2 (Prim.bvAnd undefined)
  , Prims.bpBvOr   = pure2 (Prim.bvOr  undefined)
  , Prims.bpBvXor  = pure2 (Prim.bvXor undefined)
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = pure1 (Prim.bvNeg undefined)
  , Prims.bpBvAdd  = pure2 (Prim.bvAdd undefined)
  , Prims.bpBvSub  = pure2 (Prim.bvSub undefined)
  , Prims.bpBvMul  = pure2 (Prim.bvMul undefined)
  , Prims.bpBvUDiv = divOp (Prim.bvUDiv undefined)
  , Prims.bpBvURem = divOp (Prim.bvURem undefined)
  , Prims.bpBvSDiv = divOp (Prim.bvSDiv undefined)
  , Prims.bpBvSRem = divOp (Prim.bvSRem undefined)
  , Prims.bpBvLg2  = pure1 Prim.bvLg2
    -- Bitvector comparisons
  , Prims.bpBvEq   = pure2 (Prim.bvEq  undefined)
  , Prims.bpBvsle  = pure2 (Prim.bvsle undefined)
  , Prims.bpBvslt  = pure2 (Prim.bvslt undefined)
  , Prims.bpBvule  = pure2 (Prim.bvule undefined)
  , Prims.bpBvult  = pure2 (Prim.bvult undefined)
  , Prims.bpBvsge  = pure2 (Prim.bvsge undefined)
  , Prims.bpBvsgt  = pure2 (Prim.bvsgt undefined)
  , Prims.bpBvuge  = pure2 (Prim.bvuge undefined)
  , Prims.bpBvugt  = pure2 (Prim.bvugt undefined)
    -- Bitvector shift/rotate
  , Prims.bpBvRolInt = pure2 bvRotateL
  , Prims.bpBvRorInt = pure2 bvRotateR
  , Prims.bpBvShlInt = pure3 bvShiftL
  , Prims.bpBvShrInt = pure3 bvShiftR
  , Prims.bpBvRol    = pure2 (\x y -> bvRotateL x (unsigned y))
  , Prims.bpBvRor    = pure2 (\x y -> bvRotateR x (unsigned y))
  , Prims.bpBvShl    = pure3 (\b x y -> bvShiftL b x (unsigned y))
  , Prims.bpBvShr    = pure3 (\b x y -> bvShiftR b x (unsigned y))
    -- Bitvector misc
  , Prims.bpBvPopcount = pure1 (Prim.bvPopcount undefined)
  , Prims.bpBvCountLeadingZeros = pure1 (Prim.bvCountLeadingZeros undefined)
  , Prims.bpBvCountTrailingZeros = pure1 (Prim.bvCountTrailingZeros undefined)
  , Prims.bpBvForall = unsupportedConcretePrimitive "bvForall"

    -- Integer operations
  , Prims.bpIntAdd = pure2 (+)
  , Prims.bpIntSub = pure2 (-)
  , Prims.bpIntMul = pure2 (*)
  , Prims.bpIntDiv = pure2 div
  , Prims.bpIntMod = pure2 mod
  , Prims.bpIntNeg = pure1 negate
  , Prims.bpIntAbs = pure1 abs
  , Prims.bpIntEq  = pure2 (==)
  , Prims.bpIntLe  = pure2 (<=)
  , Prims.bpIntLt  = pure2 (<)
  , Prims.bpIntMin = pure2 min
  , Prims.bpIntMax = pure2 max

    -- Array operations
  , Prims.bpArrayConstant = unsupportedConcretePrimitive "bpArrayConstant"
  , Prims.bpArrayLookup = unsupportedConcretePrimitive "bpArrayLookup"
  , Prims.bpArrayUpdate = unsupportedConcretePrimitive "bpArrayUpdate"
  , Prims.bpArrayEq = unsupportedConcretePrimitive "bpArrayEq"
  }

unsupportedConcretePrimitive :: String -> a
unsupportedConcretePrimitive = Prim.unsupportedPrimitive "concrete"

constMap :: Map Ident CValue
constMap =
  flip Map.union (Prims.constMap prims) $
  Map.fromList
  -- Shifts
  [ ("Prelude.bvShl" , bvShiftOp (Prim.bvShl undefined))
  , ("Prelude.bvShr" , bvShiftOp (Prim.bvShr undefined))
  , ("Prelude.bvSShr", bvShiftOp (Prim.bvSShr undefined))
  -- Integers
  , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", Prims.natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  -- Integers mod n
  , ("Prelude.toIntMod"  , toIntModOp)
  , ("Prelude.fromIntMod", fromIntModOp)
  , ("Prelude.intModEq"  , intModEqOp)
  , ("Prelude.intModAdd" , intModBinOp (+))
  , ("Prelude.intModSub" , intModBinOp (-))
  , ("Prelude.intModMul" , intModBinOp (*))
  , ("Prelude.intModNeg" , intModUnOp negate)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  -- Miscellaneous
  , ("Prelude.bvToNat", bvToNatOp) -- override Prims.constMap
  , ("Prelude.expByNat", Prims.expByNatOp prims)
  ]

------------------------------------------------------------

-- primitive bvToNat : (n : Nat) -> Vec n Bool -> Nat;
bvToNatOp :: CValue
bvToNatOp = constFun $ wordFun $ VNat . fromInteger . unsigned

-- primitive bvToInt : (n : Nat) -> Vec n Bool -> Integer;
bvToIntOp :: CValue
bvToIntOp = constFun $ wordFun $ VInt . unsigned

-- primitive sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: CValue
sbvToIntOp = constFun $ wordFun $ VInt . signed

-- primitive intToBv : (n : Nat) -> Integer -> Vec n Bool;
intToBvOp :: CValue
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x -> return $
    VWord $
     if n >= 0 then bv (fromIntegral n) x
               else bvNeg n $ bv (fromIntegral n) $ negate x

------------------------------------------------------------
-- BitVector operations

bvRotateL :: BitVector -> Integer -> BitVector
bvRotateL (BV w x) i = Prim.bv w ((x `shiftL` j) .|. (x `shiftR` (w - j)))
  where j = fromInteger (i `mod` toInteger w)

bvRotateR :: BitVector -> Integer -> BitVector
bvRotateR w i = bvRotateL w (- i)

bvShiftL :: Bool -> BitVector -> Integer -> BitVector
bvShiftL c (BV w x) i = Prim.bv w ((x `shiftL` j) .|. c')
  where c' = if c then (1 `shiftL` j) - 1 else 0
        j = fromInteger (i `min` toInteger w)

bvShiftR :: Bool -> BitVector -> Integer -> BitVector
bvShiftR c (BV w x) i = Prim.bv w (c' .|. (x `shiftR` j))
  where c' = if c then (full `shiftL` (w - j)) .&. full else 0
        full = (1 `shiftL` w) - 1
        j = fromInteger (i `min` toInteger w)

------------------------------------------------------------

toIntModOp :: CValue
toIntModOp =
  Prims.natFun $ \n -> return $
  Prims.intFun "toIntModOp" $ \x -> return $
  VIntMod n (x `mod` toInteger n)

fromIntModOp :: CValue
fromIntModOp =
  constFun $
  Prims.intModFun "fromIntModOp" $ \x -> pure $
  VInt x

intModEqOp :: CValue
intModEqOp =
  constFun $
  Prims.intModFun "intModEqOp" $ \x -> return $
  Prims.intModFun "intModEqOp" $ \y -> return $
  VBool (x == y)

intModBinOp :: (Integer -> Integer -> Integer) -> CValue
intModBinOp f =
  Prims.natFun $ \n -> return $
  Prims.intModFun "intModBinOp x" $ \x -> return $
  Prims.intModFun "intModBinOp y" $ \y -> return $
  VIntMod n (f x y `mod` toInteger n)

intModUnOp :: (Integer -> Integer) -> CValue
intModUnOp f =
  Prims.natFun $ \n -> return $
  Prims.intModFun "intModUnOp" $ \x -> return $
  VIntMod n (f x `mod` toInteger n)

------------------------------------------------------------

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: CValue
mkStreamOp =
  constFun $
  pureFun $ \f ->
  vStream (fmap (\n -> runIdentity (apply f (ready (VNat n)))) IntTrie.identity)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: CValue
streamGetOp =
  constFun $
  pureFun $ \xs ->
  strictFun $ \case
    VNat n -> return $ IntTrie.apply (toStream xs) (toInteger n)
    VToNat w -> return $ IntTrie.apply (toStream xs) (unsigned (toWord w))
    n -> Prims.panic "Verifier.SAW.Simulator.Concrete.streamGetOp"
               ["Expected Nat value", show n]
-}