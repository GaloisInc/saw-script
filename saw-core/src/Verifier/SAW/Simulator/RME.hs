{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}

{- |
Module      : Verifier.SAW.Simulator.RME
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.RME
  ( evalSharedTerm
  , RValue, Value(..)
  , RExtra(..)
  , toBool
  , toWord
  , withBitBlastedSATQuery
  ) where

import Control.Monad.State
import Data.Bits
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V
import Numeric.Natural

import Data.RME (RME)
import qualified Data.RME as RME
import qualified Data.RME.Vector as RMEV

import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.FiniteValue (FiniteType(..), FirstOrderType, toFiniteType)
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST (ModuleMap)
import Verifier.SAW.Utils (panic)
import Verifier.SAW.SATQuery

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable
#endif

------------------------------------------------------------

-- | Evaluator for shared terms.
evalSharedTerm :: ModuleMap -> Map Ident RValue -> Term -> IO RValue
evalSharedTerm m addlPrims t = do
    cfg <- Sim.evalGlobal m (Map.union constMap addlPrims)
           extcns (const Nothing) neutral
    Sim.evalSharedTerm cfg t
  where
    extcns ec = return $ Prim.userError $ "Unimplemented: external constant " ++ show (ecName ec)
    neutral _env nt = return $ Prim.userError $ "Could not evaluate neutral term\n:" ++ show nt

------------------------------------------------------------
-- Values

data ReedMuller

type instance EvalM ReedMuller = IO
type instance VBool ReedMuller = RME
type instance VWord ReedMuller = Vector RME
type instance VInt  ReedMuller = Integer
type instance VArray ReedMuller = ()
type instance Extra ReedMuller = RExtra

type RValue = Value ReedMuller
type RThunk = Thunk ReedMuller

data RExtra =
  AStream (Natural -> IO RValue) (IORef (Map Natural RValue))

instance Show RExtra where
  show AStream{} = "<stream>"

vBool :: RME -> RValue
vBool b = VBool b

toBool :: RValue -> RME
toBool (VBool b) = b
toBool x = error $ unwords ["Verifier.SAW.Simulator.RME.toBool", show x]

vWord :: Vector RME -> RValue
vWord x = VWord x

toWord :: RValue -> IO (Vector RME)
toWord (VWord x) = pure x
toWord (VVector vv) = traverse (\x -> toBool <$> force x) vv
toWord x = error $ unwords ["Verifier.SAW.Simulator.RME.toWord", show x]

wordFun :: (Vector RME -> RValue) -> RValue
wordFun f = strictFun (\x -> f <$> (toWord x))

genShift :: (a -> b -> b -> b) -> (b -> Integer -> b) -> b -> Vector a -> b
genShift cond f x0 v = go x0 (V.toList v)
  where
    go x [] = x
    go x (y : ys) = go (cond y (f x (2 ^ length ys)) x) ys

-- | op : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvShiftOp :: (Vector RME -> Integer -> Vector RME) -> RValue
bvShiftOp op =
  constFun $
  wordFun $ \x ->
  strictFun $ \y ->
    case y of
      VNat n   -> pure (vWord (op x (toInteger n)))
      VBVToNat _sz v -> vWord . genShift muxRMEV op x <$> toWord v
      VIntToNat _i   -> error "RME.shiftOp: intToNat TODO"
      _        -> error $ unwords ["Verifier.SAW.Simulator.RME.shiftOp", show y]

------------------------------------------------------------

pure1 :: Applicative f => (a -> b) -> a -> f b
pure1 f x = pure (f x)

pure2 :: Applicative f => (a -> b -> c) -> a -> b -> f c
pure2 f x y = pure (f x y)

pure3 :: Applicative f => (a -> b -> c -> d) -> a -> b -> c -> f d
pure3 f x y z = pure (f x y z)

prims :: Prims.BasePrims ReedMuller
prims =
  Prims.BasePrims
  { Prims.bpAsBool  = RME.isBool
  , Prims.bpUnpack  = pure
  , Prims.bpPack    = pure
  , Prims.bpBvAt    = pure2 (V.!)
  , Prims.bpBvLit   = pure2 RMEV.integer
  , Prims.bpBvSize  = V.length
  , Prims.bpBvJoin  = pure2 (V.++)
  , Prims.bpBvSlice = pure3 V.slice
    -- Conditionals
  , Prims.bpMuxBool  = pure3 RME.mux
  , Prims.bpMuxWord  = pure3 muxRMEV
  , Prims.bpMuxInt   = pure3 muxInt
  , Prims.bpMuxExtra = muxExtra
    -- Booleans
  , Prims.bpTrue   = RME.true
  , Prims.bpFalse  = RME.false
  , Prims.bpNot    = pure1 RME.compl
  , Prims.bpAnd    = pure2 RME.conj
  , Prims.bpOr     = pure2 RME.disj
  , Prims.bpXor    = pure2 RME.xor
  , Prims.bpBoolEq = pure2 RME.iff
    -- Bitvector logical
  , Prims.bpBvNot  = pure1 (V.map RME.compl)
  , Prims.bpBvAnd  = pure2 (V.zipWith RME.conj)
  , Prims.bpBvOr   = pure2 (V.zipWith RME.disj)
  , Prims.bpBvXor  = pure2 (V.zipWith RME.xor)
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = pure1 RMEV.neg
  , Prims.bpBvAdd  = pure2 RMEV.add
  , Prims.bpBvSub  = pure2 RMEV.sub
  , Prims.bpBvMul  = pure2 RMEV.mul
  , Prims.bpBvUDiv = pure2 RMEV.udiv
  , Prims.bpBvURem = pure2 RMEV.urem
  , Prims.bpBvSDiv = pure2 RMEV.sdiv
  , Prims.bpBvSRem = pure2 RMEV.srem
  , Prims.bpBvLg2  = unsupportedRMEPrimitive "bpBvLg2"
    -- Bitvector comparisons
  , Prims.bpBvEq   = pure2 RMEV.eq
  , Prims.bpBvsle  = pure2 RMEV.sle
  , Prims.bpBvslt  = pure2 RMEV.sle
  , Prims.bpBvule  = pure2 RMEV.ule
  , Prims.bpBvult  = pure2 RMEV.ult
  , Prims.bpBvsge  = pure2 (flip RMEV.sle)
  , Prims.bpBvsgt  = pure2 (flip RMEV.slt)
  , Prims.bpBvuge  = pure2 (flip RMEV.ule)
  , Prims.bpBvugt  = pure2 (flip RMEV.ult)
    -- Bitvector shift/rotate
  , Prims.bpBvRolInt = pure2 Prims.vRotateL
  , Prims.bpBvRorInt = pure2 Prims.vRotateR
  , Prims.bpBvShlInt = pure3 Prims.vShiftL
  , Prims.bpBvShrInt = pure3 Prims.vShiftR
  , Prims.bpBvRol    = pure2 (genShift muxRMEV Prims.vRotateL)
  , Prims.bpBvRor    = pure2 (genShift muxRMEV Prims.vRotateR)
  , Prims.bpBvShl    = pure3 (genShift muxRMEV . Prims.vShiftL)
  , Prims.bpBvShr    = pure3 (genShift muxRMEV . Prims.vShiftR)
    -- Bitvector misc
  , Prims.bpBvPopcount = pure1 RMEV.popcount
  , Prims.bpBvCountLeadingZeros = pure1 RMEV.countLeadingZeros
  , Prims.bpBvCountTrailingZeros = pure1 RMEV.countTrailingZeros
  , Prims.bpBvForall = unsupportedRMEPrimitive "bvForall"
    -- Integer operations
  , Prims.bpIntAdd = pure2 (+)
  , Prims.bpIntSub = pure2 (-)
  , Prims.bpIntMul = pure2 (*)
  , Prims.bpIntDiv = pure2 div
  , Prims.bpIntMod = pure2 mod
  , Prims.bpIntNeg = pure1 negate
  , Prims.bpIntAbs = pure1 abs
  , Prims.bpIntEq  = pure2 (\x y -> RME.constant (x == y))
  , Prims.bpIntLe  = pure2 (\x y -> RME.constant (x <= y))
  , Prims.bpIntLt  = pure2 (\x y -> RME.constant (x < y))
  , Prims.bpIntMin = pure2 min
  , Prims.bpIntMax = pure2 max
    -- Array operations
  , Prims.bpArrayConstant = unsupportedRMEPrimitive "bpArrayConstant"
  , Prims.bpArrayLookup = unsupportedRMEPrimitive "bpArrayLookup"
  , Prims.bpArrayUpdate = unsupportedRMEPrimitive "bpArrayUpdate"
  , Prims.bpArrayEq = unsupportedRMEPrimitive "bpArrayEq"
  }

unsupportedRMEPrimitive :: String -> a
unsupportedRMEPrimitive = Prim.unsupportedPrimitive "RME"

constMap :: Map Ident RValue
constMap =
  Map.union (Prims.constMap prims) $
  Map.fromList
  [ ("Prelude.bvShl" , bvShiftOp (Prims.vShiftL RME.false))
  , ("Prelude.bvShr" , bvShiftOp (Prims.vShiftR RME.false))
  , ("Prelude.bvSShr", bvShiftOp vSignedShiftR)
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

  -- Misc
  , ("Prelude.expByNat", Prims.expByNatOp prims)
  ]

-- primitive bvToInt : (n : Nat) -> Vec n Bool -> Integer;
bvToIntOp :: RValue
bvToIntOp = unsupportedRMEPrimitive "bvToIntOp"

-- primitive sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: RValue
sbvToIntOp = unsupportedRMEPrimitive "sbvToIntOp"

-- primitive intToBv : (n : Nat) -> Integer -> Vec n Bool;
intToBvOp :: RValue
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \x -> return $
    VWord (V.reverse (V.generate (fromIntegral n) (RME.constant . testBit x)))

muxRMEV :: RME -> Vector RME -> Vector RME -> Vector RME
muxRMEV b = V.zipWith (RME.mux b)

muxInt :: RME -> Integer -> Integer -> Integer
muxInt b x y =
  case RME.isBool b of
    Just c -> if c then x else y
    Nothing -> if x == y then x else error $ "muxRValue: VInt " ++ show (x, y)

muxExtra :: TValue ReedMuller -> RME -> RExtra -> RExtra -> IO RExtra
muxExtra (VDataType "Prelude.Stream" [TValue tp]) b s1 s2 =
  do r <- newIORef mempty
     let fn n = do x <- lookupRExtra s1 n
                   y <- lookupRExtra s2 n
                   muxRValue tp b x y
     pure (AStream fn r)
muxExtra tp _ _ _ = panic "RME.muxExtra" ["type mismatch", show tp]

muxRValue :: TValue ReedMuller -> RME -> RValue -> RValue -> IO RValue
muxRValue tp b x y = Prims.muxValue prims tp b x y

-- | Signed shift right simply copies the high order bit
--   into the shifted places.  We special case the zero
--   length vector to avoid a possible out-of-bounds error.
vSignedShiftR :: V.Vector a -> Integer -> V.Vector a
vSignedShiftR xs i
  | V.length xs > 0 = Prims.vShiftR x xs i
  | otherwise       = xs
 where x = xs V.! 0

------------------------------------------------------------

toIntModOp :: RValue
toIntModOp =
  Prims.natFun $ \n -> return $
  Prims.intFun "toIntModOp" $ \x -> return $
  VIntMod n (x `mod` toInteger n)

fromIntModOp :: RValue
fromIntModOp =
  constFun $
  Prims.intModFun "fromIntModOp" $ \x -> return $
  VInt x

intModEqOp :: RValue
intModEqOp =
  constFun $
  Prims.intModFun "intModEqOp" $ \x -> return $
  Prims.intModFun "intModEqOp" $ \y -> return $
  VBool (RME.constant (x == y))

intModBinOp :: (Integer -> Integer -> Integer) -> RValue
intModBinOp f =
  Prims.natFun $ \n -> return $
  Prims.intModFun "intModBinOp x" $ \x -> return $
  Prims.intModFun "intModBinOp y" $ \y -> return $
  VIntMod n (f x y `mod` toInteger n)

intModUnOp :: (Integer -> Integer) -> RValue
intModUnOp f =
  Prims.natFun $ \n -> return $
  Prims.intModFun "intModUnOp" $ \x -> return $
  VIntMod n (f x `mod` toInteger n)

----------------------------------------

lookupRExtra :: RExtra -> Natural -> IO RValue
lookupRExtra (AStream f r) i =
  do m <- readIORef r
     case Map.lookup i m of
       Just v -> pure v
       Nothing ->
         do v <- f i
            modifyIORef' r (Map.insert i v)
            pure v

lookupStream :: RValue -> Natural -> IO RValue
lookupStream (VExtra ex) n = lookupRExtra ex n
lookupStream _ _ = panic "RME.lookupStream" ["Expected stream value"]

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: RValue
mkStreamOp =
  constFun $
  strictFun $ \f ->
    do r <- newIORef mempty
       let fn n = apply f (ready (VNat n))
       pure (VExtra (AStream fn r))

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: RValue
streamGetOp =
  strictFun $ \(toTValue -> tp) -> return $
  pureFun $ \xs ->
  strictFun $ \case
    VNat n -> lookupStream xs n
    VBVToNat _sz bv ->
      do let loop k [] = lookupStream xs k
             loop k (b:bs)
               | Just True <- RME.isBool b
               = loop k1 bs
               | Just False <- RME.isBool b
               = loop k0 bs
               | otherwise
               = do s1 <- loop k1 bs
                    s2 <- loop 0 bs
                    muxRValue tp b s1 s2
              where
               k0 = k `shiftL` 1
               k1 = k0 + 1
         loop (0::Natural) . V.toList =<< toWord bv

    v -> panic "Verifer.SAW.Simulator.RME.streamGetOp"
               [ "Expected Nat value", show v ]

------------------------------------------------------------
-- Generating variables for arguments

newVars :: FiniteType -> State Int RValue
newVars FTBit = do
  i <- get
  put (i + 1)
  return (vBool (RME.lit i))
newVars (FTVec n t) = VVector <$> V.replicateM (fromIntegral n) (newVars' t)
newVars (FTTuple ts) = vTuple <$> traverse newVars' ts
newVars (FTRec tm) = vRecord <$> traverse newVars' tm

newVars' :: FiniteType -> State Int RThunk
newVars' shape = ready <$> newVars shape

------------------------------------------------------------
-- Bit-blasting primitives.

bitBlastBasic :: ModuleMap
              -> Map Ident RValue
              -> Map VarIndex RValue
              -> Term
              -> IO RValue
bitBlastBasic m addlPrims ecMap t = do
  let neutral _env nt = return $ Prim.userError $ "Could not evaluate neutral term\n:" ++ show nt

  cfg <- Sim.evalGlobal m (Map.union constMap addlPrims)
         (\ec -> case Map.lookup (ecVarIndex ec) ecMap of
                   Just v -> pure v
                   Nothing -> error ("RME: unknown ExtCns: " ++ show (ecName ec)))
         (const Nothing)
         neutral
  Sim.evalSharedTerm cfg t


processVar ::
  (ExtCns Term, FirstOrderType) ->
  IO (ExtCns Term, FiniteType)
processVar (ec, fot) =
  case toFiniteType fot of
    Nothing -> fail ("RME solver does not support variables of type " ++ show fot)
    Just ft -> pure (ec, ft)

withBitBlastedSATQuery ::
  SharedContext ->
  Map Ident RValue ->
  SATQuery ->
  (RME -> [(ExtCns Term, FiniteType)] -> IO a) ->
  IO a
withBitBlastedSATQuery sc addlPrims satq cont =
  do unless (Set.null (satUninterp satq)) $ fail
        "RME prover does not support uninterpreted symbols"
     t <- satQueryAsTerm sc satq
     varShapes <- mapM processVar (Map.toList (satVariables satq))
     modmap <- scGetModuleMap sc
     let vars = evalState (traverse (traverse newVars) varShapes) 0
     let varMap = Map.fromList [ (ecVarIndex ec, v) | (ec,v) <- vars ]
     bval <- bitBlastBasic modmap addlPrims varMap t
     case bval of
       VBool anf -> cont anf varShapes
       _ -> panic "Verifier.SAW.Simulator.RME.bitBlast" ["non-boolean result type."]
