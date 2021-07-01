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
  , runIdentity
  , withBitBlastedSATQuery
  ) where

import Control.Monad.Identity
import Control.Monad.State
import Data.Bits
import Data.IntTrie (IntTrie)
import qualified Data.IntTrie as IntTrie
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as V

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
evalSharedTerm :: ModuleMap -> Map Ident RPrim -> Term -> RValue
evalSharedTerm m addlPrims t =
  runIdentity $ do
    cfg <- Sim.evalGlobal m (Map.union constMap addlPrims)
           extcns (const Nothing) neutral primHandler
    Sim.evalSharedTerm cfg t
  where
    extcns ec = return $ Prim.userError $ "Unimplemented: external constant " ++ show (ecName ec)
    neutral _env nt = return $ Prim.userError $ "Could not evaluate neutral term\n:" ++ show nt
    primHandler pn msg env _tv =
      return $ Prim.userError $ unlines
        [ "Could not evaluate primitive " ++ show (primName pn)
        , "On argument " ++ show (length env)
        , Text.unpack msg
        ]

------------------------------------------------------------
-- Values

data ReedMuller

type instance EvalM ReedMuller = Identity
type instance VBool ReedMuller = RME
type instance VWord ReedMuller = Vector RME
type instance VInt  ReedMuller = Integer
type instance VArray ReedMuller = ()
type instance Extra ReedMuller = RExtra

type RValue = Value ReedMuller
type RPrim  = Prims.Prim ReedMuller
type RThunk = Thunk ReedMuller

data RExtra = AStream (IntTrie RValue)

instance Show RExtra where
  show (AStream _) = "<stream>"

vBool :: RME -> RValue
vBool b = VBool b

toBool :: RValue -> RME
toBool (VBool b) = b
toBool x = error $ unwords ["Verifier.SAW.Simulator.RME.toBool", show x]

vWord :: Vector RME -> RValue
vWord x = VWord x

toWord :: RValue -> Vector RME
toWord (VWord x) = x
toWord (VVector vv) = fmap (toBool . runIdentity . force) vv
toWord x = error $ unwords ["Verifier.SAW.Simulator.RME.toWord", show x]

vStream :: IntTrie RValue -> RValue
vStream x = VExtra (AStream x)

toStream :: RValue -> IntTrie RValue
toStream (VExtra (AStream x)) = x
toStream x = error $ unwords ["Verifier.SAW.Simulator.RME.toStream", show x]

wordFun :: (Vector RME -> RPrim) -> RPrim
wordFun f = Prims.strictFun (\x -> f (toWord x))

genShift :: (a -> b -> b -> b) -> (b -> Integer -> b) -> b -> Vector a -> b
genShift cond f x0 v = go x0 (V.toList v)
  where
    go x [] = x
    go x (y : ys) = go (cond y (f x (2 ^ length ys)) x) ys

-- | op : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvShiftOp :: (Vector RME -> Integer -> Vector RME) -> RPrim
bvShiftOp op =
  Prims.constFun $
  wordFun $ \x ->
  Prims.strictFun $ \y ->
  Prims.PrimValue $
    case y of
      VNat n   -> vWord (op x (toInteger n))
      VBVToNat _sz v -> vWord (genShift muxRMEV op x (toWord v))
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
  , Prims.bpUnpack  = Identity
  , Prims.bpPack    = Identity
  , Prims.bpBvAt    = pure2 (V.!)
  , Prims.bpBvLit   = pure2 RMEV.integer
  , Prims.bpBvSize  = V.length
  , Prims.bpBvJoin  = pure2 (V.++)
  , Prims.bpBvSlice = pure3 V.slice
    -- Conditionals
  , Prims.bpMuxBool  = pure3 RME.mux
  , Prims.bpMuxWord  = pure3 muxRMEV
  , Prims.bpMuxInt   = pure3 muxInt
  , Prims.bpMuxExtra = \tp -> pure3 (muxExtra tp)
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

constMap :: Map Ident RPrim
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
bvToIntOp :: RPrim
bvToIntOp = unsupportedRMEPrimitive "bvToIntOp"

-- primitive sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: RPrim
sbvToIntOp = unsupportedRMEPrimitive "sbvToIntOp"

-- primitive intToBv : (n : Nat) -> Integer -> Vec n Bool;
intToBvOp :: RPrim
intToBvOp =
  Prims.natFun $ \n ->
  Prims.intFun $ \x -> Prims.PrimValue $
    VWord (V.reverse (V.generate (fromIntegral n) (RME.constant . testBit x)))

muxRMEV :: RME -> Vector RME -> Vector RME -> Vector RME
muxRMEV b = V.zipWith (RME.mux b)

muxInt :: RME -> Integer -> Integer -> Integer
muxInt b x y =
  case RME.isBool b of
    Just c -> if c then x else y
    Nothing -> if x == y then x else error $ "muxRValue: VInt " ++ show (x, y)

muxExtra :: TValue ReedMuller -> RME -> RExtra -> RExtra -> RExtra
muxExtra (VDataType (primName -> "Prelude.Stream") [TValue tp] []) b (AStream xs) (AStream ys) =
  AStream (muxRValue tp b <$> xs <*> ys)
muxExtra tp _ _ _ = panic "RME.muxExtra" ["type mismatch", show tp]

muxRValue :: TValue ReedMuller -> RME -> RValue -> RValue -> RValue
muxRValue tp b x y = runIdentity $ Prims.muxValue prims tp b x y

-- | Signed shift right simply copies the high order bit
--   into the shifted places.  We special case the zero
--   length vector to avoid a possible out-of-bounds error.
vSignedShiftR :: V.Vector a -> Integer -> V.Vector a
vSignedShiftR xs i
  | V.length xs > 0 = Prims.vShiftR x xs i
  | otherwise       = xs
 where x = xs V.! 0

------------------------------------------------------------

toIntModOp :: RPrim
toIntModOp =
  Prims.natFun $ \n -> 
  Prims.intFun $ \x ->
    Prims.PrimValue (VIntMod n (x `mod` toInteger n))

fromIntModOp :: RPrim
fromIntModOp =
  Prims.constFun $
  Prims.intModFun $ \x -> 
    Prims.PrimValue (VInt x)

intModEqOp :: RPrim
intModEqOp =
  Prims.constFun $
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
    Prims.PrimValue (VBool (RME.constant (x == y)))

intModBinOp :: (Integer -> Integer -> Integer) -> RPrim
intModBinOp f =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
    Prims.PrimValue (VIntMod n (f x y `mod` toInteger n))

intModUnOp :: (Integer -> Integer) -> RPrim
intModUnOp f =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
    Prims.PrimValue (VIntMod n (f x `mod` toInteger n))

----------------------------------------

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: RPrim
mkStreamOp =
  Prims.constFun $
  Prims.strictFun $ \f ->
    Prims.PrimValue (vStream (fmap (\n -> runIdentity (apply f (ready (VNat n)))) IntTrie.identity))

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: RPrim
streamGetOp =
  Prims.tvalFun   $ \tp ->
  Prims.strictFun $ \xs ->
  Prims.strictFun $ \ix -> Prims.Prim $ case ix of
    VNat n -> pure $ IntTrie.apply (toStream xs) (toInteger n)
    VIntToNat _i -> error "RME.streamGetOp : symbolic integer TODO"
    VBVToNat _sz bv ->
      do let trie = toStream xs
             loop k [] = IntTrie.apply trie k
             loop k (b:bs)
               | Just True <- RME.isBool b
               = loop k1 bs
               | Just False <- RME.isBool b
               = loop k0 bs
               | otherwise
               = muxRValue tp b (loop k1 bs) (loop k0 bs)
              where
               k0 = k `shiftL` 1
               k1 = k0 + 1
         pure $ loop (0::Integer) (V.toList (toWord bv))

    _ -> panic "Verifer.SAW.Simulator.RME.streamGetOp"
               [ "Expected Nat value", show ix ]


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
              -> Map Ident RPrim
              -> Map VarIndex RValue
              -> Term
              -> RValue
bitBlastBasic m addlPrims ecMap t = runIdentity $ do
  let neutral _env nt = return $ Prim.userError $ "Could not evaluate neutral term\n:" ++ show nt
  let primHandler pn msg env _tv =
         return $ Prim.userError $ unlines
           [ "Could not evaluate primitive " ++ show (primName pn)
           , "On argument " ++ show (length env)
           , Text.unpack msg
           ]

  cfg <- Sim.evalGlobal m (Map.union constMap addlPrims)
         (\ec -> case Map.lookup (ecVarIndex ec) ecMap of
                   Just v -> pure v
                   Nothing -> error ("RME: unknown ExtCns: " ++ show (ecName ec)))
         (const Nothing)
         neutral
         primHandler
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
  Map Ident RPrim ->
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
     let bval = bitBlastBasic modmap addlPrims varMap t
     case bval of
       VBool anf -> cont anf varShapes
       _ -> panic "Verifier.SAW.Simulator.RME.bitBlast" ["non-boolean result type."]
