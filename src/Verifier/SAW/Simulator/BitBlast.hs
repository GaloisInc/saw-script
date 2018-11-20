{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}

{- |
Module      : Verifier.SAW.Simulator.BitBlast
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.BitBlast
  ( BValue
  , withBitBlastedPred
  , withBitBlastedTerm
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable
#endif
import Control.Monad ((<=<))
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

import Verifier.SAW.FiniteValue (FiniteType(..))
import Verifier.SAW.Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.Simulator.Concrete as Concrete
import qualified Verifier.SAW.Recognizer as R

import qualified Data.AIG as AIG

type LitVector l = AIG.BV l

------------------------------------------------------------
-- Vector operations

lvFromV :: V.Vector l -> LitVector l
lvFromV v = AIG.generate_msb0 (V.length v) ((V.!) v)

vFromLV :: LitVector l -> V.Vector l
vFromLV lv = V.generate (AIG.length lv) (AIG.at lv)

lvRotateL :: LitVector l -> Integer -> LitVector l
lvRotateL xs i
  | AIG.length xs == 0 = xs
  | otherwise = (AIG.++) (AIG.drop j xs) (AIG.take j xs)
  where j = fromInteger (i `mod` toInteger (AIG.length xs))

lvRotateR :: LitVector l -> Integer -> LitVector l
lvRotateR xs i = lvRotateL xs (- i)

lvShiftL :: l -> LitVector l -> Integer -> LitVector l
lvShiftL x xs i = (AIG.++) (AIG.drop j xs) (AIG.replicate j x)
  where j = fromInteger (min i (toInteger (AIG.length xs)))

lvShl :: l -> LitVector l -> Nat -> LitVector l
lvShl l v i = AIG.slice v j (n-j) AIG.++ AIG.replicate j l
  where n = AIG.length v
        j = fromIntegral i `min` n

lvShiftR :: l -> LitVector l -> Integer -> LitVector l
lvShiftR x xs i = (AIG.++) (AIG.replicate j x) (AIG.take (AIG.length xs - j) xs)
  where j = fromInteger (min i (toInteger (AIG.length xs)))

lvShr :: l -> LitVector l -> Nat -> LitVector l
lvShr l v i = AIG.replicate j l AIG.++ AIG.slice v 0 (n-j)
  where n = AIG.length v
        j = fromIntegral i `min` n

------------------------------------------------------------
-- Values

data BitBlast l

type instance EvalM (BitBlast l) = IO
type instance VBool (BitBlast l) = l
type instance VWord (BitBlast l) = LitVector l
type instance VInt  (BitBlast l) = Integer
type instance Extra (BitBlast l) = BExtra l

type BValue l = Value (BitBlast l)
type BThunk l = Thunk (BitBlast l)

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
flattenBValue (VRecordValue elems) = do
  AIG.concat <$> mapM (flattenBValue <=< force . snd) elems
flattenBValue _ = error $ unwords ["Verifier.SAW.Simulator.BitBlast.flattenBValue: unsupported value"]

wordFun :: (LitVector l -> IO (BValue l)) -> BValue l
wordFun f = strictFun (\x -> toWord x >>= f)

------------------------------------------------------------

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

lvSShr :: LitVector l -> Nat -> LitVector l
lvSShr v i = lvShr (AIG.msb v) v i

------------------------------------------------------------

pure1 :: Applicative f => (a -> b) -> a -> f b
pure1 f x = pure (f x)

pure2 :: Applicative f => (a -> b -> c) -> a -> b -> f c
pure2 f x y = pure (f x y)

pure3 :: Applicative f => (a -> b -> c -> d) -> a -> b -> c -> f d
pure3 f x y z = pure (f x y z)

prims :: AIG.IsAIG l g => g s -> Prims.BasePrims (BitBlast (l s))
prims be =
  Prims.BasePrims
  { Prims.bpAsBool  = AIG.asConstant be
    -- Bitvectors
  , Prims.bpUnpack  = pure1 vFromLV
  , Prims.bpPack    = pure1 lvFromV
  , Prims.bpBvAt    = pure2 AIG.at
  , Prims.bpBvLit   = pure2 (AIG.bvFromInteger be)
  , Prims.bpBvSize  = AIG.length
  , Prims.bpBvJoin  = pure2 (AIG.++)
  , Prims.bpBvSlice = pure3 (\i n v -> AIG.slice v i n)
    -- Conditionals
  , Prims.bpMuxBool  = \b x y -> AIG.lazyMux be b (pure x) (pure y)
  , Prims.bpMuxWord  = \b x y -> AIG.iteM be b (pure x) (pure y)
  , Prims.bpMuxInt   = muxInt
  , Prims.bpMuxExtra = muxBExtra be
    -- Booleans
  , Prims.bpTrue   = AIG.trueLit be
  , Prims.bpFalse  = AIG.falseLit be
  , Prims.bpNot    = pure1 AIG.not
  , Prims.bpAnd    = AIG.and be
  , Prims.bpOr     = AIG.or be
  , Prims.bpXor    = AIG.xor be
  , Prims.bpBoolEq = AIG.eq be
    -- Bitvector logical
  , Prims.bpBvNot  = pure1 (fmap AIG.not)
  , Prims.bpBvAnd  = AIG.zipWithM (AIG.and be)
  , Prims.bpBvOr   = AIG.zipWithM (AIG.or be)
  , Prims.bpBvXor  = AIG.zipWithM (AIG.xor be)
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = AIG.neg be
  , Prims.bpBvAdd  = AIG.add be
  , Prims.bpBvSub  = AIG.sub be
  , Prims.bpBvMul  = AIG.mul be
  , Prims.bpBvUDiv = AIG.uquot be
  , Prims.bpBvURem = AIG.urem be
  , Prims.bpBvSDiv = AIG.squot be
  , Prims.bpBvSRem = AIG.srem be
  , Prims.bpBvLg2  = bitblastLogBase2 be
    -- Bitvector comparisons
  , Prims.bpBvEq   = AIG.bvEq be
  , Prims.bpBvsle  = AIG.sle be
  , Prims.bpBvslt  = AIG.slt be
  , Prims.bpBvule  = AIG.ule be
  , Prims.bpBvult  = AIG.ult be
  , Prims.bpBvsge  = flip (AIG.sle be)
  , Prims.bpBvsgt  = flip (AIG.slt be)
  , Prims.bpBvuge  = flip (AIG.ule be)
  , Prims.bpBvugt  = flip (AIG.ult be)
    -- Bitvector shift/rotate
  , Prims.bpBvRolInt = pure2 lvRotateL
  , Prims.bpBvRorInt = pure2 lvRotateR
  , Prims.bpBvShlInt = pure3 lvShiftL
  , Prims.bpBvShrInt = pure3 lvShiftR
  , Prims.bpBvRol    = genShift be lvRotateL
  , Prims.bpBvRor    = genShift be lvRotateR
  , Prims.bpBvShl    = genShift be . lvShiftL
  , Prims.bpBvShr    = genShift be . lvShiftR
    -- Integer operations
  , Prims.bpIntAdd = pure2 (+)
  , Prims.bpIntSub = pure2 (-)
  , Prims.bpIntMul = pure2 (*)
  , Prims.bpIntDiv = pure2 div
  , Prims.bpIntMod = pure2 mod
  , Prims.bpIntNeg = pure1 negate
  , Prims.bpIntAbs = pure1 abs
  , Prims.bpIntEq  = pure2 (\x y -> AIG.constant be (x == y))
  , Prims.bpIntLe  = pure2 (\x y -> AIG.constant be (x <= y))
  , Prims.bpIntLt  = pure2 (\x y -> AIG.constant be (x < y))
  , Prims.bpIntMin = pure2 min
  , Prims.bpIntMax = pure2 max
  }

beConstMap :: AIG.IsAIG l g => g s -> Map Ident (BValue (l s))
beConstMap be =
  Map.union (Prims.constMap (prims be)) $
  Map.fromList
  -- Shifts
  [ ("Prelude.bvShl" , bvShiftOp (AIG.shl be) (lvShl (AIG.falseLit be)))
  , ("Prelude.bvShr" , bvShiftOp (AIG.ushr be) (lvShr (AIG.falseLit be)))
  , ("Prelude.bvSShr", bvShiftOp (AIG.sshr be) lvSShr)
  -- Integers
  , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", Prims.natToIntOp)
  , ("Prelude.intToBv" , intToBvOp be)
  , ("Prelude.bvToInt" , bvToIntOp be)
  , ("Prelude.sbvToInt", sbvToIntOp be)
  -- Integers mod n
  , ("Prelude.IntMod"    , constFun VIntType)
  , ("Prelude.toIntMod"  , toIntModOp)
  , ("Prelude.fromIntMod", VFun force)
  , ("Prelude.intModEq"  , intModEqOp be)
  , ("Prelude.intModAdd" , intModBinOp (+))
  , ("Prelude.intModSub" , intModBinOp (-))
  , ("Prelude.intModMul" , intModBinOp (*))
  , ("Prelude.intModNeg" , intModUnOp negate)
-- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp be)
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

muxBVal :: AIG.IsAIG l g => g s -> l s -> BValue (l s) -> BValue (l s) -> IO (BValue (l s))
muxBVal be = Prims.muxValue (prims be)

muxInt :: a -> Integer -> Integer -> IO Integer
muxInt _ x y = if x == y then return x else fail $ "muxBVal: VInt " ++ show (x, y)

muxBExtra :: AIG.IsAIG l g => g s -> l s -> BExtra (l s) -> BExtra (l s) -> IO (BExtra (l s))
muxBExtra _ _ _ _ = fail "Verifier.SAW.Simulator.BitBlast.iteOp: malformed arguments"

-- | Barrel-shifter algorithm. Takes a list of bits in big-endian order.
genShift ::
  AIG.IsAIG l g => g s -> (LitVector (l s) -> Integer -> LitVector (l s)) ->
  LitVector (l s) -> LitVector (l s) -> IO (LitVector (l s))
genShift be op x y = Prims.shifter (AIG.ite be) (pure2 op) x (AIG.bvToList y)

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

------------------------------------------------------------

toIntModOp :: BValue l
toIntModOp =
  Prims.natFun $ \n -> return $
  Prims.intFun "toIntModOp" $ \x -> return $
  VInt (x `mod` toInteger n)

intModEqOp :: AIG.IsAIG l g => g s -> BValue (l s)
intModEqOp be =
  constFun $
  Prims.intFun "intModEqOp" $ \x -> return $
  Prims.intFun "intModEqOp" $ \y -> return $
  VBool (AIG.constant be (x == y))

intModBinOp :: (Integer -> Integer -> Integer) -> BValue l
intModBinOp f =
  Prims.natFun $ \n -> return $
  Prims.intFun "intModBinOp x" $ \x -> return $
  Prims.intFun "intModBinOp y" $ \y -> return $
  VInt (f x y `mod` toInteger n)

intModUnOp :: (Integer -> Integer) -> BValue l
intModUnOp f =
  Prims.natFun $ \n -> return $
  Prims.intFun "intModUnOp" $ \x -> return $
  VInt (f x `mod` toInteger n)

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
              -> ModuleMap
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
    _                            -> fail $ "Verifier.SAW.Simulator.BitBlast.asPredType: non-boolean result type: "
                                    ++ scPrettyTerm defaultPPOpts t'

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
  modmap <- scGetModuleMap sc
  bval <- bitBlastBasic be modmap addlPrims t
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
    _                            -> fail $ "Verifier.SAW.Simulator.BitBlast.adAIGType: invalid AIG type: "
                                    ++ scPrettyTerm defaultPPOpts t'

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
  modmap <- scGetModuleMap sc
  bval <- bitBlastBasic be modmap addlPrims t
  bval' <- applyAll bval vars
  v <- flattenBValue bval'
  c be v

asFiniteType :: SharedContext -> Term -> IO FiniteType
asFiniteType sc t =
  scGetModuleMap sc >>= \modmap ->
  case asFiniteTypeValue (Concrete.evalSharedTerm modmap Map.empty t) of
    Just ft -> return ft
    Nothing ->
      fail $ "asFiniteType: unsupported type " ++ scPrettyTerm defaultPPOpts t
