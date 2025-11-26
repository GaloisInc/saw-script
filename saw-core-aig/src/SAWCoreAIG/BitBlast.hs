{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

{- |
Module      : SAWCoreAIG.BitBlast
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCoreAIG.BitBlast
  ( BValue
  , withBitBlastedTerm
  , withBitBlastedSATQuery
  ) where

import Control.Monad ((<=<),unless)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Vector as V
import Numeric.Natural (Natural)

import qualified SAWSupport.Pretty as PPS (defaultOpts)

import SAWCore.FiniteValue (FiniteType(..),FirstOrderType(..),toFiniteType)
import SAWCore.Name (VarName(..))
import SAWCore.Module (ModuleMap)
import qualified SAWCore.Simulator as Sim
import SAWCore.Simulator.Value
import qualified SAWCore.Simulator.Prims as Prims
import SAWCore.SATQuery
import SAWCore.SharedTerm
import qualified SAWCore.Simulator.Concrete as Concrete
import qualified SAWCore.Prim as Prim
import qualified SAWCore.Recognizer as R
import SAWCore.Term.Pretty (scPrettyTerm)

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

lvShl :: l -> LitVector l -> Natural -> LitVector l
lvShl l v i = AIG.slice v j (n-j) AIG.++ AIG.replicate j l
  where n = AIG.length v
        j = fromIntegral i `min` n

lvShiftR :: l -> LitVector l -> Integer -> LitVector l
lvShiftR x xs i = (AIG.++) (AIG.replicate j x) (AIG.take (AIG.length xs - j) xs)
  where j = fromInteger (min i (toInteger (AIG.length xs)))

lvShr :: l -> LitVector l -> Natural -> LitVector l
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
type BPrim  l = Prims.Prim (BitBlast l)
type BThunk l = Thunk (BitBlast l)

data BExtra l
  = BStream (Natural -> IO (BValue l)) (IORef (Map Natural (BValue l)))

instance Show (BExtra l) where
  show (BStream _ _) = "BStream"

vBool :: l -> BValue l
vBool l = VBool l

toBool :: BValue l -> l
toBool (VBool l) = l
toBool x = error $ unwords ["SAWCoreAIG.BitBlast.toBool", show x]

vWord :: LitVector l -> BValue l
vWord lv = VWord lv

toWord :: BValue l -> IO (LitVector l)
toWord (VWord lv) = return lv
toWord (VVector vv) = lvFromV <$> traverse (fmap toBool . force) vv
toWord x = fail $ unwords ["SAWCoreAIG.BitBlast.toWord", show x]

flattenBValue :: BValue l -> IO (LitVector l)
flattenBValue (VBool l) = return (AIG.replicate 1 l)
flattenBValue (VWord lv) = return lv
flattenBValue (VExtra (BStream _ _)) = error "SAWCoreAIG.BitBlast.flattenBValue: BStream"
flattenBValue (VVector vv) =
  AIG.concat <$> traverse (flattenBValue <=< force) (V.toList vv)
flattenBValue VUnit = return $ AIG.concat []
flattenBValue (VPair x y) = do
  vx <- flattenBValue =<< force x
  vy <- flattenBValue =<< force y
  return $ AIG.concat [vx, vy]
flattenBValue (VRecordValue elems) = do
  AIG.concat <$> mapM (flattenBValue <=< force . snd) elems
flattenBValue _ = error $ unwords ["SAWCoreAIG.BitBlast.flattenBValue: unsupported value"]

------------------------------------------------------------

-- | op : (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool
bvShiftOp :: (LitVector l -> LitVector l -> IO (LitVector l))
          -> (LitVector l -> Natural -> LitVector l)
          -> BPrim l
bvShiftOp bvOp natOp =
  Prims.constFun $
  Prims.wordFun (pure1 lvFromV) $ \x ->
  Prims.strictFun $ \y -> Prims.Prim $
    case y of
      VNat n   -> return (vWord (natOp x n))
      VBVToNat _ v -> fmap vWord (bvOp x =<< toWord v)
      _        -> error $ unwords ["SAWCoreAIG.BitBlast.shiftOp", show y]

lvSShr :: LitVector l -> Natural -> LitVector l
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
  { Prims.bpIsSymbolicEvaluator = True
  , Prims.bpAsBool  = AIG.asConstant be
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
  , Prims.bpMuxArray = unsupportedAIGPrimitive "bpMuxArray"
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
    -- Bitvector misc
  , Prims.bpBvPopcount = AIG.popCount be
  , Prims.bpBvCountLeadingZeros = AIG.countLeadingZeros be
  , Prims.bpBvCountTrailingZeros = AIG.countTrailingZeros be
  , Prims.bpBvForall = unsupportedAIGPrimitive "bvForall"

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

    -- Array operations
  , Prims.bpArrayConstant = unsupportedAIGPrimitive "bpArrayConstant"
  , Prims.bpArrayLookup = unsupportedAIGPrimitive "bpArrayLookup"
  , Prims.bpArrayUpdate = unsupportedAIGPrimitive "bpArrayUpdate"
  , Prims.bpArrayEq = unsupportedAIGPrimitive "bpArrayEq"
  , Prims.bpArrayCopy = unsupportedAIGPrimitive "bpArrayCopy"
  , Prims.bpArraySet = unsupportedAIGPrimitive "bpArraySet"
  , Prims.bpArrayRangeEq = unsupportedAIGPrimitive "bpArrayRangeEq"
  }

unsupportedAIGPrimitive :: String -> a
unsupportedAIGPrimitive = Prim.unsupportedPrimitive "AIG"

beConstMap :: AIG.IsAIG l g => g s -> Map Ident (BPrim (l s))
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
  , ("Prelude.toIntMod"  , toIntModOp)
  , ("Prelude.fromIntMod", fromIntModOp)
  , ("Prelude.intModEq"  , intModEqOp be)
  , ("Prelude.intModAdd" , intModBinOp (+))
  , ("Prelude.intModSub" , intModBinOp (-))
  , ("Prelude.intModMul" , intModBinOp (*))
  , ("Prelude.intModNeg" , intModUnOp negate)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp be)
  -- Misc
  , ("Prelude.expByNat", Prims.expByNatOp (prims be))
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

muxBExtra :: AIG.IsAIG l g => g s ->
  l s -> BExtra (l s) -> BExtra (l s) -> IO (BExtra (l s))
muxBExtra be c x y =
  do let f i = do xi <- lookupBStream (VExtra x) i
                  yi <- lookupBStream (VExtra y) i
                  muxBVal be c xi yi
     r <- newIORef Map.empty
     return (BStream f r)

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

-- primitive bvToInt : (n : Nat) -> Vec n Bool -> Integer;
bvToIntOp :: AIG.IsAIG l g => g s -> BPrim (l s)
bvToIntOp g =
  Prims.constFun $
  Prims.wordFun (pure1 lvFromV) $ \v ->
  Prims.Prim $
   case AIG.asUnsigned g v of
      Just i -> return $ VInt i
      Nothing -> fail "Cannot convert symbolic bitvector to integer"

-- primitive sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: AIG.IsAIG l g => g s -> BPrim (l s)
sbvToIntOp g =
  Prims.constFun $
  Prims.wordFun (pure1 lvFromV) $ \v ->
  Prims.Prim $
   case AIG.asSigned g v of
      Just i -> return $ VInt i
      Nothing -> fail "Cannot convert symbolic bitvector to integer"

-- primitive intToBv : (n : Nat) -> Integer -> Vec n Bool;
intToBvOp :: AIG.IsAIG l g => g s -> BPrim (l s)
intToBvOp g =
  Prims.natFun $ \n ->
  Prims.intFun $ \x -> Prims.Prim 
    (VWord <$>
     if n >= 0 then return (AIG.bvFromInteger g (fromIntegral n) x)
               else AIG.neg g (AIG.bvFromInteger g (fromIntegral n) (negate x)))

------------------------------------------------------------

toIntModOp :: BPrim l
toIntModOp =
  Prims.natFun $ \n ->
  Prims.intFun $ \x ->
    Prims.PrimValue (VIntMod n (x `mod` toInteger n))

fromIntModOp :: BPrim l
fromIntModOp =
  Prims.constFun $
  Prims.intModFun $ \x ->
    Prims.PrimValue (VInt x)

intModEqOp :: AIG.IsAIG l g => g s -> BPrim (l s)
intModEqOp be =
  Prims.constFun $
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
    Prims.PrimValue (VBool (AIG.constant be (x == y)))

intModBinOp :: (Integer -> Integer -> Integer) -> BPrim l
intModBinOp f =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
    Prims.PrimValue (VIntMod n (f x y `mod` toInteger n))

intModUnOp :: (Integer -> Integer) -> BPrim l
intModUnOp f =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
    Prims.PrimValue (VIntMod n (f x `mod` toInteger n))

----------------------------------------

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: BPrim l
mkStreamOp =
  Prims.constFun $
  Prims.strictFun $ \f ->
  Prims.Prim $
    do r <- newIORef Map.empty
       return $ VExtra (BStream (\n -> apply f (ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: AIG.IsAIG l g => g s -> BPrim (l s)
streamGetOp be =
  Prims.tvalFun   $ \_tp ->
  Prims.strictFun $ \xs ->
  Prims.strictFun $ \ix ->
  Prims.Prim $ case ix of
    VNat n -> lookupBStream xs n
    VBVToNat _ w ->
       do bs <- toWord w
          AIG.muxInteger (lazyMux be (muxBVal be)) ((2 ^ AIG.length bs) - 1) bs (lookupBStream xs)
    v -> fail (unlines ["SAWCoreAIG.BitBlast.streamGetOp", "Expected Nat value", show v])


lookupBStream :: BValue l -> Natural -> IO (BValue l)
lookupBStream (VExtra (BStream f r)) n = do
   m <- readIORef r
   case Map.lookup n m of
     Just v  -> return v
     Nothing -> do v <- f n
                   writeIORef r (Map.insert n v m)
                   return v
lookupBStream _ _ = fail "SAWCoreAIG.BitBlast.lookupBStream: expected Stream"

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

type PrimMap l g = forall s. g s -> Map Ident (BPrim (l s))

bitBlastBasic :: AIG.IsAIG l g
              => g s
              -> ModuleMap
              -> PrimMap l g
              -> Map VarIndex (BValue (l s))
              -> Term
              -> IO (BValue (l s))
bitBlastBasic be m addlPrims varMap t = do
  let primHandler = Sim.defaultPrimHandler
  cfg <- Sim.evalGlobal m (Map.union (beConstMap be) (addlPrims be))
         (bitBlastVariable varMap)
         (\_ _ -> Nothing)
         (\_ _ -> Nothing)
         primHandler
         (Prims.lazyMuxValue (prims be))
  Sim.evalSharedTerm cfg t

bitBlastVariable ::
  Map VarIndex (BValue (l s)) -> VarName -> TValue (BitBlast (l s)) ->
  IO (BValue (l s))
bitBlastVariable varMap (VarName idx name) _v =
  case Map.lookup idx varMap of
    Just var -> return var
    Nothing -> fail $
      "SAWCoreAIG.BitBlast: can't translate variable " ++
      show name ++ "(index: " ++ show idx ++ ")"

asPiTypes :: SharedContext -> Term -> IO ([(String, Term)], Term)
asPiTypes sc t =
  do t' <- scWhnf sc t
     case R.asPi t' of
       Nothing -> pure ([], t)
       Just (n, t1, t2) ->
         do (args, ret) <- asPiTypes sc t2
            pure ((Text.unpack (vnName n), t1) : args, ret)

bitBlastTerm ::
  AIG.IsAIG l g =>
  g s ->
  SharedContext ->
  PrimMap l g ->
  Term ->
  IO (BValue (l s), [(String, FiniteType)])
bitBlastTerm be sc addlPrims t = do
  ty <- scTypeOf sc t
  (args, ret) <- asPiTypes sc ty
  let frees = getAllVars t
  argShapes <- traverse (asFiniteType sc) (map snd args)
  freeShapes <- traverse (asFiniteType sc) (map snd frees)
  _retShape <- asFiniteType sc ret -- ensure return type is valid
  argVars <- traverse (newVars' be) argShapes
  fvs <- traverse (newVars be) freeShapes
  let freeMap = Map.fromList $ zip (map (vnIndex . fst) frees) fvs
  modmap <- scGetModuleMap sc
  bval <- bitBlastBasic be modmap addlPrims freeMap t
  bval' <- applyAll bval argVars
  let names =  map fst args ++ map (Text.unpack . vnName . fst) frees
      shapes = argShapes ++ freeShapes
  return (bval', zip names shapes)

-- | Bitblast a term and apply a function to the result.
withBitBlastedTerm :: AIG.IsAIG l g => AIG.Proxy l g ->
  SharedContext ->
  PrimMap l g ->
  Term ->
  (forall s. g s -> LitVector (l s) -> IO a) -> IO a
withBitBlastedTerm proxy sc addlPrims t c = AIG.withNewGraph proxy $ \be -> do
  (bval, _) <- bitBlastTerm be sc addlPrims t
  v <- flattenBValue bval
  c be v

asFiniteType :: SharedContext -> Term -> IO FiniteType
asFiniteType sc t =
  scGetModuleMap sc >>= \modmap ->
  case asFiniteTypeValue (Concrete.evalSharedTerm modmap Map.empty Map.empty t) of
    Just ft -> return ft
    Nothing ->
      fail $ "SAWCoreAIG.BitBlast.bitBlastTerm: invalid AIG type: " ++
             scPrettyTerm PPS.defaultOpts t

processVar ::
  (VarName, FirstOrderType) ->
  IO (VarName, FiniteType)
processVar (vn, fot) =
  case toFiniteType fot of
    Nothing -> fail ("ABC solver does not support variables of type " ++ show fot)
    Just ft -> pure (vn, ft)


withBitBlastedSATQuery ::
  AIG.IsAIG l g =>
  AIG.Proxy l g ->
  SharedContext ->
  PrimMap l g ->
  SATQuery ->
  (forall s. g s -> l s -> [(VarName, FiniteType)] -> IO a) ->
  IO a
withBitBlastedSATQuery proxy sc addlPrims satq cont =
  do unless (Set.null (satUninterp satq)) $ fail
        "RME prover does not support uninterpreted symbols"
     t <- satQueryAsTerm sc satq
     varShapes <- mapM processVar (Map.toList (satVariables satq))
     modmap <- scGetModuleMap sc
     AIG.withNewGraph proxy $ \be ->
       do vars <- traverse (traverse (newVars be)) varShapes
          let varMap = Map.fromList [ (vnIndex x, v) | (x, v) <- vars ]
          x <- bitBlastBasic be modmap addlPrims varMap t
          case x of
            VBool l -> cont be l varShapes
            _ -> fail "SAWCoreAIG.BitBlast.withBitBlastedSATQuery: non-boolean result type."
