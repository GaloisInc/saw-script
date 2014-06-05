{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.Simulator.BitBlast where

import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable
import qualified Data.Vector as V
import qualified Data.Vector.Storable as LV

--import Verifier.SAW.Prim (Nat)
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST (FieldName, {-Ident,-} Module)
import Verifier.SAW.SharedTerm

--import qualified Verinf.Symbolic as BE
import Verinf.Symbolic.Lit

import qualified Verifier.SAW.Recognizer as R

------------------------------------------------------------
-- Values

type BValue l = Value IO (BExtra l)
type BThunk l = Thunk IO (BExtra l)

data BExtra l
  = BBool l
  | BWord (LitVector l) -- ^ Bits in LSB order
  | BToNat Nat (LitVector l)

-- | Swap from big-endian to little-endian
lvFromV :: LV.Storable l => V.Vector l -> LV.Vector l
lvFromV v = LV.generate (V.length v) ((V.!) (V.reverse v))

-- | Swap from little-endian to big-endian
vFromLV :: LV.Storable l => LV.Vector l -> V.Vector l
vFromLV lv = V.generate (LV.length lv) ((LV.!) (LV.reverse lv))

vBool :: l -> BValue l
vBool l = VExtra (BBool l)

toBool :: BValue l -> l
toBool (VExtra (BBool l)) = l
toBool _ = error "toBool"

vWord :: LitVector l -> BValue l
vWord lv = VExtra (BWord lv)

toWord :: LV.Storable l => BValue l -> IO (LitVector l)
toWord (VExtra (BWord lv)) = return lv
toWord (VVector vv) = lvFromV <$> traverse (fmap toBool . force) vv
toWord _ = fail "toWord"

wordFun :: LV.Storable l => (LitVector l -> IO (BValue l)) -> BValue l
wordFun f = strictFun (\x -> toWord x >>= f)

-- | op :: Bool -> Bool -> Bool
boolBinOp :: (l -> l -> IO l) -> BValue l
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> vBool <$> op (toBool x) (toBool y)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n
binOp :: LV.Storable l => (LitVector l -> LitVector l -> IO (LitVector l)) -> BValue l
binOp op =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> Bool
binRel :: LV.Storable l => (LitVector l -> LitVector l -> IO l) -> BValue l
binRel op =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vBool <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
shiftOp :: LV.Storable l =>
           (LitVector l -> LitVector l -> IO (LitVector l))
        -> (LitVector l -> Nat -> LitVector l)
        -> BValue l
shiftOp bvOp natOp =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  strictFun $ \y ->
    case y of
      VExtra (BToNat _ lv) -> vWord <$> bvOp x lv
      VNat n               -> return (vWord (natOp x (fromInteger n)))
      _                    -> error "shiftOp"

------------------------------------------------------------

lvShl :: LV.Storable l => l -> LV.Vector l -> Nat -> LV.Vector l
lvShl l v i = LV.replicate j l LV.++ LV.take (n-j) v
  where n = LV.length v
        j = fromIntegral i `min` n

lvShr :: LV.Storable l => l -> LV.Vector l -> Nat -> LV.Vector l
lvShr l v i = LV.drop j v LV.++ LV.replicate j l
  where j = fromIntegral i `min` LV.length v

lvSShr :: LV.Storable l => LV.Vector l -> Nat -> LV.Vector l
lvSShr v i = LV.drop j v LV.++ LV.replicate j l
  where j = fromIntegral i `min` LV.length v
        l = LV.last v

------------------------------------------------------------

beConstMap :: LV.Storable l => BitEngine l -> Map Ident (BValue l)
beConstMap be = Map.fromList
  -- Boolean
  [ ("Prelude.True"  , vBool (beTrue be))
  , ("Prelude.False" , vBool (beFalse be))
  , ("Prelude.not"   , strictFun (return . vBool . beNeg be . toBool))
  , ("Prelude.and"   , boolBinOp (beAnd be))
  , ("Prelude.or"    , boolBinOp (beOr be))
  , ("Prelude.xor"   , boolBinOp (beXor be))
  , ("Prelude.boolEq", boolBinOp (beEq be))
  , ("Prelude.ite"   , iteOp be)
  -- Arithmetic
  , ("Prelude.bvAdd" , binOp (beAddInt be))
  , ("Prelude.bvSub" , binOp (beSubInt be))
  , ("Prelude.bvMul" , binOp (beMulInt be))
  , ("Prelude.bvAnd" , binOp (beAndInt be))
  , ("Prelude.bvOr"  , binOp (beOrInt be))
  , ("Prelude.bvXor" , binOp (beXorInt be))
  , ("Prelude.bvUDiv", binOp (beQuotUnsigned be))
  , ("Prelude.bvURem", binOp (beRemUnsigned be))
  , ("Prelude.bvSDiv", binOp (beQuot be))
  , ("Prelude.bvSRem", binOp (beRem be))
  -- Relations
  , ("Prelude.bvEq"  , binRel (beEqVector be))
  , ("Prelude.bvsle" , binRel (beSignedLeq be))
  , ("Prelude.bvslt" , binRel (beSignedLt be))
  , ("Prelude.bvule" , binRel (beUnsignedLeq be))
  , ("Prelude.bvult" , binRel (beUnsignedLt be))
  , ("Prelude.bvsge" , binRel (flip (beSignedLeq be)))
  , ("Prelude.bvsgt" , binRel (flip (beSignedLt be)))
  , ("Prelude.bvuge" , binRel (flip (beUnsignedLeq be)))
  , ("Prelude.bvugt" , binRel (flip (beUnsignedLt be)))
  -- Shifts
  , ("Prelude.bvShl" , shiftOp (beShl be) (lvShl (beFalse be)))
  , ("Prelude.bvShr" , shiftOp (beUnsignedShr be) (lvShr (beFalse be)))
  , ("Prelude.bvSShr", shiftOp (beSignedShr be) lvSShr)
  -- Nat
  , ("Prelude.Succ", Prims.succOp)
  , ("Prelude.addNat", Prims.addNatOp)
  , ("Prelude.subNat", Prims.subNatOp)
  , ("Prelude.mulNat", Prims.mulNatOp)
  , ("Prelude.minNat", Prims.minNatOp)
  , ("Prelude.maxNat", Prims.maxNatOp)
  , ("Prelude.widthNat", Prims.widthNatOp)
  -- Fin
  , ("Prelude.finDivMod", Prims.finDivModOp)
  -- Vectors
  , ("Prelude.generate", Prims.generateOp)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  ]

-- | ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
iteOp :: forall l. (LV.Storable l) => BitEngine l -> BValue l
iteOp be =
  VFun $ \_ -> return $
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> beLazyMux be muxFn (toBool b) (force x) (force y)
  where
    muxFn :: l -> BValue l -> BValue l -> IO (BValue l)
    muxFn b (VFun f)        (VFun g)        = return $ VFun (\a -> do x <- f a; y <- g a; muxFn b x y)
    muxFn b (VTuple xv)     (VTuple yv)     = VTuple <$> vectorFn b xv yv
    muxFn b (VRecord xm)    (VRecord ym)
      | Map.keys xm == Map.keys ym          = VRecord <$> sequenceA (Map.fromList
                                                [ (k, thunkFn b x y) | ((k, x), y) <- zip (Map.assocs xm) (Map.elems ym) ])
    muxFn b (VCtorApp i xv) (VCtorApp j yv) | i == j = VCtorApp i <$> vectorFn b xv yv
    muxFn b (VVector xv)    (VVector yv)    = VVector <$> vectorFn b xv yv
    muxFn _ (VNat m)        (VNat n)        | m == n = return $ VNat m
    muxFn _ (VString x)     (VString y)     | x == y = return $ VString x
    muxFn _ (VFloat x)      (VFloat y)      | x == y = return $ VFloat x
    muxFn _ (VDouble x)     (VDouble y)     | x == y = return $ VDouble y
    muxFn _ VType           VType           = return VType
    muxFn b (VExtra x)      (VExtra y)      = VExtra <$> extraFn b x y
    muxFn _ _ _ = fail "iteOp: malformed arguments"

    vectorFn :: l -> V.Vector (BThunk l) -> V.Vector (BThunk l) -> IO (V.Vector (BThunk l))
    vectorFn b xv yv
      | V.length xv == V.length yv = V.zipWithM (thunkFn b) xv yv
      | otherwise                  = fail "iteOp: malformed arguments"

    thunkFn :: l -> BThunk l -> BThunk l -> IO (BThunk l)
    thunkFn b x y = delay $ do x' <- force x; y' <- force y; muxFn b x' y'

    extraFn :: l -> BExtra l -> BExtra l -> IO (BExtra l)
    extraFn b (BBool x) (BBool y) = BBool <$> beMux be b x y
    extraFn b (BWord x) (BWord y) | LV.length x == LV.length y = BWord <$> LV.zipWithM (beMux be b) x y
    extraFn b (BToNat m x) (BToNat n y) | m == n && LV.length x == LV.length y = BToNat m <$> LV.zipWithM (beMux be b) x y
    extraFn _ _ _ = fail "iteOp: malformed arguments"

------------------------------------------------------------
-- Generating variables for arguments

data BShape 
  = BoolShape
  | VecShape Nat BShape
  | TupleShape [BShape]
  | RecShape (Map FieldName BShape)

parseShape :: (Applicative m, Monad m) => SharedTerm s -> m BShape
parseShape (R.asBoolType -> Just ()) = return BoolShape
parseShape (R.isVecType return -> Just (n R.:*: tp)) =
  VecShape n <$> parseShape tp
parseShape (R.asBitvectorType -> Just n) = pure (VecShape n BoolShape)
parseShape (R.asTupleType -> Just ts) = TupleShape <$> traverse parseShape ts
parseShape (R.asRecordType -> Just tm) = RecShape <$> traverse parseShape tm
parseShape t = do
  fail $ "bitBlast: unsupported argument type: " ++ show t

newVars :: BitEngine l -> BShape -> IO (BValue l)
newVars be BoolShape = vBool <$> beMakeInputLit be
newVars be (VecShape n tp) = VVector <$> V.replicateM (fromIntegral n) (newVars' be tp)
newVars be (TupleShape ts) = VTuple <$> traverse (newVars' be) (V.fromList ts)
newVars be (RecShape tm) = VRecord <$> traverse (newVars' be) tm

newVars' :: BitEngine l -> BShape -> IO (BThunk l)
newVars' be shape = Ready <$> newVars be shape

------------------------------------------------------------
-- Bit-blasting predicates

bitBlastBasic :: (Eq l, LV.Storable l) => BitEngine l -> Module -> SharedTerm s -> IO (BValue l)
bitBlastBasic be m = Sim.evalSharedTerm cfg
  where cfg = Sim.evalGlobal m (beConstMap be)

bitBlast :: (Eq l, LV.Storable l) => BitEngine l -> SharedContext s -> SharedTerm s -> IO l
bitBlast be sc t = do
  (argTs, _resultT) <- R.asPiList <$> scTypeOf sc t
  -- TODO: check that resultT is Bool.
  shapes <- traverse (parseShape . snd) argTs
  vars <- traverse (newVars' be) shapes
  bval <- bitBlastBasic be (scModule sc) t
  bval' <- applyAll bval vars
  case bval' of
    VExtra (BBool l) -> return l
    _ -> fail "bitBlast: non-boolean result type."
