{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.Simulator.BitBlast where

import Control.Applicative
import Control.Monad (zipWithM)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable
import qualified Data.Vector as V
import qualified Data.Vector.Storable as LV

import Verifier.SAW.Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST (FieldName, {-Ident,-} Module)
import Verifier.SAW.SharedTerm

import Verinf.Symbolic.Lit
import Verinf.Symbolic.Lit.Functional (lMuxInteger)

import qualified Verifier.SAW.Recognizer as R

------------------------------------------------------------
-- Values

type BValue l = Value IO (BExtra l)
type BThunk l = Thunk IO (BExtra l)

data BExtra l
  = BBool l
  | BWord (LitVector l) -- ^ Bits in LSB order
  | BNat (LitVector l)
  | BFin (LitVector l)

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
      VExtra (BNat lv) -> vWord <$> bvOp x lv
      VNat n           -> return (vWord (natOp x (fromInteger n)))
      _                -> error "shiftOp"

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
  , ("Prelude.finOfNat", finOfNatOp)
  -- Vectors
  , ("Prelude.generate", Prims.generateOp)
  , ("Prelude.get", getOp be)
  , ("Prelude.append", appendOp)
  , ("Prelude.vZip", vZipOp)
  , ("Prelude.foldr", foldrOp)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  , ("Prelude.bvNat", bvNatOp be)
  , ("Prelude.bvToNat", bvToNatOp)
  ]

-- | ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
iteOp :: forall l. (LV.Storable l) => BitEngine l -> BValue l
iteOp be =
  VFun $ \_ -> return $
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> beLazyMux be (muxBVal be) (toBool b) (force x) (force y)

muxBVal :: LV.Storable l => BitEngine l -> l -> BValue l -> BValue l -> IO (BValue l)
muxBVal be b (VFun f)        (VFun g)        = return $ VFun (\a -> do x <- f a; y <- g a; muxBVal be b x y)
muxBVal be b (VTuple xv)     (VTuple yv)     = VTuple <$> muxThunks be b xv yv
muxBVal be b (VRecord xm)    (VRecord ym)
  | Map.keys xm == Map.keys ym               = (VRecord . Map.fromList . zip (Map.keys xm)) <$>
                                                 zipWithM (muxThunk be b) (Map.elems xm) (Map.elems ym)
muxBVal be b (VCtorApp i xv) (VCtorApp j yv) | i == j = VCtorApp i <$> muxThunks be b xv yv
muxBVal be b (VVector xv)    (VVector yv)    = VVector <$> muxThunks be b xv yv
muxBVal _  _ (VNat m)        (VNat n)        | m == n = return $ VNat m
muxBVal _  _ (VString x)     (VString y)     | x == y = return $ VString x
muxBVal _  _ (VFloat x)      (VFloat y)      | x == y = return $ VFloat x
muxBVal _  _ (VDouble x)     (VDouble y)     | x == y = return $ VDouble y
muxBVal _  _ VType           VType           = return VType
muxBVal be b (VExtra x)      (VExtra y)      = VExtra <$> muxBExtra be b x y
muxBVal _ _ _ _ = fail "iteOp: malformed arguments"

muxThunks :: LV.Storable l => BitEngine l -> l -> V.Vector (BThunk l) -> V.Vector (BThunk l) -> IO (V.Vector (BThunk l))
muxThunks be b xv yv
  | V.length xv == V.length yv = V.zipWithM (muxThunk be b) xv yv
  | otherwise                  = fail "iteOp: malformed arguments"

muxThunk :: LV.Storable l => BitEngine l -> l -> BThunk l -> BThunk l -> IO (BThunk l)
muxThunk be b x y = delay $ do x' <- force x; y' <- force y; muxBVal be b x' y'

muxBExtra :: LV.Storable l => BitEngine l -> l -> BExtra l -> BExtra l -> IO (BExtra l)
muxBExtra be b (BBool x) (BBool y) = BBool <$> beMux be b x y
muxBExtra be b (BWord x) (BWord y) | LV.length x == LV.length y = BWord <$> LV.zipWithM (beMux be b) x y
muxBExtra be b (BNat x)  (BNat y)  | LV.length x == LV.length y = BNat  <$> LV.zipWithM (beMux be b) x y
muxBExtra be b (BFin x)  (BFin y)  | LV.length x == LV.length y = BFin  <$> LV.zipWithM (beMux be b) x y
muxBExtra _ _ _ _ = fail "iteOp: malformed arguments"

-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
getOp :: LV.Storable l => BitEngine l -> BValue l
getOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  strictFun $ \i ->
    case v of
      VVector xv ->
        case i of
          VExtra (BFin ilv) -> force =<< lMuxInteger (beLazyMux be (muxThunk be)) (V.length xv) ilv (return . (V.!) xv)
          _ -> force =<< (((V.!) xv . fromEnum . finVal) <$> Prims.finFromValue i)
      VExtra (BWord lv) ->
        case i of
          VExtra (BFin ilv) -> vBool <$> lMuxInteger (beLazyMux be (beMux be)) (LV.length lv) ilv (return . (LV.!) (LV.reverse lv))
          _ -> (vBool . (LV.!) lv . fromEnum . finRem) <$> Prims.finFromValue i
      _ -> fail "getOp: expected vector"

-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: LV.Storable l => BValue l
appendOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  case (xs, ys) of
    (VVector xv, VVector yv)         -> VVector ((V.++) xv yv)
    (VVector xv, VExtra (BWord ylv)) -> VVector ((V.++) xv (fmap (Ready . vBool) (vFromLV ylv)))
    (VExtra (BWord xlv), VVector yv) -> VVector ((V.++) (fmap (Ready . vBool) (vFromLV xlv)) yv)
    (VExtra (BWord xlv), VExtra (BWord ylv)) -> vWord ((LV.++) ylv xlv)
    _ -> error "appendOp"

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: LV.Storable l => BValue l
vZipOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  VVector (V.zipWith (\x y -> Ready (VTuple (V.fromList [x, y]))) (vectorOfBValue xs) (vectorOfBValue ys))

vectorOfBValue :: LV.Storable l => BValue l -> V.Vector (BThunk l)
vectorOfBValue (VVector xv) = xv
vectorOfBValue (VExtra (BWord lv)) = fmap (Ready . vBool) (vFromLV lv)
vectorOfBValue _ = error "vectorOfBValue"

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: LV.Storable l => BValue l
foldrOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \f -> return $
  VFun $ \z -> return $
  strictFun $ \xs -> do
    let g x m = do fx <- apply f x
                   y <- delay m
                   apply fx y
    case xs of
      VVector xv -> V.foldr g (force z) xv
      _ -> fail "foldrOp"

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNatOp :: LV.Storable l => BitEngine l -> BValue l
bvNatOp be =
  Prims.natFun $ \w -> return $
  Prims.natFun $ \x -> return $
  VExtra (BWord (beVectorFromInt be (fromIntegral w) (toInteger x)))

-- bvToNat :: (n :: Nat) -> bitvector n -> Nat;
bvToNatOp :: LV.Storable l => BValue l
bvToNatOp =
  VFun $ \_ -> return $
  wordFun $ \lv -> return $
  VExtra (BNat lv)

-- finOfNat :: (n :: Nat) -> Nat -> Fin n;
finOfNatOp :: BValue l
finOfNatOp =
  Prims.natFun $ \n -> return $
  strictFun $ \v -> return $
    case v of
      VNat i -> Prims.vFin (finFromBound (fromInteger i) n)
      VExtra (BNat lv) -> VExtra (BFin lv)
      _ -> error "finOfNatOp"

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
