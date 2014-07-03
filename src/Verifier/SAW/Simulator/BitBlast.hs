{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.Simulator.BitBlast where

import Control.Applicative
import Control.Monad (zipWithM)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable
import qualified Data.Vector as V

import Verifier.SAW.Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST (FieldName, {-Ident,-} Module)
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Recognizer as R

import qualified Data.AIG as AIG


type LitVector l = AIG.BV l

------------------------------------------------------------
-- Vector operations

lvFromV :: V.Vector l -> LitVector l
lvFromV v = AIG.generate_msb0 (V.length v) ((V.!) v)

vFromLV :: LitVector l -> V.Vector l
vFromLV lv = V.generate (AIG.length lv) (AIG.at lv)

-- | Rotates left if i is positive.
vRotate :: V.Vector a -> Int -> V.Vector a
vRotate xs i
  | V.null xs = xs
  | otherwise = (V.++) (V.drop j xs) (V.take j xs)
  where j = i `mod` V.length xs

lvRotate :: LitVector l -> Int -> LitVector l
lvRotate xs i
  | AIG.length xs == 0 = xs
  | otherwise = (AIG.++) (AIG.drop j xs) (AIG.take j xs)
  where j = (- i) `mod` AIG.length xs

------------------------------------------------------------
-- Values

type BValue l = Value IO (BExtra l)
type BThunk l = Thunk IO (BExtra l)

data BExtra l
  = BBool l
  | BWord (LitVector l) -- ^ Bits in LSB order
  | BStream (Integer -> IO (BValue l)) (IORef (Map Integer (BValue l)))
  | BNat (LitVector l)
  | BFin (LitVector l)

instance Show (BExtra l) where
  show (BBool _) = "BBool"
  show (BWord _) = "BWord"
  show (BStream _ _) = "BStream"
  show (BNat _ ) = "BNat"
  show (BFin _) = "BFin"

vBool :: l -> BValue l
vBool l = VExtra (BBool l)

toBool :: BValue l -> l
toBool (VExtra (BBool l)) = l
toBool _ = error "toBool"

vWord :: LitVector l -> BValue l
vWord lv = VExtra (BWord lv)

toWord :: BValue l -> IO (LitVector l)
toWord (VExtra (BWord lv)) = return lv
toWord (VVector vv) = lvFromV <$> traverse (fmap toBool . force) vv
toWord _ = fail "toWord"

wordFun :: (LitVector l -> IO (BValue l)) -> BValue l
wordFun f = strictFun (\x -> toWord x >>= f)

-- | op :: Bool -> Bool -> Bool
boolBinOp :: (l -> l -> IO l) -> BValue l
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> vBool <$> op (toBool x) (toBool y)

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n
binOp :: (LitVector l -> LitVector l -> IO (LitVector l)) -> BValue l
binOp op =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vWord <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> bitvector n -> Bool
binRel :: (LitVector l -> LitVector l -> IO l) -> BValue l
binRel op =
  VFun $ \_ -> return $
  wordFun $ \x -> return $
  wordFun $ \y -> vBool <$> op x y

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
shiftOp :: (LitVector l -> LitVector l -> IO (LitVector l))
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

lvShl :: l -> LitVector l -> Nat -> LitVector l
lvShl l v i = AIG.slice v j (n-j) AIG.++ AIG.replicate j l
  where n = AIG.length v
        j = fromIntegral i `min` n

lvShr :: l -> LitVector l -> Nat -> LitVector l
lvShr l v i = AIG.replicate j l AIG.++ AIG.slice v 0 (n-j)
  where n = AIG.length v
        j = fromIntegral i `min` n

lvSShr :: LitVector l -> Nat -> LitVector l
lvSShr v i = lvShr (AIG.msb v) v i

------------------------------------------------------------

beConstMap :: AIG.IsAIG l g => g s -> Map Ident (BValue (l s))
beConstMap be = Map.fromList
  -- Boolean
  [ ("Prelude.True"  , vBool (AIG.trueLit be))
  , ("Prelude.False" , vBool (AIG.falseLit be))
  , ("Prelude.not"   , strictFun (return . vBool . AIG.not . toBool))
  , ("Prelude.and"   , boolBinOp (AIG.and be))
  , ("Prelude.or"    , boolBinOp (AIG.or be))
  , ("Prelude.xor"   , boolBinOp (AIG.xor be))
  , ("Prelude.boolEq", boolBinOp (AIG.eq be))
  , ("Prelude.ite"   , iteOp be)
  -- Arithmetic
  , ("Prelude.bvAdd" , binOp (AIG.add be))
  , ("Prelude.bvSub" , binOp (AIG.sub be))
  , ("Prelude.bvMul" , binOp (AIG.mul be))
  , ("Prelude.bvAnd" , binOp (AIG.zipWithM (AIG.and be)))
  , ("Prelude.bvOr"  , binOp (AIG.zipWithM (AIG.or be)))
  , ("Prelude.bvXor" , binOp (AIG.zipWithM (AIG.xor be)))
  , ("Prelude.bvUDiv", binOp (AIG.uquot be))
  , ("Prelude.bvURem", binOp (AIG.urem be))
  , ("Prelude.bvSDiv", binOp (AIG.squot be))
  , ("Prelude.bvSRem", binOp (AIG.srem be))
  -- Relations
  , ("Prelude.bvEq"  , binRel (AIG.bvEq be))
  , ("Prelude.bvsle" , binRel (AIG.sle be))
  , ("Prelude.bvslt" , binRel (AIG.slt be))
  , ("Prelude.bvule" , binRel (AIG.ule be))
  , ("Prelude.bvult" , binRel (AIG.ult be))
  , ("Prelude.bvsge" , binRel (flip (AIG.sle be)))
  , ("Prelude.bvsgt" , binRel (flip (AIG.slt be)))
  , ("Prelude.bvuge" , binRel (flip (AIG.ule be)))
  , ("Prelude.bvugt" , binRel (flip (AIG.ult be)))
  -- Shifts
  , ("Prelude.bvShl" , shiftOp (AIG.shl be) (lvShl (AIG.falseLit be)))
  , ("Prelude.bvShr" , shiftOp (AIG.ushr be) (lvShr (AIG.falseLit be)))
  , ("Prelude.bvSShr", shiftOp (AIG.sshr be) lvSShr)
  -- Nat
  , ("Prelude.Succ", Prims.succOp)
  , ("Prelude.addNat", Prims.addNatOp)
  , ("Prelude.subNat", Prims.subNatOp)
  , ("Prelude.mulNat", Prims.mulNatOp)
  , ("Prelude.minNat", Prims.minNatOp)
  , ("Prelude.maxNat", Prims.maxNatOp)
  , ("Prelude.widthNat", Prims.widthNatOp)
  , ("Prelude.natCase", Prims.natCaseOp)
  -- Fin
  , ("Prelude.finDivMod", Prims.finDivModOp)
  , ("Prelude.finMax", Prims.finMaxOp)
  , ("Prelude.finPred", Prims.finPredOp)
  , ("Prelude.finOfNat", finOfNatOp)
  , ("Prelude.natSplitFin", Prims.natSplitFinOp)
  -- Vectors
  , ("Prelude.generate", Prims.generateOp)
  , ("Prelude.get", getOp be)
  , ("Prelude.append", appendOp)
  , ("Prelude.rotateL", rotateLOp be)
  , ("Prelude.vZip", vZipOp)
  , ("Prelude.foldr", foldrOp)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  -- Miscellaneous
  , ("Prelude.coerce", Prims.coerceOp)
  , ("Prelude.bvNat", bvNatOp be)
  , ("Prelude.bvToNat", bvToNatOp)
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

-- | ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
iteOp :: AIG.IsAIG l g => g s -> BValue (l s)
iteOp be =
  VFun $ \_ -> return $
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> lazyMux be (muxBVal be) (toBool b) (force x) (force y)

muxBVal :: AIG.IsAIG l g => g s -> l s -> BValue (l s) -> BValue (l s) -> IO (BValue (l s))
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
muxBVal be b x@(VExtra (BWord _)) y         =
  muxBVal be b (VVector (vectorOfBValue x)) y
muxBVal be b x y@(VExtra (BWord _))         =
  muxBVal be b x (VVector (vectorOfBValue y))
muxBVal _ _ x y =
  fail $ "iteOp: malformed arguments: " ++ show x ++ " " ++ show y

muxThunks :: AIG.IsAIG l g => g s -> l s
          -> V.Vector (BThunk (l s)) -> V.Vector (BThunk (l s)) -> IO (V.Vector (BThunk (l s)))
muxThunks be b xv yv
  | V.length xv == V.length yv = V.zipWithM (muxThunk be b) xv yv
  | otherwise                  = fail "iteOp: malformed arguments"

muxThunk :: AIG.IsAIG l g => g s -> l s -> BThunk (l s) -> BThunk (l s) -> IO (BThunk (l s))
muxThunk be b x y = delay $ do x' <- force x; y' <- force y; muxBVal be b x' y'

muxBExtra :: AIG.IsAIG l g => g s -> l s -> BExtra (l s) -> BExtra (l s) -> IO (BExtra (l s))
muxBExtra be b (BBool x) (BBool y) = BBool <$> AIG.mux be b x y
muxBExtra be b (BWord x) (BWord y) | AIG.length x == AIG.length y = BWord <$> AIG.zipWithM (AIG.mux be b) x y
muxBExtra be b (BNat x)  (BNat y)  | AIG.length x == AIG.length y = BNat  <$> AIG.zipWithM (AIG.mux be b) x y
muxBExtra be b (BFin x)  (BFin y)  | AIG.length x == AIG.length y = BFin  <$> AIG.zipWithM (AIG.mux be b) x y
muxBExtra _ _ _ _ = fail "iteOp: malformed arguments"

-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
getOp :: AIG.IsAIG l g => g s -> BValue (l s)
getOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \v -> return $
  strictFun $ \i ->
    case v of
      VVector xv ->
        case i of
          VExtra (BFin ilv) -> force =<< AIG.muxInteger (lazyMux be (muxThunk be)) (V.length xv) ilv (return . (V.!) xv)
          _ -> force =<< (((V.!) xv . fromEnum . finVal) <$> Prims.finFromValue i)
      VExtra (BWord lv) ->
        case i of
          VExtra (BFin ilv) -> vBool <$> AIG.muxInteger (lazyMux be (AIG.mux be)) (AIG.length lv) ilv (return . AIG.at lv)
          _ -> (vBool . AIG.at lv . fromEnum . finVal) <$> Prims.finFromValue i
      _ -> fail "getOp: expected vector"

-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: BValue l
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
    (VExtra (BWord xlv), VExtra (BWord ylv)) -> vWord ((AIG.++) xlv ylv)
    _ -> error "appendOp"

-- rotateL :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateLOp :: AIG.IsAIG l g => g s -> BValue (l s)
rotateLOp be =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \y ->
  case y of
    VNat n ->
      case xs of
        VVector xv         -> return $ VVector $ vRotate xv (fromIntegral n)
        VExtra (BWord xlv) -> return $ VExtra $ BWord $ lvRotate xlv (fromIntegral n)
        _ -> error $ "rotateLOp1: " ++ show (xs, y)
    VExtra (BNat ilv) -> do
      let (n, f) = case xs of
                     VVector xv         -> (V.length xv, VVector . vRotate xv)
                     VExtra (BWord xlv) -> (AIG.length xlv, VExtra . BWord . lvRotate xlv)
                     _ -> error $ "rotateLOp2: " ++ show (xs, y)
      r <- AIG.urem be ilv (AIG.bvFromInteger be (AIG.length ilv) (toInteger n))
      AIG.muxInteger (lazyMux be (muxBVal be)) (n - 1) r (return . f)
    _ -> error $ "rotateLOp3: " ++ show (xs, y)

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: BValue l
vZipOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  VVector (V.zipWith (\x y -> Ready (VTuple (V.fromList [x, y]))) (vectorOfBValue xs) (vectorOfBValue ys))

vectorOfBValue :: BValue l -> V.Vector (BThunk l)
vectorOfBValue (VVector xv) = xv
vectorOfBValue (VExtra (BWord lv)) = fmap (Ready . vBool) (vFromLV lv)
vectorOfBValue _ = error "vectorOfBValue"

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: BValue l
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
bvNatOp :: AIG.IsAIG l g => g s -> BValue (l s)
bvNatOp be =
  Prims.natFun $ \w -> return $
  Prims.natFun $ \x -> return $
  VExtra (BWord (AIG.bvFromInteger be (fromIntegral w) (toInteger x)))

-- bvToNat :: (n :: Nat) -> bitvector n -> Nat;
bvToNatOp :: BValue l
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
----------------------------------------

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: BValue l
mkStreamOp =
  VFun $ \_ -> return $
  strictFun $ \f -> do
    r <- newIORef Map.empty
    return $ VExtra (BStream (\n -> apply f (Ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: BValue l
streamGetOp =
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  Prims.natFun $ \n -> lookupBStream xs (toInteger n)

lookupBStream :: BValue l -> Integer -> IO (BValue l)
lookupBStream (VExtra (BStream f r)) n = do
   m <- readIORef r
   case Map.lookup n m of
     Just v  -> return v
     Nothing -> do v <- f n
                   writeIORef r (Map.insert n v m)
                   return v
lookupBStream _ _ = fail "expected Stream"

------------------------------------------------------------
-- Generating variables for arguments

data BShape
  = BoolShape
  | VecShape Nat BShape
  | TupleShape [BShape]
  | RecShape (Map FieldName BShape)

parseShape :: SharedContext s -> SharedTerm s -> IO BShape
parseShape sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asBoolType -> Just ())
      -> return BoolShape
    (R.isVecType return -> Just (n R.:*: tp))
      -> VecShape n <$> parseShape sc tp
    (R.asTupleType -> Just ts)
      -> TupleShape <$> traverse (parseShape sc) ts
    (R.asRecordType -> Just tm)
       -> RecShape <$> traverse (parseShape sc) tm
    _ -> fail $ "bitBlast: unsupported argument type: " ++ show t'

newVars :: AIG.IsAIG l g => g s -> BShape -> IO (BValue (l s))
newVars be BoolShape = vBool <$> AIG.newInput be
newVars be (VecShape n tp) = VVector <$> V.replicateM (fromIntegral n) (newVars' be tp)
newVars be (TupleShape ts) = VTuple <$> traverse (newVars' be) (V.fromList ts)
newVars be (RecShape tm) = VRecord <$> traverse (newVars' be) tm

newVars' :: AIG.IsAIG l g => g s -> BShape -> IO (BThunk (l s))
newVars' be shape = Ready <$> newVars be shape

------------------------------------------------------------
-- Bit-blasting predicates

bitBlastBasic :: AIG.IsAIG l g => g s -> Module -> SharedTerm t -> IO (BValue (l s))
bitBlastBasic be m = Sim.evalSharedTerm cfg
  where cfg = Sim.evalGlobal m (beConstMap be)

asPredType :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "non-boolean result type: " ++ show t'

bitBlast :: AIG.IsAIG l g => g s -> SharedContext t -> SharedTerm t -> IO (l s)
bitBlast be sc t = do
  ty <- scTypeOf sc t
  argTs <- asPredType sc ty
  shapes <- traverse (parseShape sc) argTs
  vars <- traverse (newVars' be) shapes
  bval <- bitBlastBasic be (scModule sc) t
  bval' <- applyAll bval vars
  case bval' of
    VExtra (BBool l) -> return l
    _ -> fail "bitBlast: non-boolean result type."
