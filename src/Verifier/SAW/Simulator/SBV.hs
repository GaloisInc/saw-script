{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Simulator.SBV where

import Data.SBV as S
import Data.SBV.Internals
import Data.SBV.LowLevel as L

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Traversable as T
import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad

import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Prim hiding (BV)
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.TypedAST (FieldName, {-Ident,-} Module)
import Verinf.Symbolic.Lit

import Debug.Trace

type SValue = Value IO SbvExtra
type SThunk = Thunk IO SbvExtra

data SbvExtra =
  SbvBool SBool |
  SbvWord SWord deriving Show

constMap :: Map Ident SValue
constMap = Map.fromList [
    -- Boolean
    ("Prelude.True", VExtra (SbvBool true)),
    ("Prelude.False", VExtra (SbvBool false)),
    ("Prelude.not", strictFun (return . vBool . bnot . toBool)),
    ("Prelude.and", boolBinOp (&&&)),
    ("Prelude.or", boolBinOp (|||)),
    ("Prelude.xor", boolBinOp (<+>)) ,
    ("Prelude.boolEq", boolBinOp (<=>)),
    ("Prelude.ite", iteOp),
    -- Arithmetic
    ("Prelude.bvAdd" , binOp L.bvAdd),
    ("Prelude.bvSub" , binOp L.bvSub),
    ("Prelude.bvMul" , binOp L.bvMul),
    ("Prelude.bvAnd" , binOp L.bvAnd),
    ("Prelude.bvOr"  , binOp L.bvOr),
    ("Prelude.bvXor" , binOp L.bvXOr),
    ("Prelude.bvUDiv", binOp L.bvUDiv),
    ("Prelude.bvURem", binOp L.bvURem),
    ("Prelude.bvSDiv", binOp L.bvSDiv),
    ("Prelude.bvSRem", binOp L.bvSRem),
    -- Relations 
    ("Prelude.bvEq"  , binRel L.bvEq),
    ("Prelude.bvsle" , binRel L.bvSLe),
    ("Prelude.bvslt" , binRel L.bvSLt),
    ("Prelude.bvule" , binRel L.bvLe),
    ("Prelude.bvult" , binRel L.bvLt),
    ("Prelude.bvsge" , binRel L.bvSGe),
    ("Prelude.bvsgt" , binRel L.bvSGt),
    ("Prelude.bvuge" , binRel L.bvGe),
    ("Prelude.bvugt" , binRel L.bvGt),
    -- Shifts
    ("Prelude.bvShl" , binOp L.bvShL),
    ("Prelude.bvShr" , binOp L.bvShR),
    ("Prelude.bvSShr", binOp L.bvSShR),
    -- Nat
    ("Prelude.Succ", Prims.succOp),
    ("Prelude.addNat", Prims.addNatOp),
    ("Prelude.subNat", Prims.subNatOp),
    ("Prelude.mulNat", Prims.mulNatOp),
    ("Prelude.minNat", Prims.minNatOp),
    ("Prelude.maxNat", Prims.maxNatOp),
    ("Prelude.widthNat", Prims.widthNatOp),
    -- Fin
    ("Prelude.finDivMod", Prims.finDivModOp),
    ("Prelude.finMax", Prims.finMaxOp),
    ("Prelude.finPred", Prims.finPredOp),
    ("Prelude.finOfNat", finOfNatOp),
    -- Vectors
    ("Prelude.generate", Prims.generateOp),
    ("Prelude.get", getOp),
    ("Prelude.append", appendOp),
    ("Prelude.rotateL", rotateLOp),
    ("Prelude.vZip", vZipOp),
    ("Prelude.foldr", foldrOp),
    -- Miscellaneous
    ("Prelude.coerce", Prims.coerceOp),
    ("Prelude.bvNat", bvNatOp),
    ("Prelude.bvToNat", bvToNatOp)
  ]

-- | Rotates left if i is positive.
vRotate :: V.Vector SThunk -> Int -> SValue
vRotate xs i
  | V.null xs = VVector xs
  | otherwise = VVector $ (V.++) (V.drop j xs) (V.take j xs)
  where j = i `mod` V.length xs

-- rotateL :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateLOp
  = 
    VFun $ \_ -> return $
    VFun $ \_ -> return $
    strictFun $ \xs -> return $
    strictFun $ \y -> wordNatOp eOp wOp eOp cOp xs y
  where 
    eOp xv i = error "cann't rotL symbolicly" -- vWord (L.bvRotL xv i)
    wOp xv i = return $ vWord (L.bvRotLC xv i)
    cOp xv i = return $ vRotate xv i

selectV :: Int -> (Int -> SThunk) -> SWord -> IO SValue
selectV m f w@(SBV (KBounded _ s) _) = do
  let bits = map (symTestBit w) [0 .. s-1]
  let sel :: Int -> [SBool] -> IO SValue
      sel offset []       = force (f offset)
      sel offset (b : bs) = do
        let bitOnValue = offset + 2 ^ (length bs)
        -- if bitOnValue > m
        --   then sel offset bs
        --   else do
        m1 <- sel bitOnValue bs
        m2 <- sel offset bs
        myMerge b m1 m2
  sel 0 bits

myMerge :: SBool -> SValue -> SValue -> IO SValue
myMerge b (VExtra (SbvBool x)) (VExtra (SbvBool y)) = return .vBool $ S.ite b x y
myMerge b (VExtra (SbvWord x)) (VExtra (SbvWord y)) = return .vWord . unComp $ S.ite b (CompSWord x) (CompSWord y)
myMerge b (VVector xs) (VVector ys) = (VVector <$>) . T.sequence $ V.zipWith zipper xs ys where
  zipper mx my = delay $ do
    x <- force mx
    y <- force my
    myMerge b x y
myMerge _ _ _ = error "cannot merge SValues"

wordNatOp :: (SWord -> SWord -> IO SValue) ->
             (SWord -> Int -> IO SValue) ->
             (V.Vector SThunk -> SWord -> IO SValue) ->
             (V.Vector SThunk -> Int -> IO SValue) ->
             SValue -> SValue -> IO SValue
wordNatOp bothSymOp symWordOp symIndOp constOp xs y = do
  case y of
    VNat n -> 
      case xs of
        VVector xv          ->  constOp xv (fromIntegral n)
        VExtra (SbvWord xv) ->  symWordOp xv (fromIntegral n)
        _ -> error $ "wordNatOp: " ++ show (xs, y)
    VExtra (SbvWord (SBV _ (Left (cwVal -> CWInteger n)))) -> 
      case xs of
        VVector xv          ->  constOp xv (fromIntegral n)
        VExtra (SbvWord xv) ->  symWordOp xv (fromIntegral n)
        _ -> error $ "wordNatOp: " ++ show (xs, y)
    VExtra (SbvWord n) -> do 
      mw <- toWord xs
      case (mw, xs) of
        (Just xv, _) -> bothSymOp xv (nOfSize xv n)
        (_, VVector xv) -> symIndOp xv n 
        _ -> error "Something awful happend in wordNatOp"
    _ -> do
      ind <- Prims.finFromValue y
      case xs of
        VVector xv -> constOp xv . fromEnum . finVal $ ind
        VExtra (SbvWord xv) -> symWordOp xv . fromEnum . finVal $ ind

nOfSize :: SWord -> SWord -> SWord
nOfSize (SBV (KBounded _ k) _) ind@(SBV (KBounded _ k2) s)
  | k == k2 = ind
  | Left (cwVal -> CWInteger ival) <- s = bitVector k ival
  | True = L.bvJoin (bitVector (k - k2) 0) ind

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNatOp :: SValue
bvNatOp = 
  Prims.natFun $ \w -> return $
  Prims.natFun $ \x -> return $
  vWord (bitVector (fromIntegral w) (toInteger x))

-- bvToNat :: (n :: Nat) -> bitvector n -> Nat;
bvToNatOp :: SValue
bvToNatOp = 
  VFun $ \_ -> return $
  strictFun $ \lv -> do
    Just w <- toWord lv
    return (vWord w)

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: SValue
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

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: SValue
vZipOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \ys -> return $
  VVector (V.zipWith (\x y -> Ready (VTuple (V.fromList [x, y]))) (toVector xs) (toVector ys))

-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: SValue
appendOp =
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  VFun $ \_ -> return $
  strictFun $ \xs -> return $
  strictFun $ \ys ->
  case (xs, ys) of
    (VVector xv, VVector yv) -> return $ VVector ((V.++) xv yv)
    (v, w) -> do
      (Just v') <- toWord v
      (Just w') <- toWord w
      return $ vWord $ bvJoin v' w'
    _ -> error "appendOp"

traceIt a b = trace (a ++ show b) b

-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
getOp :: SValue
getOp
  = VFun $ \_-> return $
        VFun $ \_-> return $
        strictFun $ \v-> return $
        strictFun $ \i-> 
          wordNatOp bothSymOp symWordOp symIndOp constOp v i
  where
    constOp xv i = force ((V.!) xv i)
    bothSymOp xv i = return (symTestSym xv i)
    symWordOp xv i = return (vBool (symTestBit xv i))
    symIndOp xv i = selectV (V.length xv) ((V.!) xv) i

symTestSym :: SWord -> SWord -> SValue
symTestSym w@(SBV (KBounded _ k) _) ind =
  vBool $ L.bvNeq (bitVector k 0) (L.bvAnd w
    (L.bvShL (bitVector k 1) (L.bvSub (bitVector k (fromIntegral (k-1))) (nOfSize w ind))))

symTestBit :: SWord -> Int -> SBool
symTestBit x@(SBV (KBounded _ w) _) i =
  bvNeq (bitVector w 0) (L.bvAnd x (bitVector w (shiftL 1 (w-i-1))))
symTestBit _ _ = error "SWord must be bounded"

-- finOfNat :: (n :: Nat) -> Nat -> Fin n;
finOfNatOp :: SValue
finOfNatOp =
  Prims.natFun $ \n -> return $
  strictFun $ \v -> return $
    case v of
      VNat i -> Prims.vFin (finFromBound (fromInteger i) n)
      VExtra x -> VExtra x
      _ -> error "finOfNatOp"

binOp :: (SWord -> SWord -> SWord) -> SValue
binOp op = VFun $ \_-> return $
          strictFun $ \mx-> return $
           strictFun $ \my-> do
            (Just x) <- toWord mx
            (Just y) <- toWord my
            return $ vWord $ op x y

binRel :: (SWord -> SWord -> SBool) -> SValue
binRel op = VFun $ \_-> return $
            strictFun $ \mx-> return $
            strictFun $ \my-> do
              (Just x) <- toWord mx
              (Just y) <- toWord my
              return $ vBool $ op x y

iteOp :: SValue
iteOp = 
    VFun $ \_ -> return $
    strictFun $ \b-> return $
    strictFun $ \x-> return $
    strictFun $ \y-> muxFn (toBool b) x y
muxFn b (VFun f) (VFun g) = return $ VFun (\a -> do x <- f a; y <- g a; muxFn b x y)
muxFn b (VCtorApp i xv) (VCtorApp j yv) | i == j = VCtorApp i <$> vectorFn b xv yv
muxFn b (VVector xv)    (VVector yv)    = VVector <$> vectorFn b xv yv
muxFn _ (VNat m)        (VNat n)        | m == n = return $ VNat m
muxFn _ (VString x)     (VString y)     | x == y = return $ VString x
muxFn _ (VFloat x)      (VFloat y)      | x == y = return $ VFloat x
muxFn _ (VDouble x)     (VDouble y)     | x == y = return $ VDouble y
muxFn _ VType           VType           = return VType
muxFn b (VExtra x)      (VExtra y)      = return $ VExtra $ extraFn b x y
muxFn _ _ _ = fail "iteOp: malformed arguments"

vectorFn :: SBool -> V.Vector SThunk -> V.Vector SThunk -> IO (V.Vector SThunk)
vectorFn b xv yv
  | V.length xv == V.length yv = V.zipWithM (thunkFn b) xv yv
  | otherwise                  = fail "iteOp: malformed arguments"

thunkFn :: SBool -> SThunk -> SThunk -> IO SThunk
thunkFn b x y = delay $ do x' <- force x; y' <- force y; muxFn b x' y'
-- thunkFn b x y = Ready <$> do x' <- force x; y' <- force y; muxFn b x' y'

extraFn :: SBool -> SbvExtra -> SbvExtra -> SbvExtra
extraFn b (SbvBool x) (SbvBool y) = SbvBool $ sBranch b x y
extraFn b (SbvWord x) (SbvWord y) = SbvWord . unComp $ sBranch b (CompSWord x) (CompSWord y)
extraFn _ _ _ = error "iteOp: malformed arguments"

boolBinOp :: (SBool -> SBool -> SBool) -> SValue
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> return $ vBool $ op (toBool x) (toBool y)

vBool :: SBool -> SValue
vBool = VExtra . SbvBool

vWord :: SWord -> SValue
vWord = VExtra . SbvWord

toBool :: SValue -> SBool
toBool (VExtra (SbvBool b)) = b
toBool _  = error "toBool"

toLitBool :: SValue -> Maybe SBool
toLitBool (VExtra (SbvBool b)) = Just b
toLitBool s = Nothing

toWord :: SValue -> IO (Maybe SWord)
toWord (VExtra (SbvWord w)) = return (Just w)
toWord (VVector vv) = ((symFromBits <$>) . T.sequence) <$> traverse (fmap toLitBool . force) vv
toWord (VNat n) = return Nothing
toWord _ = return Nothing

toVector :: SValue -> V.Vector SThunk
toVector (VVector xv) = xv
toVector (VExtra (SbvWord xv@(SBV (KBounded _ k) _))) = V.fromList (map (Ready . vBool . symTestBit xv) [0..k-1])
toVector _ = error "this word might be symbolic"

symFromBits :: Vector SBool -> SWord
symFromBits v
  = V.foldl (L.bvAdd) (bitVector l 0) $ flip V.imap (V.reverse v) $ \i b->
      unComp (S.ite b (CompSWord (symBit l i)) (CompSWord (bitVector l 0)))
  where
    l = V.length v

symBit :: Int -> Int -> SWord
symBit l i = bitVector l (shiftL 1 i)

sbvSolveBasic :: Module -> SharedTerm s -> IO SValue
sbvSolveBasic m = Sim.evalSharedTerm cfg
  where cfg = Sim.evalGlobal m constMap

asPredType :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
asPredType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> (t1 :) <$> asPredType sc t2
    (R.asBoolType -> Just ())    -> return []
    _                            -> fail $ "non-boolean result type: " ++ show t'

sbvSolve :: SharedContext s -> SharedTerm s -> Predicate
sbvSolve sc t = do
  ty <- liftIO $ scTypeOf sc t
  argTs <- liftIO $ asPredType sc ty
  shapes <- liftIO $ traverse (parseShape sc) argTs
  vars <- traverse newVars' shapes
  bval <- liftIO $ sbvSolveBasic (scModule sc) t
  bval' <- liftIO $ applyAll bval vars
  case bval' of
    VExtra (SbvBool b) -> return b
    _ -> fail "bitBlast: non-boolean result type."

data SbvShape
  = BoolShape
  | VecShape Nat SbvShape
  | TupleShape [SbvShape]
  | RecShape (Map FieldName SbvShape)

parseShape :: SharedContext s -> SharedTerm s -> IO SbvShape
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

newVars :: SbvShape -> Symbolic SValue
newVars BoolShape = vBool <$> exists_
newVars (VecShape n BoolShape) = vWord <$> symBitVector (fromIntegral n) EX
newVars (VecShape n tp) = VVector <$> V.replicateM (fromIntegral n) (newVars' tp)
newVars (TupleShape ts) = VTuple <$> traverse newVars' (V.fromList ts)
newVars (RecShape tm) = VRecord <$> traverse newVars' tm

newVars' :: SbvShape -> Symbolic SThunk
newVars' shape = Ready <$> newVars shape
