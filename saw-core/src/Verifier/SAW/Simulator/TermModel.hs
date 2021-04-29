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

import Control.Monad
import Control.Monad.Fix
import Data.IORef
--import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Map (Map)
import qualified Data.Map as Map
import Numeric.Natural

import Verifier.SAW.Prim (BitVector(..))
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator as Sim
import Verifier.SAW.Simulator.Value
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.TypedAST
         (ModuleMap, DataType(..), findCtorInMap, ctorType, ctorNumParams)
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
  do cfg <- mfix (\cfg -> Sim.evalGlobal m (Map.union (constMap sc cfg) addlPrims)
                             (extcns cfg) (const Nothing) (neutral cfg))
     v <- Sim.evalSharedTerm cfg t
     tv <- evalType cfg =<< scTypeOf sc t
     readBackValue sc cfg tv v

  where
    neutral cfg nt =
      do tm <- neutralToSharedTerm sc nt
         ty <- scTypeOf sc tm
         tyv <- evalType cfg ty
         pure (VExtra (VExtraTerm tyv tm))

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
type instance VWord  TermModel = Either (Natural, Term) BitVector
type instance VInt   TermModel = Either Term Integer
type instance VArray TermModel = TermModelArray
type instance Extra  TermModel = VExtra

data VExtra
  = VStream
       (TValue TermModel) -- element type of the stream
       Term               -- term representing this stream
       (Natural -> IO TmValue) -- concrete lookup function
       (IORef (Map Natural TmValue)) -- cashed values of lookup function
  | VExtraTerm
       (TValue TermModel) -- type of the term
       Term               -- term value

instance Show VExtra where
  show (VStream _ tm _ _) = show tm
  show (VExtraTerm _ tm) = show tm

data TermModelArray =
  TMArray
    (TValue TermModel) Term -- @a@
    (TValue TermModel) Term -- @b@
    Term -- term of type @Array a b@


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
    VVecType n VBoolType -> return (VWord (Left (n,tm)))
    VArrayType a b ->
      do a' <- readBackTValue sc cfg a
         b' <- readBackTValue sc cfg b
         return (VArray (TMArray a a' b b' tm))

    VSort _s -> TValue <$> evalType cfg tm

    VPiType t tf ->
      return (VFun (\x ->
        do v <- force x
           tbody <- tf x
           xtm <- readBackValue sc cfg t v
           body <- scApply sc tm xtm
           reflectTerm sc cfg tbody body
        ))

    -- TODO: eta-expanding vectors like this kinda sucks.  It would be
    -- better if we could treat them abstractly, as we are doing below
    -- with records, pairs and data types.  However, that would be
    -- a pretty invasive change in the primitives.
    VVecType n t ->  -- NB: t /= Bool
      do a  <- readBackTValue sc cfg t
         n' <- scNat sc n
         vs <- V.generateM (fromIntegral n) $ \i -> -- TODO fromIntegral...
                   do i' <- scNat sc (fromIntegral i)
                      tm' <- scAt sc n' a tm i'
                      ready <$> reflectTerm sc cfg t tm'
         pure (VVector vs)

    VRecordType{} -> return (VExtra (VExtraTerm tv tm))
    VPairType{} -> return (VExtra (VExtraTerm tv tm))
    VDataType{} -> return (VExtra (VExtraTerm tv tm))


readBackValue :: SharedContext -> Sim.SimulatorConfig TermModel -> TValue TermModel -> Value TermModel -> IO Term
readBackValue sc cfg = loop
  where
    loop _ VUnit = scUnitValue sc

    loop _ (VNat n) = scNat sc n

    loop _ (VBVToNat w n) =
      do tm <- loop (VVecType (fromIntegral w) VBoolType) n
         scBvToNat sc (fromIntegral w) tm

    loop _ (VIntToNat i) =
      do tm <- loop VIntType i
         scIntToNat sc tm

    loop _ (VBool (Left tm)) = return tm
    loop _ (VBool (Right b)) = scBool sc b

    loop _ (VInt (Left tm)) = return tm
    loop _ (VInt (Right i)) = scIntegerConst sc i

    loop _ (VIntMod _ (Left tm)) = return tm
    loop _ (VIntMod m (Right i)) =
      do m' <- scNat sc m
         i' <- scIntegerConst sc i
         scToIntMod sc m' i'

    loop _ (VWord (Left (_,tm))) = return tm
    loop _ (VWord (Right bv)) = scBvConst sc (fromIntegral (width bv)) (unsigned bv)

    loop _ (VArray (TMArray _ _ _ _ tm)) = return tm

    loop _ (VString s) = scString sc s

    loop _ (TValue tv) = readBackTValue sc cfg tv

    loop _ (VExtra (VExtraTerm _tp tm)) = return tm
    loop _ (VExtra (VStream _tp tm _fn _cache))  = return tm

--    loop _ (VFloat _f) = fail "readBackValue: TODO float"
--    loop _ (VDouble _f) = fail "readBackValue: TODO float"

    loop tv@VPiType{} v@VFun{} =
      do (ecs, tm) <- readBackFuns tv v
         scAbstractExts sc ecs tm

    loop (VPairType t1 t2) (VPair v1 v2) =
      do tm1 <- loop t1 =<< force v1
         tm2 <- loop t2 =<< force v2
         scPairValueReduced sc tm1 tm2

    loop (VVecType _n tp) (VVector vs) =
      do tp' <- readBackTValue sc cfg tp
         vs' <- traverse (loop tp <=< force) (V.toList vs)
         scVectorReduced sc tp' vs'

    loop (VDataType _nm _ps) (VCtorApp cnm vs) =
      case findCtorInMap (Sim.simModMap cfg) cnm of
        Nothing -> panic "readBackValue" ["Could not find constructor info", show cnm]
        Just ctor ->
          do tyv <- evalType cfg (ctorType ctor)
             vs' <- readBackCtorArgs ctor tyv (V.toList vs)
             let (ps,args) = splitAt (ctorNumParams ctor) vs'
             scCtorAppParams sc cnm ps args

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

    readBackCtorArgs cnm (VPiType tv tf) (v:vs) =
      do v' <- force v
         t  <- loop tv v'
         ty <- tf (ready v')
         ts <- readBackCtorArgs cnm ty vs
         pure (t:ts)
    readBackCtorArgs _ (VDataType _ _) [] = pure []
    readBackCtorArgs cnm _ _ = panic "readBackCtorArgs" ["constructor type mismatch", show cnm]


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




boolTerm :: SharedContext -> VBool TermModel -> IO Term
boolTerm _ (Left tm) = pure tm
boolTerm sc (Right b) = scBool sc b

wordWidth :: VWord TermModel -> Natural
wordWidth (Left (n,_)) = n
wordWidth (Right bv)   = fromIntegral (Prim.width bv)

wordTerm :: SharedContext -> VWord TermModel -> IO Term
wordTerm _  (Left (_,tm)) = pure tm
wordTerm sc (Right bv) =
  scBvConst sc (fromIntegral (Prim.width bv)) (Prim.unsigned bv)

wordValue :: SharedContext -> BitVector -> IO (Natural, Term)
wordValue sc bv =
  do let n = fromIntegral (Prim.width bv)
     tm <- scBvConst sc n (Prim.unsigned bv)
     pure (n, tm)

intTerm :: SharedContext -> VInt TermModel -> IO Term
intTerm _ (Left tm) = pure tm
intTerm sc (Right i) = scIntegerConst sc i

extraTerm :: VExtra -> IO Term
extraTerm (VStream _tp tm _ _) = pure tm
extraTerm (VExtraTerm _ tm) = pure tm

extraType :: VExtra -> IO (TValue TermModel)
extraType (VExtraTerm tp _tm) = pure tp
extraType (VStream tp _tm _fn _cache) = pure (VDataType "Prelude.Stream" [TValue tp])

unOp ::
  SharedContext ->
  (SharedContext -> t -> IO t') ->
  (a -> b) ->
  Either t a -> IO (Either t' b)
unOp sc termOp _valOp (Left t) = Left <$> termOp sc t
unOp _sc _termOp valOp (Right x) = pure . Right $! valOp x

binOp ::
  SharedContext ->
  (SharedContext -> a -> IO t) ->
  (SharedContext -> t -> t -> IO t') ->
  (a -> a -> b) ->
  Either t a -> Either t a -> IO (Either t' b)
binOp sc toTerm termOp valOp x y =
  case (x, y) of
    (Right xv, Right yv) -> pure . Right $! valOp xv yv
    (Left xtm, Right yv) ->
      do ytm <- toTerm sc yv
         Left <$> termOp sc xtm ytm
    (Right xv, Left ytm) ->
      do xtm <- toTerm sc xv
         Left <$> termOp sc xtm ytm
    (Left xtm, Left ytm) ->
      Left <$> termOp sc xtm ytm


bvUnOp ::
  SharedContext ->
  (SharedContext -> Term -> Term -> IO Term) ->
  (BitVector -> BitVector) ->
  VWord TermModel -> IO (VWord TermModel)
bvUnOp sc termOp valOp = \case
  Right bv -> pure . Right $! valOp bv
  Left (n,tm) ->
    do n' <- scNat sc n
       tm' <- termOp sc n' tm
       pure (Left (n,tm'))


bvBinOp ::
  SharedContext ->
  (SharedContext -> Term -> Term -> Term -> IO Term) ->
  (BitVector -> BitVector -> BitVector) ->
  VWord TermModel -> VWord TermModel -> IO (VWord TermModel)
bvBinOp sc termOp valOp = binOp sc wordValue termOp' valOp
  where
    termOp' _ (n,x) (_,y) =
      do n' <- scNat sc n
         tm <- termOp sc n' x y
         pure (n, tm)


intDivOp ::
  SharedContext ->
  (SharedContext -> Term -> Term -> IO Term) ->
  (Integer -> Integer -> Integer) ->
  VInt TermModel -> VInt TermModel -> IO (VInt TermModel)

-- Special case for concrete divide-by-0:
-- return the term instead of producing an error
intDivOp sc termOp _intOp x y@(Right 0) =
  do x' <- intTerm sc x
     y' <- intTerm sc y
     Left <$> termOp sc x' y'
intDivOp sc termOp intOp x y =
  binOp sc scIntegerConst termOp intOp x y


bvDivOp ::
  SharedContext ->
  (SharedContext -> Term -> Term -> Term -> IO Term) ->
  (BitVector -> BitVector -> Maybe BitVector) ->
  VWord TermModel -> VWord TermModel -> IO (VWord TermModel)
bvDivOp sc termOp valOp x y = fixup =<< binOp sc wordValue termOp' valOp x y
  where
    -- Special case for concrete divide-by-0:
    -- return the term instead of producing an error
    fixup (Left l) = pure (Left l)
    fixup (Right (Just bv)) = pure (Right bv)
    fixup (Right Nothing) =
      do let n = wordWidth x
         n' <- scNat sc n
         xtm <- wordTerm sc x
         ytm <- wordTerm sc y
         tm <- termOp sc n' xtm ytm
         pure (Left (n,tm))

    termOp' _ (n,xtm) (_,ytm) =
      do n' <- scNat sc n
         tm <- termOp sc n' xtm ytm
         pure (n, tm)

bvCmpOp ::
  SharedContext ->
  (SharedContext -> Term -> Term -> Term -> IO Term) ->
  (BitVector -> BitVector -> Bool) ->
  VWord TermModel -> VWord TermModel -> IO (VBool TermModel)
bvCmpOp sc termOp valOp = binOp sc wordValue termOp' valOp
  where
    termOp' _ (n,x) (_,y) =
      do n' <- scNat sc n
         termOp sc n' x y

prims :: SharedContext -> Sim.SimulatorConfig TermModel -> Prims.BasePrims TermModel
prims sc cfg =
  Prims.BasePrims
  { Prims.bpAsBool  = \case
       Left _  -> Nothing
       Right b -> Just b

  , Prims.bpUnpack  = \case
       Right bv -> pure (fmap Right (Prim.unpackBitVector bv))

       Left (n,tm) ->
              do n' <- scNat sc n
                 a  <- scBoolType sc
                 V.generateM (fromIntegral n) (\i ->
                    Left <$> (scAt sc n' a tm =<< scNat sc (fromIntegral i)))

  , Prims.bpPack = \vs ->
       case traverse id vs of
         Right bs -> pure (Right (Prim.packBitVector bs))
         Left _ ->
           do a <- scBoolType sc
              ts <- traverse (\case Left tm -> pure tm; Right b -> scBool sc b) (V.toList vs)
              v <- scVector sc a ts
              let n = fromIntegral (V.length vs)
              return (Left (n, v))

  , Prims.bpBvAt = \w i ->
       case w of
         Right bv -> pure . Right $! Prim.bvAt bv i
         Left (n,tm) ->
           do n' <- scNat sc n
              a <- scBoolType sc
              i' <- scNat sc (fromIntegral i)
              Left <$> scAt sc n' a tm i'

  , Prims.bpBvLit = \w x -> pure (Right (Prim.bv w x))

  , Prims.bpBvSize = \case
       Right bv   -> Prim.width bv
       Left (n,_) -> fromIntegral n -- gross, TODO

  , Prims.bpBvJoin =
       let f _ (xn,xtm) (yn,ytm) =
               do xn' <- scNat sc xn
                  yn' <- scNat sc yn
                  a   <- scBoolType sc
                  tm  <- scAppend sc xn' yn' a xtm ytm
                  return (xn+yn, tm)
        in binOp sc wordValue f Prim.append_bv

  , Prims.bpBvSlice = \m n -> \case
         Right bv -> pure . Right $! Prim.slice_bv m n (Prim.width bv - m - n) bv
         Left  (w,tm) ->
           do m' <- scNat sc (fromIntegral m)
              n' <- scNat sc (fromIntegral n)
              o' <- scNat sc (w - fromIntegral m - fromIntegral n)
              a  <- scBoolType sc
              tm' <- scSlice sc a m' n' o' tm
              return (Left (fromIntegral n, tm'))

    -- conditionals
  , Prims.bpMuxBool = \c x y ->
       case c of
         Right b -> if b then pure x else pure y
         Left tm ->
           do x' <- boolTerm sc x
              y' <- boolTerm sc y
              a  <- scBoolType sc
              Left <$> scIte sc a tm x' y'

  , Prims.bpMuxWord = \c x y ->
       case c of
         Right b -> if b then pure x else pure y
         Left tm ->
           do x' <- wordTerm sc x
              y' <- wordTerm sc y
              a  <- scBitvector sc (wordWidth x)
              tm' <- scIte sc a tm x' y'
              pure (Left (wordWidth x, tm'))

  , Prims.bpMuxInt = \c x y ->
       case c of
         Right b -> if b then pure x else pure y
         Left tm ->
           do x' <- intTerm sc x
              y' <- intTerm sc y
              a  <- scIntegerType sc
              Left <$> scIte sc a tm x' y'

  , Prims.bpMuxExtra = \c x y ->
       case c of
         Right b -> if b then pure x else pure y
         Left tm ->
           do tp <- extraType x
              x' <- extraTerm x
              y' <- extraTerm y
              a  <- readBackTValue sc cfg tp
              VExtraTerm tp <$> scIte sc a tm x' y'

    -- Booleans
  , Prims.bpTrue   = Right True
  , Prims.bpFalse  = Right False
  , Prims.bpNot    = unOp sc scNot not
  , Prims.bpAnd    = binOp sc scBool scAnd (&&)
  , Prims.bpOr     = binOp sc scBool scOr  (||)
  , Prims.bpXor    = binOp sc scBool scXor (/=)
  , Prims.bpBoolEq = binOp sc scBool scBoolEq (==)

    -- Bitvector logical
  , Prims.bpBvNot  = bvUnOp  sc scBvNot Prim.bvNot
  , Prims.bpBvAnd  = bvBinOp sc scBvAnd Prim.bvAnd
  , Prims.bpBvOr   = bvBinOp sc scBvOr  Prim.bvOr
  , Prims.bpBvXor  = bvBinOp sc scBvXor Prim.bvXor

    -- Bitvector arithmetic
  , Prims.bpBvNeg  = bvUnOp  sc scBvNeg  Prim.bvNeg
  , Prims.bpBvAdd  = bvBinOp sc scBvAdd  Prim.bvAdd
  , Prims.bpBvSub  = bvBinOp sc scBvSub  Prim.bvSub
  , Prims.bpBvMul  = bvBinOp sc scBvMul  Prim.bvMul
  , Prims.bpBvUDiv = bvDivOp sc scBvUDiv Prim.bvUDiv
  , Prims.bpBvURem = bvDivOp sc scBvURem Prim.bvURem
  , Prims.bpBvSDiv = bvDivOp sc scBvSDiv Prim.bvSDiv
  , Prims.bpBvSRem = bvDivOp sc scBvSRem Prim.bvSRem
  , Prims.bpBvLg2  = bvUnOp  sc scBvLg2  Prim.bvLg2

    -- Bitvector comparisons
  , Prims.bpBvEq   = bvCmpOp sc scBvEq  Prim.bvEq
  , Prims.bpBvsle  = bvCmpOp sc scBvSLe Prim.bvsle
  , Prims.bpBvslt  = bvCmpOp sc scBvSLt Prim.bvslt
  , Prims.bpBvule  = bvCmpOp sc scBvULe Prim.bvule
  , Prims.bpBvult  = bvCmpOp sc scBvULt Prim.bvult
  , Prims.bpBvsge  = bvCmpOp sc scBvSGe Prim.bvsge
  , Prims.bpBvsgt  = bvCmpOp sc scBvSGt Prim.bvsgt
  , Prims.bpBvuge  = bvCmpOp sc scBvUGe Prim.bvuge
  , Prims.bpBvugt  = bvCmpOp sc scBvUGt Prim.bvugt

    -- Bitvector shift/rotate
  , Prims.bpBvShlInt = \c x amt ->
      case (c, x) of
        (Right c', Right x') -> pure . Right $! Prim.bvShiftL c' x' amt
        _ -> do let n = wordWidth x
                n'  <- scNat sc n
                a   <- scBoolType sc
                ctm <- boolTerm sc c
                xtm <- wordTerm sc x
                amttm <- scNat sc (fromInteger amt) -- TODO, should probably be a Natural?
                tm <- scGlobalApply sc "Prelude.shiftL" [n',a,ctm,xtm,amttm]
                pure (Left (n, tm))

  , Prims.bpBvShrInt = \c x amt ->
      case (c, x) of
        (Right c', Right x') -> pure . Right $! Prim.bvShiftR c' x' amt
        _ -> do let n = wordWidth x
                n'  <- scNat sc n
                a   <- scBoolType sc
                ctm <- boolTerm sc c
                xtm <- wordTerm sc x
                amttm <- scNat sc (fromInteger amt) -- TODO, should probably be a Natural?
                tm <- scGlobalApply sc "Prelude.shiftR" [n',a,ctm,xtm,amttm]
                pure (Left (n, tm))

  , Prims.bpBvShl = \c x amt ->
      case (c, x, amt) of
        (Right c', Right x', Right amt') -> pure . Right $! Prim.bvShiftL c' x' (Prim.unsigned amt')
        _ -> do let n = wordWidth x
                n'  <- scNat sc n
                a   <- scBoolType sc
                ctm <- boolTerm sc c
                xtm <- wordTerm sc x
                let an = wordWidth amt
                amttm <- scBvToNat sc an =<< wordTerm sc amt
                tm <- scGlobalApply sc "Prelude.shiftL" [n',a,ctm,xtm,amttm]
                return (Left (n, tm))

  , Prims.bpBvShr = \c x amt ->
      case (c, x, amt) of
        (Right c', Right x', Right amt') -> pure . Right $! Prim.bvShiftR c' x' (Prim.unsigned amt')
        _ -> do let n = wordWidth x
                n'  <- scNat sc n
                a   <- scBoolType sc
                ctm <- boolTerm sc c
                xtm <- wordTerm sc x
                let an = wordWidth amt
                amttm <- scBvToNat sc an =<< wordTerm sc amt
                tm <- scGlobalApply sc "Prelude.shiftR" [n',a,ctm,xtm,amttm]
                return (Left (n, tm))

  , Prims.bpBvRolInt = \x amt ->
      case x of
        Right x' -> pure . Right $! Prim.bvRotateL x' amt
        Left (n,xtm) ->
          do n' <- scNat sc n
             a  <- scBoolType sc
             amttm <- scNat sc (fromInteger amt) -- TODO Natural
             tm <- scGlobalApply sc "Prelude.rotateL" [n',a,xtm,amttm]
             return (Left (n,tm))

  , Prims.bpBvRorInt = \x amt ->
      case x of
        Right x' -> pure . Right $! Prim.bvRotateR x' amt
        Left (n,xtm) ->
          do n' <- scNat sc n
             a  <- scBoolType sc
             amttm <- scNat sc (fromInteger amt) -- TODO Natural
             tm <- scGlobalApply sc "Prelude.rotateR" [n',a,xtm,amttm]
             return (Left (n,tm))

  , Prims.bpBvRol = \x amt ->
      case (x, amt) of
        (Right x', Right amt') -> pure . Right $! Prim.bvRotateL x' (Prim.unsigned amt')
        _ ->
          do let n = wordWidth x
             n' <- scNat sc n
             a  <- scBoolType sc
             xtm <- wordTerm sc x
             let an = wordWidth amt
             amttm <- scBvToNat sc an =<< wordTerm sc amt
             tm <- scGlobalApply sc "Prelude.rotateL" [n',a,xtm,amttm]
             return (Left (n,tm))

  , Prims.bpBvRor = \x amt ->
      case (x, amt) of
        (Right x', Right amt') -> pure . Right $! Prim.bvRotateR x' (Prim.unsigned amt')
        _ ->
          do let n = wordWidth x
             n' <- scNat sc n
             a  <- scBoolType sc
             xtm <- wordTerm sc x
             let an = wordWidth amt
             amttm <- scBvToNat sc an =<< wordTerm sc amt
             tm <- scGlobalApply sc "Prelude.rotateR" [n',a,xtm,amttm]
             return (Left (n,tm))

    -- Bitvector misc
  , Prims.bpBvPopcount = bvUnOp sc scBvPopcount Prim.bvPopcount
  , Prims.bpBvCountLeadingZeros = bvUnOp sc scBvCountLeadingZeros Prim.bvCountLeadingZeros
  , Prims.bpBvCountTrailingZeros = bvUnOp sc scBvCountTrailingZeros Prim.bvCountTrailingZeros

  , Prims.bpBvForall = \n f ->
      do bvty <- scBitvector sc n
         ec   <- scFreshEC sc "x" bvty
         ecTm <- scExtCns sc ec
         res  <- f (Left (n,ecTm))
         case res of
           -- computed a constant boolean without consulting the variable, just return it
           Right b -> return (Right b)
           Left  resTm ->
             do n' <- scNat sc n
                fn <- scAbstractExts sc [ec] resTm
                Left <$> scBvForall sc n' fn

    -- Integer operations
  , Prims.bpIntAdd = binOp sc scIntegerConst scIntAdd (+)
  , Prims.bpIntSub = binOp sc scIntegerConst scIntSub (-)
  , Prims.bpIntMul = binOp sc scIntegerConst scIntMul (*)
  , Prims.bpIntDiv = intDivOp sc scIntDiv div
  , Prims.bpIntMod = intDivOp sc scIntMod mod
  , Prims.bpIntNeg = unOp  sc scIntNeg negate
  , Prims.bpIntAbs = unOp  sc scIntAbs abs
  , Prims.bpIntEq  = binOp sc scIntegerConst scIntEq (==)
  , Prims.bpIntLe  = binOp sc scIntegerConst scIntLe (<=)
  , Prims.bpIntLt  = binOp sc scIntegerConst scIntLt (<)
  , Prims.bpIntMin = binOp sc scIntegerConst scIntMin min
  , Prims.bpIntMax = binOp sc scIntegerConst scIntMax max

    -- Array operations
  , Prims.bpArrayConstant = \a b v ->
      do v' <- readBackValue sc cfg b v
         a'   <- readBackTValue sc cfg a
         b'   <- readBackTValue sc cfg b
         tm   <- scArrayConstant sc a' b' v'
         pure (TMArray a a' b b' tm)

  , Prims.bpArrayLookup = \(TMArray a a' b b' arr) idx ->
      do idx' <- readBackValue sc cfg a idx
         val  <- scArrayLookup sc a' b' arr idx'
         reflectTerm sc cfg b val

  , Prims.bpArrayUpdate = \(TMArray a a' b b' arr) idx val ->
      do idx' <- readBackValue sc cfg a idx
         val' <- readBackValue sc cfg b val
         arr' <- scArrayUpdate sc a' b' arr idx' val'
         pure (TMArray a a' b b' arr')

  , Prims.bpArrayEq = \(TMArray _ a' _ b' arr1) (TMArray _ _ _ _ arr2) ->
      if arr1 == arr2 then
        pure (Right True)
      else
        Left <$> scArrayEq sc a' b' arr1 arr2
  }


constMap :: SharedContext -> Sim.SimulatorConfig TermModel -> Map Ident TmValue
constMap sc cfg = Map.union (Map.fromList localPrims) (Prims.constMap pms)
  where
  pms = prims sc cfg

  localPrims =
    -- Shifts
    [ ("Prelude.bvShl" , bvShiftOp sc cfg id   scBvShl  Prim.bvShl)
    , ("Prelude.bvShr" , bvShiftOp sc cfg id   scBvShr  Prim.bvShr)
    , ("Prelude.bvSShr", bvShiftOp sc cfg succ scBvSShr Prim.bvSShr)

    -- Integers
    , ("Prelude.intToNat", intToNatOp sc)
    , ("Prelude.natToInt", natToIntOp sc)
    , ("Prelude.intToBv" , intToBvOp sc)
    , ("Prelude.bvToInt" , bvToIntOp sc cfg)
    , ("Prelude.sbvToInt", sbvToIntOp sc cfg)

{- TODO!
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
-}

    -- Miscellaneous
    , ("Prelude.expByNat", Prims.expByNatOp pms)
    ]


-- intToNat : Integer -> Nat;
intToNatOp :: SharedContext -> TmValue
intToNatOp _sc =
  strictFun $ \case
    VInt (Right i) -> pure . VNat $! fromInteger (max 0 i)
    x -> pure (VIntToNat x)

-- natToInt : Nat -> Integer;
natToIntOp :: SharedContext -> TmValue
natToIntOp sc =
  strictFun $ \case
    VNat n  ->
      pure . VInt . Right $! toInteger n

    VIntToNat (VInt (Right i)) ->
      pure . VInt . Right $! max 0 i
    VIntToNat (VInt (Left tm)) ->
      do z <- scIntegerConst sc 0
         VInt . Left <$> scIntMax sc z tm

    VBVToNat _ (VWord (Right bv)) ->
      pure . VInt . Right $! Prim.unsigned bv
    VBVToNat _ (VWord (Left (n, tm))) ->
      do n' <- scNat sc n
         VInt . Left <$> scBvToInt sc n' tm

    _ -> panic "natToIntOp" ["Expected nat value"]


-- primitive intToBv : (n:Nat) -> Integer -> Vec n Bool;
intToBvOp :: SharedContext -> TmValue
intToBvOp sc =
  Prims.natFun' "intToBvOp" $ \n -> pure $
  strictFun $ \case
    VInt (Right i) -> pure . VWord . Right $! Prim.bv (fromIntegral n) i -- TODO fromIntegral
    VInt (Left tm) ->
      do n' <- scNat sc n
         tm' <- scIntToBv sc n' tm
         pure (VWord (Left (n,tm')))
    _ -> panic "intToBvOp" ["expected integer value"]

-- bvToInt : (n:Nat) -> Vec n Bool -> Integer;
bvToIntOp :: SharedContext -> Sim.SimulatorConfig TermModel -> TmValue
bvToIntOp sc cfg =
  Prims.natFun' "bvToIntOp" $ \n -> pure $
  strictFun $ \case
    VWord (Right bv) -> pure . VInt . Right $! Prim.unsigned bv
    x ->
      do n' <- scNat sc n
         tm <- readBackValue sc cfg (VVecType n VBoolType) x
         VInt . Left <$> scBvToInt sc n' tm

-- sbvToInt : (n:Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: SharedContext -> Sim.SimulatorConfig TermModel -> TmValue
sbvToIntOp sc cfg =
  Prims.natFun' "sbvToIntOp" $ \n -> pure $
  strictFun $ \case
    VWord (Right bv) -> pure . VInt . Right $! Prim.signed bv
    x ->
      do n' <- scNat sc n
         tm <- readBackValue sc cfg (VVecType n VBoolType) x
         VInt . Left <$> scSbvToInt sc n' tm

-- | (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool
bvShiftOp ::
  SharedContext ->
  Sim.SimulatorConfig TermModel ->
  (Natural -> Natural) ->
  (SharedContext -> Term -> Term -> Term -> IO Term) ->
  (BitVector -> Int -> BitVector) ->
  TmValue
bvShiftOp sc cfg szf tmOp bvOp =
  Prims.natFun' "bvShiftOp" $ \n0 -> pure $
  strictFun $ \w -> pure $
  strictFun $ \amt ->
    case (w, amt) of
      (VWord (Right w'), VNat amt') ->
        let amt'' = fromInteger (min (toInteger (Prim.width w')) (toInteger amt'))
         in pure . VWord . Right $! bvOp w' amt''
      _ ->
        do let n = szf n0
           n0'  <- scNat sc n0
           w'   <- readBackValue sc cfg (VVecType n VBoolType) w
           amt' <- readBackValue sc cfg (VDataType "Prelude.Nat" []) amt
           tm   <- tmOp sc n0' w' amt'
           pure (VWord (Left (n, tm)))

{-

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