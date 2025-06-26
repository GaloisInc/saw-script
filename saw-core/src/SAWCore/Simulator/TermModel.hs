{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}

{- |
Module      : SAWCore.Simulator.TermModel
Copyright   : Galois, Inc. 2012-2021
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Simulator.TermModel
       ( TmValue, TermModel, Value(..), TValue(..)
       , VExtra(..)
       , readBackValue, readBackTValue
       , normalizeSharedTerm, normalizeSharedTerm'
       , extractUninterp
       ) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.Except

import Data.IORef
import qualified Data.Text as Text
import Data.Maybe (fromMaybe)
import qualified Data.Vector as V
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Numeric.Natural


import SAWCore.Module (ModuleMap, dtExtCns)
import SAWCore.Name
import SAWCore.Panic (panic)
import SAWCore.Prim (BitVector(..))
import qualified SAWCore.Prim as Prim
import SAWCore.Prelude.Constants
import qualified SAWCore.Simulator as Sim
import SAWCore.Simulator.Value
import qualified SAWCore.Simulator.Prims as Prims
import SAWCore.SharedTerm
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (showTerm)

------------------------------------------------------------

type ReplaceUninterpMap = Map VarIndex [(ExtCns Term, [Term])]


extractUninterp ::
  (?recordEC :: BoundECRecorder) =>
  SharedContext ->
  ModuleMap ->
  Map Ident TmPrim {- ^ additional primitives -} ->
  Map VarIndex TmValue {- ^ ExtCns values -} ->
  Set VarIndex {- ^ 'unints' Constants in this set are kept uninterpreted -} ->
  Set VarIndex {- ^ 'opaque' Constants in this set are not evaluated -} ->
  Term ->
  IO (Term, ReplaceUninterpMap)
extractUninterp sc m addlPrims ecVals unintSet opaqueSet t =
  do mapref <- newIORef mempty
     cfg <- mfix (\cfg -> Sim.evalGlobal' m (Map.union addlPrims (constMap sc cfg))
                             (extcns cfg mapref) (uninterpreted cfg mapref) (neutral cfg) (primHandler cfg))
     v <- Sim.evalSharedTerm cfg t
     tv <- evalType cfg =<< scTypeOf sc t
     t' <- readBackValue sc cfg tv v
     replMap <- readIORef mapref
     return (t', replMap)

 where
    uninterpreted cfg mapref tf ec@(EC ix _nm ty)
      | Set.member ix opaqueSet = Just $
          do tm <- scTermF sc tf
             reflectTerm sc cfg ty tm
      | Set.member ix unintSet = Just (replace sc cfg mapref ec)
      | otherwise = Nothing

    extcns cfg mapref tf ec@(EC ix _nm ty)
      | Set.member ix unintSet = replace sc cfg mapref ec
      | otherwise =
          case Map.lookup ix ecVals of
            Just v  -> return v
            Nothing ->
              do tm <- scTermF sc tf
                 reflectTerm sc cfg ty tm

    neutral cfg env nt =
      do env' <- traverse (\(x,ty) -> readBackValue sc cfg ty =<< force x) env
         tm   <- instantiateVarList sc 0 env' =<< neutralToSharedTerm sc nt
         tyv  <- evalType cfg =<< scTypeOf sc tm
         reflectTerm sc cfg tyv tm

    primHandler cfg ec _msg env tp =
      do let nm = Name (ecVarIndex ec) (ecName ec)
         args <- reverse <$> traverse (\(x,ty) -> readBackValue sc cfg ty =<< force x) env
         prim <- scTermF sc (Constant nm)
         f    <- foldM (scApply sc) prim args
         reflectTerm sc cfg tp f

replace ::
  (?recordEC :: BoundECRecorder) =>
  SharedContext ->
  Sim.SimulatorConfig TermModel ->
  IORef ReplaceUninterpMap ->
  ExtCns (TValue TermModel) ->
  IO (Value TermModel)
replace sc cfg mapref ec = loop [] (ecType ec)
  where
    loop :: [Term] -> TValue TermModel -> IO (Value TermModel)
    loop env (VPiType nm xty body) =
        return $ VFun nm $ \x ->
          do ty <- applyPiBody body x
             xtm <- readBackValue sc cfg xty =<< force x
             loop (xtm:env) ty

    loop env ty =
      do let args = reverse env
         ty' <- readBackTValue sc cfg ty
         newec <- scFreshEC sc (toShortName (ecName ec)) ty'
         modifyIORef mapref (Map.alter (Just . ((newec,args):) . fromMaybe []) (ecVarIndex ec))
         reflectTerm sc cfg ty =<< scFlatTermF sc (ExtCns newec)

normalizeSharedTerm ::
  SharedContext ->
  ModuleMap ->
  Map Ident TmPrim {- ^ additional primitives -} ->
  Map VarIndex TmValue {- ^ ExtCns values -} ->
  Set VarIndex {- ^ opaque constants -} ->
  Term ->
  IO Term
normalizeSharedTerm sc m addlPrims =
  normalizeSharedTerm' sc m (const $ Map.union addlPrims)

normalizeSharedTerm' ::
  SharedContext ->
  ModuleMap ->
  (Sim.SimulatorConfig TermModel -> Map Ident TmPrim -> Map Ident TmPrim)
    {- ^ function which adds additional primitives -} ->
  Map VarIndex TmValue {- ^ ExtCns values -} ->
  Set VarIndex {- ^ opaque constants -} ->
  Term ->
  IO Term
normalizeSharedTerm' sc m primsFn ecVals opaqueSet t =
  do let ?recordEC = \_ec -> return ()
     cfg <- mfix (\cfg -> Sim.evalGlobal' m (primsFn cfg (constMap sc cfg))
                              (extcns cfg) (constants cfg) (neutral cfg) (primHandler cfg))
     v <- Sim.evalSharedTerm cfg t
     tv <- evalType cfg =<< scTypeOf sc t
     readBackValue sc cfg tv v

  where
    constants cfg tf ec
      | Set.member (ecVarIndex ec) opaqueSet = Just $
          do let ?recordEC = \_ec -> return ()
             tm <- scTermF sc tf
             reflectTerm sc cfg (ecType ec) tm

      | otherwise = Nothing

    extcns cfg tf ec =
      let ?recordEC = \_ec -> return () in
      case Map.lookup (ecVarIndex ec) ecVals of
        Just v  -> return v
        Nothing ->
          do tm <- scTermF sc tf
             reflectTerm sc cfg (ecType ec) tm

    neutral cfg env nt =
      do let ?recordEC = \_ec -> return ()
         env' <- traverse (\(x,ty) -> readBackValue sc cfg ty =<< force x) env
         tm   <- instantiateVarList sc 0 env' =<< neutralToSharedTerm sc nt
         tyv  <- evalType cfg =<< scTypeOf sc tm
         reflectTerm sc cfg tyv tm

    primHandler cfg ec _msg env tp =
      do let ?recordEC = \_ec -> return ()
         let nm = Name (ecVarIndex ec) (ecName ec)
         args <- reverse <$> traverse (\(x,ty) -> readBackValue sc cfg ty =<< force x) env
         prim <- scTermF sc (Constant nm)
         f    <- foldM (scApply sc) prim args
         reflectTerm sc cfg tp f

------------------------------------------------------------
-- Values

data TermModel

type TmValue = Value TermModel
type TmPrim  = Prims.Prim TermModel

type instance EvalM  TermModel = IO
type instance VBool  TermModel = Either Term Bool
-- VWord records the bitwidth together with the term in the @Left@ case
type instance VWord  TermModel = Either (Natural, Term) BitVector
type instance VInt   TermModel = Either Term Integer
type instance VArray TermModel = TermModelArray
type instance Extra  TermModel = VExtra

data VExtra
  = VExtraTerm
       !(TValue TermModel) -- type of the term
       !Term               -- term value (closed term!)
  | VExtraStream
       !(TValue TermModel) -- type of the stream elements
       !(Thunk TermModel -> MValue TermModel) -- function to compute stream values
       !(IORef (Map Natural (Value TermModel))) -- cache of concrete values
       !(Lazy IO Term) -- stream value as a term (closed term!)

instance Show VExtra where
  show (VExtraTerm ty tm) = "<extra> " ++ showTerm tm ++ " : " ++ show ty
  show (VExtraStream ty _ _ _) = "<stream of " ++ show ty ++ ">"

data TermModelArray =
  TMArray
    (TValue TermModel) Term -- @a@
    (TValue TermModel) Term -- @b@
    Term -- term of type @Array a b@ (closed term!)


type BoundECRecorder = ExtCns Term -> IO ()

readBackTValue :: (?recordEC :: BoundECRecorder) =>
  SharedContext ->
  Sim.SimulatorConfig TermModel ->
  TValue TermModel ->
  IO Term
readBackTValue sc cfg = loop
  where
  loop tv =
    case tv of
      VUnitType -> scUnitType sc
      VBoolType -> scBoolType sc
      VStringType -> scStringType sc
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
      VDataType nm ps vs ->
        do let nm' = Name (ecVarIndex nm) (ecName nm)
           (ps',vs') <- splitAt (length ps) <$> readBackDataTypeParams (ecType nm) (ps++vs)
           scDataTypeAppParams sc nm' ps' vs'
      VPiType{} ->
        do (ecs, tm) <- readBackPis tv
           scGeneralizeExts sc ecs tm
      VRecursorType d ps m mty ->
        do let d' = Name (ecVarIndex d) (ecName d)
           ps'  <- readBackDataTypeParams (ecType d) ps
           m'   <- readBackValue sc cfg mty m
           mty' <- loop mty
           scFlatTermF sc (RecursorType d' ps' m' mty')
      VTyTerm _s tm ->
        pure tm

  readBackDataTypeParams (VPiType _nm t body) (v:vs) =
    do v' <- readBackValue sc cfg t v
       t' <- applyPiBody body (ready v)
       vs' <- readBackDataTypeParams t' vs
       return (v':vs')

  readBackDataTypeParams _ [] = return []
  readBackDataTypeParams ty _ =
      panic "readBackTValue / readBackDataTypeParams" [
          "Arity mismatch in data type in readback",
          "Remaining type: " <> Text.pack (show ty)
      ]

  readBackPis (VPiType nm t pibody) =
    do t' <- loop t
       ec <- scFreshEC sc nm t'
       ?recordEC ec
       ecTm <- scExtCns sc ec
       ecVal <- delay (reflectTerm sc cfg t ecTm)
       body <- applyPiBody pibody ecVal
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

reflectTerm ::
  (?recordEC :: BoundECRecorder) =>
  SharedContext ->
  Sim.SimulatorConfig TermModel ->
  TValue TermModel ->
  Term {- ^ closed term to reflect -} ->
  IO (Value TermModel)
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

    VSort s -> pure (TValue (VTyTerm s tm))

    VPiType nm t pibody ->
      return (VFun nm (\x ->
        do v <- force x
           tbody <- applyPiBody pibody x
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

    VStringType{}   -> return (VExtra (VExtraTerm tv tm))
    VRecordType{}   -> return (VExtra (VExtraTerm tv tm))
    VPairType{}     -> return (VExtra (VExtraTerm tv tm))
    VDataType{}     -> return (VExtra (VExtraTerm tv tm))
    VRecursorType{} -> return (VExtra (VExtraTerm tv tm))
    VTyTerm{}       -> return (VExtra (VExtraTerm tv tm))

-- | Given a value, which must have the given type,
--   reconstruct a closed term representing the value.
readBackValue ::
  (?recordEC :: BoundECRecorder) =>
  SharedContext ->
  Sim.SimulatorConfig TermModel ->
  TValue TermModel ->
  Value TermModel ->
  IO Term
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
    loop _ (VExtra (VExtraStream _tp _fn _ref tm)) = liftIO (force tm)

    loop tv@VPiType{} v@VFun{} =
      do (ecs, tm) <- readBackFuns tv v
         scAbstractExtsEtaCollapse sc ecs tm

    loop (VPairType t1 t2) (VPair v1 v2) =
      do tm1 <- loop t1 =<< force v1
         tm2 <- loop t2 =<< force v2
         scPairValueReduced sc tm1 tm2

    loop (VVecType _n tp) (VVector vs) =
      do tp' <- readBackTValue sc cfg tp
         vs' <- traverse (loop tp <=< force) (V.toList vs)
         scVectorReduced sc tp' vs'

    loop (VDataType _nm _ps _ixs) (VCtorApp cnm ps vs) =
      do let nm = Name (ecVarIndex cnm) (ecName cnm)
         (ps',vs') <- splitAt (length ps) <$> readBackCtorArgs cnm (ecType cnm) (ps++vs)
         scCtorAppParams sc nm ps' vs'

    loop (VRecordType fs) (VRecordValue vs) =
      do let fm = Map.fromList fs
         let build (k,v) =
                  case Map.lookup k fm of
                    Nothing ->
                       panic "readBackValue / loop" $ [
                           "Field mismatch in record value:",
                           "Fields in type:"
                         ] ++ fs' ++ [
                           "Fields in value:"
                         ] ++ vs'
                       where showField (f, ty) =
                                 "   " <> f <> ": " <> Text.pack (show ty)
                             showValue (f, _v) =
                                 -- v is a thunk, can't print it
                                 -- XXX: we're going to force them all
                                 -- anyway, maybe do that as a first
                                 -- pass on vs?
                                 "   " <> f
                             fs' = map showField fs
                             vs' = map showValue vs
                    Just t ->
                       do tm <- loop t =<< force v
                          return (k,tm)
         vs' <- Map.fromList <$> traverse build vs
         scRecord sc vs'

    loop tv v =
        panic "readBackValue / loop" [
            "Type mismatch",
            "Type we have: " <> Text.pack (show tv),
            "For value: " <> Text.pack (show v)
        ]

    readBackCtorArgs cnm (VPiType _nm tv body) (v:vs) =
      do v' <- force v
         t  <- loop tv v'
         ty <- applyPiBody body (ready v')
         ts <- readBackCtorArgs cnm ty vs
         pure (t:ts)
    readBackCtorArgs _ (VDataType _ _ _) [] = pure []
    readBackCtorArgs cnm _ _ =
      panic "readBackValue / readBackCtorArgs" [
          "Constructor type mismatch: " <> Text.pack (show cnm)
      ]


    readBackFuns (VPiType _ tv pibody) (VFun nm f) =
      do t' <- readBackTValue sc cfg tv
         ec <- scFreshEC sc nm t'
         ?recordEC ec
         ecTm <- scExtCns sc ec
         ecVal <- delay (reflectTerm sc cfg tv ecTm)
         tbody <- applyPiBody pibody ecVal
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

prims :: (?recordEC :: BoundECRecorder) =>
  SharedContext -> Sim.SimulatorConfig TermModel -> Prims.BasePrims TermModel
prims sc cfg =
  Prims.BasePrims
  { Prims.bpIsSymbolicEvaluator = False

  , Prims.bpAsBool  = \case
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
        in binOp sc wordValue f (Prim.append_bv undefined undefined ())

  , Prims.bpBvSlice = \m n -> \case
         Right bv -> pure . Right $! Prim.slice_bv () m n (Prim.width bv - m - n) bv
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

  , Prims.bpMuxArray = \c x@(TMArray a a' b b' arr1) y@(TMArray _ _ _ _ arr2) ->
       case c of
         Right bb -> if bb then pure x else pure y
         Left tm ->
           do t <- scArrayType sc a' b'
              arr' <- scIte sc t tm arr1 arr2
              return $ TMArray a a' b b' arr'

  , Prims.bpMuxExtra = \tp c x y ->
       case c of
         Right b -> if b then pure x else pure y
         Left tm ->
           do x' <- readBackValue sc cfg tp (VExtra x)
              y' <- readBackValue sc cfg tp (VExtra y)
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
  , Prims.bpBvNot  = bvUnOp  sc scBvNot (Prim.bvNot undefined)
  , Prims.bpBvAnd  = bvBinOp sc scBvAnd (Prim.bvAnd undefined)
  , Prims.bpBvOr   = bvBinOp sc scBvOr  (Prim.bvOr  undefined)
  , Prims.bpBvXor  = bvBinOp sc scBvXor (Prim.bvXor undefined)

    -- Bitvector arithmetic
  , Prims.bpBvNeg  = bvUnOp  sc scBvNeg  (Prim.bvNeg  undefined)
  , Prims.bpBvAdd  = bvBinOp sc scBvAdd  (Prim.bvAdd  undefined)
  , Prims.bpBvSub  = bvBinOp sc scBvSub  (Prim.bvSub  undefined)
  , Prims.bpBvMul  = bvBinOp sc scBvMul  (Prim.bvMul  undefined)
  , Prims.bpBvUDiv = bvDivOp sc scBvUDiv (Prim.bvUDiv undefined)
  , Prims.bpBvURem = bvDivOp sc scBvURem (Prim.bvURem undefined)
  , Prims.bpBvSDiv = bvDivOp sc scBvSDiv (Prim.bvSDiv undefined)
  , Prims.bpBvSRem = bvDivOp sc scBvSRem (Prim.bvSRem undefined)
  , Prims.bpBvLg2  = bvUnOp  sc scBvLg2  Prim.bvLg2

    -- Bitvector comparisons
  , Prims.bpBvEq   = bvCmpOp sc scBvEq  (Prim.bvEq  undefined)
  , Prims.bpBvsle  = bvCmpOp sc scBvSLe (Prim.bvsle undefined)
  , Prims.bpBvslt  = bvCmpOp sc scBvSLt (Prim.bvslt undefined)
  , Prims.bpBvule  = bvCmpOp sc scBvULe (Prim.bvule undefined)
  , Prims.bpBvult  = bvCmpOp sc scBvULt (Prim.bvult undefined)
  , Prims.bpBvsge  = bvCmpOp sc scBvSGe (Prim.bvsge undefined)
  , Prims.bpBvsgt  = bvCmpOp sc scBvSGt (Prim.bvsgt undefined)
  , Prims.bpBvuge  = bvCmpOp sc scBvUGe (Prim.bvuge undefined)
  , Prims.bpBvugt  = bvCmpOp sc scBvUGt (Prim.bvugt undefined)

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
  , Prims.bpBvPopcount = bvUnOp sc scBvPopcount (Prim.bvPopcount undefined)
  , Prims.bpBvCountLeadingZeros = bvUnOp sc scBvCountLeadingZeros (Prim.bvCountLeadingZeros undefined)
  , Prims.bpBvCountTrailingZeros = bvUnOp sc scBvCountTrailingZeros (Prim.bvCountTrailingZeros undefined)

  , Prims.bpBvForall = \n f ->
      do bvty <- scBitvector sc n
         ec   <- scFreshEC sc "x" bvty
         ?recordEC ec
         ecTm <- scExtCns sc ec
         res  <- f (Left (n,ecTm))
         case res of
           -- computed a constant boolean without consulting the variable, just return it
           Right b -> return (Right b)
           Left  resTm ->
             do n' <- scNat sc n
                fn <- scAbstractExtsEtaCollapse sc [ec] resTm
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
         a' <- readBackTValue sc cfg a
         b' <- readBackTValue sc cfg b
         tm <- scArrayConstant sc a' b' v'
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

  , Prims.bpArrayCopy = \(TMArray a a' b b' arr1) idx1 (TMArray _ _ _ _ arr2) idx2 len ->
      do let n = wordWidth idx1
         n' <- scNat sc n
         idx1' <- wordTerm sc idx1
         idx2' <- wordTerm sc idx2
         len' <- wordTerm sc len
         arr' <- scArrayCopy sc n' b' arr1 idx1' arr2 idx2' len'
         pure (TMArray a a' b b' arr')

  , Prims.bpArraySet = \(TMArray a a' b b' arr) idx val len ->
      do let n = wordWidth idx
         n' <- scNat sc n
         idx' <- wordTerm sc idx
         val' <- readBackValue sc cfg b val
         len' <- wordTerm sc len
         arr' <- scArraySet sc n' b' arr idx' val' len'
         pure (TMArray a a' b b' arr')

  , Prims.bpArrayRangeEq = \(TMArray _ _ _ b' arr1) idx1 (TMArray _ _ _ _ arr2) idx2 len ->
      do let n = wordWidth idx1
         n' <- scNat sc n
         idx1' <- wordTerm sc idx1
         idx2' <- wordTerm sc idx2
         len' <- wordTerm sc len
         Left <$> scArrayRangeEq sc n' b' arr1 idx1' arr2 idx2' len'
  }


constMap :: (?recordEC :: BoundECRecorder) => SharedContext -> Sim.SimulatorConfig TermModel -> Map Ident TmPrim
constMap sc cfg = Map.union (Map.fromList localPrims) (Prims.constMap pms)
  where
  pms = prims sc cfg

  localPrims =
    -- Shifts
    [ ("Prelude.bvShl" , bvShiftOp sc cfg id   scBvShl  (Prim.bvShl undefined))
    , ("Prelude.bvShr" , bvShiftOp sc cfg id   scBvShr  (Prim.bvShr undefined))
    , ("Prelude.bvSShr", bvShiftOp sc cfg succ scBvSShr (Prim.bvSShr undefined))

    -- Integers
    , ("Prelude.intToNat", intToNatOp sc)
    , ("Prelude.bvToNat" , bvToNatOp sc)
    , ("Prelude.natToInt", natToIntOp sc)
    , ("Prelude.intToBv" , intToBvOp sc)
    , ("Prelude.bvToInt" , bvToIntOp sc cfg)
    , ("Prelude.sbvToInt", sbvToIntOp sc cfg)

    , ("Prelude.error"   , errorOp sc cfg)

    -- Integers mod n
    , ("Prelude.toIntMod"  , toIntModOp sc)
    , ("Prelude.fromIntMod", fromIntModOp sc)
    , ("Prelude.intModEq"  , intModEqOp sc)
    , ("Prelude.intModAdd" , intModAddOp sc)
    , ("Prelude.intModSub" , intModSubOp sc)
    , ("Prelude.intModMul" , intModMulOp sc)
    , ("Prelude.intModNeg" , intModNegOp sc)

    -- Streams
    , ("Prelude.MkStream", mkStreamOp sc cfg)
    , ("Prelude.streamGet", streamGetOp)

    -- Miscellaneous
    , ("Prelude.expByNat", Prims.expByNatOp pms)
    ]

errorOp :: (?recordEC :: BoundECRecorder) => SharedContext -> Sim.SimulatorConfig TermModel -> TmPrim
errorOp sc cfg =
  Prims.tvalFun   $ \tv ->
  Prims.stringFun $ \msg ->
  Prims.Prim $
    do ty' <- readBackTValue sc cfg tv
       err  <- scGlobalDef sc "Prelude.error"
       msg' <- scString sc msg
       tm   <- scApplyAll sc err [ty',msg']
       reflectTerm sc cfg tv tm

-- intToNat : Integer -> Nat;
intToNatOp :: SharedContext -> TmPrim
intToNatOp _sc =
  Prims.strictFun $ \x ->
  Prims.Prim $
  case x of
    VInt (Right i) -> pure . VNat $! fromInteger (max 0 i)
    _ -> pure (VIntToNat x)

-- bvToNat : (n : Nat) -> Vec n Bool -> Nat;
bvToNatOp :: SharedContext -> TmPrim
bvToNatOp _sc =
  Prims.natFun $ \n ->
  Prims.strictFun $ \x ->
  Prims.PrimValue $
    case x of
      VWord (Right bv) -> VNat (fromInteger (unsigned bv))
      _ -> VBVToNat (fromIntegral n) x

-- natToInt : Nat -> Integer;
natToIntOp :: SharedContext -> TmPrim
natToIntOp sc = Prims.PrimFilterFun "natToInt" f (Prims.PrimValue . VInt)
  where
    f (VNat n) =
      pure . Right $! toInteger n

    f (VIntToNat (VInt (Right i))) =
      pure . Right $! max 0 i

    f (VIntToNat (VInt (Left tm))) =
      Left <$> liftIO
       (do z <- scIntegerConst sc 0
           scIntMax sc z tm)

    f (VBVToNat _ (VWord (Right bv))) =
      pure . Right $! Prim.unsigned bv

    f (VBVToNat _ (VWord (Left (n,tm)))) =
      Left <$> liftIO
       (do n' <- scNat sc n
           scBvToInt sc n' tm)

    f _ = mzero

-- primitive intToBv : (n:Nat) -> Integer -> Vec n Bool;
intToBvOp :: SharedContext -> TmPrim
intToBvOp sc =
  Prims.natFun $ \n ->
  Prims.PrimFilterFun "intToBv" (f n) (Prims.PrimValue . VWord)
 where
   f n (VInt (Right i)) =
     pure . Right $! Prim.bv (fromIntegral n) i -- TODO fromIntegral

   f n (VInt (Left tm)) =
     Left <$> liftIO
      (do n' <- scNat sc n
          tm' <- scIntToBv sc n' tm
          pure (n,tm'))

   f _ _ = mzero

-- bvToInt : (n:Nat) -> Vec n Bool -> Integer;
bvToIntOp :: SharedContext -> Sim.SimulatorConfig TermModel -> TmPrim
bvToIntOp _sc _cfg =
  Prims.natFun $ \_n ->
  Prims.PrimFilterFun "bvToInt" f (Prims.PrimValue . VInt)
 where
  f (VWord (Right bv)) = pure . Right $! Prim.unsigned bv
  f _ = mzero

-- sbvToInt : (n:Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: SharedContext -> Sim.SimulatorConfig TermModel -> TmPrim
sbvToIntOp _sc _cfg =
  Prims.natFun $ \_n ->
  Prims.PrimFilterFun "sbvToInt" f (Prims.PrimValue . VInt)
 where
  f (VWord (Right bv)) = pure . Right $! Prim.signed bv
  f _ = mzero

-- | (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool
bvShiftOp ::
  (?recordEC :: BoundECRecorder) =>
  SharedContext ->
  Sim.SimulatorConfig TermModel ->
  (Natural -> Natural) ->
  (SharedContext -> Term -> Term -> Term -> IO Term) ->
  (BitVector -> Int -> BitVector) ->
  TmPrim
bvShiftOp sc cfg szf tmOp bvOp =
  Prims.natFun $ \n0 ->
  Prims.strictFun $ \w ->
  Prims.strictFun $ \amt ->
  Prims.Prim $
    case (w, amt) of
      (VWord (Right w'), VNat amt') ->
        let amt'' = fromInteger (min (toInteger (Prim.width w')) (toInteger amt'))
         in pure . VWord . Right $! bvOp w' amt''
      _ ->
        do let n = szf n0
           n0'  <- scNat sc n0
           w'   <- readBackValue sc cfg (VVecType n VBoolType) w
           dt   <- scRequireDataType sc preludeNatIdent
           pn   <- traverse (evalType cfg) (dtExtCns dt)
           amt' <- readBackValue sc cfg (VDataType pn [] []) amt
           tm   <- tmOp sc n0' w' amt'
           pure (VWord (Left (n, tm)))


toIntModOp ::
  SharedContext ->
  TmPrim
toIntModOp sc =
  Prims.natFun $ \n ->
  Prims.intFun $ \x ->
  Prims.Prim $
    case x of
      Left tm ->
        do n' <- scNat sc n
           VIntMod n . Left <$> scToIntMod sc n' tm
      Right i ->
        pure . VIntMod n . Right $ i `mod` toInteger n

fromIntModOp ::
  SharedContext ->
  TmPrim
fromIntModOp sc =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.Prim $
    case x of
      -- NB, concrete values are maintained in reduced form
      Right i -> pure (VInt (Right i))
      Left tm ->
        do n' <- scNat sc n
           VInt . Left <$> scFromIntMod sc n' tm

intModNegOp :: SharedContext -> TmPrim
intModNegOp sc =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.Prim $
    case x of
      Left tm ->
        do n' <- scNat sc n
           VIntMod n . Left <$> scIntModNeg sc n' tm
      Right i -> pure . VIntMod n . Right $! (negate i `mod` toInteger n)

intModEqOp :: SharedContext -> TmPrim
intModEqOp sc =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
  Prims.Prim
    (VBool <$> intModBinOp sc scIntModEq (==) n x y)

intModAddOp :: SharedContext -> TmPrim
intModAddOp sc =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
  Prims.Prim $
    let f a b = (a+b) `mod` toInteger n
     in VIntMod n <$> intModBinOp sc scIntModAdd f n x y

intModSubOp :: SharedContext -> TmPrim
intModSubOp sc =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
  Prims.Prim $
    let f a b = (a-b) `mod` toInteger n
     in VIntMod n <$> intModBinOp sc scIntModSub f n x y

intModMulOp :: SharedContext -> TmPrim
intModMulOp sc =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
  Prims.Prim $
    let f a b = (a*b) `mod` toInteger n
     in VIntMod n <$> intModBinOp sc scIntModMul f n x y


intModBinOp ::
  SharedContext ->
  (SharedContext -> Term -> Term -> Term -> IO Term) ->
  (Integer -> Integer -> b) ->
  Natural -> Either Term Integer -> Either Term Integer -> IO (Either Term b)
intModBinOp sc termOp valOp n = binOp sc toTerm termOp' valOp
  where
    toTerm _ i =
      do n' <- scNat sc n
         scToIntMod sc n' =<< scIntegerConst sc i

    termOp' _ x y =
      do n' <- scNat sc n
         termOp sc n' x y

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: (?recordEC :: BoundECRecorder) =>
  SharedContext -> Sim.SimulatorConfig TermModel -> TmPrim
mkStreamOp sc cfg =
  Prims.tvalFun $ \ty ->
  Prims.strictFun $ \f ->
  Prims.PrimExcept $
    case f of
      VFun nm fn ->
        do ref <- liftIO (newIORef mempty)
           stm <- liftIO $ delay $ do
                     natDT <- scRequireDataType sc preludeNatIdent
                     natPN <- traverse (evalType cfg) (dtExtCns natDT)
                     ty' <- readBackTValue sc cfg ty
                     ftm <- readBackValue sc cfg (VPiType nm (VDataType natPN [] []) (VNondependentPi ty)) f
                     scGlobalApply sc (mkIdent preludeModuleName "MkStream") [ty',ftm]
           return (VExtra (VExtraStream ty fn ref stm))

      _ -> throwE "expected function value"

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: TmPrim
streamGetOp =
  Prims.tvalFun   $ \_ty ->
  Prims.strictFun $ \xs ->
  Prims.natFun $ \ix ->
  Prims.PrimExcept $
    case xs of
      VExtra (VExtraStream _ fn ref _tm) ->
        liftIO (Map.lookup ix <$> readIORef ref) >>= \case
          Just v  -> return v
          Nothing -> lift $
            do v <- fn (ready (VNat ix))
               liftIO (atomicModifyIORef' ref (\m' -> (Map.insert ix v m', ())))
               return v

      _ -> throwE "expected stream value"
