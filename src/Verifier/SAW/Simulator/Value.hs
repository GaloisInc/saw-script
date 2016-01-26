{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Verifier.SAW.Simulator.Value
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.Value
       ( module Verifier.SAW.Simulator.Value
       , module Verifier.SAW.Simulator.MonadLazy
       ) where

import Prelude hiding (mapM)

import Control.Monad (foldM, liftM)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V

import Verifier.SAW.FiniteValue (FiniteType(..))
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import Verifier.SAW.Simulator.MonadLazy

------------------------------------------------------------
-- Values and Thunks

data Value m b w e
  = VFun !(Thunk m b w e -> m (Value m b w e))
  | VUnit
  | VPair (Thunk m b w e) (Thunk m b w e) -- TODO: should second component be strict?
  | VEmpty
  | VField FieldName (Thunk m b w e) !(Value m b w e)
  | VCtorApp !Ident !(Vector (Thunk m b w e))
  | VVector !(Vector (Thunk m b w e))
  | VBool b
  | VWord w
  | VToNat (Value m b w e)
  | VNat !Integer
  | VInt !Integer
  | VString !String
  | VFloat !Float
  | VDouble !Double
  | VPiType !(Value m b w e) !(Thunk m b w e -> m (Value m b w e))
  | VUnitType
  | VPairType (Value m b w e) (Value m b w e)
  | VEmptyType
  | VFieldType FieldName !(Value m b w e) !(Value m b w e)
  | VDataType !Ident [Value m b w e]
  | VType -- ^ Other unknown type
  | VExtra e

type Thunk m b w e = Lazy m (Value m b w e)

strictFun :: Monad m => (Value m b w e -> m (Value m b w e)) -> Value m b w e
strictFun f = VFun (\x -> force x >>= f)

pureFun :: Monad m => (Value m b w e -> Value m b w e) -> Value m b w e
pureFun f = VFun (\x -> liftM f (force x))

constFun :: Monad m => Value m b w e -> Value m b w e
constFun x = VFun (\_ -> return x)

instance Show e => Show (Value m b w e) where
  showsPrec p v =
    case v of
      VFun {}        -> showString "<<fun>>"
      VUnit          -> showString "()"
      VPair{}        -> showString "<<tuple>>"
      VEmpty         -> showString "{}"
      VField f _ _   -> showString "{" . showString f . showString " = _, ...}"
      VCtorApp s xv
        | V.null xv  -> shows s
        | otherwise  -> shows s . showList (toList xv)
      VVector xv     -> showList (toList xv)
      VBool _        -> showString "<<boolean>>"
      VWord _        -> showString "<<bitvector>>"
      VToNat x       -> showString "bvToNat " . showParen True (shows x)
      VNat n         -> shows n
      VInt i         -> shows i
      VFloat float   -> shows float
      VDouble double -> shows double
      VString s      -> shows s
      VPiType t _    -> showParen True
                        (shows t . showString " -> ...")
      VUnitType      -> showString "#()"
      VPairType x y  -> showParen True (shows x . showString " * " . shows y)
      VEmptyType {}  -> showString "<<record type>>"
      VFieldType {}  -> showString "<<record type>>"
      VDataType s vs
        | null vs    -> shows s
        | otherwise  -> shows s . showList vs
      VType          -> showString "_"
      VExtra x       -> showsPrec p x
    where
      toList = map (const Nil) . V.toList

data Nil = Nil

instance Show Nil where
  show Nil = "_"

------------------------------------------------------------
-- Basic operations on values

vTuple :: Monad m => [Thunk m b w e] -> Value m b w e
vTuple [] = VUnit
vTuple (x : xs) = VPair x (ready (vTuple xs))

vTupleType :: Monad m => [Value m b w e] -> Value m b w e
vTupleType [] = VUnitType
vTupleType (x : xs) = VPairType x (vTupleType xs)

valPairLeft :: (Monad m, Show e) => Value m b w e -> m (Value m b w e)
valPairLeft (VPair t1 _) = force t1
valPairLeft v = fail $ "valPairLeft: Not a pair value: " ++ show v

valPairRight :: (Monad m, Show e) => Value m b w e -> m (Value m b w e)
valPairRight (VPair _ t2) = force t2
valPairRight v = fail $ "valPairRight: Not a pair value: " ++ show v

vRecord :: Map FieldName (Thunk m b w e) -> Value m b w e
vRecord m = foldr (uncurry VField) VEmpty (Map.assocs m)

valRecordSelect :: (Monad m, Show e) => FieldName -> Value m b w e -> m (Value m b w e)
valRecordSelect k (VField k' x r) = if k == k' then force x else valRecordSelect k r
valRecordSelect k VEmpty = fail $ "valRecordSelect: record field not found: " ++ k
valRecordSelect _ v = fail $ "valRecordSelect: Not a record value: " ++ show v

apply :: Monad m => Value m b w e -> Thunk m b w e -> m (Value m b w e)
apply (VFun f) x = f x
apply _ _ = fail "Not a function value"

applyAll :: Monad m => Value m b w e -> [Thunk m b w e] -> m (Value m b w e)
applyAll = foldM apply

asFiniteTypeValue :: Value m b w e -> Maybe FiniteType
asFiniteTypeValue v =
  case v of
    VDataType "Prelude.Bool" [] -> return FTBit
    VDataType "Prelude.Vec" [VNat n, v1] -> do
      t1 <- asFiniteTypeValue v1
      return (FTVec (fromInteger n) t1)
    VUnitType -> return (FTTuple [])
    VPairType v1 v2 -> do
      t1 <- asFiniteTypeValue v1
      t2 <- asFiniteTypeValue v2
      case t2 of
        FTTuple ts -> return (FTTuple (t1 : ts))
        _ -> Nothing
    VEmptyType -> return (FTRec Map.empty)
    VFieldType k v1 v2 -> do
      t1 <- asFiniteTypeValue v1
      t2 <- asFiniteTypeValue v2
      case t2 of
        FTRec tm -> return (FTRec (Map.insert k t1 tm))
        _ -> Nothing
    _ -> Nothing
