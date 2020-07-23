{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}  -- For `Show` instance, it's OK.
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TupleSections #-}

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

import Control.Monad (foldM, liftM, mapM)
import Data.Kind (Type)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V

import Verifier.SAW.FiniteValue (FiniteType(..))
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Utils (panic)

import Verifier.SAW.Simulator.MonadLazy

------------------------------------------------------------
-- Values and Thunks

{- | The type of values.
Values are parameterized by the /name/ of an instantiation.
The concrete parameters to use are computed from the name using
a collection of type families (e.g., 'EvalM', 'VBool', etc.). -}
data Value l
  = VFun !(Thunk l -> MValue l)
  | VUnit
  | VPair (Thunk l) (Thunk l) -- TODO: should second component be strict?
  | VCtorApp !Ident !(Vector (Thunk l))
  | VVector !(Vector (Thunk l))
  | VVecType (Value l) (Value l)
  | VBool (VBool l)
  | VBoolType
  | VWord (VWord l)
  | VToNat (Value l)
  | VNat !Integer
  | VInt (VInt l)
  | VIntType
  | VArray (VArray l)
  | VArrayType (Value l) (Value l)
  | VString !String
  | VFloat !Float
  | VDouble !Double
  | VPiType !(Value l) !(Thunk l -> MValue l)
  | VUnitType
  | VPairType (Value l) (Value l)
  | VDataType !Ident [Value l]
  | VRecordType ![(String, Value l)]
  | VRecordValue ![(String, Thunk l)]
  | VType -- ^ Other unknown type
  | VExtra (Extra l)

type Thunk l = Lazy (EvalM l) (Value l)

-- | Evaluation monad for value instantiation 'l'
type family EvalM l :: Type -> Type
-- | Booleans for value instantiation 'l'
type family VBool l :: Type
-- | Words for value instantiation 'l'
type family VWord l :: Type
-- | Integers for value instantiation 'l'
type family VInt  l :: Type
-- | SMT arrays for value instantiation 'l'
type family VArray l :: Type
-- | Additional constructors for instantiation 'l'
type family Extra l :: Type

-- | Short-hand for a monadic value.
type MValue l     = EvalM l (Value l)

-- | Short-hand for a monadic boolean.
type MBool  l     = EvalM l (VBool l)

-- | Short-hand for a monadic word.
type MWord l      = EvalM l (VWord l)

-- | Short-hand for a monadic integer.
type MInt l       = EvalM l (VInt  l)

-- | Short-hand for a monadic array.
type MArray l     = EvalM l (VArray l)

-- | Short hand to specify that the evaluation monad is a monad (very common)
type VMonad l     = Monad (EvalM l)

-- | Short hand to specify that the evaluation monad is a lazy monad.
type VMonadLazy l = MonadLazy (EvalM l)




-- | Language instantiations with a specific monad.
data WithM (m :: Type -> Type) l
type instance EvalM (WithM m l) = m
type instance VBool (WithM m l) = VBool l
type instance VWord (WithM m l) = VWord l
type instance VInt  (WithM m l) = VInt l
type instance VArray (WithM m l) = VArray l
type instance Extra (WithM m l) = Extra l

--------------------------------------------------------------------------------

strictFun :: VMonad l => (Value l -> MValue l) -> Value l
strictFun f = VFun (\x -> force x >>= f)

pureFun :: VMonad l => (Value l -> Value l) -> Value l
pureFun f = VFun (\x -> liftM f (force x))

constFun :: VMonad l => Value l -> Value l
constFun x = VFun (\_ -> return x)

instance Show (Extra l) => Show (Value l) where
  showsPrec p v =
    case v of
      VFun {}        -> showString "<<fun>>"
      VUnit          -> showString "()"
      VPair{}        -> showString "<<tuple>>"
      VCtorApp s xv
        | V.null xv  -> shows s
        | otherwise  -> shows s . showList (toList xv)
      VVector xv     -> showList (toList xv)
      VBool _        -> showString "<<boolean>>"
      VBoolType      -> showString "Bool"
      VWord _        -> showString "<<bitvector>>"
      VToNat x       -> showString "bvToNat " . showParen True (shows x)
      VNat n         -> shows n
      VInt _         -> showString "<<integer>>"
      VIntType       -> showString "Integer"
      VArray{}       -> showString "<<array>>"
      VArrayType{}   -> showString "Array"
      VFloat float   -> shows float
      VDouble double -> shows double
      VString s      -> shows s
      VPiType t _    -> showParen True
                        (shows t . showString " -> ...")
      VUnitType      -> showString "#()"
      VPairType x y  -> showParen True (shows x . showString " * " . shows y)
      VDataType s vs
        | null vs    -> shows s
        | otherwise  -> shows s . showList vs
      VRecordType [] -> showString "{}"
      VRecordType ((fld,_):_) ->
        showString "{" . showString fld . showString " :: _, ...}"
      VRecordValue [] -> showString "{}"
      VRecordValue ((fld,_):_) ->
        showString "{" . showString fld . showString " = _, ...}"
      VVecType n a   -> showString "Vec " . showParen True (showsPrec p n)
                        . showString " " . showParen True (showsPrec p a)
      VType          -> showString "_"
      VExtra x       -> showsPrec p x
    where
      toList = map (const Nil) . V.toList

data Nil = Nil

instance Show Nil where
  show Nil = "_"

------------------------------------------------------------
-- Basic operations on values

vTuple :: VMonad l => [Thunk l] -> Value l
vTuple [] = VUnit
vTuple [_] = error "vTuple: unsupported 1-tuple"
vTuple [x, y] = VPair x y
vTuple (x : xs) = VPair x (ready (vTuple xs))

vTupleType :: VMonad l => [Value l] -> Value l
vTupleType [] = VUnitType
vTupleType [t] = t
vTupleType (t : ts) = VPairType t (vTupleType ts)

valPairLeft :: (VMonad l, Show (Extra l)) => Value l -> MValue l
valPairLeft (VPair t1 _) = force t1
valPairLeft v = panic "Verifier.SAW.Simulator.Value.valPairLeft" ["Not a pair value:", show v]

valPairRight :: (VMonad l, Show (Extra l)) => Value l -> MValue l
valPairRight (VPair _ t2) = force t2
valPairRight v = panic "Verifier.SAW.Simulator.Value.valPairRight" ["Not a pair value:", show v]

vRecord :: Map FieldName (Thunk l) -> Value l
vRecord m = VRecordValue (Map.assocs m)

valRecordProj :: (VMonad l, Show (Extra l)) => Value l -> String -> MValue l
valRecordProj (VRecordValue fld_map) fld
  | Just t <- lookup fld fld_map = force t
valRecordProj v@(VRecordValue _) fld =
  panic "Verifier.SAW.Simulator.Value.valRecordProj"
  ["Record field not found:", fld, "in value:", show v]
valRecordProj v _ =
  panic "Verifier.SAW.Simulator.Value.valRecordProj"
  ["Not a record value:", show v]

apply :: (VMonad l, Show (Extra l)) => Value l -> Thunk l -> MValue l
apply (VFun f) x = f x
apply (VPiType _ f) x = f x
apply v _x = panic "Verifier.SAW.Simulator.Value.apply" ["Not a function value:", show v]

applyAll :: (VMonad l, Show (Extra l)) => Value l -> [Thunk l] -> MValue l
applyAll = foldM apply

asFiniteTypeValue :: Value l -> Maybe FiniteType
asFiniteTypeValue v =
  case v of
    VBoolType -> return FTBit
    VVecType (VNat n) v1 -> do
      t1 <- asFiniteTypeValue v1
      return (FTVec (fromInteger n) t1)
    VUnitType -> return (FTTuple [])
    VPairType v1 v2 -> do
      t1 <- asFiniteTypeValue v1
      t2 <- asFiniteTypeValue v2
      case t2 of
        FTTuple ts -> return (FTTuple (t1 : ts))
        _ -> return (FTTuple [t1, t2])
    VRecordType elem_tps ->
      FTRec <$> Map.fromList <$>
      mapM (\(fld,tp) -> (fld,) <$> asFiniteTypeValue tp) elem_tps
    _ -> Nothing
