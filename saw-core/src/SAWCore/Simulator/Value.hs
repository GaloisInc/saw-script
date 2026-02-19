{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}  -- For `Show` instance, it's OK.

{- |
Module      : SAWCore.Simulator.Value
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Simulator.Value
  ( Value(..)
  , TValue(..)
  , PiBody(..)
  , VRecursor(..)
  -- * Type families
  , EvalM
  , VBool
  , VWord
  , VInt
  , VArray
  , Extra
  , WithM
  -- * Type synonyms
  , Thunk
  , MValue
  , MBool
  , MWord
  , MInt
  , MArray
  , VMonad
  , VMonadLazy
  -- * Value combinators
  , vStrictFun
  , vFunList
  , vStrictFunList
  , vTuple
  , vTupleType
  , valPairLeft
  , valPairRight
  , vRecord
  , valRecordProj
  , apply
  , applyAll
  , applyPiBody
  -- * Recognizers
  , asFiniteTypeValue
  , asFirstOrderTypeValue
  , asFirstOrderTypeTValue
  , suffixTValue
  -- * Re-exports
  , module SAWCore.Simulator.MonadLazy
  ) where

import Control.Monad (foldM)
import Data.Kind (Type)
import Data.IntMap (IntMap)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as V
import Numeric.Natural
import GHC.Stack

import SAWCore.Name
import SAWCore.Panic (panic)
import SAWCore.FiniteValue (FiniteType(..), FirstOrderType(..))
import SAWCore.SharedTerm
import SAWCore.Term.Functor
import SAWCore.Term.Pretty

import SAWCore.Simulator.MonadLazy

------------------------------------------------------------
-- Values and Thunks

{- | SAWCore Values. Values are parameterized by the /name/ of an
instantiation.
The concrete parameters to use are computed from the name using
a collection of type families (e.g., 'EvalM', 'VBool', etc.). -}
data Value l
  = VFun !(Thunk l -> MValue l)
  | VUnit
  | VPair (Thunk l) (Thunk l) -- TODO: should second component be strict?
  | VCtorApp !Name !(TValue l) ![Thunk l] ![Thunk l]
  | VCtorMux ![Thunk l] !(IntMap (VBool l, Name, TValue l, [Thunk l]))
    -- ^ A mux tree of possible constructor values of a data type.
    -- The list of data type parameters is kept outside the mux.
    -- The 'IntMap' keys are 'VarIndex'es of each constructor name.
    -- The 'VBool' predicates must be mutually-exclusive and one
    -- must always be true.
  | VVector !(Vector (Thunk l))
  | VBool (VBool l)
  | VWord (VWord l)
  | VBVToNat !Int (Value l) -- TODO: don't use @Int@ for this, use @Natural@
  | VIntToNat (Value l)
  | VNat !Natural
  | VInt (VInt l)
  | VIntMod !Natural (VInt l)
  | VRational (VInt l) (VInt l)
  | VArray (VArray l)
  | VString !Text
  | VEmptyRecord
  | VRecordValue !FieldName (Thunk l) !(Value l) -- strict in spine of record
  | VExtra (Extra l)
  | TValue (TValue l)

data VRecursor l
  = VRecursor
     !Name -- data type name
     !Int        -- number of index parameters
     !(Map VarIndex (Thunk l)) -- constructor eliminators

-- | The subset of values that represent types.
data TValue l
  = VVecType !Natural !(TValue l)
  | VBoolType
  | VIntType
  | VIntModType !Natural
  | VRationalType
  | VArrayType !(TValue l) !(TValue l)
  | VPiType !(TValue l) !(PiBody l)
  | VStringType
  | VUnitType
  | VPairType !(TValue l) !(TValue l)
  | VDataType !Name ![Value l] ![Value l] -- ^ name, parameters, indices
  | VEmptyRecordType
  | VRecordType !FieldName !(TValue l) !(TValue l)
  | VSort !Sort
  | VTyTerm !Sort !Term

data PiBody l
  = VDependentPi !(Thunk l -> EvalM l (TValue l))
  | VNondependentPi !(TValue l)

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

instance Show (Extra l) => Show (Value l) where
  showsPrec p v =
    case v of
      VFun {}        -> showString "<<fun>>"
      VUnit          -> showString "()"
      VPair{}        -> showString "<<tuple>>"
      VCtorApp c _ty _ps _xv -> shows (toAbsoluteName (nameInfo c))
      VCtorMux {}    -> showString "<<constructor>>"
      VVector xv     -> showList (toList xv)
      VBool _        -> showString "<<boolean>>"
      VWord _        -> showString "<<bitvector>>"
      VBVToNat n x   -> showString "bvToNat " . shows n . showString " " . showParen True (shows x)
      VIntToNat x    -> showString "intToNat " . showParen True (shows x)
      VNat n         -> shows n
      VInt _         -> showString "<<integer>>"
      VIntMod n _    -> showString ("<<Z " ++ show n ++ ">>")
      VRational{}    -> showString "<<rational>>"
      VArray{}       -> showString "<<array>>"
      VString s      -> shows s
      VEmptyRecord   -> showString "{}"
      VRecordValue fld _ _ ->
        showString "{" . showString (Text.unpack fld) . showString " = _, ...}"
      VExtra x       -> showsPrec p x
      TValue x       -> showsPrec p x
    where
      toList = map (const Nil) . V.toList

instance Show (Extra l) => Show (TValue l) where
  showsPrec p v =
    case v of
      VBoolType      -> showString "Bool"
      VStringType    -> showString "String"
      VIntType       -> showString "Integer"
      VIntModType n  -> showParen True (showString "IntMod " . shows n)
      VRationalType  -> showString "Rational"
      VArrayType{}   -> showString "Array"
      VPiType t _    -> showParen True
                        (shows t . showString " -> ...")
      VUnitType      -> showString "#()"
      VPairType x y  -> showParen True (shows x . showString " * " . shows y)
      VDataType s ps vs ->
          let s' = Text.unpack $ toAbsoluteName (nameInfo s) in
          case ps ++ vs of
            [] -> shows s'
            vs' -> shows s' . showList vs'
      VEmptyRecordType -> showString "{}"
      VRecordType fld _ _ ->
        showString "{" . showString (Text.unpack fld) . showString " :: _, ...}"
      VVecType n a   -> showString "Vec " . shows n
                        . showString " " . showParen True (showsPrec p a)
      VSort s        -> shows s

      VTyTerm _ tm   -> showString "TyTerm (" . (\x -> ppTermPureDefaults tm ++ x) . showString ")"

data Nil = Nil

instance Show Nil where
  show Nil = "_"

------------------------------------------------------------
-- Basic operations on values

-- | Create a 'Value' for a strict function.
vStrictFun :: VMonad l => (Value l -> MValue l) -> Value l
vStrictFun k = VFun $ \x -> force x >>= k

-- | Create a 'Value' for a lazy multi-argument function.
vFunList :: forall l. VMonad l => Int -> ([Thunk l] -> MValue l) -> MValue l
vFunList n0 k = go n0 []
  where
    go :: Int -> [Thunk l] -> MValue l
    go 0 args = k (reverse args)
    go n args = pure $ VFun (\x -> go (n - 1) (x : args))

-- | Create a 'Value' for a strict multi-argument function.
vStrictFunList :: forall l. VMonad l => Int -> ([Value l] -> MValue l) -> MValue l
vStrictFunList n0 k = go n0 []
  where
    go :: Int -> [Value l] -> MValue l
    go 0 args = k (reverse args)
    go n args = pure $ vStrictFun $ \v -> go (n - 1) (v : args)

vTuple :: VMonad l => [Thunk l] -> Value l
vTuple [] = VUnit
vTuple [_] = error "vTuple: unsupported 1-tuple"
vTuple [x, y] = VPair x y
vTuple (x : xs) = VPair x (ready (vTuple xs))

vTupleType :: VMonad l => [TValue l] -> TValue l
vTupleType [] = VUnitType
vTupleType [t] = t
vTupleType (t : ts) = VPairType t (vTupleType ts)

valPairLeft :: (HasCallStack, VMonad l, Show (Extra l)) => Value l -> MValue l
valPairLeft (VPair t1 _) = force t1
valPairLeft v = panic "valPairLeft" ["Not a pair value: " <> Text.pack (show v)]

valPairRight :: (HasCallStack, VMonad l, Show (Extra l)) => Value l -> MValue l
valPairRight (VPair _ t2) = force t2
valPairRight v = panic "valPairRight" ["Not a pair value: " <> Text.pack (show v)]

vRecord :: Map FieldName (Thunk l) -> Value l
vRecord m = foldr (\(f, t) -> VRecordValue f t) VEmptyRecord (Map.assocs m)

valRecordProj :: (HasCallStack, VMonad l, Show (Extra l)) => Value l -> FieldName -> MValue l
valRecordProj v fld = go v
  where
    go (VRecordValue fld1 t1 v1)
      | fld == fld1 = force t1
      | otherwise = go v1
    go VEmptyRecord =
      panic "valRecordProj"
      [ "Record field " <> Text.pack (show fld) <> " not found in value: " <>
        Text.pack (show v)
      ]
    go _ =
      panic "valRecordProj" ["Not a record value: " <> Text.pack (show v)]

apply :: (HasCallStack, VMonad l, Show (Extra l)) => Value l -> Thunk l -> MValue l
apply (VFun f) x = f x
apply (TValue (VPiType _ body)) x = TValue <$> applyPiBody body x

apply v _x = panic "apply" ["Not a function value: " <> Text.pack (show v)]

applyAll :: (VMonad l, Show (Extra l)) => Value l -> [Thunk l] -> MValue l
applyAll = foldM apply

{-# INLINE applyPiBody #-}
applyPiBody :: VMonad l => PiBody l -> Thunk l -> EvalM l (TValue l)
applyPiBody (VDependentPi f) x    = f x
applyPiBody (VNondependentPi t) _ = pure t

-- | Return the 'FiniteType' corresponding to the given 'Value', if
-- one exists.
-- If @asFiniteTypeValue v = Just t@, then the term returned by
-- 'SAWCore.FiniteValue.scFiniteType' applied to @t@ should evaluate
-- to @v@.
asFiniteTypeValue :: Value l -> Maybe FiniteType
asFiniteTypeValue v =
  case v of
    TValue tv -> asFiniteTypeTValue tv
    _ -> Nothing

-- | Return the 'FiniteType' corresponding to the given 'TValue', if
-- one exists.
-- If @asFiniteTypeValue tv = Just t@, then the term returned by
-- 'SAWCore.FiniteValue.scFiniteType' applied to @t@ should evaluate
-- to @TValue tv@.
asFiniteTypeTValue :: TValue l -> Maybe FiniteType
asFiniteTypeTValue v =
  case v of
    VBoolType -> return FTBit
    VVecType n v1 -> do
      t1 <- asFiniteTypeTValue v1
      return (FTVec n t1)
    VUnitType -> return (FTTuple [])
    VPairType v1 v2 -> do
      t1 <- asFiniteTypeTValue v1
      t2 <- asFiniteTypeTValue v2
      case t2 of
        FTTuple ts -> return (FTTuple (t1 : ts))
        _ -> return (FTTuple [t1, t2])
    VEmptyRecordType -> Just (FTRec Map.empty)
    VRecordType fname v1 v2 ->
      do t1 <- asFiniteTypeTValue v1
         t2 <- asFiniteTypeTValue v2
         -- scFiniteType only produces nested record types with field
         -- names in strictly increasing order.
         -- In the case of duplicate or non-sorted field names, this
         -- TValue does not correspond to any canonical record type,
         -- so we return Nothing.
         case t2 of
           FTRec tm | lessThanKeys fname tm -> Just (FTRec (Map.insert fname t1 tm))
           _ -> Nothing
    VStringType   -> Nothing
    VPiType{}     -> Nothing
    VDataType{}   -> Nothing
    VSort{}       -> Nothing
    VTyTerm{}     -> Nothing
    VIntType      -> Nothing
    VIntModType{} -> Nothing
    VRationalType{} -> Nothing
    VArrayType{}  -> Nothing
  where

asFirstOrderTypeValue :: Value l -> Maybe FirstOrderType
asFirstOrderTypeValue v =
  case v of
    TValue tv -> asFirstOrderTypeTValue tv
    _ -> Nothing

asFirstOrderTypeTValue :: TValue l -> Maybe FirstOrderType
asFirstOrderTypeTValue v =
  case v of
    VBoolType     -> return FOTBit
    VVecType n v1 -> FOTVec n <$> asFirstOrderTypeTValue v1
    VIntType      -> return FOTInt
    VIntModType m -> return (FOTIntMod m)
    VRationalType -> return FOTRational
    VArrayType a b ->
      FOTArray <$> asFirstOrderTypeTValue a <*> asFirstOrderTypeTValue b
    VUnitType -> return (FOTTuple [])
    VPairType v1 v2 -> do
      t1 <- asFirstOrderTypeTValue v1
      t2 <- asFirstOrderTypeTValue v2
      case t2 of
        FOTTuple ts -> return (FOTTuple (t1 : ts))
        _ -> return (FOTTuple [t1, t2])
    VEmptyRecordType -> Just (FOTRec Map.empty)
    VRecordType fname v1 v2 ->
      do t1 <- asFirstOrderTypeTValue v1
         t2 <- asFirstOrderTypeTValue v2
         -- scFirstOrderType only produces nested record types with
         -- field names in strictly increasing order.
         -- In the case of duplicate or non-sorted field names, this
         -- TValue does not correspond to any canonical record type,
         -- so we return Nothing.
         case t2 of
           FOTRec tm | lessThanKeys fname tm -> Just (FOTRec (Map.insert fname t1 tm))
           _ -> Nothing

    VStringType -> Nothing
    VPiType{}   -> Nothing
    VDataType{} -> Nothing
    VSort{}     -> Nothing
    VTyTerm{}   -> Nothing

-- | Is the given key less than all keys in the given map?
lessThanKeys :: (Ord k) => k -> Map k a -> Bool
lessThanKeys k m =
  case Map.minViewWithKey m of
    Just ((k', _), _) -> k < k'
    Nothing -> True

-- | A (partial) injective mapping from type values to strings. These
-- are intended to be useful as suffixes for names of type instances
-- of uninterpreted constants.
suffixTValue :: TValue sym -> Maybe String
suffixTValue tv =
  case tv of
    VVecType n a ->
      do a' <- suffixTValue a
         Just ("_Vec_" ++ show n ++ a')
    VBoolType -> Just "_Bool"
    VIntType -> Just "_Int"
    VIntModType n -> Just ("_IntMod_" ++ show n)
    VRationalType -> Just "_Rational"
    VArrayType a b ->
      do a' <- suffixTValue a
         b' <- suffixTValue b
         Just ("_Array" ++ a' ++ b')
    VPiType _ _ -> Nothing
    VUnitType -> Just "_Unit"
    VPairType a b ->
      do a' <- suffixTValue a
         b' <- suffixTValue b
         Just ("_Pair" ++ a' ++ b')

    VStringType -> Nothing
    VDataType {} -> Nothing
    VEmptyRecordType -> Nothing
    VRecordType {} -> Nothing
    VSort {} -> Nothing
    VTyTerm{} -> Nothing
