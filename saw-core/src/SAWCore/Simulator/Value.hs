{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}  -- For `Show` instance, it's OK.
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TupleSections #-}

{- |
Module      : SAWCore.Simulator.Value
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Simulator.Value
       ( module SAWCore.Simulator.Value
       , module SAWCore.Simulator.MonadLazy
       ) where

import Prelude hiding (mapM)

import Control.Monad (foldM, mapM)
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

import qualified SAWSupport.Pretty as PPS (Doc, Opts, defaultOpts, render)

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
  | VArray (VArray l)
  | VString !Text
  | VRecordValue ![(FieldName, Thunk l)]
  | VExtra (Extra l)
  | TValue (TValue l)

data VRecursor l
  = VRecursor
     !Name -- data type name
     !(TValue l) -- data type kind
     ![Value l]  -- data type parameters
     !Int        -- number of index parameters
     !(Value l)  -- motive function
     !(TValue l) -- type of motive
     !(Map VarIndex (Thunk l)) -- constructor eliminators and their types
     !(TValue l) -- type of recursor function

-- | The subset of values that represent types.
data TValue l
  = VVecType !Natural !(TValue l)
  | VBoolType
  | VIntType
  | VIntModType !Natural
  | VArrayType !(TValue l) !(TValue l)
  | VPiType !(TValue l) !(PiBody l)
  | VStringType
  | VUnitType
  | VPairType !(TValue l) !(TValue l)
  | VDataType !Name !(TValue l) ![Value l] ![Value l]
  | VRecordType ![(FieldName, TValue l)]
  | VSort !Sort
  | VTyTerm !Sort !Term

data PiBody l
  = VDependentPi !(Thunk l -> EvalM l (TValue l))
  | VNondependentPi !(TValue l)

-- | Neutral terms represent computations that are blocked
--   because some internal term cannot be evaluated
--   (e.g., because it is a variable, because it's definition
--   is being hidden, etc.)
data NeutralTerm
  = NeutralBox Term -- the thing blocking evaluation
  | NeutralPairLeft NeutralTerm   -- left pair projection
  | NeutralPairRight NeutralTerm  -- right pair projection
  | NeutralRecordProj NeutralTerm FieldName -- record projection
  | NeutralApp NeutralTerm Term -- function application
  | NeutralConstant -- A constant value with no definition
      Name

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
      VArray{}       -> showString "<<array>>"
      VString s      -> shows s
      VRecordValue [] -> showString "{}"
      VRecordValue ((fld,_):_) ->
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
      VArrayType{}   -> showString "Array"
      VPiType t _    -> showParen True
                        (shows t . showString " -> ...")
      VUnitType      -> showString "#()"
      VPairType x y  -> showParen True (shows x . showString " * " . shows y)
      VDataType s _ ps vs
        | null (ps++vs) -> shows s
        | otherwise  -> shows s . showList (ps++vs)
      VRecordType [] -> showString "{}"
      VRecordType ((fld,_):_) ->
        showString "{" . showString (Text.unpack fld) . showString " :: _, ...}"
      VVecType n a   -> showString "Vec " . shows n
                        . showString " " . showParen True (showsPrec p a)
      VSort s        -> shows s

      VTyTerm _ tm   -> showString "TyTerm (" . (\x -> showTerm tm ++ x) . showString ")"

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
vRecord m = VRecordValue (Map.assocs m)

valRecordProj :: (HasCallStack, VMonad l, Show (Extra l)) => Value l -> FieldName -> MValue l
valRecordProj (VRecordValue fld_map) fld
  | Just t <- lookup fld fld_map = force t
valRecordProj v@(VRecordValue _) fld =
  panic "valRecordProj" [
      "Record field " <> Text.pack (show fld) <> " not found in value: " <>
          Text.pack (show v)
  ]
valRecordProj v _ =
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

asFiniteTypeValue :: Value l -> Maybe FiniteType
asFiniteTypeValue v =
  case v of
    TValue tv -> asFiniteTypeTValue tv
    _ -> Nothing

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
    VRecordType elem_tps ->
      FTRec <$> Map.fromList <$>
      mapM (\(fld,tp) -> (fld,) <$> asFiniteTypeTValue tp) elem_tps
    _ -> Nothing

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
    VArrayType a b ->
      FOTArray <$> asFirstOrderTypeTValue a <*> asFirstOrderTypeTValue b
    VUnitType -> return (FOTTuple [])
    VPairType v1 v2 -> do
      t1 <- asFirstOrderTypeTValue v1
      t2 <- asFirstOrderTypeTValue v2
      case t2 of
        FOTTuple ts -> return (FOTTuple (t1 : ts))
        _ -> return (FOTTuple [t1, t2])
    VRecordType elem_tps ->
      FOTRec . Map.fromList <$>
        mapM (traverse asFirstOrderTypeTValue) elem_tps

    VStringType   -> Nothing
    VPiType{}   -> Nothing
    VDataType{} -> Nothing
    VSort{}     -> Nothing
    VTyTerm{}   -> Nothing

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
    VRecordType {} -> Nothing
    VSort {} -> Nothing
    VTyTerm{} -> Nothing


neutralToTerm :: NeutralTerm -> Term
neutralToTerm = loop
  where
  loop (NeutralBox tm) = tm
  loop (NeutralPairLeft nt) =
    Unshared (FTermF (PairLeft (loop nt)))
  loop (NeutralPairRight nt) =
    Unshared (FTermF (PairRight (loop nt)))
  loop (NeutralRecordProj nt f) =
    Unshared (FTermF (RecordProj (loop nt) f))
  loop (NeutralApp nt arg) =
    Unshared (App (loop nt) arg)
  loop (NeutralConstant nm) =
    Unshared (Constant nm)

neutralToSharedTerm :: SharedContext -> NeutralTerm -> IO Term
neutralToSharedTerm sc = loop
  where
  loop (NeutralBox tm) = pure tm
  loop (NeutralPairLeft nt) =
    scFlatTermF sc . PairLeft =<< loop nt
  loop (NeutralPairRight nt) =
    scFlatTermF sc . PairRight =<< loop nt
  loop (NeutralRecordProj nt f) =
    do tm <- loop nt
       scFlatTermF sc (RecordProj tm f)
  loop (NeutralApp nt arg) =
    do tm <- loop nt
       scApply sc tm arg
  loop (NeutralConstant nm) =
    do scConst sc nm

ppNeutral :: PPS.Opts -> NeutralTerm -> PPS.Doc
ppNeutral opts = ppTerm opts . neutralToTerm

-- XXX this shouldn't be a Show instance
instance Show NeutralTerm where
  show = PPS.render PPS.defaultOpts . ppNeutral PPS.defaultOpts
