{- |
Module      : SAWCore.Recognizer
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Lightweight calculus for composing patterns as functions.
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module SAWCore.Recognizer
  ( Recognizer
  , (<:>), (<:), emptyl, endl
  , (:*:)(..)
  , asFTermF

  , asGlobalDef
  , isGlobalDef
  , asApp
  , (<@>), (@>), (<@)
  , asApplyAll
  , asGlobalApply
  , asPairType
  , asPairValue
  , asPairSelector
  , asTupleType
  , asTupleValue
  , asTupleSelector
  , asRecordType
  , asRecordValue
  , asRecordSelector
  , asRecursorApp
  , asRecursorType
  , asNat
  , asBvNat
  , asUnsignedConcreteBv
  , asBvToNat
  , asUnsignedConcreteBvToNat
  , asArrayValue
  , asStringLit
  , asLambda
  , asLambdaList
  , asPi
  , asPiList
  , asLocalVar
  , asConstant
  , asVariable
  , asSort
  , asSortWithFlags
    -- * Prelude recognizers.
  , asBool
  , asBoolType
  , asNatType
  , asIntegerType
  , asIntModType
  , asBitvectorType
  , asVectorType
  , asVecType
  , isVecType
  , asMux
  , asEq
  , asEqTrue
  , asArrayType
  ) where

import Control.Lens
import Control.Monad
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import Data.Text (Text)
import Numeric.Natural (Natural)

import SAWCore.Name
import SAWCore.Term.Functor
import SAWCore.Prelude.Constants

data a :*: b = (:*:) a b
  deriving (Eq,Ord,Show)

instance Field1 (a :*: b) (a' :*: b) a a' where
  _1 k (a :*: b) = indexed k (0 :: Int) a <&> (:*: b)

instance Field2 (a :*: b) (a :*: b') b b' where
  _2 k (a :*: b) = (a :*:) <$> indexed k (1 :: Int) b

toPair :: a :*: b -> (a, b)
toPair (a :*: b) = (a, b)

type Recognizer t a = t -> Maybe a

-- | Recognizes the head and tail of a list, and returns head.
(<:) :: Recognizer t a -> Recognizer [t] () -> Recognizer [t] a
(<:) f g (h:r) = do x <- f h; _ <- g r; return x
(<:) _ _ [] = Nothing

-- | Recognizes the head and tail of a list, and returns both.
(<:>) :: Recognizer t a -> Recognizer [t] b -> Recognizer [t] (a :*: b)
(<:>) f g (h:r) = do x <- f h; y <- g r; return (x :*: y)
(<:>) _ _ [] = Nothing

-- | Recognizes empty list
emptyl :: Recognizer [t] ()
emptyl [] = return ()
emptyl _ = Nothing

-- | Recognizes singleton list
endl :: Recognizer t a -> Recognizer [t] a
endl f = f <: emptyl

asFTermF :: Recognizer Term (FlatTermF Term)
asFTermF (unwrapTermF -> FTermF ftf) = return ftf
asFTermF _ = Nothing

asModuleIdentifier :: Recognizer Name Ident
asModuleIdentifier nm =
  case nameInfo nm of
    ModuleIdentifier ident -> Just ident
    _ -> Nothing

asGlobalDef :: Recognizer Term Ident
asGlobalDef t =
  case unwrapTermF t of
    Constant nm -> asModuleIdentifier nm
    _ -> Nothing

isGlobalDef :: Ident -> Recognizer Term ()
isGlobalDef i t = do
  o <- asGlobalDef t
  if i == o then Just () else Nothing

asApp :: Recognizer Term (Term, Term)
asApp (unwrapTermF -> App x y) = return (x, y)
asApp _ = Nothing

(<@>) :: Recognizer Term a -> Recognizer Term b -> Recognizer Term (a :*: b)
(<@>) f g t = do
  (a,b) <- asApp t
  liftM2 (:*:) (f a) (g b)

-- | Recognizes a function application, and returns argument.
(@>) :: Recognizer Term () -> Recognizer Term b -> Recognizer Term b
(@>) f g t = do
  (x, y) <- asApp t
  liftM2 (const id) (f x) (g y)

-- | Recognizes a function application, and returns the function
(<@) :: Recognizer Term a -> Recognizer Term () -> Recognizer Term a
(<@) f g t = do
  (x, y) <- asApp t
  liftM2 const (f x) (g y)

asApplyAll :: Term -> (Term, [Term])
asApplyAll = go []
  where go xs t =
          case asApp t of
            Nothing -> (t, xs)
            Just (t', x) -> go (x : xs) t'

asGlobalApply :: Ident -> Recognizer Term [Term]
asGlobalApply i t =
  do let (f, xs) = asApplyAll t
     isGlobalDef i f
     pure xs

asPairType :: Recognizer Term (Term, Term)
asPairType t = do
  ftf <- asFTermF t
  case ftf of
    PairType x y -> return (x, y)
    _            -> Nothing

asPairValue :: Recognizer Term (Term, Term)
asPairValue t = do
  ftf <- asFTermF t
  case ftf of
    PairValue x y -> return (x, y)
    _             -> Nothing

asPairSelector :: Recognizer Term (Term, Bool)
asPairSelector t = do
  ftf <- asFTermF t
  case ftf of
    PairLeft x  -> return (x, False)
    PairRight x -> return (x, True)
    _           -> Nothing

destTupleType :: Term -> [Term]
destTupleType t =
  case unwrapTermF t of
    FTermF (PairType x y) -> x : destTupleType y
    _ -> [t]

destTupleValue :: Term -> [Term]
destTupleValue t =
  case unwrapTermF t of
    FTermF (PairValue x y) -> x : destTupleType y
    _ -> [t]

asTupleType :: Recognizer Term [Term]
asTupleType t =
  do ftf <- asFTermF t
     case ftf of
       UnitType     -> Just []
       PairType x y -> Just (x : destTupleType y)
       _            -> Nothing

asTupleValue :: Recognizer Term [Term]
asTupleValue t =
  do ftf <- asFTermF t
     case ftf of
       UnitValue     -> Just []
       PairValue x y -> Just (x : destTupleValue y)
       _             -> Nothing

asTupleSelector :: Recognizer Term (Term, Int)
asTupleSelector t = do
  ftf <- asFTermF t
  case ftf of
    PairLeft x  -> return (x, 1)
    PairRight y -> do (x, i) <- asTupleSelector y; return (x, i+1)
    _           -> Nothing

asRecordType :: Recognizer Term (Map FieldName Term)
asRecordType t = do
  ftf <- asFTermF t
  case ftf of
    RecordType elems -> return $ Map.fromList elems
    _                -> Nothing

asRecordValue :: Recognizer Term (Map FieldName Term)
asRecordValue t = do
  ftf <- asFTermF t
  case ftf of
    RecordValue elems -> return $ Map.fromList elems
    _                 -> Nothing

asRecordSelector :: Recognizer Term (Term, FieldName)
asRecordSelector t = do
  RecordProj u s <- asFTermF t
  return (u, s)

asRecursorType :: Recognizer Term (Name, [Term], Term, Term)
asRecursorType t =
  do RecursorType d ps motive motive_ty <- asFTermF t
     return (d,ps,motive,motive_ty)

asRecursorApp :: Recognizer Term (Term, CompiledRecursor Term, [Term])
asRecursorApp t =
  do RecursorApp rc ixs <- asFTermF t
     Recursor crec <- asFTermF rc
     return (rc, crec, ixs)

asNat :: Recognizer Term Natural
asNat (unwrapTermF -> FTermF (NatLit i)) = pure i
asNat (asGlobalApply preludeZeroIdent -> Just []) = pure 0
asNat (asGlobalApply preludeSuccIdent -> Just [asNat -> Just i]) = pure (i+1)
asNat _ = Nothing

-- | Recognize an application of @bvNat@
asBvNat :: Recognizer Term (Term, Term)
asBvNat = fmap toPair . ((isGlobalDef "Prelude.bvNat" @> return) <@> return)

-- | Try to convert the given term of type @Vec w Bool@ to a concrete 'Natural',
-- taking into account nat, bitvector and integer conversions (treating all
-- bitvectors as unsigned)
asUnsignedConcreteBv :: Recognizer Term Natural
asUnsignedConcreteBv (asApplyAll -> (asGlobalDef -> Just "Prelude.bvNat",
                                     [asNat -> Just n, v])) =
  (`mod` (2 ^ n)) <$> asUnsignedConcreteBvToNat v
asUnsignedConcreteBv (asArrayValue -> Just (asBoolType -> Just _,
                                            mapM asBool -> Just bits)) =
  return $ foldl' (\n bit -> if bit then 2*n+1 else 2*n) 0 bits
asUnsignedConcreteBv (asApplyAll -> (asGlobalDef -> Just "Prelude.intToBv",
                                     [asNat -> Just n, i])) = case i of
  (asApplyAll -> (asGlobalDef -> Just "Prelude.natToInt", [v])) ->
    (`mod` (2 ^ n)) <$> asUnsignedConcreteBvToNat v
  (asApplyAll -> (asGlobalDef -> Just "Prelude.bvToInt", [_, bv])) ->
    asUnsignedConcreteBv bv
  _ -> Nothing
asUnsignedConcreteBv _ = Nothing

-- | Recognize an application of @bvToNat@
asBvToNat :: Recognizer Term (Term, Term)
asBvToNat = fmap toPair . ((isGlobalDef "Prelude.bvToNat" @> return) <@> return)

-- | Try to convert the given term of type @Nat@ to a concrete 'Natural',
-- taking into account nat, bitvector and integer conversions (treating all
-- bitvectors as unsigned)
asUnsignedConcreteBvToNat :: Recognizer Term Natural
asUnsignedConcreteBvToNat (asNat -> Just v) = return v
asUnsignedConcreteBvToNat (asBvToNat -> Just (_, bv)) = asUnsignedConcreteBv bv
asUnsignedConcreteBvToNat (asApplyAll -> (asGlobalDef -> Just "Prelude.intToNat",
                                        [i])) = case i of
  (asApplyAll -> (asGlobalDef -> Just "Prelude.natToInt", [v])) ->
    asUnsignedConcreteBvToNat v
  (asApplyAll -> (asGlobalDef -> Just "Prelude.bvToInt", [_, bv])) ->
    asUnsignedConcreteBv bv
  _ -> Nothing
asUnsignedConcreteBvToNat _ = Nothing

asArrayValue :: Recognizer Term (Term, [Term])
asArrayValue (unwrapTermF -> FTermF (ArrayValue tp tms)) =
  return (tp, V.toList tms)
asArrayValue _ = Nothing

asStringLit :: Recognizer Term Text
asStringLit t = do StringLit i <- asFTermF t; return i

asLambda :: Recognizer Term (LocalName, Term, Term)
asLambda (unwrapTermF -> Lambda s ty body) = return (s, ty, body)
asLambda _ = Nothing

asLambdaList :: Term -> ([(LocalName, Term)], Term)
asLambdaList = go []
  where go r (asLambda -> Just (nm,tp,rhs)) = go ((nm,tp):r) rhs
        go r rhs = (reverse r, rhs)

asPi :: Recognizer Term (LocalName, Term, Term)
asPi (unwrapTermF -> Pi nm tp body) = return (nm, tp, body)
asPi _ = Nothing

-- | Decomposes a term into a list of pi bindings, followed by a right
-- term that is not a pi binding.
asPiList :: Term -> ([(LocalName, Term)], Term)
asPiList = go []
  where go r (asPi -> Just (nm,tp,rhs)) = go ((nm,tp):r) rhs
        go r rhs = (reverse r, rhs)

asLocalVar :: Recognizer Term DeBruijnIndex
asLocalVar (unwrapTermF -> LocalVar i) = return i
asLocalVar _ = Nothing

asConstant :: Recognizer Term Name
asConstant (unwrapTermF -> Constant nm) = pure nm
asConstant _ = Nothing

asVariable :: Recognizer Term (ExtCns Term)
asVariable t =
  case unwrapTermF t of
    Variable ec -> pure ec
    _           -> Nothing

asSort :: Recognizer Term Sort
asSort t = do
  ftf <- asFTermF t
  case ftf of
    Sort s _ -> return s
    _      -> Nothing

asSortWithFlags :: Recognizer Term (Sort, SortFlags)
asSortWithFlags t = do
  ftf <- asFTermF t
  case ftf of
    Sort s h -> return (s, h)
    _      -> Nothing



-- | Returns term as a constant Boolean if it is one.
asBool :: Recognizer Term Bool
asBool (isGlobalDef "Prelude.True" -> Just ()) = return True
asBool (isGlobalDef "Prelude.False" -> Just ()) = return False
asBool _ = Nothing

asBoolType :: Recognizer Term ()
asBoolType = isGlobalDef "Prelude.Bool"

asNatType :: Recognizer Term ()
asNatType (asConstant -> Just o)
  | nameInfo o == ModuleIdentifier preludeNatIdent = pure ()
asNatType _ = Nothing

asIntegerType :: Recognizer Term ()
asIntegerType = isGlobalDef "Prelude.Integer"

asIntModType :: Recognizer Term Natural
asIntModType = isGlobalDef "Prelude.IntMod" @> asNat

asVectorType :: Recognizer Term (Term, Term)
asVectorType = fmap toPair . ((isGlobalDef "Prelude.Vec" @> return) <@> return)

isVecType :: Recognizer Term a -> Recognizer Term (Natural :*: a)
isVecType tp = (isGlobalDef "Prelude.Vec" @> asNat) <@> tp

asVecType :: Recognizer Term (Natural :*: Term)
asVecType = isVecType return

asBitvectorType :: Recognizer Term Natural
asBitvectorType = (isGlobalDef "Prelude.Vec" @> asNat) <@ asBoolType

asMux :: Recognizer Term (Term :*: Term :*: Term :*: Term)
asMux = isGlobalDef "Prelude.ite" @> return <@> return <@> return <@> return

asEq :: Recognizer Term (Term, Term, Term)
asEq t =
  do l <- asGlobalApply "Prelude.Eq" t
     case l of
       [a, x, y] -> Just (a, x, y)
       _ -> Nothing

asEqTrue :: Recognizer Term Term
asEqTrue t =
  case (isGlobalDef "Prelude.EqTrue" @> return) t of
    Just x -> Just x
    Nothing ->
      do (a,x,y) <- asEq t
         isGlobalDef "Prelude.Bool" a
         isGlobalDef "Prelude.True" y
         return x

asArrayType :: Recognizer Term (Term :*: Term)
asArrayType = (isGlobalDef "Prelude.Array" @> return) <@> return
