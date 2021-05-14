{- |
Module      : Verifier.SAW.Recognizer
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

module Verifier.SAW.Recognizer
  ( Recognizer
  , (<:>), (<:), emptyl, endl
  , (:*:)(..)
  , asFTermF

  , asGlobalDef
  , isGlobalDef
  , asApp
  , (<@>), (@>), (<@)
  , asApplyAll
  , asPairType
  , asPairValue
  , asPairSelector
  , asTupleType
  , asTupleValue
  , asTupleSelector
  , asRecordType
  , asRecordValue
  , asRecordSelector
  , asCtorParams
  , asCtor
  , asDataType
  , asDataTypeParams
  , asRecursorApp
  , asRecursorType
  , isDataType
  , asNat
  , asBvNat
  , asUnsignedConcreteBv
  , asStringLit
  , asLambda
  , asLambdaList
  , asPi
  , asPiList
  , asLocalVar
  , asConstant
  , asExtCns
  , asSort
    -- * Prelude recognizers.
  , asBool
  , asBoolType
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
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import Numeric.Natural (Natural)

import Verifier.SAW.Term.Functor
import Verifier.SAW.Prelude.Constants

data a :*: b = (:*:) a b
  deriving (Eq,Ord,Show)

instance Field1 (a :*: b) (a' :*: b) a a' where
  _1 k (a :*: b) = indexed k (0 :: Int) a <&> (:*: b)

instance Field2 (a :*: b) (a :*: b') b b' where
  _2 k (a :*: b) = (a :*:) <$> indexed k (1 :: Int) b

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

asModuleIdentifier :: Recognizer (ExtCns e) Ident
asModuleIdentifier (EC _ nmi _) =
  case nmi of
    ModuleIdentifier ident -> Just ident
    _ -> Nothing

asGlobalDef :: Recognizer Term Ident
asGlobalDef t =
  case unwrapTermF t of
    FTermF (Primitive pn) -> Just (primName pn)
    Constant ec _ -> asModuleIdentifier ec
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

-- | Test whether a term is an application of a constructor, and, if so, return
-- the constructor, its parameters, and its arguments
asCtorParams :: Recognizer Term (PrimName Term, [Term], [Term])
asCtorParams t = do CtorApp c ps args <- asFTermF t; return (c,ps,args)

-- | A version of 'asCtorParams' that combines the parameters and normal args
asCtor :: Recognizer Term (PrimName Term, [Term])
asCtor t = do CtorApp c ps args <- asFTermF t; return (c,ps ++ args)

-- | A version of 'asDataType' that returns the parameters separately
asDataTypeParams :: Recognizer Term (PrimName Term, [Term], [Term])
asDataTypeParams t = do DataTypeApp c ps args <- asFTermF t; return (c,ps,args)

-- | A version of 'asDataTypeParams' that combines the params and normal args
asDataType :: Recognizer Term (PrimName Term, [Term])
asDataType t = do DataTypeApp c ps args <- asFTermF t; return (c,ps ++ args)

asRecursorType :: Recognizer Term (PrimName Term, [Term], Term, Term)
asRecursorType t =
  do RecursorType d ps motive motive_ty <- asFTermF t
     return (d,ps,motive,motive_ty)

asRecursorApp :: Recognizer Term (Term, CompiledRecursor Term, [Term], Term)
asRecursorApp t =
  do RecursorApp rec ixs arg <- asFTermF t
     Recursor crec <- asFTermF rec
     return (rec, crec, ixs, arg)

isDataType :: PrimName Term -> Recognizer [Term] a -> Recognizer Term a
isDataType i p t = do
  (o,l) <- asDataType t
  if i == o then p l else Nothing

asNat :: Recognizer Term Natural
asNat (unwrapTermF -> FTermF (NatLit i)) = return i
asNat (asCtor -> Just (c, []))
  | primName c == preludeZeroIdent = return 0
asNat (asCtor -> Just (c, [asNat -> Just i]))
  | primName c == preludeSuccIdent = return (i+1)
asNat _ = Nothing

asBvNat :: Recognizer Term (Natural :*: Natural)
asBvNat = (isGlobalDef "Prelude.bvNat" @> asNat) <@> asNat

asUnsignedConcreteBv :: Recognizer Term Natural
asUnsignedConcreteBv term = do
  (n :*: v) <- asBvNat term
  return $ mod v (2 ^ n)

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

asConstant :: Recognizer Term (ExtCns Term, Term)
asConstant (unwrapTermF -> Constant ec t) = return (ec, t)
asConstant _ = Nothing

asExtCns :: Recognizer Term (ExtCns Term)
asExtCns t = do
  ftf <- asFTermF t
  case ftf of
    ExtCns ec -> return ec
    _         -> Nothing

asSort :: Recognizer Term Sort
asSort t = do
  ftf <- asFTermF t
  case ftf of
    Sort s -> return s
    _      -> Nothing

-- | Returns term as a constant Boolean if it is one.
asBool :: Recognizer Term Bool
asBool (isGlobalDef "Prelude.True" -> Just ()) = return True
asBool (isGlobalDef "Prelude.False" -> Just ()) = return False
asBool _ = Nothing

asBoolType :: Recognizer Term ()
asBoolType = isGlobalDef "Prelude.Bool"

asIntegerType :: Recognizer Term ()
asIntegerType = isGlobalDef "Prelude.Integer"

asIntModType :: Recognizer Term Natural
asIntModType = isGlobalDef "Prelude.IntMod" @> asNat

asVectorType :: Recognizer Term (Term, Term)
asVectorType = helper ((isGlobalDef "Prelude.Vec" @> return) <@> return) where
  helper r t =
    do (n :*: a) <- r t
       return (n, a)

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
  do (o, l) <- asDataType t
     case l of
       [a, x, y] | "Prelude.Eq" == primName o -> return (a, x, y)
       _ -> Nothing

asEqTrue :: Recognizer Term Term
asEqTrue = isGlobalDef "Prelude.EqTrue" @> return

asArrayType :: Recognizer Term (Term :*: Term)
asArrayType = (isGlobalDef "Prelude.Array" @> return) <@> return
