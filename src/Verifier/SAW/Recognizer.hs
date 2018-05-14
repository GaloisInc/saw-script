-- Lightweight calculus for composing patterns as functions.
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Recognizer
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Recognizer
  ( Recognizer
  , (<:>), (<:), emptyl, endl
  , (:*:)(..)
  , asFTermF

  , asGlobalDef
  , isGlobalDef
  , asApp
  , (<@>), (@>)
  , asApplyAll
  , asPairType
  , asPairValue
  , asPairSelector
  , asTupleType
  , asTupleValue
  , asTupleSelector
  , asOldTupleType
  , asOldTupleValue
  , asOldTupleSelector
  , asFieldType
  , asFieldValue
  , asRecordType
  , asRecordValue
  , asRecordSelector
  , asOldRecordType
  , asOldRecordValue
  , asOldRecordSelector
  , asCtorParams
  , asCtor
  , asCtorOrNat
  , asDataType
  , asDataTypeParams
  , asRecursorApp
  , isDataType
  , asNatLit
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
  , Nat
  , asBitvectorType
  , asVectorType
  , asVecType
  , isVecType
  , asMux
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Verifier.SAW.Prim
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty
import Verifier.SAW.Prelude.Constants
import Text.Read (readMaybe)

data a :*: b = (:*:) a b
  deriving (Eq,Ord,Show)

instance Field1 (a :*: b) (a' :*: b) a a' where
  _1 k (a :*: b) = indexed k (0 :: Int) a <&> (:*: b)

instance Field2 (a :*: b) (a :*: b') b b' where
  _2 k (a :*: b) = (a :*:) <$> indexed k (1 :: Int) b

type Recognizer m t a = t -> m a

-- | Tries both recognizers.
(<>) :: Alternative f => Recognizer f t a -> Recognizer f t a -> Recognizer f t a
(<>) f g t = f t <|> g t

-- | Recognizes the head and tail of a list, and returns head.
(<:) :: Monad f
     => Recognizer f t a -> Recognizer f [t] () -> Recognizer f [t] a
(<:) f g (h:r) = do x <- f h; _ <- g r; return x
(<:) _ _ [] = fail "empty-list"

-- | Recognizes the head and tail of a list, and returns head.
(<:>) :: Monad f
     => Recognizer f t a -> Recognizer f [t] b -> Recognizer f [t] (a :*: b)
(<:>) f g (h:r) = do x <- f h; y <- g r; return (x :*: y)
(<:>) _ _ [] = fail "empty-list"

-- | Recognizes empty list
emptyl :: Monad m => Recognizer m [t] ()
emptyl [] = return ()
emptyl _ = fail "non-empty"

-- | Recognizes singleton list
endl :: Monad f => Recognizer f t a -> Recognizer f [t] a
endl f = f <: emptyl

asFTermF :: (Monad f) => Recognizer f Term (FlatTermF Term)
asFTermF (unwrapTermF -> FTermF ftf) = return ftf
asFTermF _ = fail "not ftermf"

asGlobalDef :: (Monad f) => Recognizer f Term Ident
asGlobalDef t = do GlobalDef i <- asFTermF t; return i

isGlobalDef :: (Monad f) => Ident -> Recognizer f Term ()
isGlobalDef i t = do
  o <- asGlobalDef t
  if i == o then return () else fail ("not " ++ show i)

asApp :: (Monad f) => Recognizer f Term (Term, Term)
asApp (unwrapTermF -> App x y) = return (x, y)
asApp _ = fail "not app"

(<@>) :: (Monad f)
      => Recognizer f Term a -> Recognizer f Term b -> Recognizer f Term (a :*: b)
(<@>) f g t = do
  (a,b) <- asApp t
  liftM2 (:*:) (f a) (g b)

-- | Recognizes a function application, and returns argument.
(@>) :: (Monad f) => Recognizer f Term () -> Recognizer f Term b -> Recognizer f Term b
(@>) f g t = do
  (x, y) <- asApp t
  liftM2 (const id) (f x) (g y)

-- | Recognizes a function application, and returns the function
(<@) :: (Monad f) => Recognizer f Term a -> Recognizer f Term () -> Recognizer f Term a
(<@) f g t = do
  (x, y) <- asApp t
  liftM2 const (f x) (g y)

asApplyAll :: Term -> (Term, [Term])
asApplyAll = go []
  where go xs t =
          case asApp t of
            Nothing -> (t, xs)
            Just (t', x) -> go (x : xs) t'

asPairType :: (Monad m) => Recognizer m Term (Term, Term)
asPairType t = do
  ftf <- asFTermF t
  case ftf of
    PairType x y -> return (x, y)
    _            -> fail "asPairType"

asPairValue :: (Monad m) => Recognizer m Term (Term, Term)
asPairValue t = do
  ftf <- asFTermF t
  case ftf of
    PairValue x y -> return (x, y)
    _             -> fail "asPairValue"

asPairSelector :: (Monad m) => Recognizer m Term (Term, Bool)
asPairSelector t = do
  ftf <- asFTermF t
  case ftf of
    PairLeft x  -> return (x, False)
    PairRight x -> return (x, True)
    _           -> fail "asPairSelector"

asTupleType :: (Monad m) => Recognizer m Term [Term]
asTupleType t = do
  ftf <- asFTermF t
  case ftf of
    RecordType (recordAListAsTuple -> Just ts) -> return ts
    _                                          -> fail "asTupleType"

asTupleValue :: (Monad m) => Recognizer m Term [Term]
asTupleValue t = do
  ftf <- asFTermF t
  case ftf of
    RecordValue (recordAListAsTuple -> Just ts) -> return ts
    _                                           -> fail "asTupleValue"

asTupleSelector :: (Monad m) => Recognizer m Term (Term, Int)
asTupleSelector t = do
  ftf <- asFTermF t
  case ftf of
    RecordProj u (readMaybe -> Just i) -> return (u, i)
    _                                  -> fail "asTupleSelector"

asOldTupleType :: (Monad m) => Recognizer m Term [Term]
asOldTupleType t = do
  ftf <- asFTermF t
  case ftf of
    UnitType     -> return []
    PairType x y -> do xs <- asTupleType y; return (x : xs)
    _            -> fail "asTupleType"

asOldTupleValue :: (Monad m) => Recognizer m Term [Term]
asOldTupleValue t = do
  ftf <- asFTermF t
  case ftf of
    UnitValue     -> return []
    PairValue x y -> do xs <- asTupleValue y; return (x : xs)
    _             -> fail "asTupleValue"

asOldTupleSelector :: (Monad m) => Recognizer m Term (Term, Int)
asOldTupleSelector t = do
  ftf <- asFTermF t
  case ftf of
    PairLeft x  -> return (x, 1)
    PairRight y -> do (x, i) <- asTupleSelector y; return (x, i+1)
    _           -> fail "asTupleSelector"

asFieldType :: (Monad m) => Recognizer m Term (Term, Term, Term)
asFieldType t = do
  ftf <- asFTermF t
  case ftf of
    FieldType x y z -> return (x, y, z)
    _               -> fail "asFieldType"

asFieldValue :: (Monad m) => Recognizer m Term (Term, Term, Term)
asFieldValue t = do
  ftf <- asFTermF t
  case ftf of
    FieldValue x y z -> return (x, y, z)
    _                -> fail "asFieldValue"

asRecordType :: (Monad m) => Recognizer m Term (Map FieldName Term)
asRecordType t = do
  ftf <- asFTermF t
  case ftf of
    RecordType elems -> return $ Map.fromList elems
    _                -> fail $ "asRecordType: " ++ showTerm t

-- | Old version of 'asRecordType', that works on old-style record types
asOldRecordType :: (Monad m) => Recognizer m Term (Map FieldName Term)
asOldRecordType t = do
  ftf <- asFTermF t
  case ftf of
    EmptyType       -> return Map.empty
    FieldType f x y -> do m <- asRecordType y
                          s <- asStringLit f
                          return (Map.insert s x m)
    _               -> fail $ "asRecordType: " ++ showTerm t


asRecordValue :: (Monad m) => Recognizer m Term (Map FieldName Term)
asRecordValue t = do
  ftf <- asFTermF t
  case ftf of
    RecordValue elems -> return $ Map.fromList elems
    _                 -> fail $ "asRecordValue: " ++ showTerm t

-- | Old version of 'asRecordValue', that uses 'EmptyValue' and 'FieldValue'
asOldRecordValue :: (Monad m) => Recognizer m Term (Map FieldName Term)
asOldRecordValue t = do
  ftf <- asFTermF t
  case ftf of
    EmptyValue       -> return Map.empty
    FieldValue f x y -> do m <- asRecordValue y
                           s <- asStringLit f
                           return (Map.insert s x m)
    _                -> fail $ "asRecordValue: " ++ showTerm t

asRecordSelector :: (Monad m) => Recognizer m Term (Term, FieldName)
asRecordSelector t = do
  RecordProj u s <- asFTermF t
  return (u, s)

asOldRecordSelector :: (Monad m) => Recognizer m Term (Term, FieldName)
asOldRecordSelector t = do
  RecordSelector u i <- asFTermF t
  s <- asStringLit i
  return (u, s)

-- | Test whether a term is an application of a constructor, and, if so, return
-- the constructor, its parameters, and its arguments
asCtorParams :: (Monad f) => Recognizer f Term (Ident, [Term], [Term])
asCtorParams t = do CtorApp c ps args <- asFTermF t; return (c,ps,args)

-- | Just like 'asCtorParams', but treat natural number literals as constructor
-- applications, i.e., @0@ becomes the constructor @Zero@, and any non-zero
-- literal @k@ becomes @Succ (k-1)@
asCtorOrNat :: (Alternative f, Monad f) =>
               Recognizer f Term (Ident, [Term], [Term])
asCtorOrNat = asCtorParams <> (asNatLit >=> helper . toInteger) where
  helper 0 = return (preludeZeroIdent, [], [])
  helper k =
    if k > 0 then
      return (preludeSuccIdent, [], [Unshared (FTermF (NatLit $ k-1))])
    else error "asCtorOrNat: negative natural number literal!"


-- | A version of 'asCtorParams' that combines the parameters and normal args
asCtor :: (Monad f) => Recognizer f Term (Ident, [Term])
asCtor t = do CtorApp c ps args <- asFTermF t; return (c,ps ++ args)

-- | A version of 'asDataType' that returns the parameters separately
asDataTypeParams :: (Monad f) => Recognizer f Term (Ident, [Term], [Term])
asDataTypeParams t = do DataTypeApp c ps args <- asFTermF t; return (c,ps,args)

-- | A version of 'asDataTypeParams' that combines the params and normal args
asDataType :: (Monad f) => Recognizer f Term (Ident, [Term])
asDataType t = do DataTypeApp c ps args <- asFTermF t; return (c,ps ++ args)

asRecursorApp :: Monad f => Recognizer f Term (Ident,[Term],Term,
                                               [(Ident,Term)],[Term],Term)
asRecursorApp t =
  do RecursorApp d params p_ret cs_fs ixs arg <- asFTermF t;
     return (d, params, p_ret, cs_fs, ixs, arg)

isDataType :: (Monad f) => Ident -> Recognizer f [Term] a -> Recognizer f Term a
isDataType i p t = do
  (o,l) <- asDataType t
  if i == o then p l else fail "not datatype"

asNatLit :: (Monad f) => Recognizer f Term Nat
asNatLit t = do NatLit i <- asFTermF t; return (fromInteger i)

asStringLit :: (Monad f) => Recognizer f Term String
asStringLit t = do StringLit i <- asFTermF t; return i

asLambda :: (Monad m) => Recognizer m Term (String, Term, Term)
asLambda (unwrapTermF -> Lambda s ty body) = return (s, ty, body)
asLambda _ = fail "not a lambda"

asLambdaList :: Term -> ([(String, Term)], Term)
asLambdaList = go []
  where go r (asLambda -> Just (nm,tp,rhs)) = go ((nm,tp):r) rhs
        go r rhs = (reverse r, rhs)

asPi :: (Monad m) => Recognizer m Term (String, Term, Term)
asPi (unwrapTermF -> Pi nm tp body) = return (nm, tp, body)
asPi _ = fail "not a Pi term"

-- | Decomposes a term into a list of pi bindings, followed by a right
-- term that is not a pi binding.
asPiList :: Term -> ([(String, Term)], Term)
asPiList = go []
  where go r (asPi -> Just (nm,tp,rhs)) = go ((nm,tp):r) rhs
        go r rhs = (reverse r, rhs)

asLocalVar :: (Monad m) => Recognizer m Term DeBruijnIndex
asLocalVar (unwrapTermF -> LocalVar i) = return i
asLocalVar _ = fail "not a local variable"

asConstant :: (Monad m) => Recognizer m Term (String, Term, Term)
asConstant (unwrapTermF -> Constant s x t) = return (s, x, t)
asConstant _ = fail "asConstant: not a defined constant"

asExtCns :: (Monad m) => Recognizer m Term (ExtCns Term)
asExtCns t = do
  ftf <- asFTermF t
  case ftf of
    ExtCns ec -> return ec
    _         -> fail "asExtCns"

asSort :: (Monad m) => Recognizer m Term Sort
asSort t = do
  ftf <- asFTermF t
  case ftf of
    Sort s -> return s
    _      -> fail $ "asSort: " ++ showTerm t

-- | Returns term as a constant Boolean if it is one.
asBool :: (Monad f) => Recognizer f Term Bool
asBool (asCtor -> Just ("Prelude.True",  [])) = return True
asBool (asCtor -> Just ("Prelude.False", [])) = return False
asBool _ = fail "not bool"

asBoolType :: (Monad f) => Recognizer f Term ()
asBoolType = isDataType "Prelude.Bool" emptyl

asIntegerType :: (Monad f) => Recognizer f Term ()
asIntegerType = isGlobalDef "Prelude.Integer"

asVectorType :: (Monad f) => Recognizer f Term (Term, Term)
asVectorType = helper ((isGlobalDef "Prelude.Vec" @> return) <@> return) where
  helper r t =
    do (n :*: a) <- r t
       return (n, a)

isVecType :: (Monad f)
          => Recognizer f Term a -> Recognizer f Term (Nat :*: a)
isVecType tp = (isGlobalDef "Prelude.Vec" @> asNatLit) <@> tp

asVecType :: (Monad f) => Recognizer f Term (Nat :*: Term)
asVecType = isVecType return

asBitvectorType :: (Alternative f, Monad f) => Recognizer f Term Nat
asBitvectorType =
  (isGlobalDef "Prelude.bitvector" @> asNatLit)
  <> ((isGlobalDef "Prelude.Vec" @> asNatLit)
      <@ isDataType "Prelude.Bool" emptyl)

asMux :: (Monad f) => Recognizer f Term (Term :*: Term :*: Term :*: Term)
asMux = isGlobalDef "Prelude.ite" @> return <@> return <@> return <@> return
