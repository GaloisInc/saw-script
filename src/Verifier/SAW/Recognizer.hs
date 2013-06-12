-- Lightweight calculus for composing patterns as functions.
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Recognizer 
  ( Recognizer
  , (<:), emptyl, endl
  , (:*:)(..)
  , asFTermF

  , asGlobalDef
  , isGlobalDef
  , asApp
  , (<@>), (@>)
  , asApplyAll
  , asTupleValue
  , asTupleSelector
  , asRecordValue
  , asRecordSelector
  , asCtor
  , asDataType
  , isDataType
  , asNatLit
  , asLambda
  , asLocalVar
    -- * Prelude recognizers.
  , asBool
  , asBoolType
  , asBitvectorType
  , asMux
  ) where

import Control.Applicative
import Control.Monad
import Data.Map (Map)
import Verifier.SAW.TypedAST

data a :*: b = (:*:) a b
  deriving (Eq,Ord,Show)

type Recognizer m t a = t -> m a

-- | Tries both recognizers and returns first that succeeds.
(<>) :: Alternative f => Recognizer f t a -> Recognizer f t a -> Recognizer f t a
(<>) f g t = f t <|> g t

-- | Recognizes the head and tail of a list, and returns head.
(<:) :: Monad f
     => Recognizer f t a -> Recognizer f [t] () -> Recognizer f [t] a
(<:) f g (h:r) = do x <- f h; _ <- g r; return x
(<:) _ _ [] = fail "empty-list"

-- | Recognizes empty list
emptyl :: Monad m => Recognizer m [t] ()
emptyl [] = return ()
emptyl _ = fail "non-empty"

-- | Recognizes singleton list
endl :: Monad f => Recognizer f t a -> Recognizer f [t] a
endl f = f <: emptyl

asFTermF :: (Monad f, Termlike t) => Recognizer f t (FlatTermF t)
asFTermF (unwrapTermF -> FTermF ftf) = return ftf
asFTermF _ = fail "not ftermf"

asGlobalDef :: (Monad f, Termlike t) => Recognizer f t Ident
asGlobalDef t = do GlobalDef i <- asFTermF t; return i

isGlobalDef :: (Monad f, Termlike t) => Ident -> Recognizer f t ()
isGlobalDef i t = do
  o <- asGlobalDef t
  if i == o then return () else fail ("not " ++ show i)

asApp :: (Monad f, Termlike t) => Recognizer f t (t, t)
asApp t = do App x y <- asFTermF t; return (x,y)

(<@>) :: (Monad f, Termlike t)
      => Recognizer f t a -> Recognizer f t b -> Recognizer f t (a :*: b)
(<@>) f g t = do
  (a,b) <- asApp t
  liftM2 (:*:) (f a) (g b)

-- | Recognizes a function application, and returns argument.
(@>) :: (Monad f, Termlike t) => Recognizer f t () -> Recognizer f t b -> Recognizer f t b
(@>) f g t = do
  (x, y) <- asApp t
  liftM2 (const id) (f x) (g y)

asApplyAll :: Termlike t => t -> (t, [t])
asApplyAll = go []
  where go xs t =
          case asApp t of
            Nothing -> (t, xs)
            Just (t', x) -> go (x : xs) t'

asTupleValue :: (Monad m, Termlike t) => Recognizer m t [t]
asTupleValue t = do TupleValue ts <- asFTermF t; return ts

asTupleSelector :: (Monad m, Termlike t) => Recognizer m t (t, Int)
asTupleSelector t = do TupleSelector u i <- asFTermF t; return (u,i)

asRecordValue :: (Monad m, Termlike t) => Recognizer m t (Map FieldName t)
asRecordValue t = do RecordValue m <- asFTermF t; return m

asRecordSelector :: (Monad m, Termlike t) => Recognizer m t (t, FieldName)
asRecordSelector t = do RecordSelector u i <- asFTermF t; return (u,i)

asCtor :: (Monad f, Termlike t) => Recognizer f t (Ident, [t])
asCtor t = do CtorApp c l <- asFTermF t; return (c,l)

asDataType :: (Monad f, Termlike t) => Recognizer f t (Ident, [t])
asDataType t = do DataTypeApp c l <- asFTermF t; return (c,l) 

isDataType :: (Monad f, Termlike t) => Ident -> Recognizer f [t] a -> Recognizer f t a
isDataType i p t = do
  (o,l) <- asDataType t
  if i == o then p l else fail "not datatype"

asNatLit :: (Monad f, Termlike t) => Recognizer f t Integer
asNatLit t = do NatLit i <- asFTermF t; return i

asLambda :: (Monad m, Termlike t) => Recognizer m t (String, t, t)
asLambda (unwrapTermF -> Lambda (PVar s 0 _) ty body) = return (s, ty, body)
asLambda _ = fail "not a lambda"

asLocalVar :: (Monad m, Termlike t) => Recognizer m t (DeBruijnIndex, t)
asLocalVar (unwrapTermF -> LocalVar i ty) = return (i, ty)
asLocalVar _ = fail "not a local variable"

-- | Returns term as a constant Boolean if it is one.
asBool :: (Monad f, Termlike t) => Recognizer f t Bool
asBool (asCtor -> Just ("Prelude.True",  [])) = return True
asBool (asCtor -> Just ("Prelude.False", [])) = return False
asBool _ = fail "not bool"

asBoolType :: (Monad f, Termlike t) => Recognizer f t ()
asBoolType = isDataType "Prelude.Bool" emptyl

asBitvectorType :: (Alternative f, Monad f, Termlike t) => Recognizer f t Integer
asBitvectorType =
  (isGlobalDef "Prelude.bitvector" @> asNatLit)
  <> isDataType "Prelude.Vec" 
                (asNatLit <: endl (isDataType "Prelude.Bool" emptyl))

asMux :: (Monad f, Termlike t) => Recognizer f t (t :*: t :*: t :*: t)
asMux = isGlobalDef "Prelude.ite" @> return <@> return <@> return <@> return
