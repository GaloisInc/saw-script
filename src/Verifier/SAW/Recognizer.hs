-- Lightweight calculus for composing patterns as functions.
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Recognizer 
  ( Recognizer
  , (<:), emptyl, endl
  , (:*:)(..)
  , (<@>), (@>)
  , asApp
  , asApplyAll
  , asFTermF
  , asCtor
  , asDataType
  , isDataType
  , asGlobalDef
  , isGlobalDef
  , asNatLit
  , asBool
  , asBoolType
  , asBitvectorType
  , asMux
  ) where

import Control.Applicative
import Control.Monad
import Verifier.SAW.TypedAST

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

data a :*: b = (:*:) a b

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

asApp :: (Monad f, Termlike t) => Recognizer f t (t, t)
asApp t = do App x y <- asFTermF t; return (x,y)

asApplyAll :: Termlike t => t -> (t, [t])
asApplyAll = go []
  where go xs t =
          case asApp t of
            Nothing -> (t, xs)
            Just (t', x) -> go (x : xs) t'

asCtor :: (Monad f, Termlike t) => Recognizer f t (Ident, [t])
asCtor t = do CtorApp c l <- asFTermF t; return (c,l)

asDataType :: (Monad f, Termlike t) => Recognizer f t (Ident, [t])
asDataType t = do DataTypeApp c l <- asFTermF t; return (c,l) 

asGlobalDef :: (Monad f, Termlike t) => Recognizer f t Ident
asGlobalDef t = do GlobalDef i <- asFTermF t; return i

isGlobalDef :: (Monad f, Termlike t) => Ident -> Recognizer f t ()
isGlobalDef i t = do
  o <- asGlobalDef t
  if i == o then return () else fail ("not " ++ show i)

asNatLit :: (Monad f, Termlike t) => Recognizer f t Integer
asNatLit t = do NatLit i <- asFTermF t; return i

-- | Returns term as a constant Boolean if it can be evaluated as one.
-- bh: Is this really intended to do *evaluation*? Or is it supposed to work like asNatLit?
asBool :: (Monad f, Termlike t) => Recognizer f t Bool
asBool (asCtor -> Just ("Prelude.True",  [])) = return True
asBool (asCtor -> Just ("Prelude.False", [])) = return False
asBool _ = fail "not bool"

isDataType :: (Monad f, Termlike t) => Ident -> Recognizer f [t] a -> Recognizer f t a
isDataType i p t = do
  (o,l) <- asDataType t
  if i == o then p l else fail "not datatype"

asBoolType :: (Monad f, Termlike t) => Recognizer f t ()
asBoolType = isDataType "Prelude.Bool" emptyl

asBitvectorType :: (Alternative f, Monad f, Termlike t) => Recognizer f t Integer
asBitvectorType =
  (isGlobalDef "Prelude.bitvector" @> asNatLit)
  <> isDataType "Prelude.Vec" 
                (asNatLit <: endl (isDataType "Prelude.Bool" emptyl))

asMux :: (Monad f, Termlike t) => Recognizer f t (t :*: t :*: t :*: t)
asMux = isGlobalDef "Prelude.ite" @> return <@> return <@> return <@> return