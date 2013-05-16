-- Lightweight calculus for composing patterns as functions.
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Recognizer 
  ( Recognizer
  , firstMatch
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
import Verifier.SAW.TypedAST

type Recognizer t a = t -> Maybe a

isAny :: Recognizer t t
isAny = Just

-- | Tries both recognizers and returns first that succeeds.
firstMatch :: Recognizer t a -> Recognizer t a -> Recognizer t a
firstMatch f _ (f -> Just a) = Just a
firstMatch _ g t = g t

-- | Recognizes the head and tail of a list, and returns head.
(<:) :: Recognizer t a -> Recognizer [t] () -> Recognizer [t] a
(<:) f g ((f -> Just a) : (g -> Just ())) = Just a
(<:) _ _ _ = Nothing

-- | Recognizes empty list
emptyl :: Recognizer [t] ()
emptyl [] = Just ()
emptyl _ = Nothing

-- | Recognizes singleton list
endl :: Recognizer t a -> Recognizer [t] a
endl f = f <: emptyl

asFTermF :: Termlike t => Recognizer t (FlatTermF t)
asFTermF (unwrapTermF -> FTermF ftf) = Just ftf
asFTermF _ = Nothing

data a :*: b = (:*:) a b

(<@>) :: Termlike t => Recognizer t a -> Recognizer t b -> Recognizer t (a :*: b)
(<@>) f g t = do
  (a,b) <- asApp t
  (:*:) <$> f a <*> g b

-- | Recognizes a function application, and returns argument.
(@>) :: Termlike t => Recognizer t () -> Recognizer t b -> Recognizer t b
(@>) f g (asApp -> Just (f -> Just (), y)) = g y
(@>) _ _ _ = Nothing

asApp :: Termlike t => Recognizer t (t, t)
asApp t = do App x y <- asFTermF t; return (x,y)

asApplyAll :: Termlike t => t -> (t, [t])
asApplyAll = go []
  where go xs t =
          case asApp t of
            Nothing -> (t, xs)
            Just (t', x) -> go (x : xs) t'

asCtor :: Termlike t => Recognizer t (Ident, [t])
asCtor t = do CtorApp c l <- asFTermF t; return (c,l)

asDataType :: Termlike t => Recognizer t (Ident, [t])
asDataType t = do DataTypeApp c l <- asFTermF t; return (c,l) 

asGlobalDef :: Termlike t => Recognizer t Ident
asGlobalDef t = do GlobalDef i <- asFTermF t; return i

isGlobalDef :: Termlike t => Ident -> Recognizer t ()
isGlobalDef i (asGlobalDef -> Just o) | i == o = Just ()
isGlobalDef _ _ = Nothing

asNatLit :: Termlike t => Recognizer t Integer
asNatLit t = do NatLit i <- asFTermF t; return i

-- | Returns term as a constant Boolean if it can be evaluated as one.
-- bh: Is this really intended to do *evaluation*? Or is it supposed to work like asNatLit?
asBool :: Termlike t => Recognizer t Bool
asBool (asCtor -> Just ("Prelude.True",  [])) = Just True
asBool (asCtor -> Just ("Prelude.False", [])) = Just False
asBool _ = Nothing

isDataType :: Termlike t => Ident -> Recognizer [t] a -> Recognizer t a
isDataType i p (asDataType -> Just (o,l)) | i == o = p l
isDataType _ _ _ = Nothing

asBoolType :: Termlike t => Recognizer t ()
asBoolType = isDataType "Prelude.Bool" emptyl

asBitvectorType :: Termlike t => Recognizer t Integer
asBitvectorType =
  firstMatch (isGlobalDef "Prelude.bitvector" @> asNatLit) $
    isDataType "Prelude.Vec" 
               (asNatLit <: endl (isDataType "Prelude.Bool" emptyl))

asMux :: Termlike t => Recognizer t (t :*: t :*: t :*: t)
asMux = isGlobalDef "Prelude.ite" @> isAny <@> isAny <@> isAny <@> isAny
