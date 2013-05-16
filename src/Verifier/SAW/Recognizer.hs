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
  , isDataType
  , asBoolType
  , asBitvectorType
  , asMux
  ) where

import Control.Applicative
import Verifier.SAW.TypedAST
import Verifier.SAW.SharedTerm

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

data a :*: b = (:*:) a b

(<@>) :: Termlike t => Recognizer t a -> Recognizer t b -> Recognizer t (a :*: b)
(<@>) f g t = do
  (a,b) <- asApp t
  (:*:) <$> f a <*> g b

-- | Recognizes a function application, and returns argument.
(@>) :: Termlike t => Recognizer t () -> Recognizer t b -> Recognizer t b
(@>) f g (asApp -> Just (f -> Just (), y)) = g y
(@>) _ _ _ = Nothing

asApp :: Termlike t => Recognizer t (t,t)
asApp t = do App x y <- asFTermF t; return (x,y)

asApplyAll :: Termlike t => t -> (t, [t])
asApplyAll = go []
  where go xs t =
          case asApp t of
            Nothing -> (t, xs)
            Just (t', x) -> go (x : xs) t'

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