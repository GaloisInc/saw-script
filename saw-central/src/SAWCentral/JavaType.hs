{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWCentral.JavaType
Description : Representation of Java types for use in SAW
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

This module contains the `JavaType` type that we use to represent Java
types in Crucible specifications and in SAWScript.
-}

module SAWCentral.JavaType (
    JavaType(..),
    prettyJavaType
  ) where

import Data.Text (Text)
--import qualified Data.Text as Text

import qualified Prettyprinter as PP

import qualified SAWSupport.Pretty as PPS


-- | Adapted from type 'JavaType' in Java.sawcore.
data JavaType
  = JavaBoolean
  | JavaByte
  | JavaChar
  | JavaShort
  | JavaInt
  | JavaLong
  | JavaFloat
  | JavaDouble
  | JavaArray Int JavaType
  | JavaClass Text
  deriving (Eq, Show)

prettyJavaType :: PPS.Opts -> JavaType -> PPS.Doc
prettyJavaType ppopts ty0 = case ty0 of
    JavaBoolean -> "bool"
    JavaByte -> "byte"
    JavaChar -> "char"
    JavaShort -> "short"
    JavaInt -> "int"
    JavaLong -> "long"
    JavaFloat -> "float"
    JavaDouble -> "double"
    JavaArray sz ty1 -> prettyJavaType ppopts ty1 <> "[" <> PPS.prettyInt ppopts sz <> "]"
    JavaClass name -> PP.pretty name
