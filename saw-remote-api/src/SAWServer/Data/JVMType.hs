{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWServer.Data.JVMType () where

import Control.Applicative
import qualified Data.Aeson as JSON
import Data.Aeson (withObject, withText, (.:))

import SAWCentral.JavaExpr

data JVMTypeTag
  = TagPrimType
  | TagArrayType
  | TagClassType

instance JSON.FromJSON JVMTypeTag where
  parseJSON =
    withText "JVM type tag" $
    \case
      "primitive type" -> pure TagPrimType
      "array type" -> pure TagArrayType
      "class type" -> pure TagClassType
      _ -> empty

data PrimTypeTag
  = TagBoolean
  | TagByte
  | TagChar
  | TagDouble
  | TagFloat
  | TagInt
  | TagLong
  | TagShort

instance JSON.FromJSON PrimTypeTag where
  parseJSON =
    withText "JVM primitive type tag" $
    \case
      "boolean" -> pure TagBoolean
      "byte" -> pure TagByte
      "char" -> pure TagChar
      "double" -> pure TagDouble
      "float" -> pure TagFloat
      "int" -> pure TagInt
      "long" -> pure TagLong
      "short" -> pure TagShort
      _ -> empty

instance JSON.FromJSON JavaType where
  parseJSON =
    primType

    where
      primType =
        withObject "JVM type" $ \o ->
        o .: "type" >>=
        \case
          TagPrimType ->
            o .: "primitive" >>=
            \case
              TagBoolean -> pure JavaBoolean
              TagByte -> pure JavaByte
              TagChar -> pure JavaChar
              TagDouble -> pure JavaDouble
              TagFloat -> pure JavaFloat
              TagInt -> pure JavaInt
              TagLong -> pure JavaLong
              TagShort -> pure JavaShort
          TagArrayType -> JavaArray <$> o .: "size" <*> o .: "element type"
          TagClassType -> JavaClass <$> o .: "class name"
