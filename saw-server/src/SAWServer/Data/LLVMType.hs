{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWServer.Data.LLVMType (JSONLLVMType, llvmType) where

import Control.Applicative
import qualified Data.Aeson as JSON
import Data.Aeson (withObject, withText, (.:))
import qualified Data.Text as T


import Text.LLVM.AST (FloatType(..), Type'(..), Type, Ident(..), PrimType(..))

newtype JSONLLVMIdent = JSONLLVMIdent { getIdent :: Ident }

instance JSON.FromJSON JSONLLVMIdent where
   parseJSON =
     withText "LLVM identifier" $ pure . JSONLLVMIdent . Ident . T.unpack

newtype JSONLLVMType = JSONLLVMType { getLLVMType :: Type' JSONLLVMIdent }


data LLVMTypeTag
  = TagPrimType
  | TagAlias
  | TagArray
  | TagFunTy
  | TagPtrTo
  | TagStruct
  | TagPackedStruct
  | TagVector
  | TagOpaque

instance JSON.FromJSON LLVMTypeTag where
  parseJSON =
    withText "LLVM type tag" $
    \case
      "primitive type" -> pure TagPrimType
      "type alias" -> pure TagAlias
      "array"-> pure TagArray
      "function" -> pure TagFunTy
      "pointer" -> pure TagPtrTo
      "struct" -> pure TagStruct
      "packed struct" -> pure TagPackedStruct
      "vector" -> pure TagVector
      "opaque" -> pure TagOpaque
      _ -> empty

data PrimTypeTag
  = TagLabel
  | TagVoid
  | TagInteger
  | TagFloatType
  | TagX86mmx
  | TagMetadata

instance JSON.FromJSON PrimTypeTag where
  parseJSON =
    withText "LLVM primitive type tag" $
    \case
      "label" -> pure TagLabel
      "void" -> pure TagVoid
      "integer" -> pure TagInteger
      "float" -> pure TagFloatType
      "X86mmx" -> pure TagX86mmx
      "metadata" -> pure TagMetadata
      _ -> empty

newtype JSONFloatType = JSONFloatType { getFloatType :: FloatType }

instance JSON.FromJSON JSONFloatType where
  parseJSON =
    withText "LLVM float type" $ \t -> fmap JSONFloatType $
    case t of
      "half" -> pure Half
      "float" -> pure Float
      "double" -> pure Double
      "fp128" -> pure Fp128
      "x86_fp80" -> pure X86_fp80
      "PPC_fp128" -> pure PPC_fp128
      _ -> empty


instance JSON.FromJSON JSONLLVMType where
  parseJSON =
    primType

    where
      primType =
        withObject "LLVM type" $ \o -> fmap JSONLLVMType $
        o .: "type" >>=
        \case
          TagPrimType ->
            fmap PrimType $
            o .: "primitive" >>=
            \case
              TagLabel -> pure Label
              TagVoid -> pure Void
              TagInteger -> Integer <$> o .: "size"
              TagFloatType ->
                FloatType . getFloatType <$> o .: "float type"
              TagX86mmx -> pure X86mmx
              TagMetadata -> pure Metadata
          TagAlias -> Alias <$> o .: "alias of"
          TagArray -> Array <$> o .: "size" <*> (getLLVMType <$> o .: "element type")
          TagFunTy -> FunTy <$> (getLLVMType <$> o .: "return type") <*> (fmap getLLVMType <$> o .: "argument types") <*> o .: "varargs"
          TagPtrTo -> PtrTo <$> (getLLVMType <$> o .: "to type")
          TagStruct -> Struct <$> (fmap getLLVMType <$> o .: "fields")
          TagPackedStruct -> PackedStruct <$> (fmap getLLVMType <$> o .: "fields")
          TagVector -> Vector <$> o .: "size" <*> (getLLVMType <$> o .: "element type")
          TagOpaque -> pure Opaque

llvmType :: JSONLLVMType -> Type
llvmType = fmap getIdent . getLLVMType
