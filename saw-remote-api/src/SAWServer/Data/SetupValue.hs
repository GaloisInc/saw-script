{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Data.SetupValue (CrucibleSetupVal) where

import Control.Applicative
import Data.Aeson (FromJSON(..), withObject, withText, (.:))

import SAWServer

data SetupValTag
  = TagServerValue
  | TagNullValue
  | TagCryptol
  | TagArrayValue
  | TagFieldLValue
  | TagElemLValue
  | TagGlobalInit
  | TagGlobalLValue

instance FromJSON SetupValTag where
  parseJSON =
    withText "tag for setup value" $
    \case
      "saved" -> pure TagServerValue
      "null value" -> pure TagNullValue
      "Cryptol" -> pure TagCryptol
      "array value" -> pure TagArrayValue
      "field lvalue" -> pure TagFieldLValue
      "element lvalue" -> pure TagElemLValue
      "global initializer" -> pure TagGlobalInit
      "global lvalue" -> pure TagGlobalLValue
      _ -> empty

instance FromJSON cryptolExpr => FromJSON (CrucibleSetupVal cryptolExpr) where
  parseJSON v = fromObject v
    where
      fromObject = withObject "saved value or Cryptol expression" $ \o ->
        o .: "setup value" >>=
        \case
          TagServerValue -> ServerValue <$> o .: "name"
          TagNullValue -> pure NullValue
          TagCryptol -> CryptolExpr <$> o .: "expression"
          TagArrayValue -> ArrayValue <$> o .: "elements"
          TagFieldLValue -> FieldLValue <$> o .: "base" <*> o .: "field"
          TagElemLValue -> ElementLValue <$> o .: "base" <*> o .: "index"
          TagGlobalInit -> GlobalInitializer <$> o .: "name"
          TagGlobalLValue -> GlobalLValue <$> o .: "name"
