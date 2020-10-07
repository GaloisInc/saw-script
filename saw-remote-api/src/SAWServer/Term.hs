{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Term (JSONModuleName(..)) where

import Control.Applicative
import Data.Aeson (FromJSON(..), ToJSON(..))
import Data.Aeson as JSON
import qualified Data.Text as T
import qualified Data.Vector as V

import Verifier.SAW.Term.Functor

newtype JSONModuleName = JSONModuleName ModuleName

instance FromJSON JSONModuleName where
  parseJSON val = literal val <|> structured val
    where
      literal =
        withText "module name as string" $
        pure . JSONModuleName . mkModuleName . map T.unpack . T.splitOn "."
      structured =
        withArray "module name as list of parts" $ \v ->
        do parts <- traverse parseJSON (V.toList v)
           pure $ JSONModuleName $ mkModuleName $ map T.unpack parts

instance ToJSON JSONModuleName where
  toJSON (JSONModuleName n) = toJSON (show n)
