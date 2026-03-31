{-# LANGUAGE TemplateHaskell #-}

module Language.Isabelle.Template
  ( Template
  , Applied
  , name
  , apply
  , loadAll
  ) where

import           System.FilePath ((</>), stripExtension, takeFileName)

import           Control.Monad (forM)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Encoding as BS
import qualified Data.FileEmbed as FE
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (catMaybes)
import qualified Data.Text as T

import           Text.Regex (subRegex, mkRegex)

data Template = Template { raw_content :: String, name :: String }
  deriving (Eq, Ord, Show)

newtype Applied = Applied String
  deriving (Eq, Ord)

instance Show Applied where
  show (Applied s) = s

embeddedTemplates :: [(FilePath, BS.ByteString)]
embeddedTemplates = $(FE.embedDir ("saw-core-isabelle" </> "isabelle" </> "templates"))


loadAll :: IO (Map String Template)
loadAll = do
  loaded <- forM embeddedTemplates $ \(file, bs) -> 
    case stripExtension "thy_template" (takeFileName file) of
      Just nm -> do
        let str = T.unpack (BS.decode BS.localeEncoding bs)
        return $ Just (nm, Template str nm)
      Nothing -> return Nothing
  return $ Map.fromList $ catMaybes loaded

apply :: Template -> [String] -> Applied
apply t args = Applied $ foldr go (raw_content t) (zip [1..] args)
  where
    go :: (Int, String) -> String -> String
    go (idx, arg) s = subRegex (mkRegex ("\\$" ++ show idx)) s arg
