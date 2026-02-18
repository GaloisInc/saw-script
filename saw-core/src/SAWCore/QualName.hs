{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveLift #-}

{- |
Module      : SAWCore.QualName
Copyright   : Galois, Inc. 2012-2026
License     : BSD3
Maintainer  : dmatichuk@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Qualified names with namespaces,paths and subpaths.
-}

module SAWCore.QualName
  ( Namespace(..)
  , readNamespace
  , QualName(..)
  , fullPath
  , fullPathNE
  , fromPath
  , fromNameIndex
  , qualify
  , split
  , ppQualName
  , aliases
  ) where

import Data.Char (isAlpha, isAlphaNum, isPrint, ord)
import           Data.Hashable
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text

import qualified Data.List.NonEmpty as NE

import qualified Language.Haskell.TH.Syntax as TH


import qualified Prettyprinter as PP
import Text.Printf (printf)

data Namespace =
  NamespaceCore | NamespaceCryptol | NamespaceFresh | NamespaceYosys | NamespaceLLVM
  deriving (Eq, Ord, Enum, Bounded, TH.Lift)

instance Hashable Namespace where
  hashWithSalt s ns = hashWithSalt s (fromEnum ns)

renderNamespace :: Namespace -> Text
renderNamespace = \case
  NamespaceCore -> "core"
  NamespaceCryptol -> "cryptol"
  NamespaceFresh -> "fresh"
  NamespaceYosys -> "yosys"
  NamespaceLLVM -> "llvm"

instance Show Namespace where
  show ns = Text.unpack $ renderNamespace ns

namespaceMap :: Map Text Namespace
namespaceMap = Map.fromList $ map (\ns -> (renderNamespace ns, ns)) [minBound..maxBound]

readNamespace :: Text -> Maybe Namespace
readNamespace txt = Map.lookup txt namespaceMap

-- | A name with optional additional qualification
data QualName = QualName
  { path :: [Text]
  , subPath :: [Text]
  , baseName :: Text
  , index :: Maybe Int
  , namespace :: Maybe Namespace
  }
  deriving (Eq, Ord, TH.Lift)

fullPath :: QualName -> [Text]
fullPath qn = path qn ++ subPath qn ++ [baseName qn]

fullPathNE :: QualName -> NE.NonEmpty Text
fullPathNE qn = NE.fromList (fullPath qn)

instance Hashable QualName where
  hashWithSalt s (QualName a b c d e) = s
    `hashWithSalt` a
    `hashWithSalt` b
    `hashWithSalt` c
    `hashWithSalt` d
    `hashWithSalt` e

fromPath :: Namespace -> NE.NonEmpty Text -> QualName
fromPath ns ps = QualName (NE.init ps) [] (NE.last ps) Nothing (Just ns)

fromNameIndex :: Namespace -> Text -> Int -> QualName
fromNameIndex ns nm i = QualName [] [] nm (Just i) (Just ns)

-- | Append a base name to a given 'QualName', pushing the existing
--   base name into the path (or subpath, if it is nonempty).
qualify :: QualName -> Text -> QualName
qualify qn txt = do
  let prevBaseName = baseName qn
  case subPath qn of
    [] -> qn { path = path qn ++ [prevBaseName], baseName = txt }
    sps -> qn { subPath = sps ++ [prevBaseName], baseName = txt }

-- | Split a qualified name into a qualifier and base name.
split :: QualName -> Maybe (QualName, Text)
split qn = case subPath qn of
  [] -> case path qn of
    (p:ps) ->
      Just $ (qn { path = ps, baseName = p }, baseName qn)
    _ -> Nothing
  (p:sps) ->
    Just $ (qn { subPath = sps, baseName = p }, baseName qn)

-- | True if the given path element may be printed directly. If not, it
-- must be prefixed with '!?', quoted and escaped.
validPathElem :: Text -> Bool
validPathElem txt = case Text.uncons txt of
  Just (c, txt') ->
    (isAlpha c || c == '_') &&
    Text.all (\c_ -> isAlphaNum c_ || c_ == '\'' || c_ == '_') txt'
  Nothing -> False


escapeInnerString :: Text -> Text
escapeInnerString = Text.concatMap go
  where
    go c = case c of
      '"' -> "\\\""
      '\\' -> "\\\\"
      '\a' -> "\\a"
      '\b' -> "\\b"
      '\t' -> "\\t"
      '\n' -> "\\n"
      '\v' -> "\\v"
      '\f' -> "\\f"
      '\r' -> "\\r"
      _ -> case isPrint c of
        True -> Text.singleton c
        False -> "\\x" <> Text.pack (printf "%06X" (ord c))

-- | Valid aliases for a partially-qualified name, from most to least precise
aliasesRev :: QualName -> [Text]
aliasesRev qn = do
  sps <- subPathText
  ps <- pathText
  ix <- indexSuffix
  ns <- namespaceSuffix
  let bn = pathElem $ baseName qn
  return $ ps <> sps <> bn <> ix <> ns
  where
    opt :: Maybe Text -> [Text]
    opt mtxt = case mtxt of
      Nothing -> [Text.empty]
      Just txt -> [txt, Text.empty]

    indexSuffix :: [Text]
    indexSuffix = opt $
      fmap (\i -> "`" <> Text.pack (show i)) (index qn)

    namespaceSuffix :: [Text]
    namespaceSuffix = opt $
      (fmap (\ns -> "@" <> renderNamespace ns) (namespace qn))

    pathElem :: Text -> Text
    pathElem txt = case validPathElem txt of
      True -> txt
      False -> "!?\"" <> escapeInnerString txt <> "\""

    pathText :: [Text]
    pathText = opt $
      case path qn of
        [] -> Nothing
        ps -> Just $ Text.intercalate "::" (map pathElem ps) <> "::"

    subPathText :: [Text]
    subPathText = opt $
      case subPath qn of
        [] -> Nothing
        sp -> Just $ "|::" <> Text.intercalate "::" (map pathElem sp) <> "::"

-- | Valid aliases for a qualified name, from least to most precise
aliases :: QualName -> [Text]
aliases qn = List.reverse (aliasesRev qn)

-- | Fully-qualified rendering of a qualified name, including namespace
ppQualName :: QualName -> Text
ppQualName qn = List.head (aliasesRev qn)

instance PP.Pretty QualName where
  pretty qn = PP.pretty $ List.head (aliasesRev qn)

instance Show QualName where
  show qn = Text.unpack (ppQualName qn)