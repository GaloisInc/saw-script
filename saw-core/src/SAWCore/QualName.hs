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
  , simpleName
  , fullPath
  , fullPathNE
  , fromPath
  , fromNameIndex
  , qualify
  , split
  , POpts(..)
  , PrintMode(..)
  , ppQualName
  , aliases
  , aliasesOpts
  , allAliasesPOpts
  , fullyQualifiedPOpts
  , freshen
  ) where

import           Control.Applicative ((<|>))

import           Data.Char (isAlpha, isAlphaNum, isDigit)
import           Data.Hashable
import qualified Data.List as List
import qualified Data.List.NonEmpty as NE
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Language.Haskell.TH.Syntax (Lift)
import qualified Prettyprinter as PP

import           SAWSupport.Pretty (ppStringLiteral)
import           SAWCore.Panic (panic)

data Namespace =
  NamespaceCore | NamespaceCryptol | NamespaceFresh | NamespaceYosys | NamespaceLLVM | NamespaceFree
  deriving (Eq, Ord, Enum, Bounded, Lift)

instance Hashable Namespace where
  hashWithSalt s ns = hashWithSalt s (fromEnum ns)

renderNamespace :: Namespace -> Text
renderNamespace = \case
  NamespaceCore -> "core"
  NamespaceCryptol -> "cryptol"
  NamespaceFresh -> "fresh"
  NamespaceYosys -> "yosys"
  NamespaceLLVM -> "llvm"
  -- distinguished namespace for ad-hoc free variables
  NamespaceFree -> "free"

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
  deriving (Eq, Ord, Lift)

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

simpleName :: Text -> QualName
simpleName nm = QualName [] [] nm Nothing Nothing

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

-- | Split a qualified name into a qualifier, base name and index.
split :: QualName -> Maybe (QualName, Text, Maybe Int)
split qn = do
  path' <-
    do sps@(_:_) <- return $ subPath qn
       return $ qn { subPath = List.init sps, baseName = List.last sps, index = Nothing}
    <|>
    do ps@(_:_) <- return $ path qn
       return $ qn { path = List.init ps, baseName = List.last ps, index = Nothing}
  return $ (path', baseName qn, index qn)

-- | Generate a fresh qualified name from an existing name, avoiding
--   clashes with any of the given "used" names (when rendered fully-qualified).
freshen :: Set Text -> QualName -> QualName
freshen used qn | Set.member (ppQualName qn) used =
  case qn of
    QualName [] [] nm Nothing Nothing | validPathElem nm ->
      let next_qn = qn { baseName = nextBaseName nm}
      in freshen used next_qn
    _ ->
      let
        next_ix = case index qn of
          Nothing -> Just 1
          Just i -> Just (i + 1)
        next_qn = qn { index = next_ix }
      in freshen used next_qn
freshen _ qn = qn

-- | Generate a variant of a name by incrementing the number at the
-- end, or appending the number 1 if there is none.
nextBaseName :: Text -> Text
nextBaseName = Text.pack . reverse . go . reverse . Text.unpack
  where
    go :: String -> String
    go (c : cs)
      | c == '9'  = '0' : go cs
      | isDigit c = succ c : cs
    go cs = '1' : cs

-- | True if the given path element may be printed directly. If not, it
-- must be prefixed with '!?', quoted and escaped.
validPathElem :: Text -> Bool
validPathElem txt = case Text.uncons txt of
  Just (c, txt') ->
    (isAlpha c || c == '_') &&
    Text.all (\c_ -> isAlphaNum c_ || c_ == '\'' || c_ == '_') txt'
  Nothing -> False

data PrintMode =
    AlwaysPrint -- ^ field is printed if it is available
  | NeverPrint  -- ^ field is never printed
  | MaybePrint  -- ^ prints one or two aliases:
                --   one with the field present (if available)
                --   and one with it absent

-- | Print options for controlling which aliases to render for a 'QualName'.
data POpts = POpts
  { pPath :: PrintMode
  , pSubPath :: PrintMode
  , pNamespace :: PrintMode
  , pIndex :: PrintMode
  }

-- | Print all possible aliases
allAliasesPOpts :: POpts
allAliasesPOpts = POpts MaybePrint MaybePrint MaybePrint MaybePrint

-- | Print the most qualified alias
fullyQualifiedPOpts :: POpts
fullyQualifiedPOpts = POpts AlwaysPrint AlwaysPrint AlwaysPrint AlwaysPrint

-- | Valid aliases for a qualified name, from least to most precise,
--   constrained by the provided 'POpts'.
aliasesOpts :: POpts -> QualName -> [Text]
aliasesOpts opts qn = do
  ns <- namespaceSuffix
  ix <- indexSuffix
  ps <- pathText
  sps <- subPathText
  let pathSuffix = if Text.null sps && Text.null ps then Text.empty else ":"
  let bn = pathElem $ baseName qn
  return $ ps <> sps <> pathSuffix <> bn <> ix <> ns
  where
    opt :: PrintMode -> Maybe Text -> [Text]
    opt mode mtxt = case (mode, mtxt) of
      (NeverPrint,_) -> [Text.empty]
      (_, Nothing) -> [Text.empty]
      (AlwaysPrint, Just txt) -> [txt]
      (MaybePrint, Just txt) -> [Text.empty, txt]

    indexSuffix :: [Text]
    indexSuffix = opt (pIndex opts) $
      fmap (\i -> "`" <> Text.pack (show i)) (index qn)

    namespaceSuffix :: [Text]
    namespaceSuffix = opt (pNamespace opts) $
      (fmap (\ns -> "@" <> renderNamespace ns) (namespace qn))

    pathElem :: Text -> Text
    pathElem txt = case validPathElem txt of
      True -> txt
      False -> "!?" <> ppStringLiteral txt

    pathText :: [Text]
    pathText = opt (pPath opts) $
      case path qn of
        [] -> Nothing
        ps -> Just $ Text.intercalate "::" (map pathElem ps) <> ":"

    subPathText :: [Text]
    subPathText = opt (pSubPath opts) $
      case subPath qn of
        [] -> Nothing
        sp -> Just $ "|:" <> Text.intercalate "::" (map pathElem sp) <> ":"

-- | Aliases for a qualified name, from least to most precise.
--   The list is nonempty, as it will always include the rendered base
--   name as the first element.
aliases :: QualName -> [Text]
aliases qn = aliasesOpts allAliasesPOpts qn

-- | Fully-qualified rendering of a qualified name. Equivalent to
--   the last element of 'aliases'.
ppQualName :: QualName -> Text
ppQualName qn = case aliasesOpts fullyQualifiedPOpts qn of
  [nm] -> nm
  nms -> panic "ppQualName" $
    ["unexpected number of fully-qualified aliases: "] ++ nms

instance PP.Pretty QualName where
  pretty qn = PP.pretty $ ppQualName qn

instance Show QualName where
  show qn = Text.unpack (ppQualName qn)