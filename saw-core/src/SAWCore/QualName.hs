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
  , QualName
  , qnNamespace
  , qnBaseName
  , qnPath
  , qnSubPath
  , qnIndex
  , qnFullPath
  , qnFullPathNE
  , pathToQualName
  , indexedQualName
  , mkQualName
  , qualifyName
  , splitQualName
  , parse
  , render
  , renderPath
  , aliases
  ) where

import qualified Data.Foldable as Foldable
import           Data.Hashable
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Read as Text
import Control.Monad.Except
import Control.Monad (unless)
import qualified Data.List.NonEmpty as NE

import qualified Language.Haskell.TH.Syntax as TH
import Data.Char (isAlpha, isAlphaNum)

{-# INLINE debugParse #-}
debugParse :: Bool
debugParse = True

type ParseM = Either [Text]

rethrow :: Text -> ParseM a -> ParseM a
rethrow e f  = f `catchError` \e' -> throwError (e:e')

throwOne :: Text -> ParseM a
throwOne e = throwError [e]

-- | Hide parse errors for exported functions unless debugging is enabled.
squelch :: ParseM a -> ParseM a
squelch f | debugParse = f
squelch f = f `catchError` \_ -> throwError []

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

readNamespace :: Text -> ParseM Namespace
readNamespace txt = case Map.lookup txt namespaceMap of
  Just ns -> pure ns
  Nothing -> throwOne $ "readNamespace: namespace not found: " <> txt

splitM :: Bool -> Char -> Text -> ParseM (Text,Text)
splitM fwd c txt = rethrow err $ do
  nonEmpty txt
  let txt' = if fwd then txt else Text.reverse txt
  let (lhs,rhs) = Text.break (==c) txt'
  case Text.uncons rhs of
    Nothing -> throwOne $ "empty rhs"
    Just(_,rhs') -> case fwd of
      True -> return (lhs, rhs')
      False -> return (Text.reverse rhs', Text.reverse lhs)
  where
    err = "splitM: failed to split on char '" <> Text.singleton c <> "' in '"
      <> txt

splitOnM :: Text -> Text -> ParseM [Text]
splitOnM _ txt | Text.null txt = throwOne "splitOnM: empty argument"
splitOnM sep txt = return $ Text.splitOn sep txt

unsnocM :: [a] -> ParseM ([a], a)
unsnocM [] = throwOne "unsnocM: empty list"
unsnocM xs = return $ (List.init xs, List.last xs)

splitFirst :: (a -> Maybe a) -> [a] -> Maybe ([a],[a])
splitFirst f xs = go [] xs
  where
    go pref ys = case ys of
      [] -> Nothing
      (y:ys') -> case f y of
        Just y' -> Just (List.reverse pref,y':ys')
        Nothing -> go (y:pref) ys'

parsePath :: Text -> ParseM ([Text], [Text], Text)
parsePath txt0 = rethrow ("parsePath: failed to parse: " <> txt0) $ do
  path_nm <- splitOnM "::" txt0
  (path_subpath,nm) <- unsnocM path_nm
  case splitFirst (Text.stripSuffix "[") path_subpath of
    Just (path, subpath_) -> do
      (subpath,subpath_last_) <- unsnocM subpath_
      case (Text.stripSuffix "]" subpath_last_) of
        Just subpath_last -> return (path, subpath ++ [subpath_last], nm)
        Nothing -> throwOne "could not find closing bracket in subpath"
    Nothing -> return (path_subpath, [], nm)

data QualName = QualName
  { qnNamespace :: Namespace
  , qnBaseName :: Text
  , qnPath :: [Text]
  , qnSubPath :: [Text]
  , qnIndex :: Maybe Int
  }
  deriving (Eq, Ord, TH.Lift)

qnFullPath :: QualName -> [Text]
qnFullPath qn = qnPath qn ++ qnSubPath qn ++ [qnBaseName qn]

qnFullPathNE :: QualName -> NE.NonEmpty Text
qnFullPathNE qn = NE.fromList (qnFullPath qn)

instance Hashable QualName where
  hashWithSalt s (QualName a b c d e) = s
    `hashWithSalt` a
    `hashWithSalt` b
    `hashWithSalt` c
    `hashWithSalt` d
    `hashWithSalt` e


validPathElem :: Text -> Bool
validPathElem txt =
     not (Text.null txt)
  && Text.all (\c -> not (c == '[' || c == ']')) txt
  && (not (Text.isInfixOf "::" txt))

validQualifierElem :: Text -> Bool
validQualifierElem txt = validPathElem txt && Text.all isAlpha txt

-- Pulled from Cryptol.Parser.Lexer.x
validNameSymbols :: [Char]
validNameSymbols = ['!','#','$','%','&','*','-','.',':','<','=','>','?','@','^','~','\\','/']

validBaseName :: Text -> Bool
validBaseName txt = validPathElem txt && case Text.uncons txt of
  Nothing -> False
  Just (c,txt') -> case isAlpha c of
    True -> Text.all (\c_ -> isAlphaNum c_ || c_ == '\'' || c_== '_') txt'
    False -> (c == '_' && Text.null txt') ||
      Text.all (\c_ -> List.elem c_ validNameSymbols) txt

pathToQualName :: (Foldable t) => Namespace -> t Text -> Either [Text] QualName
pathToQualName ns ps = squelch $ case ps' of
  [] -> throwOne "pathToQualName: empty path"
  _ -> mkQualName ns (List.init ps') [] (List.last ps') Nothing
  where
    ps' = Foldable.toList ps

indexedQualName :: Namespace -> Text -> Int -> Either [Text] QualName
indexedQualName ns nm i = squelch $ mkQualName ns [] [] nm (Just i)

mkQualName :: Namespace -> [Text] -> [Text] -> Text -> Maybe Int -> Either [Text] QualName
mkQualName ns ps sps nm idx = squelch $ rethrow err $ do
  unless (validBaseName nm) $
    throwOne $ "mkQualName: invalid base name: " <> nm
  mapM_ checkQual (ps ++ sps)
  return $ QualName ns nm ps sps idx
  where
    err = Text.intercalate " " $
      [ "mkQualName failed: "
      , renderNamespace ns
      , "[" <> Text.intercalate ", " ps <> "]"
      , "[" <> Text.intercalate ", " sps <> "]"
      , nm
      , Text.pack (show idx)
      ]

    checkQual txt = unless (validQualifierElem txt) $
      throwOne $ "mkQualName: invalid path qualifier element: " <> txt

-- | Append a base name to a given 'QualName', pushing the existing
--   base name into the path (or subpath, if it is nonempty).
qualifyName :: QualName -> Text -> Either [Text] QualName
qualifyName qn txt = do
  let prevBaseName = qnBaseName qn
  unless (validBaseName txt) $
    throwOne $ "qualifyName: invalid base name: " <> txt
  unless (validQualifierElem prevBaseName) $
    throwOne $ "qualifyName: cannot convert base name to qualifier element: " <> prevBaseName
  case qnSubPath qn of
    [] -> return $ qn { qnPath = qnPath qn ++ [prevBaseName], qnBaseName = txt }
    sps -> return $ qn { qnSubPath = sps ++ [prevBaseName], qnBaseName = txt }

-- | Split a qualified name into a qualifier and base name.
splitQualName :: QualName -> Either [Text] (QualName, Text)
splitQualName qn = case qnSubPath qn of
  [] -> case qnPath qn of
    (p:ps) | validBaseName p ->
      return $ (qn { qnPath = ps, qnBaseName = p }, qnBaseName qn)
    _ -> bad
  (p:sps) | validBaseName p ->
    return $ (qn { qnSubPath = sps, qnBaseName = p }, qnBaseName qn)
  _ -> bad
  where
    bad = throwOne $ "splitQualName: cannot split qualified name: " <> render qn

nonEmpty :: Text -> ParseM ()
nonEmpty txt = case Text.null txt of
  True -> throwOne "nonEmpty: unexpected empty Text"
  False -> return ()


parse :: Text -> Either [Text] QualName
parse txt0 = squelch $ rethrow err $ do
  (txt1, ns_txt) <- splitM False '@' txt0
  ns <- readNamespace ns_txt
  let (mi, txt3) = case splitM False '#' txt1 of
        Right (txt2,si)
          | Right (i,s) <- Text.decimal si
          , Text.null s
         -> (Just i, txt2)
        _ -> (Nothing, txt1)
  (path,subpath,nm) <- parsePath txt3
  mkQualName ns path subpath nm mi
  where
    err = "parse: failed to parse qualified name: " <> txt0

data RenderOpts = RenderOpts { optRenderNamespace :: Maybe Bool }

defaultRenderOpts :: RenderOpts
defaultRenderOpts = RenderOpts Nothing

-- | Valid aliases for a qualified name, from most to least precise
aliasesRev :: RenderOpts -> QualName -> [Text]
aliasesRev opts qn = do
  sps <- subPathText
  ps <- pathText
  ix <- indexSuffix
  ns <- namespaceSuffix
  let bn = qnBaseName qn
  return $ ps <> sps <> bn <> ix <> ns
  where
    opt :: Maybe Bool -> Maybe Text -> [Text]
    opt mopt mtxt = case mtxt of
      Nothing -> [Text.empty]
      Just txt -> case mopt of
        Nothing -> [txt, Text.empty]
        Just True -> [txt]
        Just False -> [Text.empty]

    indexSuffix :: [Text]
    indexSuffix = opt Nothing $
      fmap (\i -> "#" <> Text.pack (show i)) (qnIndex qn)

    namespaceSuffix :: [Text]
    namespaceSuffix = opt (optRenderNamespace opts) $
      Just $ "@" <> renderNamespace (qnNamespace qn)

    pathText :: [Text]
    pathText = opt Nothing $
      case qnPath qn of
        [] -> Nothing
        ps -> Just $ Text.intercalate "::" ps <> "::"

    subPathText :: [Text]
    subPathText = opt Nothing $
      case qnSubPath qn of
        [] -> Nothing
        sp -> Just $ "[" <> Text.intercalate "::" sp <> "]" <> "::"

-- | Valid aliases for a qualified name, from least to most precise
aliases :: QualName -> [Text]
aliases qn = List.reverse (aliasesRev defaultRenderOpts qn)

-- | Fully-qualified rendering of a qualified name, including namespace
render :: QualName -> Text
render qn = List.head (aliasesRev defaultRenderOpts qn)

-- | Fully-qualified rendering of a qualified name, without namespace
renderPath :: QualName -> Text
renderPath qn = List.head (aliasesRev (defaultRenderOpts { optRenderNamespace = Just False }) qn)

instance Show QualName where
  show qn = Text.unpack (render qn)