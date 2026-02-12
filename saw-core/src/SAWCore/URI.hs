{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : SAWCore.URI
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
  , mkQualName
  , parse
  , render
  ) where

import           Data.Hashable
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map

import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Read as Text

data Namespace =
  NamespaceCore | NamespaceCryptol | NamespaceFresh | NamespaceYosys | NamespaceLLVM
  deriving (Eq, Ord, Enum, Bounded)

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

readNamespace :: MonadFail m => Text -> m Namespace
readNamespace txt = case Map.lookup txt namespaceMap of
  Just ns -> pure ns
  Nothing -> fail $ "readNamespace: namespace not found: " ++ Text.unpack txt

splitM :: MonadFail m => Bool -> Char -> Text -> m (Text,Text)
splitM fwd c txt = do
  nonEmpty err txt
  let txt' = if fwd then txt else Text.reverse txt
  let (lhs,rhs) = Text.break (==c) txt'
  case Text.uncons rhs of
    Nothing -> fail err
    Just(_,rhs') -> case fwd of
      True -> return (lhs, rhs')
      False -> return (Text.reverse rhs', Text.reverse lhs)
  where
    err = "splitM: failed to split on char '" ++ [c] ++ "' in '"
      ++ Text.unpack txt

splitOnM :: MonadFail m => Text -> Text -> m [Text]
splitOnM _ txt | Text.null txt = fail "splitOnM: empty argument"
splitOnM sep txt = return $ Text.splitOn sep txt

unsnocM :: MonadFail m => [a] -> m ([a], a)
unsnocM [] = fail "unsnocM: empty list"
unsnocM xs = return $ (List.init xs, List.last xs)

parsePath :: MonadFail m => Text -> m ([Text], [Text], Text)
parsePath txt0 = do
  case splitM True '[' txt0 of
    Just (path_txt, subpath_txt_) -> do
      path <- splitOnM path_txt
      (subpath_txt, s) <- splitM False ']' subpath_txt_
      True <- return $ Text.null s
      subpath_nm <- splitOnM subpath_txt
      (subpath,nm) <- unsnocM subpath_nm
      return (path, subpath, nm)
    Nothing -> do
      path_nm <- splitOnM txt0
      (path,nm) <- unsnocM path_nm
      return (path, [], nm)

data QualName = QualName
  { qnNameSpace :: Namespace
  , qnBaseName :: Text
  , qnPath :: [Text]
  , qnSubPath :: [Text]
  , qnIndex :: Maybe Int
  }
  deriving (Eq, Ord)


instance Hashable QualName where
  hashWithSalt s (QualName a b c d e) = s
    `hashWithSalt` a 
    `hashWithSalt` b
    `hashWithSalt` c
    `hashWithSalt` d
    `hashWithSalt` e


invalidPathElem :: Text -> Bool
invalidPathElem txt = 
     Text.null txt 
  || Text.any (\c -> c == '[' || c == ']') txt
  || Text.isInfixOf "::" txt

pathToQualName :: (MonadFail m, Foldable t) => Namespace -> t Text -> m QualName
pathToQualName _ [] = fail "pathToQualName: empty path"
pathToQualName ns ps = mkQualName ns (List.init ps) [] (List.last ps) (-1)

indexedQualName :: Namespace -> Text -> Int -> m QualName
indexedQualName ns nm i = mkQualName ns [] [] nm i

mkQualName :: (MonadFail m) => Namespace -> [Text] -> [Text] -> Text -> Maybe Int -> m QualName
mkQualName ns ps sps nm idx = do
  mapM_ go (nm : ps ++ sps)
  return $ QualName ns nm ps sps idx
  where
    go txt = case invalidPathElem txt of
      True -> fail $ "mkQualName: invalid path element: " ++ Text.unpack txt
      False -> return ()

nonEmpty :: MonadFail m => String -> Text -> m ()
nonEmpty msg txt = case Text.null txt of
  True -> fail msg
  False -> return ()



parse :: MonadFail m => Text -> m QualName
parse txt0 = do
  (txt1, ns_txt) <- splitM False '@' txt0
  ns <- readNameSpace ns_txt
  let (i', txt3) = case splitM False '#' txt1 of
        Just (txt2,si)
          | Right (i,s) <- Text.decimal si
          , Text.null s
         -> (i, txt2)
        _ -> (-1, txt1)
  (path,subpath,nm) <- parsePath txt3
  mkQualName path subpath nm i'

render :: QualName -> Text
render uri =
     renderNameSpace (uriNameSpace uri)
  <> ":" <> pathBody <> suffix
  where
    suffix :: Text
    suffix = case uriIndex uri of
      Nothing -> Text.empty
      Just i -> "#" <> Text.pack (show i)

    pathBody :: Text
    pathBody = case uriPath uri of
      [] -> percentEncode $ uriBaseName uri
      ps -> "/" <> Text.intercalate "/" (map percentEncode (ps ++ [uriBaseName uri]))

instance Show QualName where
  show uri = Text.unpack (renderURI uri)