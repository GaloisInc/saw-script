{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : SAWCore.URI
Copyright   : Galois, Inc. 2012-2026
License     : BSD3
Maintainer  : dmatichuk@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Simple URI implementation with namespaces and paths.
-}

module SAWCore.URI 
  ( Namespace(..)
  , URI
  , mkURI
  , parseURI
  , renderURI
  ) where

import qualified Data.Foldable as Foldable
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

parsePath :: MonadFail m => Text -> m ([Text], Text)
parsePath txt
  | not (Text.null txt)
  , ps <- map percentDecode $ Text.splitOn "/" txt
  = case ps of
      -- allow for a leading '/'
      (p:ps') | Text.null p -> mkPath ps'
      _ -> mkPath ps
parsePath txt =
  fail $ "parsePath: invalid path: " ++ (Text.unpack txt)

data URI = URI 
  { uriNamespace :: Namespace
  , uriBaseName :: Text
  , uriPath :: [Text]
  , uriIndex :: Maybe Int
  }
  deriving (Eq, Ord)

instance Hashable URI where
  hashWithSalt s (URI a b c d) = s
    `hashWithSalt` a 
    `hashWithSalt` b
    `hashWithSalt` c
    `hashWithSalt` d

percentEncode :: Text -> Text
percentEncode txt = Text.replace "/" "%2F" $ Text.replace "%" "%25" txt

percentDecode :: Text -> Text
percentDecode txt = Text.replace "%25" "%" $ Text.replace "%2F" "/" txt

mkPath :: (MonadFail m) => [Text] -> m ([Text], Text)
mkPath ps = case (List.any Text.null ps,ps) of
  (False, _:_) -> return (List.init ps,List.last ps)
  _ -> fail $ "mkPath: invalid path: " ++ show ps

mkURI :: (MonadFail m, Foldable t) => Namespace -> t Text -> Maybe Int -> m URI
mkURI ns ps idx = do
  (ps', nm) <- mkPath (Foldable.toList ps)
  return $ URI ns nm ps' idx

nonEmpty :: MonadFail m => String -> Text -> m ()
nonEmpty msg txt = case Text.null txt of
  True -> fail msg
  False -> return ()

splitM :: MonadFail m => Bool -> Char -> Text -> m (Text,Text)
splitM fwd c txt = do
  nonEmpty err txt
  let txt' = if fwd then txt else Text.reverse txt
  let (lhs,rhs) = Text.break (==c) txt'
  nonEmpty err lhs
  case Text.uncons rhs of
    Nothing -> fail err
    Just(_,rhs') -> case fwd of
      True -> return (lhs, rhs')
      False -> return (Text.reverse rhs', Text.reverse lhs)
  where
    err = "splitM: failed to split on char '" ++ [c] ++ "' in '"
      ++ Text.unpack txt

parseURI :: MonadFail m => Text -> m URI
parseURI txt0 = do
  (ns, txt1) <- splitM True ':' txt0
  ns' <- readNamespace ns
  let (mi, txt3) = case splitM False '#' txt1 of
        Just (txt2,si)
          | Right (i,s) <- Text.decimal si
          , Text.null s
         -> (Just i, txt2)
        _ -> (Nothing, txt1)
  (ps,nm) <- parsePath txt3
  return $ URI ns' nm ps mi

renderURI :: URI -> Text
renderURI uri =
     renderNamespace (uriNamespace uri)
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

instance Show URI where
  show uri = Text.unpack (renderURI uri)