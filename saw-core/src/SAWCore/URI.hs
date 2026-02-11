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
  ( NameSpace(..)
  , URI
  , mkPathURI
  , mkIdxURI
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

data NameSpace =
  NameSpaceCore | NameSpaceCryptol | NameSpaceFresh | NameSpaceYoSys | NameSpaceLLVM
  deriving (Eq, Ord, Enum, Bounded)

instance Hashable NameSpace where
  hashWithSalt s ns = hashWithSalt s (fromEnum ns)

renderNameSpace :: NameSpace -> Text
renderNameSpace = \case
  NameSpaceCore -> "core"
  NameSpaceCryptol -> "cryptol"
  NameSpaceFresh -> "fresh"
  NameSpaceYoSys -> "yosys"
  NameSpaceLLVM -> "llvm"

instance Show NameSpace where
  show ns = Text.unpack $ renderNameSpace ns

nameSpaceMap :: Map Text NameSpace
nameSpaceMap = Map.fromList $ map (\ns -> (renderNameSpace ns, ns)) [minBound..maxBound]

readNameSpace :: MonadFail m => Text -> m NameSpace
readNameSpace txt = case Map.lookup txt nameSpaceMap of
  Just ns -> pure ns
  Nothing -> fail $ "readNameSpace: namespace not found: " ++ Text.unpack txt

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
  { uriNameSpace :: NameSpace
  , uriBaseName :: Text
  , uriPathIdx :: Either [Text] Int
  }
  deriving (Eq, Ord)

uriQualifier :: URI -> [Text]
uriQualifier uri = case uriPathIdx uri of
  Left ps -> ps
  Right _ -> []

instance Hashable URI where
  hashWithSalt s (URI a b c) = s
    `hashWithSalt` a 
    `hashWithSalt` b
    `hashWithSalt` c

percentEncode :: Text -> Text
percentEncode txt = Text.replace "/" "%2F" $ Text.replace "%" "%25" txt

percentDecode :: Text -> Text
percentDecode txt = Text.replace "%25" "%" $ Text.replace "%2F" "/" txt

mkPath :: (Foldable t, MonadFail m) => t Text -> m ([Text], Text)
mkPath ps = case (List.any Text.null ps',ps') of
  (False, _:_) -> return (List.init ps',List.last ps')
  _ -> fail $ "mkPath: invalid path: " ++ show ps'
  where
    ps' = Foldable.toList ps

mkPathURI :: (Foldable t, MonadFail m) => NameSpace -> t Text -> m URI
mkPathURI ns ps = do
  (ps', nm) <- mkPath ps
  return $ URI ns nm (Left ps')

mkIdxURI :: (MonadFail m) => NameSpace -> Text -> Int -> m URI
mkIdxURI ns nm i = do
  ([],nm') <- mkPath [nm]
  return $ URI ns nm' (Right i)

nonEmpty :: MonadFail m => String -> Text -> m ()
nonEmpty msg txt = case Text.null txt of
  True -> fail msg
  False -> return ()

splitM :: MonadFail m => Char -> Text -> m (Text,Text)
splitM c txt = do
  nonEmpty err txt
  let (lhs, rhs) = Text.break (==c) txt
  nonEmpty err lhs
  case Text.uncons rhs of
    Nothing -> return (lhs, Text.empty)
    Just(_,rhs') -> return (lhs, rhs')
  where
    err = "splitM: failed to split on char '" ++ [c] ++ "' in '"
      ++ Text.unpack txt

parseURI :: MonadFail m => Text -> m URI
parseURI txt0 = do
  (ns, txt1) <- splitM ':' txt0
  ns' <- readNameSpace ns
  (si_rev, txt2_rev) <- splitM '#' (Text.reverse txt1)
  let si = Text.reverse si_rev
  (mi, txt2) <- case Text.null txt2_rev of
    False
      | Right (i,s) <- Text.decimal si
      , Text.null s
      -> pure $ (Just i, Text.reverse txt2_rev)
    _ -> pure (Nothing, txt1)
  case mi of
    Just i -> return $ URI ns' (percentDecode txt2) (Right i)
    Nothing -> do
      (ps,nm) <- parsePath txt2
      return $ URI ns' nm (Left ps)

renderURI :: URI -> Text
renderURI uri =
     renderNameSpace (uriNameSpace uri)
  <> ":" <> pathBody <> suffix
  where
    suffix :: Text
    suffix = case uriPathIdx uri of
      Left _ -> Text.empty
      Right i -> "#" <> Text.pack (show i)

    pathBody :: Text
    pathBody = case uriQualifier uri of
      [] -> percentEncode $ uriBaseName uri
      ps -> "/" <> Text.intercalate "/" (map percentEncode (ps ++ [uriBaseName uri]))

instance Show URI where
  show uri = Text.unpack (renderURI uri)