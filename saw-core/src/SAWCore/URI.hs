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
  ( URI(..)
  , mkScheme
  , mkPathPiece
  , mkFragment
  , mkURI
  , render

  ) where

import           Data.Hashable
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Text (Text)
import qualified Data.Text as Text

data URI = URI 
  { uriScheme :: Maybe Text 
  , uriAuthority :: Either Bool ()
  , uriPath :: Maybe (Bool, NonEmpty Text)
  , uriQuery :: [()]
  , uriFragment :: Maybe Text
  }
 deriving (Eq,Ord,Show)

instance Hashable URI where
  hashWithSalt s (URI a b c d e) = s
    `hashWithSalt` a 
    `hashWithSalt` b
    `hashWithSalt` c
    `hashWithSalt` d
    `hashWithSalt` e

mkScheme :: Text -> Maybe Text
mkScheme nm = Just nm

mkPathPiece :: Text -> Maybe Text
mkPathPiece nm = Just nm

mkFragment :: Text -> Maybe Text
mkFragment nm = Just nm


nonEmpty :: MonadFail m => Text -> m ()
nonEmpty txt = case Text.null txt of
  True -> fail "nonEmpty"
  False -> return ()

splitM :: MonadFail m => (Char -> Bool) -> Text -> m (NonEmpty Text)
splitM f txt = do
  nonEmpty txt
  (p:ps) <- return $ Text.split f txt
  return $ p :| ps

breakM :: MonadFail m => (Char -> Bool) -> Text -> m (Text,Text)
breakM f txt = nonEmpty txt >> (return $ Text.break f txt)

sepM :: MonadFail m => Char -> Text -> m (Maybe (Text, Text))
sepM c txt = do
  (ns,rest) <- breakM (==c) txt
  nonEmpty ns
  case Text.uncons rest of
    Nothing -> return $ Nothing
    Just (_,rest') -> return $ Just (ns,rest')

mkURI :: Text -> Maybe URI
mkURI txt = do
  (mns, txt') <- sepM ':' txt >>= \case
    Nothing -> return (Nothing, txt)
    Just (ns,txt') -> return (Just ns, txt')
  (mf, txt'') <- sepM '#' txt' >>= \case
    Nothing -> return (Nothing, txt')
    Just (txt'', f) -> return (Just f, txt'')
  ps <- splitM (=='/') txt''
  ps' <- case ps of
    (p :| (p':ps')) | Text.null p -> return $ p' :| ps'
    _ -> return ps
  return $ URI mns (Left True) (Just (False, ps')) [] mf

render :: URI -> Text
render uri = schemePrefix uri <> pathBody uri <> fragmentSuffix uri

schemePrefix :: URI -> Text
schemePrefix uri = case uriScheme uri of
  Just s -> s <> ":"
  Nothing -> Text.empty

fragmentSuffix :: URI -> Text
fragmentSuffix uri = case uriFragment uri of
  Just f -> "#" <> f
  Nothing -> Text.empty

pathBody :: URI -> Text
pathBody uri = case uriPath uri of
  Just (_,p :| ps) -> case ps of
    [] -> p
    _ -> "/" <> Text.intercalate "/" (p:ps)
  Nothing -> Text.empty