{- |
Module      : Verifier.SAW.Name
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Various kinds of names.
-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Verifier.SAW.Name
  ( -- * Module names
    ModuleName, mkModuleName
  , preludeName
  , moduleNameText
  , moduleNamePieces
   -- * Identifiers
  , Ident(identModule, identBaseName), identName, mkIdent
  , parseIdent
  , isIdent
  , identText
  , identPieces
    -- * NameInfo
  , NameInfo(..)
  , toShortName
  , toAbsoluteName
  , moduleIdentToURI
  , nameURI
  , nameAliases
  ) where

import           Control.Exception (assert)
import           Data.Char
import           Data.Hashable
import           Data.List
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Maybe
import           Data.String (IsString(..))
import           Data.Text (Text)
import qualified Data.Text as Text
import           GHC.Generics (Generic)
import           Text.URI
import qualified Language.Haskell.TH.Syntax as TH
import           Instances.TH.Lift () -- for instance TH.Lift Text

import Verifier.SAW.Utils (panic, internalError)


-- Module Names ----------------------------------------------------------------

newtype ModuleName = ModuleName Text
  deriving (Eq, Ord, Generic, TH.Lift)

instance Hashable ModuleName -- automatically derived

instance Show ModuleName where
  show (ModuleName s) = Text.unpack s


moduleNameText :: ModuleName -> Text
moduleNameText (ModuleName x) = x

moduleNamePieces :: ModuleName -> [Text]
moduleNamePieces (ModuleName x) = Text.splitOn (Text.pack ".") x

-- | Create a module name given a list of strings with the top-most
-- module name given first.
mkModuleName :: [String] -> ModuleName
mkModuleName [] = error "internal: mkModuleName given empty module name"
mkModuleName nms = assert (all isCtor nms) $ ModuleName (Text.pack s)
  where s = intercalate "." (reverse nms)

preludeName :: ModuleName
preludeName = mkModuleName ["Prelude"]


-- Identifiers -----------------------------------------------------------------

data Ident =
  Ident
  { identModule :: ModuleName
  , identBaseName :: Text
  }
  deriving (Eq, Ord, Generic)

instance Hashable Ident -- automatically derived

instance Show Ident where
  show (Ident m s) = shows m ('.' : Text.unpack s)

identText :: Ident -> Text
identText i = moduleNameText (identModule i) <> Text.pack "." <> identBaseName i

identPieces :: Ident -> NonEmpty Text
identPieces i =
  case moduleNamePieces (identModule i) of
    [] -> identBaseName i :| []
    (x:xs) -> x :| (xs ++ [identBaseName i])

identName :: Ident -> String
identName = Text.unpack . identBaseName

instance Read Ident where
  readsPrec _ str =
    let (str1, str2) = break (not . isIdChar) str in
    [(parseIdent str1, str2)]

mkIdent :: ModuleName -> String -> Ident
mkIdent m s = Ident m (Text.pack s)

-- | Parse a fully qualified identifier.
parseIdent :: String -> Ident
parseIdent s0 =
    case reverse (breakEach s0) of
      (_:[]) -> internalError $ "parseIdent given empty module name."
      (nm:rMod) -> mkIdent (mkModuleName (reverse rMod)) nm
      _ -> internalError $ "parseIdent given bad identifier " ++ show s0
  where breakEach s =
          case break (=='.') s of
            (h,[]) -> [h]
            (h,'.':r) -> h : breakEach r
            _ -> internalError "parseIdent.breakEach failed"

instance IsString Ident where
  fromString = parseIdent

isIdent :: String -> Bool
isIdent (c:l) = isAlpha c && all isIdChar l
isIdent [] = False

isCtor :: String -> Bool
isCtor (c:l) = isUpper c && all isIdChar l
isCtor [] = False

-- | Returns true if character can appear in identifier.
isIdChar :: Char -> Bool
isIdChar c = isAlphaNum c || (c == '_') || (c == '\'') || (c == '.')


--------------------------------------------------------------------------------
-- NameInfo


-- | Descriptions of the origins of names that may be in scope
data NameInfo
  = -- | This name arises from an exported declaration from a module
    ModuleIdentifier Ident

  | -- | This name was imported from some other programming language/scope
    ImportedName
      URI      -- ^ An absolutely-qualified name, which is required to be unique
      [Text]   -- ^ A collection of aliases for this name.  Sorter or "less-qualified"
               --   aliases should be nearer the front of the list

 deriving (Eq,Ord,Show)

nameURI :: NameInfo -> URI
nameURI =
  \case
    ModuleIdentifier i -> moduleIdentToURI i
    ImportedName uri _ -> uri

nameAliases :: NameInfo -> [Text]
nameAliases =
  \case
    ModuleIdentifier i -> [identBaseName i, identText i]
    ImportedName _ aliases -> aliases

toShortName :: NameInfo -> Text
toShortName (ModuleIdentifier i) = identBaseName i
toShortName (ImportedName uri []) = render uri
toShortName (ImportedName _ (x:_)) = x

toAbsoluteName :: NameInfo -> Text
toAbsoluteName (ModuleIdentifier i) = identText i
toAbsoluteName (ImportedName uri _) = render uri

moduleIdentToURI :: Ident -> URI
moduleIdentToURI ident = fromMaybe (panic "moduleIdentToURI" ["Failed to constructed ident URI", show ident]) $
  do sch  <- mkScheme "sawcore"
     path <- mapM mkPathPiece (identPieces ident)
     pure URI
       { uriScheme = Just sch
       , uriAuthority = Left True -- absolute path
       , uriPath   = Just (False, path)
       , uriQuery  = []
       , uriFragment = Nothing
       }

