{- |
Module      : SAWCore.Name
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Various kinds of names.
-}

{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module SAWCore.Name
  ( -- * Module names
    ModuleName, mkModuleName
  , preludeName
  , moduleNameText
  , moduleNamePieces
   -- * Identifiers
  , Ident(identModule, identBaseName), identName, mkIdent, mkSafeIdent
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
    -- * ExtCns
  , VarIndex
  , ExtCns(..)
  , scFreshNameURI
    -- * Display Name Environments
  , DisplayNameEnv(..)
  , emptyDisplayNameEnv
  , extendDisplayNameEnv
  , filterDisplayNameEnv
  , mergeDisplayNameEnv
  , resolveDisplayName
  , bestDisplayName
  ) where

import           Numeric (showHex)
import           Data.Char
import           Data.Hashable
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.String (IsString(..))
import           Data.Text (Text)
import qualified Data.Text as Text
import           GHC.Generics (Generic)
import           Text.URI
import qualified Language.Haskell.TH.Syntax as TH
import           Instances.TH.Lift () -- for instance TH.Lift Text

import SAWCore.Panic (panic)


-- Module Names ----------------------------------------------------------------

newtype ModuleName = ModuleName Text
  deriving (Eq, Ord, Generic, TH.Lift)

instance Hashable ModuleName -- automatically derived

instance Show ModuleName where
  show (ModuleName s) = Text.unpack s


moduleNameText :: ModuleName -> Text
moduleNameText (ModuleName x) = x

moduleNamePieces :: ModuleName -> [Text]
moduleNamePieces (ModuleName x) = Text.splitOn "." x

-- | Create a module name given a list of strings with the top-most
-- module name given first.
mkModuleName :: [Text] -> ModuleName
mkModuleName nms = ModuleName $ Text.intercalate "." nms

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

mkIdent :: ModuleName -> Text -> Ident
mkIdent m s = Ident m s

-- | Make a \"coq-safe\" identifier from a string that might contain
-- non-identifier characters, where we use the SAW core notion of identifier
-- characters as letters, digits, underscore and primes. Any disallowed
-- character is mapped to the string @__xNN@, where @NN@ is the hexadecimal code
-- for that character. Additionally, a SAW core identifier is not allowed to
-- start with a prime, so a leading underscore is added in such a case.
mkSafeIdent :: ModuleName -> String -> Ident
mkSafeIdent _ [] = fromString "_"
mkSafeIdent mnm nm =
  let is_safe_char c = isAlphaNum c || c == '_' || c == '\'' in
  mkIdent mnm $ Text.pack $
  (if nm!!0 == '\'' then ('_' :) else id) $
  concatMap
  (\c -> if is_safe_char c then [c] else
           "__x" ++ showHex (ord c) "")
  nm

-- | Parse a fully qualified identifier.
parseIdent :: String -> Ident
parseIdent s0 =
    case reverse (breakEach s0) of
      (_:[]) -> panic "parseIdent" ["Empty module name"]
      (nm:rMod) -> mkIdent (mkModuleName (reverse rMod)) nm
      _ -> panic "parseIdent" ["Bad identifier " <> Text.pack s0]
  where breakEach s =
          case break (=='.') s of
            (h, []) -> [Text.pack h]
            (h, _ : r) -> Text.pack h : breakEach r

instance IsString Ident where
  fromString = parseIdent

isIdent :: String -> Bool
isIdent (c:l) = isAlpha c && all isIdChar l
isIdent [] = False

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
      [Text]   -- ^ A collection of aliases for this name.  Shorter or "less-qualified"
               --   aliases should be nearer the front of the list

 deriving (Eq,Ord,Show)

instance Hashable NameInfo where
  hashWithSalt x nmi =
    case nmi of
      ModuleIdentifier ident -> hashWithSalt x ident
      ImportedName uri _ -> hashWithSalt x uri

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
moduleIdentToURI ident = fromMaybe (panic "moduleIdentToURI" ["Failed to construct ident URI: " <> identText ident]) $
  do sch  <- mkScheme "sawcore"
     path <- mapM mkPathPiece (identPieces ident)
     pure URI
       { uriScheme = Just sch
       , uriAuthority = Left True -- absolute path
       , uriPath   = Just (False, path)
       , uriQuery  = []
       , uriFragment = Nothing
       }


-- External Constants ----------------------------------------------------------

type VarIndex = Int

-- | An external constant with a name.
-- Names are not necessarily unique, but the var index should be.
data ExtCns e =
  EC
  { ecVarIndex :: !VarIndex
  , ecName :: !NameInfo
  , ecType :: !e
  }
  deriving (Show, Functor, Foldable, Traversable)

instance Eq (ExtCns e) where
  x == y = ecVarIndex x == ecVarIndex y

instance Ord (ExtCns e) where
  compare x y = compare (ecVarIndex x) (ecVarIndex y)

instance Hashable (ExtCns e) where
  hashWithSalt x ec = hashWithSalt x (ecName ec)


scFreshNameURI :: Text -> VarIndex -> URI
scFreshNameURI nm i = fromMaybe (panic "scFreshNameURI" ["Failed to construct name URI: <> " <> nm <> "  " <> Text.pack (show i)]) $
  do sch <- mkScheme "fresh"
     nm' <- mkPathPiece (if Text.null nm then "_" else nm)
     i'  <- mkFragment (Text.pack (show i))
     pure URI
       { uriScheme = Just sch
       , uriAuthority = Left False -- relative path
       , uriPath   = Just (False, (nm' :| []))
       , uriQuery  = []
       , uriFragment = Just i'
       }


-- Display Name Environments --------------------------------------------------------

-- | A 'DisplayNameEnv' encodes the mappings between display names (type
-- 'Text') and internal names (type 'VarIndex'). Multiple display
-- names may be associated with each internal name; these are stored
-- in priority order, with preferred display names first.
data DisplayNameEnv =
  DisplayNameEnv
  { displayNames :: !(IntMap [Text]) -- Keyed by VarIndex; preferred names come first.
  , displayIndexes :: !(Map Text IntSet)
  }
-- Invariants: The 'displayNames' and 'displayIndexes' maps should be
-- inverses of each other. That is, 'displayNames' maps @i@ to a list
-- containing @x@ if and only if 'displayIndexes' maps @x@ to a set
-- containing @i@.

emptyDisplayNameEnv :: DisplayNameEnv
emptyDisplayNameEnv = DisplayNameEnv mempty mempty

-- | Extend a 'DisplayNameEnv' by providing new 'Text' display names
-- for a given 'VarIndex'. Display names should be provided in
-- priority order, with preferred names first. If the 'VarIndex'
-- already exists in the map, then add the new display names with
-- higher priority while keeping the old ones.
extendDisplayNameEnv :: VarIndex -> [Text] -> DisplayNameEnv -> DisplayNameEnv
extendDisplayNameEnv i aliases env =
  DisplayNameEnv
  { displayNames = IntMap.insertWith List.union i aliases (displayNames env)
  , displayIndexes = foldr insertAlias (displayIndexes env) aliases
  }
  where
    insertAlias :: Text -> Map Text IntSet -> Map Text IntSet
    insertAlias x m = Map.insertWith IntSet.union x (IntSet.singleton i) m

-- | Filter display names in a 'DisplayNameEnv' that satisfy a predicate.
filterDisplayNameEnv :: (Text -> Bool) -> DisplayNameEnv -> DisplayNameEnv
filterDisplayNameEnv p env =
  DisplayNameEnv
  { displayNames = IntMap.filter (not . null) $ fmap (filter p) $ displayNames env
  , displayIndexes = Map.filterWithKey (\k _ -> p k) $ displayIndexes env
  }

-- | Merge two 'DisplayNameEnv's, giving higher priority to display
-- names from the first argument.
mergeDisplayNameEnv :: DisplayNameEnv -> DisplayNameEnv -> DisplayNameEnv
mergeDisplayNameEnv env1 env2 =
  DisplayNameEnv
  { displayNames = IntMap.unionWith List.union (displayNames env1) (displayNames env2)
  , displayIndexes = Map.unionWith IntSet.union (displayIndexes env1) (displayIndexes env2)
  }

-- | Look up a 'Text' display name in an environment, returning the
-- list of indexes it could resolve to.
resolveDisplayName :: DisplayNameEnv -> Text -> [VarIndex]
resolveDisplayName env x =
  case Map.lookup x (displayIndexes env) of
    Nothing -> []
    Just s -> IntSet.elems s

-- | Return the first display name for the given 'VarIndex' that is
-- unambiguous in the naming environment. If there is no unambiguous
-- alias, then return 'Nothing'.
bestDisplayName :: DisplayNameEnv -> VarIndex -> Maybe Text
bestDisplayName env i =
  do aliases <- IntMap.lookup i (displayNames env)
     go aliases
  where
    go [] = Nothing
    go (x : xs) =
      case Map.lookup x (displayIndexes env) of
        Nothing -> panic "bestDisplayName" ["Invariant violated: Missing key " <> x]
        Just vs
          | IntSet.size vs == 1 -> Just x
          | otherwise -> go xs
