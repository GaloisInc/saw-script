{- |
Module      : Verifier.SAW.Name
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
    -- * ExtCns
  , VarIndex
  , ExtCns(..)
  , scFreshNameURI
  , PrimName(..)
    -- * Naming Environments
  , SAWNamingEnv(..)
  , emptySAWNamingEnv
  , registerName
  , resolveURI
  , resolveName
  , bestAlias
  ) where

import           Control.Exception (assert)
import           Data.Char
import           Data.Hashable
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String (IsString(..))
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
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
mkModuleName :: [Text] -> ModuleName
mkModuleName [] = error "internal: mkModuleName given empty module name"
mkModuleName nms = assert (all (isCtor . Text.unpack) nms) $ ModuleName s
  where s = Text.intercalate "." (reverse nms)

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

-- | Parse a fully qualified identifier.
parseIdent :: String -> Ident
parseIdent s0 =
    case reverse (breakEach s0) of
      (_:[]) -> internalError $ "parseIdent given empty module name."
      (nm:rMod) -> mkIdent (mkModuleName (reverse rMod)) nm
      _ -> internalError $ "parseIdent given bad identifier " ++ show s0
  where breakEach s =
          case break (=='.') s of
            (h, []) -> [Text.pack h]
            (h, _ : r) -> Text.pack h : breakEach r

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


-- External Constants ----------------------------------------------------------

type VarIndex = Word64

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
  hashWithSalt x ec = hashWithSalt x (ecVarIndex ec)


-- Primitive Names ------------------------------------------------------------

-- | Names of SAWCore primitives, data types and data type constructors.
data PrimName e =
  PrimName
  { primVarIndex :: !VarIndex
  , primName     :: !Ident
  , primType     :: e
  }
  deriving (Show, Functor, Foldable, Traversable)

instance Eq (PrimName e) where
  x == y = primVarIndex x == primVarIndex y

instance Ord (PrimName e) where
  compare x y = compare (primVarIndex x) (primVarIndex y)

instance Hashable (PrimName e) where
  hashWithSalt x pn = hashWithSalt x (primVarIndex pn)



scFreshNameURI :: Text -> VarIndex -> URI
scFreshNameURI nm i = fromMaybe (panic "scFreshNameURI" ["Failed to constructed name URI", show nm, show i]) $
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


-- Naming Environments ---------------------------------------------------------

data SAWNamingEnv = SAWNamingEnv
  { resolvedNames :: !(Map VarIndex NameInfo)
  , absoluteNames :: !(Map URI VarIndex)
  , aliasNames    :: !(Map Text (Set VarIndex))
  }
-- Invariants: The 'resolvedNames' and 'absoluteNames' maps should be
-- inverses of each other. That is, 'resolvedNames' maps @i@ to @n@ if
-- and only if 'absoluteNames' maps @nameURI n@ to @i@. Also, every
-- 'VarIndex' appearing in 'aliasNames' must be present as a key in
-- 'resolvedNames'.

emptySAWNamingEnv :: SAWNamingEnv
emptySAWNamingEnv = SAWNamingEnv mempty mempty mempty

-- | Add a new name entry in a 'SAWNamingEnv'. Returns 'Left' if
-- there is already an entry under the same URI.
registerName :: VarIndex -> NameInfo -> SAWNamingEnv -> Either URI SAWNamingEnv
registerName i nmi env =
  case Map.lookup uri (absoluteNames env) of
    Just _ -> Left uri
    Nothing ->
      Right $
      SAWNamingEnv
      { resolvedNames = Map.insert i nmi (resolvedNames env)
      , absoluteNames = Map.insert uri i (absoluteNames env)
      , aliasNames    = foldr insertAlias (aliasNames env) aliases
      }
  where
    uri = nameURI nmi
    aliases = render uri : nameAliases nmi

    insertAlias :: Text -> Map Text (Set VarIndex) -> Map Text (Set VarIndex)
    insertAlias x m = Map.insertWith Set.union x (Set.singleton i) m

resolveURI :: SAWNamingEnv -> URI -> Maybe VarIndex
resolveURI env uri = Map.lookup uri (absoluteNames env)

resolveName :: SAWNamingEnv -> Text -> [(VarIndex, NameInfo)]
resolveName env nm =
  case Map.lookup nm (aliasNames env) of
    Nothing -> []
    Just vs -> [ (v, findName v (resolvedNames env)) | v <- Set.toList vs ]
  where
    findName v m =
      case Map.lookup v m of
        Just nmi -> nmi
        Nothing -> panic "resolveName" ["Unbound VarIndex when resolving name", show nm, show v]

-- | Return the first alias (according to 'nameAliases') that is
-- unambiguous in the naming environment. If there is no unambiguous
-- alias, then return the URI.
bestAlias :: SAWNamingEnv -> NameInfo -> Either URI Text
bestAlias env nmi = go (nameAliases nmi)
  where
    go [] = Left (nameURI nmi)
    go (x : xs) =
      case Map.lookup x (aliasNames env) of
        Nothing -> go xs
        Just vs
          | Set.size vs == 1 -> Right x
          | otherwise -> go xs
