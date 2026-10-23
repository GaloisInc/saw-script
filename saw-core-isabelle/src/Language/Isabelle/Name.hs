{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Isabelle.Name
  ( IsaKind(..)
  , isTypeK
  , Name(..)
  , TheoryName
  , pattern TheoryName
  , pattern Name
  , nmQual
  , thyNm
  , thyQualified
  , HasName(..)
  , HasIdent(..)
  , variants
  , cleanName
  , guardUnderscores
  , freshIdent
  , qualifiedIdent
  ) where

import           Data.List (stripPrefix, intercalate)

import qualified Cryptol.TypeCheck.PP as Cry

import           Language.Isabelle.Syntax (Syntax, pattern InfixSyn)
import           Language.Isabelle.Output (Output,HasOutput,out)


type Ident = String

replace :: String -> String -> String -> String
replace _ _ [] = []
replace inp outp src@(hd:tl) =
  let (hdr,rest) = splitAt (length inp) src
  in case hdr == inp of
    True -> outp ++ replace inp outp rest
    False -> hd : replace inp outp tl

cleanTheoryName :: Ident -> Ident
cleanTheoryName i = replace "::" "_" i

data TheoryName = TheoryNameCtr { thyNm :: Ident, thyQualified :: Bool }
  deriving (Eq, Ord)

instance Show TheoryName where
  show nm = thyNm nm

pattern TheoryName :: Ident -> Bool -> TheoryName
pattern TheoryName nm b <- TheoryNameCtr nm b where
  TheoryName nm b = TheoryNameCtr (cleanTheoryName nm) b


class HasIdent t where
  identOf :: t -> Ident
  default identOf :: (HasName t) => t -> Ident
  identOf t = cleanName (nameOf t)

  mapIdent :: (Ident -> Ident) -> t -> t
  default mapIdent :: (HasName t) => (Ident -> Ident) -> t -> t
  mapIdent f = mapName (\nm -> nm { nmStr = f (nmStr nm) })


instance HasIdent TheoryName where
  identOf = thyNm
  mapIdent f t = t { thyNm = f (thyNm t) }

data IsaKind = Term | Typ | TNum
  deriving (Eq, Ord, Show)

isTypeK :: IsaKind -> Bool
isTypeK = \case
  Term -> False
  Typ -> True
  TNum -> True

data Name =
    QName { nmThy :: TheoryName, nmStr :: Ident, nmQual_ :: [Ident], nmSyn :: Syntax, nmKind :: IsaKind  }
  | SimpleName { nmStr :: Ident }
  deriving (Eq, Ord, Show)

nmQual :: Name -> [Ident]
nmQual nm = case nm of
  QName{} -> nmQual_ nm
  SimpleName{} -> []

pattern Name :: TheoryName -> Ident -> Syntax -> IsaKind -> Name
pattern Name nmThy nmStr nmSyn nmKind = QName nmThy nmStr [] nmSyn nmKind

instance HasName Name where
  nameOf nm = nm
  mapName f = f

instance HasIdent Name

thyQual :: (HasOutput, Output t) => TheoryName -> t -> String
thyQual thy t = case thyQualified thy of
  True -> thyNm thy ++ "." ++ out t
  False -> out t

class HasName t where
  nameOf :: t -> Name
  mapName :: (Name -> Name) -> t -> t

qualifiedIdent :: HasName t => t -> String
qualifiedIdent t = case nameOf t of
  nm@QName{} -> thyNm (nmThy nm) ++ "." ++ cleanName nm
  nm@SimpleName{} -> cleanName nm

keywords :: [String]
keywords = ["mod", "div", "xor", "undefined", "in"]

stripSuffix :: Eq a => [a] -> [a] -> Maybe [a]
stripSuffix suf l = case stripPrefix suf (reverse l) of
  Just l' -> Just (reverse l')
  Nothing -> Nothing

guardKeywords :: String -> String
guardKeywords s = if elem s keywords then
  s ++ "'"
  else case stripSuffix "'" s of
    Just s' -> guardKeywords s' ++ "'"
    Nothing -> s

symbolOverrides :: String -> String
symbolOverrides s = case s of
  "==>" -> "\\<longrightarrow>"
  "/\\\\" -> "\\<and>"
  "\\\\/" -> "\\<or>"
  _ -> s

cleanPrefix :: String -> String -> Ident -> Ident
cleanPrefix pref repl s = case stripPrefix pref s of
  Just s' -> repl ++ s'
  -- avoid name clashes with things already prefixed with the replacement
  Nothing -> case stripPrefix repl s of
    Just{} -> repl ++ s
    Nothing -> s

cleanSuffix :: String -> String -> Ident -> Ident
cleanSuffix pref repl s = case stripSuffix pref s of
  Just s' -> s' ++ repl
  -- avoid name clashes with things already suffixed with the replacement
  Nothing -> case stripSuffix repl s of
    Just{} -> s ++ repl
    Nothing -> s

cleanSymbol :: Char -> String
cleanSymbol c = case c of
  '(' -> "lb"
  ')' -> "rb"
  ' ' -> "_"
  '<' -> "lt"
  '>' -> "gt"
  '=' -> "eq"
  _ -> [c]

cleanNameSymbols :: Ident -> Ident
cleanNameSymbols s = concat $ map cleanSymbol s

cleanIdent :: String -> Ident
cleanIdent str = symbolOverrides
   $ guardBackslash
   $ cleanPrefix "_" "i_"
   $ cleanPrefix "$" "s_"
   $ cleanSuffix "_" "_U"
   $ cleanNameSymbols
   $ guardKeywords str

pathIdent :: String -> String
pathIdent [] = []
pathIdent (p:ps) = ("\\<^sub>" ++ [p]) ++ pathIdent ps

cleanName :: Name -> Ident
cleanName nm = cleanIdent (nmStr nm) ++
  intercalate "_" (map (pathIdent . cleanIdent) (nmQual nm))

guardUnderscores :: Ident -> Ident
guardUnderscores i = concat $ map go i
  where
    go :: Char -> String
    go c = case [c] of
      "_" -> "'_"
      s -> s

guardBackslash :: Ident -> Ident
guardBackslash i = concat $ map go i
  where
    go :: Char -> String
    go c = case [c] of
      "\\" -> "\\\\"
      s -> s

-- | Infinite list of name variants.
variants :: Name -> [Name]
variants nm = map (\nm_ -> nm { nmStr = pref ++ nm_ }) (Cry.nameList baseNms)
  where
    baseNms = case nmStr nm of
      "" -> []
      "'" -> []
      _ -> [nmStr nm]
    pref = case nmStr nm of
      "'" -> "'"
      _ -> ""

-- | Infinite list of identifier variants
variantIdents :: Ident -> [Ident]
variantIdents nm = (map (\suf -> nm ++ suf) (Cry.nameList []))

-- | Returns a variant of a name that does not clash with the given list
freshIdent ::
  [Ident] {- ^ existing identifiers -} ->
  Ident {- ^ prospective name -} ->
  Ident
freshIdent exNms tryNm = go (tryNm:variantIdents tryNm)
  where
    go :: [String] -> String
    go (nm:nms) | nm `elem` exNms = go nms
    go (nm:_) = nm
    go [] = error "freshIdent: impossible empty list"

instance Output Name where
  out t = case t of
    QName{} -> case nmSyn t of
      InfixSyn s -> symbolOverrides $ guardBackslash $ s
      _ -> thyQual (nmThy t) (cleanName t)
    SimpleName{} -> cleanName t
