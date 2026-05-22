{-# LANGUAGE PatternSynonyms #-}

module Language.Isabelle.Syntax (Syntax(..), Fixity(..), pattern InfixSyn, pattern SymbolSyn ) where

data Fixity = Infix | Prefix | Postfix | Nofix
  deriving (Eq, Ord, Show)

data Syntax =
    MixFix3 String String String
  | MixFix2 String String
  | MixFix1 String String
  | ListSyn Fixity String String String
  | Symbol Fixity String
  | NoSyn
  deriving (Eq, Ord, Show)

pattern InfixSyn :: String -> Syntax
pattern InfixSyn s = Symbol Infix s

pattern SymbolSyn :: String -> Syntax
pattern SymbolSyn s = Symbol Nofix s