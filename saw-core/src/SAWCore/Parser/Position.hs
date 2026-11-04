{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWCore.Parser.Position
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Parser.Position
  ( Pos(..)
  , incLine
  , incCol
  , Positioned(..)
  , PosPair(..)
  ) where

import qualified Data.Text as Text
import System.FilePath (makeRelative)

import qualified Language.Haskell.TH.Syntax as TH

import SAWSupport.Position

data Pos = Pos { -- | Base directory to use for pretty printing purposes
                 posBase :: !FilePath
               , posPath  :: !FilePath
               , posLine  :: !Int
               , posCol   :: !Int
               }
  deriving (Show, TH.Lift)

posTuple :: Pos -> (Int,Int,FilePath)
posTuple x = (posLine x, posCol x, posPath x)

-- Eq instance  overridden to compare positions in the same file more efficiently.
instance Eq Pos where
  x == y = posTuple x == posTuple y

-- Ord instance  overridden to compare positions in the same file more efficiently.
instance Ord Pos where
  compare x y = compare (posTuple x) (posTuple y)

instance IsPosition Pos where
  ppPosition p = rp <> ":" <> line <> ":" <> col
    where rp = Text.pack $ makeRelative (posBase p) (posPath p)
          line = Text.pack $ show (posLine p)
          col = Text.pack $ show (posCol p)

incLine :: Pos -> Pos
incLine p = p { posLine = 1 + posLine p, posCol = 0 }

incCol :: Pos -> Pos
incCol p = p { posCol = 1 + posCol p }

class Positioned v where
  pos :: v -> Pos

data PosPair v = PosPair { _pos :: !Pos, val :: !v }
  deriving (Eq, Ord, Functor, Show, TH.Lift)

instance Positioned (PosPair v) where
  pos (PosPair p _) = p

