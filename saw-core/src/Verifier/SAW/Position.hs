{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveLift #-}

{- |
Module      : Verifier.SAW.Position
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Position
  ( Pos(..)
  , ppPos
  , incLine
  , incCol
  , Positioned(..)
  , PosPair(..)
  ) where

import qualified Language.Haskell.TH.Syntax as TH
import System.FilePath (makeRelative)

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

ppPos :: Pos -> String
ppPos p = rp ++ ':' : show (posLine p) ++ ':' : show (posCol p) ++ ":"
  where rp = makeRelative (posBase p) (posPath p)

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

