module Verifier.SAW.Position
  ( Pos(..)
  , ppPos
  , incLine
  , incCol
  , Positioned(..)
  , PosPair(..), val
  ) where

import Data.Monoid
import System.FilePath (makeRelative)

data Pos = Pos { posPath  :: !FilePath
               , posLine  :: !Int
               , posCol   :: !Int
               }
  deriving (Show)

-- Eq instance  overridden to compare positions in the same file more efficiently.
instance Eq Pos where
  (Pos xp xl xc) == (Pos yp yl yc) =
    (xl == yl) && (xc == yc) && (xp == yp)

-- Ord instance  overridden to compare positions in the same file more efficiently.
instance Ord Pos where
  compare (Pos xp xl xc) (Pos yp yl yc) =
    compare xl yl <> compare xc yc <> compare xp yp

ppPos :: FilePath -> Pos -> String
ppPos bp p = rp ++ ':' : show (posLine p) ++ ':' : show (posCol p) ++ ":"
  where rp = makeRelative bp (posPath p)

incLine :: Pos -> Pos
incLine p = p { posLine = 1 + posLine p, posCol = 0 }

incCol :: Pos -> Pos
incCol p = p { posCol = 1 + posCol p }

class Positioned v where
  pos :: v -> Pos

data PosPair v = PosPair !Pos !v
  deriving (Eq, Ord, Functor, Show)

val :: PosPair v -> v
val (PosPair _ v) = v 

instance Positioned (PosPair v) where
  pos (PosPair p _) = p

