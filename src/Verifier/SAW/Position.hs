module Verifier.SAW.Position
  ( Pos(..)
  , incLine
  , incCol
  , ppPos
  , Positioned(..)
  ) where

import System.FilePath (makeRelative)

data Pos = Pos { posPath  :: !FilePath
               , posLine  :: !Int
               , posCol   :: !Int
               }
  deriving (Eq, Show)

ppPos :: FilePath -> Pos -> String
ppPos bp p = rp ++ ':' : show (posLine p) ++ ':' : show (posCol p) ++ ":"
  where rp = makeRelative bp (posPath p)

incLine :: Pos -> Pos
incLine p = p { posLine = 1 + posLine p, posCol = 0 }

incCol :: Pos -> Pos
incCol p = p { posCol = 1 + posCol p }

data Positioned v = Positioned { pos :: !Pos, val :: !v }
  deriving (Functor, Show)
