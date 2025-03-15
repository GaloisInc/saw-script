{-# Language DeriveTraversable #-}
{-# Language TemplateHaskell #-}
{-# Options_GHC -Wno-unused-foralls #-}
module Heapster.Located
  ( Located(..),
    Pos(..),
    HasPos(..),
  )where

import Data.Binding.Hobbits

-- | A thing paired with its location
data Located a = Located
  { locPos :: !Pos      -- ^ location
  , locThing :: a       -- ^ thing
  }
  deriving (Functor, Foldable, Traversable, Show)

-- | A position in a text-file
data Pos = Pos
  { posChar :: !Int     -- ^ 0-based absolute index
  , posLine :: !Int     -- ^ 1-based line number
  , posCol  :: !Int     -- ^ 1-based column number
  }
  deriving Show

-- | Convenience class for types of things with a known location
class HasPos a where
  -- | Get contained position
  pos :: a -> Pos

-- | Returns 'locPos'
instance HasPos (Located a) where
  pos = locPos

-- | Returns itself
instance HasPos Pos where
  pos = id

mkNuMatching [t| Pos |]
