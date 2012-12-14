-- | Provides utility functions about general data structured used by SAW.
-- Declarations here should refer primarily to terms defined in other packages.
-- SAW-specific declarations should be stored in separate modules.
module Verifier.SAW.Utils 
  ( module Data.Foldable
  , sumBy
  ) where

import Data.Foldable

sumBy :: (Foldable t, Num b) => (a -> b) -> t a -> b
sumBy f = foldl' fn 0
  where fn e v = e + f v

