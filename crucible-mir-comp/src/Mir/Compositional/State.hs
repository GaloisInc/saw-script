{-# Language ConstraintKinds #-}
{-# Language ImplicitParams #-}
module Mir.Compositional.State where

import Data.IORef
import qualified SAWCore.SharedTerm as SAW

data MirState sym = MirState

type UsesMirState sym = (?mirState :: MirState sym)

newMirState :: IO (MirState sym)
newMirState = pure MirState