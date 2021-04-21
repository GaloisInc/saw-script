{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Main(main) where

import qualified Mir.Language as Mir
import Mir.Compositional (compositionalOverrides)
import Mir.Cryptol (cryptolOverrides)

main :: IO ()
main = Mir.mainWithExtraOverrides $
    compositionalOverrides `Mir.orOverride` cryptolOverrides
