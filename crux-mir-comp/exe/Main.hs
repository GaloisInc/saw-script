module Main(main) where

import qualified Mir.Language as Mir
import qualified Mir.Compositional as Mir

main :: IO ()
main = Mir.mainWithExtraOverrides Mir.compositionalOverrides
