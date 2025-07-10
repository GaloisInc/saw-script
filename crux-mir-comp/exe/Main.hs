module Main(main) where

import GHC.IO.Encoding (setLocaleEncoding, utf8)

import qualified Mir.Language as Mir
import Mir.Compositional (compositionalOverrides)
import Mir.Cryptol (cryptolOverrides)
import Mir.State (newMirState)

main :: IO ()
main = do
    setLocaleEncoding utf8
    s <- newMirState
    Mir.mainWithExtraOverrides s $
      compositionalOverrides `Mir.orOverride` cryptolOverrides
