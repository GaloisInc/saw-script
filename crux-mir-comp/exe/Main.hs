{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Main(main) where

import GHC.IO.Encoding (setLocaleEncoding, utf8)

import qualified Mir.Language as Mir
import Mir.Compositional.State(newMirState)
import Mir.Compositional (compositionalOverrides)
import Mir.Cryptol (cryptolOverrides)

main :: IO ()
main = do
    setLocaleEncoding utf8
    let initUser = Mir.InitUserState newMirState
    Mir.mainWithExtraOverrides initUser $
      compositionalOverrides `Mir.orOverride` cryptolOverrides
