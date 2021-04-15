{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Main(main) where

import qualified Mir.Language as Mir
import Mir.Compositional (compositionalOverrides)
import Mir.Cryptol (cryptolOverrides)

main :: IO ()
main = Mir.mainWithExtraOverrides $
    compositionalOverrides `orOverride` cryptolOverrides

orOverride ::
    Mir.BindExtraOverridesFn -> Mir.BindExtraOverridesFn -> Mir.BindExtraOverridesFn
orOverride f g symOnline cs name cfg =
    case f symOnline cs name cfg of
        Just x -> Just x
        Nothing -> g symOnline cs name cfg
