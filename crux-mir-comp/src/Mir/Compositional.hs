{-# Language RankNTypes #-}

module Mir.Compositional
where

import Data.Text (Text)

import Lang.Crucible.Backend
import Lang.Crucible.CFG.Core
import Lang.Crucible.Simulator

import Crux
import Crux.Types

import Mir.Intrinsics
import Mir.Language (BindExtraOverridesFn)

compositionalOverrides ::
    forall args ret blocks sym rtp a r .
    (IsSymInterface sym) =>
    Maybe (SomeOnlineSolver sym) -> Text -> CFG MIR blocks args ret ->
    Maybe (OverrideSim (Model sym) sym MIR rtp a r ())
compositionalOverrides symOnline name cfg
  | otherwise = Nothing

