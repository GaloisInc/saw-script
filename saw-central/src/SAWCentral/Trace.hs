{- |
Module      : SAWCentral.Trace
Description : Stack traces for SAW-Script interpreter.
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}
{-# LANGUAGE OverloadedStrings #-}

-- This module should be used as follows:
--    import SAWCentral.Trace (Trace)
--    import qualified SAWCentral.Trace as Trace

module SAWCentral.Trace (
    Trace(),
    empty,
    legacyPush,
    legacyPop,
    ppTrace
 ) where

import Data.Text (Text)
import qualified Data.Text as Text

import SAWCentral.Panic (panic)

-- A stack trace is a list of frames, with the most recent frame at
-- the head of the list.
--
-- In the legacy implementation, each frame is an arbitrary string as
-- cooked up upstream.
newtype Trace = Trace [String]

-- | The starting trace.
empty :: Trace
empty = Trace []

-- | Push a new frame on a trace.
legacyPush :: String -> Trace -> Trace
legacyPush f (Trace fs) = Trace (f : fs)

-- | Pop a frame off a trace.
legacyPop :: Trace -> Trace
legacyPop (Trace t) = case t of
  [] -> panic "Trace.legacyPop" ["Popping empty stack"]
  _ : t' -> Trace t'

-- | Pretty-print a trace. For now, just unlines the strings.
--   Reverse it first so the most recent frame comes out at the
--   bottom.
ppTrace :: Trace -> Text
ppTrace (Trace fs) = Text.pack $ unlines $ reverse fs
