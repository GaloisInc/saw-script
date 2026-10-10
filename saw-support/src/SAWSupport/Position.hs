{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWSupport.Console
Description : Console messages and error printing infrastructure
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

This module contains infrastructure for dealing with source positions.
-}

module SAWSupport.Position (
    IsPosition(..)
  )
  where

import Data.Text (Text)

import qualified Prettyprinter as PP

import qualified SAWSupport.Pretty as PPS


-- | Class that labels source position types and provides a common
--   print interface for them.
class IsPosition t where
    -- Either function is sufficient to define the other.
    --
    -- There's an implicit assumption here that the printing options
    -- don't affect the way positions print. If that changes, the
    -- interface should change accordingly.

    {-# MINIMAL ppPosition | prettyPosition #-}
    ppPosition :: t -> Text
    prettyPosition :: t -> PPS.Doc

    -- | Print a position to a `PPS.Doc`.
    ppPosition pos = PPS.renderText PPS.defaultOpts $ prettyPosition pos
    -- | Print a position to `Text`.
    prettyPosition pos = PP.pretty $ ppPosition pos

