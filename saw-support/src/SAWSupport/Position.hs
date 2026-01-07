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

class IsPosition t where
    ppPosition :: t -> Text
    prettyPosition :: t -> PPS.Doc

    -- Either function is sufficient to define the other.
    --
    -- There's an implicit assumption here that the printing options
    -- don't affect the way positions print. If that changes, the
    -- interface should change accordingly.
    ppPosition pos = PPS.renderText PPS.defaultOpts $ prettyPosition pos
    prettyPosition pos = PP.pretty $ ppPosition pos

