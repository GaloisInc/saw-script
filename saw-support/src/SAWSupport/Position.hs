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

import qualified SAWSupport.Pretty as PPS

class IsPosition t where
    ppPosition :: t -> Text
    prettyPosition :: t -> PPS.Doc


