{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWSupport.Panic
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}

module SAWSupport.Panic (panic) where

import Data.Text (Text)

import SAWSupport.PanicSupport

-- | Raise a fatal error. See commentary in PanicSupport.
--   Arguments are "location" (one string) and "description" (multiple
--   strings).
panic :: HasCallStack => Text -> [Text] -> a
panic loc descs = doPanic "saw-support" loc descs
