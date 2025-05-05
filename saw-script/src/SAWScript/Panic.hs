{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.Panic
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

module SAWScript.Panic (panic) where

import Data.Text (Text)

import SAWSupport.PanicSupport

-- | Raise a fatal error. See commentary in PanicSupport.
--   Arguments are "location" (one string) and "description" (multiple
--   strings).
panic :: HasCallStack => Text -> [Text] -> a
panic loc descs = doPanic "saw-script" loc descs
