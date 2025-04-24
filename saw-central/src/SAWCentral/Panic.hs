{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWCentral.Panic
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}

module SAWCentral.Panic
  (HasCallStack, panic) where

import qualified Data.Text as Text
--import Data.Text (Text)

import SAWSupport.PanicSupport

-- | Raise a fatal error. See commentary in PanicSupport.
--   Arguments are "location" (one string) and "description" (multiple
--   strings).
--
--   For now take String rather than Text. We can update all the call
--   sites to Text later.
panic :: HasCallStack => String -> [String] -> a
panic loc descs = doPanic "saw-central" (Text.pack loc) (map Text.pack descs)
