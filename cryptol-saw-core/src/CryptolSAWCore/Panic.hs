{-# LANGUAGE OverloadedStrings #-}

module CryptolSAWCore.Panic (panic) where

import Data.Text (Text)

import SAWSupport.PanicSupport

-- | Raise a fatal error. See commentary in PanicSupport.
--   Arguments are "location" (one string) and "description" (multiple
--   strings).
panic :: HasCallStack => Text -> [Text] -> a
panic loc msgs = doPanic "cryptol-saw-core" loc msgs
