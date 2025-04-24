{-# LANGUAGE OverloadedStrings #-}

module CryptolSAWCore.Panic
 ( panic, unimplemented )
 where

import qualified Data.Text as Text
import Data.Text (Text)

import SAWSupport.PanicSupport

-- | Raise a fatal error. See commentary in PanicSupport.
--   Arguments are "location" (one string) and "description" (multiple
--   strings).
panic :: HasCallStack => Text -> [Text] -> a
panic loc msgs = doPanic "cryptol-saw-core" loc msgs

unimplemented :: HasCallStack => String -> a
unimplemented name = panic "unimplemented" [Text.pack name]
