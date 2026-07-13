module Mir.Compositional.Panic where

import Data.Text (Text,pack)

import SAWSupport.PanicSupport

-- | Raise a fatal error. See commentary in PanicSupport.
--   Arguments are "location" (one string) and "description" (multiple
--   strings).
panic :: HasCallStack => Text -> [Text] -> a
panic loc msgs = doPanic (pack "crucible-mir-comp") loc msgs