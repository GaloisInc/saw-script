{-# LANGUAGE OverloadedStrings #-}

module SAWCoreWhat4.Panic (panic) where

import qualified Data.Text as Text

import SAWSupport.PanicSupport

-- | Raise a fatal error. See commentary in PanicSupport.
--   Arguments are "location" (one string) and "description" (multiple
--   strings).
--
--   For now take String rather than Text. We can update all the call
--   sites to Text later.
panic :: HasCallStack => String -> [String] -> a
panic loc msgs = doPanic "saw-core-what4" (Text.pack loc) (map Text.pack msgs)
