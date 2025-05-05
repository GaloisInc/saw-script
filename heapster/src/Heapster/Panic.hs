{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : Heapster.Panic
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

-- Panic hooks. See SAWSupport.PanicSupport for discussion.

module Heapster.Panic (panic) where

import qualified Data.Text as Text

import SAWSupport.PanicSupport

-- FUTURE: switch from String to Text. This requires turning on
-- OverloadedStrings, which currently causes thousands of errors in
-- Heapster because of ambiguous prettyprinter instances; that needs
-- to be mopped up first.
panic :: HasCallStack => String -> [String] -> a
panic loc msgs = doPanic "heapster" (Text.pack loc) (map Text.pack msgs)
