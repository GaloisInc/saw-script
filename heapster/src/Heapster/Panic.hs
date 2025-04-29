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

panic :: HasCallStack => String -> [String] -> a
panic loc msgs = doPanic "heapster" (Text.pack loc) (map Text.pack msgs)
