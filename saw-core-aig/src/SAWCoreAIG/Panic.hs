{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWCoreAIG.Panic
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

-- Panic hooks. See SAWSupport.PanicSupport for discussion.

module SAWCoreAIG.Panic (panic) where

import Data.Text (Text)

import SAWSupport.PanicSupport

panic :: HasCallStack => Text -> [Text] -> a
panic loc msgs = doPanic "saw-core-aig" loc msgs
