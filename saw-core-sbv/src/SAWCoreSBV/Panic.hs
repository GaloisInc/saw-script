{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWCoreSBV.Panic
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

-- Panic hooks. See SAWSupport.PanicSupport for discussion.

module SAWCoreSBV.Panic (panic) where

import Data.Text (Text)

import SAWSupport.PanicSupport

panic :: HasCallStack => Text -> [Text] -> a
panic loc msgs = doPanic "saw-core-sbv" loc msgs
