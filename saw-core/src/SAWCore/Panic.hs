{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Trustworthy #-}
{- |
Module      : SAWCore.Panic
Copyright   : Galois, Inc. 2012-2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

-- Panic hooks. See SAWSupport.PanicSupport for discussion.

module SAWCore.Panic (panic) where

import Data.Text (Text)

import SAWSupport.PanicSupport

panic :: HasCallStack => Text -> [Text] -> a
panic loc msgs = doPanic "saw-core" loc msgs
