{-# LANGUAGE OverloadedStrings #-}

module Language.Isabelle.Panic (panic) where

import qualified Data.Text as Text

import SAWSupport.PanicSupport

panic :: HasCallStack => String -> [String] -> a
panic loc msgs = doPanic "saw-core-isabelle" (Text.pack loc) (map Text.pack msgs)