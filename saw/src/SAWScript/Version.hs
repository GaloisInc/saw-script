-- |
-- Module      :  SAWScript.Version
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  saw@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

module SAWScript.Version (
    hashText
  , versionText
  , shortVersionText
  ) where

-- import Paths_saw_script (version)
-- import GitRev (hash)
-- import Data.Version (showVersion)

hash :: String
hash = "<nice try>"

hashText :: String
hashText = " (" ++ hash ++ ")"

versionText :: String
versionText = "version " ++ shortVersionText

shortVersionText :: String
shortVersionText = {- showVersion version ++  -}hashText
