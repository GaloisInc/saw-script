-- |
-- Module      :  SAWVersion.Version
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  saw@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

module SAWVersion.Version (
    versionText
  , shortVersionText
  ) where

import Paths_saw (version)
import SAWVersion.GitRev (foundGit, hash, branch)
import Data.Version (showVersion)

gitText :: String
gitText =
    if foundGit then
        case (hash, branch) of
            (Nothing, Nothing) -> "<non-dev build>"
            (Just h, Nothing) -> h ++ " <unknown-branch>"
            (Nothing, Just b) -> "<unknown-hash> " ++ b
            (Just h, Just b) -> h ++ " " ++ b
    else
        "<VCS-less build>"

shortVersionText :: String
shortVersionText = showVersion version ++ " (" ++ gitText ++ ")"

versionText :: String
versionText = "version " ++ shortVersionText
