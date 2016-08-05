{- |
Module           : $Header$
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.TopLevel
  ( TopLevel(..)
  , TopLevelRO(..)
  , TopLevelRW(..)
  , runTopLevel
  , io
  , getSharedContext
  , getJavaCodebase
  , getOptions
  , getHandleAlloc
  , getTopLevelRO
  , getTopLevelRW
  , putTopLevelRW
  ) where

import SAWScript.Value
