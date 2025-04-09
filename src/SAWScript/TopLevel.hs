{- |
Module      : SAWScript.TopLevel
Description : TopLevel monad for SAW-Script interpreter.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
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
  , localOptions
  , putTopLevelRW
  , makeCheckpoint
  , restoreCheckpoint
  ) where

import SAWScript.Value
