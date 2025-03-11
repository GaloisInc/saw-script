{- |
Module      : SAWCentral.TopLevel
Description : TopLevel monad for SAW-Script interpreter.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWCentral.TopLevel
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

import SAWCentral.Value
