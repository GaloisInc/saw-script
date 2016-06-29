{- |
Module      : Verifier.SAW.Unique
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Unique (getUniqueInt) where

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

globalRef :: IORef Int
{-# NOINLINE globalRef #-}
globalRef = unsafePerformIO (newIORef 0)

-- | Get the next unique integer, and increment the global counter
getUniqueInt :: IO Int
getUniqueInt = atomicModifyIORef' globalRef (\x -> (x+1, x))
