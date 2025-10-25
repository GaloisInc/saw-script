{- |
Module      : SAWScript.REPL
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWScript.REPL (run) where

import Control.Monad (unless)
import Data.Maybe (isJust)

import SAWCentral.Options (Options(..))
import SAWScript.REPL.Logo (displayLogo)
import SAWScript.REPL.Monad (initREPL, runREPL)
import SAWScript.REPL.Haskeline (repl)

-- | Startup function, called from main.
--
--   If a filename is given, the file is loaded and run in batch mode
--   (as if typed into the REPL). Otherwise we take interactive input
--   from stdin.
--
run :: Maybe FilePath -> Options -> IO ()
run mfile opts = do
  let batchmode = isJust mfile
  unless batchmode $
      displayLogo $ useColor opts
  rst <- initREPL batchmode opts
  (_result, _rst') <- runREPL (repl mfile) rst
  return ()
