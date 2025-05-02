{- |
Module      : SAWScript.REPL
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWScript.REPL (run, runFromFile) where

import SAWCentral.Options (Options(..))
import SAWScript.REPL.Logo (displayLogo)
import SAWScript.REPL.Haskeline (repl)

-- | Main function
run :: Options -> IO ()
run opts = do
  displayLogo $ useColor opts
  repl Nothing opts (return ())

-- | Alternate main function for batch mode
runFromFile :: FilePath -> Options -> IO ()
runFromFile file opts = do
  repl (Just file) opts (return ())
