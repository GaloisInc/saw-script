{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.REPL
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWScript.REPL (run, reenterTopLevel, reenterProofScript) where

import Control.Monad (unless)
import Data.Maybe (isJust)

import SAWCentral.Options (Options(..))
import SAWCentral.Proof (ProofState)
import SAWCentral.Value (TopLevelRO, TopLevelRW)

import SAWScript.Panic (panic)
import SAWScript.REPL.Logo (displayLogo)
import SAWScript.REPL.Monad (initREPL, resumeREPL, runREPL, REPLState(..))
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
  rst <- initREPL batchmode opts reenterTopLevel reenterProofScript
  (_result, _rst') <- runREPL (repl mfile) rst
  return ()

-- | Function to enter a nested TopLevel REPL, passed down into the interpreter
--   to avoid cyclic dependencies.
--
--   Note that there isn't any REPL state that needs to be transferred to the
--   nested instance, only the interpreter state.
--
reenterTopLevel :: TopLevelRO -> TopLevelRW -> IO TopLevelRW
reenterTopLevel ro rw = do
    let rst = resumeREPL ro rw Nothing
    (_result, rst') <- runREPL (repl Nothing) rst
    return $ rTopLevelRW rst'

-- | Function to enter a nested ProofScript REPL, passed down into the interpreter
--   to avoid cyclic dependencies.
--
--   Note that there isn't any REPL state that needs to be transferred to the
--   nested instance, only the interpreter state.
--
reenterProofScript :: TopLevelRO -> TopLevelRW -> ProofState -> IO (TopLevelRW, ProofState)
reenterProofScript ro rw pst = do
    let rst = resumeREPL ro rw (Just pst)
    (_result, rst') <- runREPL (repl Nothing) rst
    let rw' = rTopLevelRW rst'
        pst' = case rProofState rst' of
          Nothing -> panic "reenterProofScript" ["Proof state disappeared!?"]
          Just ps -> ps
    return (rw', pst')
