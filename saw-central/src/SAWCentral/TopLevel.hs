{- |
Module      : SAWCentral.TopLevel
Description : TopLevel monad for SAW-Script interpreter.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWCentral.TopLevel
    -- used by SAWCentral.Builtins and a lot of other places
  ( TopLevel(..)
  , TopLevelRO(..)
  , TopLevelRW(..)
    -- used by SAWCentral.Builtins, SAWScript.REPL.Monad, SAWScript.Interpreter,
    --    SAWServer.TopLevel
  , runTopLevel
    -- used by ... a lot of places, let's not try to make a list just yet
  , io
    -- used by SAWCentral.Builtins and basically everywhere else
  , getSharedContext
    -- used by SAWCentral.Builtins, various other places in SAWCentral,
    --    SAWScript.Interpreter
  , getOptions
    -- used in SAWCentral.Crucible.*, SAWCentral.Builtins,
    --    SAWServer.SAWServer, SAWServer.Ghost, SAWServer.LLVMCrucibleSetup
  , getHandleAlloc
    -- used in SAWCentral.Builtins SAWScript.REPL.Monad, SAWScript.AutoMatch
    -- also accessible via SAWCentral.TopLevel
  , getTopLevelRO
    -- used in SAWCentral.Crucible.*.Builtins.hs, SAWCentral.Crucible.X86,
    --    SAWCentral.Bisimulation, SAWCentral.Builtins,
    --    SAWScript.Interpreter, SAWScript.AutoMatch,
    --    SAWServer.Yosys
  , getTopLevelRW
    -- used in SAWCentral.Crucible.LLVM.X86, SAWCentral.Crucible.LLVM.Builtins,
    --    SAWCentral.Builtins, SAWScript.Interpreter
  , putTopLevelRW
    -- used by SAWScript.REPL.Monad
  , makeCheckpoint
    -- used by SAWScript.REPL.Monad
  , restoreCheckpoint
  ) where

import SAWCentral.Value
