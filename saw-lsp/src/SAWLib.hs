module SAWLib where

import SAWScript.REPL.Command
import SAWScript.REPL.Monad
import SAWScript.Interpreter (interpretStmt)
import SAWScript.Options (defaultOptions)
import SAWScript.Value
import SAWScript.REPL.Haskeline
import System.Console.Haskeline

sample = 
  do
    -- proof_subshell
    let Just c = parseCommand findCommand "include \"sample.saw\""
        Just c2 = parseCommand findCommand "prove_print (proof_subshell ()) {{ True }}"
    runCommand c
    runCommand c2
  where
    findCommand _ = mempty

run = runREPL False defaultOptions sample


{-
Basing SAW interactions on the REPL work done in `../saw`:
- Receive a (line,col) pair specifying where to break
- Parse the entire file as `[Stmt]` or similar
- Look for the two things (of an appropriate shape/type, probably `Stmt` inside
  `Block` or something similar) that bracket the point
  - If we don't find that the user clicked in a block, probably fail
- Feed all statements prior to the block to the REPL via `interpretStmt`
- Modify the block to include a checkpoint statement and a subshell statement
  - And perhaps to exclude everything after the user's click (other than the
    statement under proof, of course)
- Send the block over via `interpretStmt`


Question: can I wrap the library in an abstraction that does some state-tracking
(i.e. whether or not it's in a subshell) and always (or almost always) exposes a
`String -> IO (Either _ String)` function?


-}
