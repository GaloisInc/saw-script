{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use underscore" #-}

module REPL where

import Control.Concurrent (threadDelay)
import Control.Monad (void)
import System.IO
import System.Process
import Text.Printf (printf)
import Prelude hiding (interact, print, putStr, putStrLn)

data REPL s = REPL {replProc :: Process, replState :: s}

data Process = Process
  { pStdin :: Handle,
    pStdout :: Handle,
    pStderr :: Handle,
    pHandle :: ProcessHandle
  }

command :: Process -> String -> IO [String]
command Process {..} cmd =
  do
    hPutStr pStdin cmd
    hPutChar pStdin '\n'
    hFlush pStdin
    readOutput Process {..}

readOutput :: Process -> IO [String]
readOutput Process {..} = lines . reverse <$> go []
  where
    go cur =
      do
        wait_ (hReady pStdout) id
        c <- hGetChar pStdout
        case c of
          '\EOT' -> pure cur
          _ -> go (c : cur)

include :: Process -> FilePath -> IO [String]
include p f = command p (printf "include \"%s\";" f)

wait :: IO a -> (a -> Bool) -> IO a
wait action good = go (1 :: Int)
  where
    go delay
      | delay > maxDelay = error "too long"
      | otherwise =
          do
            threadDelay delay
            result <- action
            if good result
              then pure result
              else go (delay * 2)

    maxDelay = 2 * 1024 * 1024

wait_ :: IO a -> (a -> Bool) -> IO ()
wait_ action good = void (wait action good)

terminate :: Process -> IO ()
terminate Process {..} = cleanupProcess (Just pStdin, Just pStdout, Just pStderr, pHandle)

sawProcess :: CreateProcess
sawProcess = CreateProcess {..}
  where
    cmdspec = RawCommand "/Users/sam/Desktop/projects/do1/saw-script/bin/saw" ["--no-color", "--verbose=lsp"]
    cwd = Nothing
    env = Nothing
    std_in = CreatePipe
    std_out = CreatePipe
    std_err = CreatePipe
    close_fds = True
    create_group = False
    delegate_ctlc = True
    detach_console = False
    create_new_console = False
    new_session = False
    child_group = Nothing
    child_user = Nothing
    use_process_jobs = False

saw :: IO Process
saw =
  do
    (Just pStdin, Just pStdout, Just pStderr, pHandle) <- createProcess sawProcess
    True <- hWaitForInput pStdout 5_000
    let p = Process {..}
    _ <- readOutput p
    pure p

-- proofMode :: String -> ProofScript ()
-- prove_print z3 {{ }};
