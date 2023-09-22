{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NumericUnderscores #-}

module WorkerGovernor where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad (forever, void)
import Control.Monad.IO.Class
import Control.Monad.State (MonadState, StateT, evalStateT, gets, modify)
import Data.Map (Map)
import Data.Map qualified as Map
import Logging qualified as L
import Message (Action (..), Result (..), ThreadHandle, threadHandle)

data WorkerGovernorState = WorkerGovernorState
  { wgInput :: TChan Action,
    wgFresh :: Int,
    wgThreads :: Map ThreadHandle ThreadId,
    wgOutput :: TChan Result
  }

mkWorkerGovernorState :: TChan Action -> TChan Result -> WorkerGovernorState
mkWorkerGovernorState aChan rChan =
  WorkerGovernorState
    { wgInput = aChan,
      wgFresh = 0,
      wgThreads = mempty,
      wgOutput = rChan
    }

newtype WorkerGovernor a = WorkerGovernor
  { unWorkerGovernor :: StateT WorkerGovernorState IO a
  }
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadIO,
      MonadState WorkerGovernorState
    )

runWorkerGovernor :: WorkerGovernor a -> WorkerGovernorState -> IO a
runWorkerGovernor (WorkerGovernor action) = evalStateT action

readAction :: WorkerGovernor Action
readAction =
  do
    input <- gets wgInput
    liftIO (atomically (readTChan input))

writeResult :: Result -> WorkerGovernor ()
writeResult res =
  do
    output <- gets wgOutput
    liftIO (atomically (writeTChan output res))

registerThread :: ThreadId -> WorkerGovernor ThreadHandle
registerThread tid =
  do
    handle <- gets (threadHandle . wgFresh)
    modify
      \WorkerGovernorState {..} ->
        WorkerGovernorState
          { wgFresh = succ wgFresh,
            wgThreads = Map.insert handle tid wgThreads,
            ..
          }
    pure handle

launchWorkerGovernor :: TChan Action -> TChan Result -> IO ()
launchWorkerGovernor actionChannel resultChannel =
  do
    L.initializeLogging logName "worker-governor.log"
    let st = mkWorkerGovernorState actionChannel resultChannel
    void (forkIO (runWorkerGovernor (forever workerGovernor) st))

workerGovernor :: WorkerGovernor ()
workerGovernor =
  do
    debug "ready to read action"
    action <- readAction
    debug $ "read " <> show action
    result <-
      case action of
        Spawn -> spawn
        Kill tID -> kill tID
    writeResult result

spawn :: WorkerGovernor Result
spawn =
  do
    tID <- liftIO (forkIO (forever (threadDelay 1_000_000)))
    tHandle <- registerThread tID
    pure (Pending tHandle)

kill :: ThreadHandle -> WorkerGovernor Result
kill tHandle =
  do
    threads <- gets wgThreads
    case threads Map.!? tHandle of
      Nothing -> pure (Failure "thread not found")
      Just tID -> liftIO (killThread tID) >> pure (Success "thread killed")

--------------------------------------------------------------------------------

logName :: String
logName = "WorkerGovernor"

debug :: String -> WorkerGovernor ()
debug = L.debug logName
