{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module WorkerGovernor where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad (forever, void)
import Control.Monad.IO.Class
import Control.Monad.State (MonadState, StateT, evalStateT, gets, modify)
import Data.Map (Map)
import Data.Map qualified as Map
import Responder.Result (Result (..), ThreadHandle, threadHandle)

data Action
  = Spawn
  | Kill ThreadHandle

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
  let st = mkWorkerGovernorState actionChannel resultChannel
   in void (forkIO (runWorkerGovernor (forever workerGovernor) st))

workerGovernor :: WorkerGovernor ()
workerGovernor =
  do
    action <- readAction
    result <-
      case action of
        Spawn -> spawn
        Kill tID -> kill tID
    writeResult result

spawn :: WorkerGovernor Result
spawn =
  do
    tID <- liftIO (forkIO (forever (pure ())))
    tHandle <- registerThread tID
    pure (Pending tHandle)

kill :: ThreadHandle -> WorkerGovernor Result
kill tHandle =
  do
    threads <- gets wgThreads
    case threads Map.!? tHandle of
      Nothing -> pure (Failure "thread not found")
      Just tID -> liftIO (killThread tID) >> pure Success
