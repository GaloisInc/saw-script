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
import SAWScript.AST (Stmt)
import SAWT.Checkpoint (Checkpoints)
import Worker (Worker, interpretSAWScript, mkWorkerState, runWorker)

data WorkerGovernorState = WorkerGovernorState
  { wgInput :: TChan Action,
    wgFresh :: Int,
    wgThreads :: Map ThreadHandle ThreadId,
    wgCheckpoints :: TVar Checkpoints,
    wgOutput :: TChan Result
  }

newWorkerGovernorState :: TChan Action -> TChan Result -> IO WorkerGovernorState
newWorkerGovernorState aChan rChan =
  do
    cks <- newTVarIO mempty
    pure
      WorkerGovernorState
        { wgInput = aChan,
          wgFresh = 0,
          wgThreads = mempty,
          wgOutput = rChan,
          wgCheckpoints = cks
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
    st <- newWorkerGovernorState actionChannel resultChannel
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
        Interpret stmts -> interpret stmts
        Kill tID -> kill tID
    writeResult result

spawn :: WorkerGovernor Result
spawn =
  do
    tID <- liftIO (forkIO (forever (threadDelay 1_000_000)))
    tHandle <- registerThread tID
    pure (Pending tHandle)

interpret :: [Stmt] -> WorkerGovernor Result
interpret stmts =
  do
    tID <- forkWorker (interpretSAWScript stmts)
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

forkWorker :: Worker a -> WorkerGovernor ThreadId
forkWorker action =
  do
    rChan <- gets wgOutput
    ckVar <- gets wgCheckpoints
    let st = mkWorkerState ckVar rChan
    liftIO (forkIO (void (actAndReport st rChan)))
  where
    actAndReport state chan =
      do
        result <- runWorker action state
        atomically $
          writeTChan chan $
            case result of
              Left err -> Failure err
              Right res -> Success "worker finished"

--------------------------------------------------------------------------------

logName :: String
logName = "WorkerGovernor"

debug :: String -> WorkerGovernor ()
debug = L.debug logName
