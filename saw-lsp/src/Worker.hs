{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}

module Worker where

import Control.Concurrent.STM (TChan, TVar, atomically, modifyTVar', readTVarIO)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, StateT, evalStateT, gets, modify)
import Control.Monad.Trans (lift)
import Message (Result)
import SAWScript.AST
import SAWScript.Value qualified as SAW
import SAWT.Checkpoint (Checkpoint (..), Checkpoints, Script)
import SAWT.Checkpoint qualified as C
import Logging qualified as L
import SAWT.State (SAWT)
import SAWT.State qualified as SAWT

-- Workers are SAW computations that have access to shared memory, which
-- functions as a cache for intermediate results of proof script interpretation.

data WorkerState = WorkerState
  { wsCheckpoints :: TVar Checkpoints,
    wsResultChan :: TChan Result,
    wsScript :: Script
  }

mkWorkerState :: TVar Checkpoints -> TChan Result -> WorkerState
mkWorkerState checkpoints chan =
  WorkerState
    { wsCheckpoints = checkpoints,
      wsResultChan = chan,
      wsScript = C.emptyScript
    }

--------------------------------------------------------------------------------

newtype Worker a = Worker {unWorker :: StateT WorkerState (SAWT IO) a}
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadIO,
      MonadState WorkerState
    )

runWorker :: Worker a -> WorkerState -> IO a
runWorker (Worker action) workerState =
  do
    tid <- myThreadId
    let tnum = last (words (show tid)) -- XXX make better
    L.initializeLogging logName ("worker" <> tnum <> ".log")
    sawEnv <- SAWT.newSAWEnv
    let sawAction = evalStateT action workerState
    SAWT.evalSAWT sawAction sawEnv

liftSAW :: SAWT IO a -> Worker a
liftSAW = Worker . lift

--------------------------------------------------------------------------------

getScript :: Worker Script
getScript = gets wsScript

putScript :: Script -> Worker ()
putScript script = modify (\ws -> ws {wsScript = script})

pushScript :: Stmt -> Worker ()
pushScript stmt =
  do
    script <- getScript
    putScript (C.addStmtToScript stmt script)

--------------------------------------------------------------------------------

findCheckpoint :: Script -> Worker (Maybe Checkpoint)
findCheckpoint script =
  do
    cksVar <- gets wsCheckpoints
    cks <- liftIO (readTVarIO cksVar)
    pure (C.findCheckpoint cks script)

createCheckpoint :: SAW.Value -> [String] -> Worker Checkpoint
createCheckpoint value output =
  do
    sawCheckpoint <- liftSAW SAWT.createSAWCheckpoint
    pure (C.createCheckpoint sawCheckpoint value output)

cacheCheckpoint :: Script -> Checkpoint -> Worker ()
cacheCheckpoint script ck =
  do
    ckVar <- gets wsCheckpoints
    liftIO (atomically (modifyTVar' ckVar (C.addCheckpoint script ck)))

restoreCheckpoint :: Checkpoint -> Worker ()
restoreCheckpoint Checkpoint {..} = liftSAW (SAWT.restoreSAWCheckpoint ckEnv)

--------------------------------------------------------------------------------

-- what do we want workers to be able to do?
-- - [x] Interpret scripts, populating the shared memory along the way
-- - [ ] Signal progress
-- - [ ] Signal errors
-- - [ ] Signal results

interpretSAWStmt :: Stmt -> Worker Checkpoint
interpretSAWStmt stmt =
  do
    debug $ "about to interpret " <> show stmt
    script <- C.addStmtToScript stmt <$> getScript
    checkpoint <- findCheckpoint script
    case checkpoint of
      Nothing ->
        do
          (value, output) <- liftSAW (SAWT.interpretStmt stmt)
          ck <- createCheckpoint value output
          cacheCheckpoint script ck
          putScript script
          pure ck
      Just ck ->
        do
          restoreCheckpoint ck
          putScript script
          pure ck

--------------------------------------------------------------------------------

logName :: String
logName = "Worker"

debug :: String -> Worker ()
debug = L.debug logName
