{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Worker where

import Control.Concurrent (myThreadId)
import Control.Concurrent.STM (TChan, TVar, atomically, readTVarIO, writeTChan, writeTVar)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, StateT, evalStateT, gets, modify)
import Control.Monad.Trans (lift)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Message (Result (..))
import SAWScript.AST
import SAWScript.AST qualified as SAW
import SAWScript.Value qualified as SAW
import SAWT.Checkpoint (Checkpoint (..), Checkpoints, Script)
import SAWT.Checkpoint qualified as C
import Logging qualified as L
import SAWT.State (SAWT)
import SAWT.State qualified as SAWT
import Util.FList (FList (..), after, fingers)

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

alertResponder :: Result -> Worker ()
alertResponder res =
  do
    chan <- gets wsResultChan
    liftIO (atomically (writeTChan chan res))

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

getCheckpoints :: Worker Checkpoints
getCheckpoints =
  do
    cksVar <- gets wsCheckpoints
    liftIO (readTVarIO cksVar)

putCheckpoints :: Checkpoints -> Worker ()
putCheckpoints cks =
  do
    cksVar <- gets wsCheckpoints
    liftIO (atomically (writeTVar cksVar cks))

findCheckpoint :: Script -> Worker (Maybe Checkpoint)
findCheckpoint script =
  do
    cks <- getCheckpoints
    pure (C.findCheckpoint cks script)

createCheckpoint :: SAW.Value -> [String] -> Worker Checkpoint
createCheckpoint value output =
  do
    sawCheckpoint <- liftSAW SAWT.createSAWCheckpoint
    pure (C.createCheckpoint sawCheckpoint value output)

cacheCheckpoint :: Script -> Checkpoint -> Worker ()
cacheCheckpoint script ck =
  do
    cks <- getCheckpoints
    let cks' = C.addCheckpoint script ck cks
    putCheckpoints cks'

restoreCheckpoint :: Checkpoint -> Worker ()
restoreCheckpoint Checkpoint {..} = liftSAW (SAWT.restoreSAWCheckpoint ckEnv)

--------------------------------------------------------------------------------

-- what do we want workers to be able to do?
-- - [x] Interpret scripts, populating the shared memory along the way
-- - [ ] Signal progress
-- - [ ] Signal errors
-- - [x] Signal results

interpretSAWScript :: [Stmt] -> Worker ()
interpretSAWScript stmts =
  do
    case stmts of
      [] -> pure ()
      (s : ss) ->
        do
          checkpoint <- interpretSAWScriptNE (s :| ss)
          -- the checkpoint has already been cached, but we'll need to unpack it
          -- to display the goal
          alertResponder (Success "finished interpreting script")

interpretSAWScriptNE :: NonEmpty Stmt -> Worker Checkpoint
interpretSAWScriptNE stmts@(s :| ss) =
  do
    cks <- getCheckpoints
    case longestCachedPrefix cks (s : ss) of
      Nothing -> interpretSAWStmts stmts
      Just (ck, rest) ->
        do
          restoreCheckpoint ck
          case rest of
            [] -> pure ck
            (r : rs) -> interpretSAWStmts (r :| rs)

interpretSAWStmts :: NonEmpty Stmt -> Worker Checkpoint
interpretSAWStmts stmts = NE.last <$> mapM interpretSAWStmt stmts

-- | According to the checkpoints we have available, what is the longest prefix
-- of the provided script that we've already interpreted?
longestCachedPrefix :: Checkpoints -> [SAW.Stmt] -> Maybe (Checkpoint, [SAW.Stmt])
longestCachedPrefix checks stmts = go (orderedPartitions stmts)
  where
    go partitions =
      case partitions of
        [] -> Nothing
        (flist : ss) ->
          let context = prefix flist
           in -- leaky Script abstraction here...
              case C.findCheckpoint checks (C.Script context) of
                Just ck -> Just (ck, after flist)
                Nothing -> go ss

-- | All partitions (prefix-suffix pairs, represented here as FLists) of the
-- statement list, in descending order of prefix length
orderedPartitions :: [SAW.Stmt] -> [FList SAW.Stmt]
orderedPartitions = reverse . fingers

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
