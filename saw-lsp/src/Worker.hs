{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Worker where

import Control.Concurrent (myThreadId)
import Control.Concurrent.STM (TChan, TVar, atomically, readTVarIO, writeTChan, writeTVar)
import Control.Monad (when)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, StateT, evalStateT, gets, modify)
import Control.Monad.Trans (lift)
import Data.Bifunctor (first)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as Text
import Logging qualified as L
import Message (Position, Result (..))
import SAWScript.AST
import SAWScript.AST qualified as SAW
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser (parseModule)
import SAWScript.Value qualified as SAW
import SAWT.Checkpoint (Checkpoint (..), Checkpoints, Script)
import SAWT.Checkpoint qualified as C
import SAWT.Monad (SAWT)
import SAWT.Monad qualified as SAWT
import Util.FList (FList (..), after, fingers)
import Worker.Truncate (truncateScript)

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

newtype Worker a = Worker {unWorker :: StateT WorkerState (ExceptT String (SAWT IO)) a}
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadIO,
      MonadError String,
      MonadState WorkerState
    )

runWorker :: Worker a -> WorkerState -> IO (Either String a)
runWorker (Worker action) workerState =
  do
    tnum <- last . words . show <$> myThreadId -- XXX make better
    L.initializeLogging logName ("worker-" <> tnum <> ".log")
    let exceptAction = evalStateT action workerState
        sawAction = runExceptT exceptAction
    sawEnv <- SAWT.newSAWEnv
    SAWT.evalSAWT sawAction sawEnv

liftSAW :: SAWT IO a -> Worker a
liftSAW = Worker . lift . lift

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

parseSAWFile :: FilePath -> Text -> Either String [Stmt]
parseSAWFile path text =
  do
    let lexed = lexSAW path (Text.unpack text)
    first show (parseModule lexed)

-- | If provided a position, interpret only the script truncated at that
-- position and send a DisplayGoal message on completion
interpretSAWScript :: FilePath -> Text -> Maybe Position -> Worker ()
interpretSAWScript filePath fileText position =
  do
    stmts <- case parseSAWFile filePath fileText of
      Left err -> throwError err
      Right ss -> pure ss
    let stmts' =
          case position of
            Nothing -> stmts
            Just p -> truncateScript p "XXX" stmts
    case stmts' of
      [] -> throwError "empty script"
      (s : ss) ->
        do
          Checkpoint {..} <- interpretSAWScriptNE (s :| ss)
          let output = intercalate "\n" ckOutput
          when (isJust position) (alertResponder (DisplayGoal output))

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
    debug "about to interpret stmt"
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
