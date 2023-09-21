module WorkerGovernor where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad (forever, void)
import Responder.Result (Result (..))

data Action
  = Spawn
  | Kill ThreadId

launchWorkerGovernor :: TChan Action -> TChan Result -> IO ()
launchWorkerGovernor actionChannel resultChannel =
  void (forkIO (forever (workerGovernor actionChannel resultChannel)))

workerGovernor :: TChan Action -> TChan Result -> IO ()
workerGovernor actionChannel resultChannel =
  do
    action <- atomically (readTChan actionChannel)
    case action of
      Spawn -> spawn
      Kill tid -> kill tid
  where
    alertResponder = atomically . writeTChan resultChannel
    spawn =
      do
        tid <- forkIO (forever (pure ()))
        alertResponder (Pending tid)
    kill tid =
      do
        killThread tid
        alertResponder Success
