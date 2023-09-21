module WorkerGovernor where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad (forever, void)

data Action
  = Spawn
  | Kill ThreadId

launchWorkerGovernor :: TChan Action -> IO ()
launchWorkerGovernor channel = void (forkIO (forever (workerGovernor channel)))

workerGovernor :: TChan Action -> IO ()
workerGovernor channel =
  do
    action <- atomically (readTChan channel)
    case action of
      Spawn -> forkIO (forever (pure ())) >>= alertResponder
      Kill tid -> killThread tid
  where
    alertResponder = undefined
