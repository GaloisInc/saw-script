module Server.Reactor (launchReactor, ReactorInput (..)) where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM
import Control.Monad (forever, void)

newtype ReactorInput = ReactorAction (IO ())

launchReactor :: TChan ReactorInput -> IO ()
launchReactor channel = void (forkIO (reactor channel))

reactor :: TChan ReactorInput -> IO ()
reactor channel = forever $ act channel

act :: TChan ReactorInput -> IO ()
act channel =
  do
    ReactorAction action <- atomically $ readTChan channel
    action
