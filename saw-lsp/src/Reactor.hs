module Reactor (reactor, ReactorInput (..)) where

import Control.Concurrent.STM
import Control.Monad (forever)

newtype ReactorInput = ReactorAction (IO ())

reactor :: TChan ReactorInput -> IO ()
reactor channel = forever $ act channel

act :: TChan ReactorInput -> IO ()
act channel =
  do
    ReactorAction action <- atomically $ readTChan channel
    action