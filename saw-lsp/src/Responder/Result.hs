module Responder.Result where

import Control.Concurrent (ThreadId)

data Result
  = Pending ThreadId
  | Success
  | Failure String
