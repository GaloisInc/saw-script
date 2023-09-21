module Responder.Result (Result (..), ThreadHandle, threadHandle) where

newtype ThreadHandle = ThreadHandle Int
  deriving (Eq, Ord)

threadHandle :: Int -> ThreadHandle
threadHandle = ThreadHandle

data Result
  = Pending ThreadHandle
  | Success
  | Failure String
