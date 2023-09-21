module Responder.Result (Result (..), ThreadHandle, threadHandle) where

newtype ThreadHandle = ThreadHandle Int
  deriving (Eq, Ord, Show)

threadHandle :: Int -> ThreadHandle
threadHandle = ThreadHandle

data Result
  = Pending ThreadHandle
  | Success
  | Failure String
