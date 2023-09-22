module Message where

newtype ThreadHandle = ThreadHandle Int
  deriving (Eq, Ord, Show)

threadHandle :: Int -> ThreadHandle
threadHandle = ThreadHandle

data Result
  = Pending ThreadHandle
  | Success String
  | Failure String
  deriving (Show)

data Action
  = Spawn
  | Kill ThreadHandle
  deriving (Show)
