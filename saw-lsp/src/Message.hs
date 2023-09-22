module Message where

import SAWScript.AST (Stmt)

newtype ThreadHandle = ThreadHandle Int
  deriving (Eq, Ord, Show)

threadHandle :: Int -> ThreadHandle
threadHandle = ThreadHandle

data Result
  = Pending ThreadHandle
  | DisplayGoal String
  | Success String
  | Failure String
  deriving (Show)

data Action
  = Spawn
  | Interpret [Stmt]
  | Kill ThreadHandle
  deriving (Show)
