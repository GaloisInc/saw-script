{-# LANGUAGE BlockArguments #-}

module Message where

import Data.Aeson ((.:))
import Data.Aeson qualified as Aeson
import Data.Text (Text)
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
  | Interpret FilePath Text
  | InterpretToPoint FilePath Text Position
  | Kill ThreadHandle
  deriving (Show)

-- Include absolute offset?
data Position = Position
  { line :: Int,
    character :: Int
  }
  deriving (Show)

instance Aeson.FromJSON Position where
  parseJSON = Aeson.withObject "Position" \v ->
    Position <$> v .: "line" <*> v .: "character"
