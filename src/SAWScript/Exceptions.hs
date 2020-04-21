{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.Exceptions
  ( TypeErrors(..), failTypecheck
  , TopLevelException(..)
  ) where

import Control.Exception

import What4.ProgramLoc (ProgramLoc)

import SAWScript.Position (Pos(..))

newtype TypeErrors = TypeErrors [(Pos, String)]

instance Show TypeErrors where
  show (TypeErrors []) = "Unspecified type error"
  show (TypeErrors [(pos, msg)]) = show pos ++ ": " ++ msg
  show (TypeErrors errs) = "Type errors:\n" ++ showErrs errs
    where showErrs = unlines . map showErr
          showErr (pos, msg) = "  " ++ show pos ++ ": " ++ msg

instance Exception TypeErrors where

failTypecheck :: [(Pos, String)] -> a
failTypecheck = throw . TypeErrors

data TopLevelException
  = TopLevelException Pos String
  | JavaException Pos String
  | CrucibleSetupException ProgramLoc String
  | OverrideMatcherException ProgramLoc String
  deriving Show
instance Exception TopLevelException
