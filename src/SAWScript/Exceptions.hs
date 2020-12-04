{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.Exceptions
  ( TypeErrors(..), failTypecheck
  , TopLevelException(..)
  , TraceException(..)
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
  | LLVMMethodSpecException ProgramLoc String

instance Show TopLevelException where
  show (TopLevelException _ msg) = msg
  show (JavaException _ msg) = msg
  show (CrucibleSetupException _ msg) = msg
  show (OverrideMatcherException _ msg) = msg
  show (LLVMMethodSpecException _ msg) = msg

instance Exception TopLevelException

data TraceException = TraceException String

instance Show TraceException where
  show (TraceException msg) = "Stack trace:\n" ++ msg

instance Exception TraceException
