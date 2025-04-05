{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWCentral.Exceptions
  ( TypeErrors(..), failTypecheck
  , TopLevelException(..)
  , TraceException(..)
  , topLevelExceptionToException
  , topLevelExceptionFromException
  ) where

import Control.Exception
import Data.Typeable (cast)

import What4.ProgramLoc (ProgramLoc)

import SAWCentral.Position (Pos(..))

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
  | forall e. Exception e => SomeTopLevelException e

instance Show TopLevelException where
  show (TopLevelException _ msg) = msg
  show (JavaException _ msg) = msg
  show (CrucibleSetupException _ msg) = msg
  show (OverrideMatcherException _ msg) = msg
  show (LLVMMethodSpecException _ msg) = msg
  show (SomeTopLevelException e) = show e

-- | To use a custom structured exception type that works with the
-- saw-script REPL's exception handlers and stack tracing, define
-- 'toException' as 'topLevelExceptionToException' in the custom
-- exception type's 'Exception' class instance.
topLevelExceptionToException :: Exception e => e -> SomeException
topLevelExceptionToException = toException . SomeTopLevelException

-- | To use a custom structured exception type that works with the
-- saw-script REPL's exception handlers and stack tracing, define
-- 'fromException' as 'topLevelExceptionFromException' in the custom
-- exception type's 'Exception' class instance.
topLevelExceptionFromException :: Exception e => SomeException -> Maybe e
topLevelExceptionFromException x =
  do SomeTopLevelException a <- fromException x
     cast a

instance Exception TopLevelException

data TraceException = TraceException [String] SomeException

instance Show TraceException where
  show (TraceException msg ex) =
    unlines (["Stack trace:"] ++ msg ++ [displayException ex])

instance Exception TraceException
