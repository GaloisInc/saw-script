{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.Exceptions (TypeErrors(..), failTypecheck) where

import Control.Exception

import SAWScript.Utils


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
