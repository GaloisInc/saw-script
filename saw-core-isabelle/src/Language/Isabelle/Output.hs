{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
module Language.Isabelle.Output
  ( Output(..)
  , HasOutput
  , indent
  , withTemplates
  , getTemplate
  , brackets
  , quotes
  , cartouche
  , line
  , lines
  , addSep
  , spaces
  ) where

import Prelude hiding (lines)

import qualified Data.Map as Map
import           Data.Map ( Map )

import qualified Language.Isabelle.Template as Template
import qualified Language.Isabelle.Panic as Panic

data OutputData =
  OutputData { curIndent :: Int, prevIndent :: Int, templates :: Map String Template.Template}

noOutputData :: OutputData
noOutputData = OutputData 0 0 Map.empty

type HasOutput = (?outputData :: OutputData)

class Output t where
  out  :: HasOutput => t -> String

instance Output String where
  out = id

indent :: HasOutput => Int -> (HasOutput => t) -> t
indent i f =
    let
      old_data = ?outputData
      old_indent = curIndent old_data
    in let
      ?outputData = old_data { curIndent = (i + old_indent), prevIndent = old_indent }
    in f

withTemplates :: Map String Template.Template -> (HasOutput => t) -> t
withTemplates m f =
  let ?outputData = noOutputData { templates = m} in f

getTemplate :: HasOutput => String -> Template.Template
getTemplate nm = case Map.lookup nm (templates ?outputData) of
  Just template -> template
  Nothing -> Panic.panic "Unexpected missing template" [nm]

brackets :: String -> String
brackets s = "(" ++ s ++ ")"

quotes :: String -> String
quotes s = "\"" ++ s ++ "\""

cartouche :: String -> String
cartouche s = "\\<open>" ++ s ++ "\\<close>"

tab :: Int
tab = 2

getIndent :: HasOutput => Int
getIndent = curIndent ?outputData

line :: HasOutput => String
line = "\n" ++ concat (replicate (getIndent * tab) " ")


prefix_padding :: HasOutput => String
prefix_padding =
  let i = getIndent - (prevIndent ?outputData)
  in if i > 0 then
    concat (replicate (i * tab) " ")
  else ""

lines :: HasOutput => [String] -> String
lines [] = ""
lines [l] = l
lines (l:ls) = prefix_padding ++ l ++ line ++ (indent 0 $ lines ls)

addSep :: String -> [String] -> [String]
addSep _ [] = []
addSep _ [l] = [l]
addSep sep (l:ls) = (l ++ sep):(addSep sep ls)


spaces :: [String] -> String
spaces [s] = s
spaces (s1:s2) = s1 ++ " " ++ (spaces s2)
spaces [] = ""

instance Output Template.Applied where
  out t = show t