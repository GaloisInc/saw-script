{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : lerkok
-}

{- This module is inspired by NHC's Unlit.hs code; modified and monadified to deal with
   first Cryptol's and then SAWScript's literate style and send back an appropriate
   error message instead of calling error.

   --------------------------------------------------------------------------------
   COPYRIGHT NOTICE as required by the NHC98 distribution:
     Following the copyright notice on: http://www.haskell.org/nhc98/copyright.html;
     this use falls into the category "right to re-use a small number of modules
     of this software which does not perform substantially the same task as this
     software, for instance, by re-using a parser but not the entire compiler."

     Hereby we acknowledge the inspirational use of the Unlit.hs module from the
     NHC98 distribution, which can be freely obtained from "http://www.haskell.org/nhc98"
     Galois retains the rights to this particular module, in accordance with the
     NHC copyright statement as found in "http://www.haskell.org/nhc98/copyright.html"
   --------------------------------------------------------------------------------

   Note that while we were inspired by NHC's Unlit.hs code, the code below is
   significantly rewritten to fit the current needs.
-}

module SAWScript.Unlit (unlitCode, unlitCommands) where

import Control.Monad (liftM)
import Data.Char (isSpace)
import Data.List(isPrefixOf)
import Prelude hiding(lines)

unlitCode :: String -> Either (Int, String) String
unlitCode = unlit "code" True

unlitCommands :: String -> Either (Int, String) String
unlitCommands = unlit "commands" False

unlit :: String -> Bool -> String -> Either (Int, String) String
unlit name allowBirdtracks contents =
    case result of
      OK s     -> Right s
      Fail i s -> Left (i, s)
  where result = do classified <- classify name allowBirdtracks noBeginLine $
                                  zip [1..] $ lines contents id
                    if null [1::Int | Program _ <- classified]
                       then Fail 0 "No code fragments found in literate file"
                       else do  adjacent 1 (head classified) (tail classified)
                                return (unlines (map unclassify classified))

        lines []             acc = [acc []]
        lines ('\^M':'\n':s) acc = acc [] : lines s id      -- DOS
        lines ('\^M':s)      acc = acc [] : lines s id      -- MacOS
        lines ('\n':s)       acc = acc [] : lines s id      -- Unix
        lines (c:s)          acc = lines s (acc . (c:))

data Classified = Program String
                | Blank
                | Comment

noBeginLine :: Int
noBeginLine = -1

insideBlock :: Int -> Bool
insideBlock bl = bl /= noBeginLine

data Exception a = OK a | Fail Int String
instance Monad Exception where
  return         = OK
  OK a     >>= f = f a
  Fail i s >>= _ = Fail i s

classify :: String -> Bool -> Int -> [(Int, String)] -> Exception [Classified]
classify name allowBirdtracks = classify' where
    classify' bl []
        | not (insideBlock bl) = return []
        | otherwise           = Fail bl $ "Unmatched \"\\begin{" ++ name ++ "}\" marker"
    classify' bl ((ln, ('\\':line)):lines)
        | ("begin{" ++ name ++ "}") `isPrefixOf` line
        = if insideBlock bl
          then Fail ln $ "Nested \"\\begin{" ++ name ++ "}\" markers found, earlier start was on line " ++ show bl
          else (Blank:) `liftM` (classify' ln lines)
        | ("end{" ++ name ++ "}") `isPrefixOf` line
        = if insideBlock bl
          then (Blank:) `liftM` (classify' noBeginLine lines)
          else Fail ln $ "\"\\end{" ++ name ++ "}\" marker found with no corresponding begin marker"
        | insideBlock bl
        = (Program line:) `liftM` (classify' bl lines)
        | otherwise
        = (Comment:) `liftM` (classify' bl lines)
    classify' bl ((ln, '>':line):lines)
        | allowBirdtracks && insideBlock bl
        = Fail ln $ "'>' marker found in a \"\\begin{" ++ name ++ "}\" block started on line " ++ show bl
        | allowBirdtracks
        = (Program (' ':line):) `liftM` (classify' bl lines)
    classify' bl ((_, line):lines)
        | insideBlock bl   = (Program line:) `liftM` rest
        | all isSpace line = (Blank:)        `liftM` rest
        | otherwise        = (Comment:)      `liftM` rest
        where rest = classify' bl lines


unclassify :: Classified -> String
unclassify (Program s) = s
unclassify Blank       = ""
unclassify Comment     = ""

adjacent :: Int -> Classified -> [Classified] -> Exception ()
adjacent 1 line lines = adjacent 2 line lines -- force evaluation of line no
adjacent n (Program _) (Comment : _)   = Fail n "program line found before comment line in literate file"
adjacent n Comment     (Program _ : _) = Fail n "comment line found before program line in literate file"
adjacent n _           (line:lines)    = adjacent (n+1) line lines
adjacent _ _           []              = return ()
