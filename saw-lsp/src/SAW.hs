{-# LANGUAGE BlockArguments #-}

module SAW where

import Data.Aeson (withObject, (.:))
import Data.Aeson.Types (FromJSON (parseJSON))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Language.LSP.Types (Uri)
import REPL (Process, include, saw, terminate)
import System.IO (hFlush)
import System.IO.Temp (withSystemTempFile)
import Text.Printf (printf)

{-
REPL as state management

Idea: SAW comes prepackaged with checkpointing facilities, which could make it
easy to leverage the REPL for small to medium proof workloads

Danger: over-reliance on syntactic recognition of a language with enough
higher-order constructs to mask whatever syntax we look for

No "interpret to point", but rather "prove this {{ term }}"?

"Prove term" prompts user dialog to select the statements they wish to include?

Proof minibuf?

If you want to interpret "to point", you must necessarily be in a `[Stmt]`-like
environment

The Dumb Thing
- User requests interpret to point
- Insert "print "<SENTINEL>"; print_goal; <freshvar> <- proof_checkpoint ();
  proof_subshell();" immediately following point
- `include` this file (including all content after point)
- A user inserts another statement (to "ground truth" - i.e. the proof script
  itself) after mark, and interprets again:
  - The REPL is in a position to add this new statement to its context and
    continue, but how can we tell?
    - Recognize that the new point is after the previous point
    - Recognize that the document up to the *previous* point did not change
    - Recognize that the addition parses as a `[Stmt]`
    - *Now* we can just ship this addendum to the REPL linewise
      - And probably pop in another checkpoint

Could be fun to draw some symbols atop the proof script to represent to the user
the checkpoints available to them
- But ideally, I guess this would be opaque
-}

interpretToPoint :: Process -> Text -> Position -> IO Text
interpretToPoint process script posn =
  do
    withSystemTempFile "saw-script" \file handle ->
      do
        Text.hPutStrLn handle script'
        hFlush handle
        result <- include process file
        case dropWhile (/= Text.unpack sentinel) result of
          [] -> error $ "no sentinel: " <> unlines result
          (_ : result') -> pure (Text.pack (unlines result'))
  where
    script' = interruptScript script posn

interpretToPoint' :: FilePath -> Position -> IO Text
interpretToPoint' fp posn =
  do
    sawProc <- saw
    script <- Text.readFile fp
    result <- interpretToPoint sawProc script posn
    terminate sawProc
    pure result

interruptScript :: Text -> Position -> Text
interruptScript sawScript posn = before <> injection <> after
  where
    injection =
      Text.intercalate
        " "
        [ printSentinel,
          printGoal,
          bindCheckpoint freshvar,
          proofSubshell
        ]
    (before, after) = sawScript `splitAtPosn` posn
    freshvar = Text.pack (printf "checkpoint_%x" (hash before))

splitAtPosn :: Text -> Position -> (Text, Text)
splitAtPosn t Position {..} = (before, after)
  where
    before = Text.intercalate "\n" (linesBefore <> [charsBefore])
    after = Text.intercalate "\n" (charsAfter : linesAfter)
    (linesBefore, linesAfter') = splitAt line t'
    (lineToSplit, linesAfter) =
      case linesAfter' of
        [] -> error "no split"
        (l : ls) -> (l, ls)
    (charsBefore, charsAfter) = Text.splitAt character lineToSplit
    t' = Text.lines t

-- TODO
hash :: Text -> Int
hash t = 0xdeadbeef

printSentinel :: Text
printSentinel = "let _ = run (print \"" <> sentinel <> "\");"

sentinel :: Text
sentinel = "~*~*~*~*~*~*~*~*~*~*~*~*~*~*~*~*"

printGoal :: Text
printGoal = "print_goal;"

bindCheckpoint :: Text -> Text
bindCheckpoint freshvar = freshvar <> " <- proof_checkpoint;"

proofSubshell :: Text
proofSubshell = "proof_subshell ();"

data InterpretParams = InterpretParams
  { posn :: Position,
    offset :: Int,
    uri :: Uri
  }
  deriving (Show)

-- Include absolute offset?
data Position = Position
  { line :: Int,
    character :: Int
  }
  deriving (Show)

instance FromJSON InterpretParams where
  parseJSON = withObject "InterpretParams" \v ->
    InterpretParams <$> v .: "posn" <*> v .: "offset" <*> v .: "uri"

instance FromJSON Position where
  parseJSON = withObject "Position" \v ->
    Position <$> v .: "line" <*> v .: "character"