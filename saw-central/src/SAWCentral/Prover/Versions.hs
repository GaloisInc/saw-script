module SAWCentral.Prover.Versions (checkYicesVersion) where

import Data.List (intercalate)
import Data.Maybe (catMaybes)
import System.Directory (findExecutable)
import System.Process (readProcess)
import Text.Read (readMaybe)

-- XXX: why do we have a second copy of the logic to run Yices and get
-- the version string out? One would think the copy in
-- SolverVersions.hs should be sufficient.

data Version
  = Version [Int]
  deriving (Eq, Ord, Show)

parseVersion :: String -> Version
parseVersion = Version . fixup . go [[]]
  where
    go (n : ns) (c : cs) | '0' <= c && c <= '9' = go ((c : n) : ns) cs
    go (n : ns) ('.' : cs) = go ([] : n : ns) cs
    go ns _ = ns
    fixup = reverse . catMaybes . map (readMaybe . reverse)

prettyVersion :: Version -> String
prettyVersion (Version xs) = intercalate "." (map show xs)

parseYicesVersion :: String -> Version
parseYicesVersion = go . map words . lines
  where
    go (("Yices" : version : _) : _) = parseVersion version
    go _ = Version []

getYicesVersion :: IO (Maybe Version)
getYicesVersion = do
   mpath <- findExecutable "yices"
   case mpath of
     Just yices -> (Just . parseYicesVersion) <$> readProcess yices ["--version"] ""
     Nothing -> return Nothing

checkYicesVersion :: IO ()
checkYicesVersion = do
  mv <- getYicesVersion
  case mv of
    Just v | v < Version [2,6,1] ->
      fail $ unlines
        [ "Yices version " ++ prettyVersion v ++ " is not supported."
        , "Version 2.6.1 or greater is required for path satisfiability checking."
        ]
    Nothing ->
      fail $ unlines
        [ "Yices executable 'yices' not found."
        , "Version 2.6.1 or greater is required for path satisfiability checking."
        ]
    _ -> return ()
