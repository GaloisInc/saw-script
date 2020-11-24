{- |
Module      : SAWScript.Position
Description : Positions in source code
Maintainer  : jhendrix, atomb
Stability   : provisional
-}

{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWScript.Position where

import Control.Lens
import Data.Data (Data)
import Data.List (intercalate)
import GHC.Generics (Generic)
import System.Directory (makeRelativeToCurrentDirectory)
import System.FilePath (makeRelative, isAbsolute, (</>), takeDirectory)
import qualified Data.Text as Text
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.String as PP

import qualified What4.ProgramLoc as W4
import qualified What4.FunctionName as W4

-- Pos ------------------------------------------------------------------------

data Pos = Range !FilePath -- file
                 !Int !Int -- start line, col
                 !Int !Int -- end line, col
         | Unknown
         | PosInternal String
         | PosREPL
  deriving (Data, Generic, Eq)

renderDoc :: PP.Doc ann -> String
renderDoc doc = PP.renderString (PP.layoutPretty opts doc)
  where opts = PP.LayoutOptions (PP.AvailablePerLine 80 0.8)

endPos :: FilePath -> Pos
endPos f = Range f 0 0 0 0

fmtPos :: Pos -> String -> String
fmtPos p m = show p ++ ":\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

spanPos :: Pos -> Pos -> Pos
spanPos (PosInternal str) _ = PosInternal str
spanPos PosREPL _ = PosREPL
spanPos _ (PosInternal str) = PosInternal str
spanPos _ PosREPL = PosREPL
spanPos Unknown p = p
spanPos p Unknown = p
spanPos (Range f sl sc el ec) (Range _ sl' sc' el' ec') =  Range f l c l' c'
  where
    (l, c) = minPos sl sc sl' sc'
    (l', c') = maxPos el ec el' ec'
    minPos l1 c1 l2 c2 | l1 < l2   = (l1, c1)
                       | l1 == l2  = (l1, min c1 c2)
                       | otherwise = (l2, c2)
    maxPos l1 c1 l2 c2 | l1 < l2   = (l2, c2)
                       | l1 == l2  = (l1, max c1 c2)
                       | otherwise = (l1, c1)

fmtPoss :: [Pos] -> String -> String
fmtPoss [] m = fmtPos (PosInternal "saw-script internal") m
fmtPoss ps m = "[" ++ intercalate ",\n " (map show ps) ++ "]:\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

posRelativeToCurrentDirectory :: Pos -> IO Pos
posRelativeToCurrentDirectory (Range f sl sc el ec) = makeRelativeToCurrentDirectory f >>= \f' -> return (Range f' sl sc el ec)
posRelativeToCurrentDirectory Unknown               = return Unknown
posRelativeToCurrentDirectory (PosInternal s)       = return $ PosInternal s
posRelativeToCurrentDirectory PosREPL               = return PosREPL

posRelativeTo :: FilePath -> Pos -> Pos
posRelativeTo d (Range f sl sc el ec) = Range (makeRelative d f) sl sc el ec
posRelativeTo _ Unknown               = Unknown
posRelativeTo _ (PosInternal s)       = PosInternal s
posRelativeTo _ PosREPL               = PosREPL

routePathThroughPos :: Pos -> FilePath -> FilePath
routePathThroughPos (Range f _ _ _ _) fp
  | isAbsolute fp = fp
  | True          = takeDirectory f </> fp
routePathThroughPos _ fp = fp

instance Show Pos where
  -- show (Pos f 0 0)           = f ++ ":end-of-file"
  -- show (Pos f l c)           = f ++ ":" ++ show l ++ ":" ++ show c
  show (Range f 0 0 0 0) = f ++ ":end-of-file"
  show (Range f sl sc el ec) = f ++ ":" ++ show sl ++ ":" ++ show sc ++ "-" ++ show el ++ ":" ++ show ec
  show Unknown               = "unknown"
  show (PosInternal s)       = "[internal:" ++ s ++ "]"
  show PosREPL               = "REPL"


toW4Loc :: Text.Text -> Pos -> W4.ProgramLoc
toW4Loc fnm =
  \case
    Unknown -> mkLoc fnm W4.InternalPos
    PosREPL -> mkLoc (fnm <> " <REPL>") W4.InternalPos
    PosInternal nm -> mkLoc (fnm <> " " <> Text.pack nm) W4.InternalPos
    Range file sl sc _el _ec ->
      mkLoc fnm (W4.SourcePos (Text.pack file) sl sc)
  where mkLoc nm = W4.mkProgramLoc (W4.functionNameFromText nm)

-- Positioned -----------------------------------------------------------------

class Positioned a where
  getPos :: a -> Pos

instance Positioned Pos where
  getPos p = p

maxSpan :: (Functor t, Foldable t, Positioned a) => t a -> Pos
maxSpan xs = foldr spanPos Unknown (fmap getPos xs)

-- WithPos -----------------------------------------------------------------

data WithPos a = WithPos { _wpPos :: Pos, _wpVal :: a }
  deriving (Data, Eq, Functor, Foldable, Generic, Show, Traversable)

wpPos :: Simple Lens (WithPos a) Pos
wpPos = lens _wpPos (\s v -> s { _wpPos = v })

wpVal :: Simple Lens (WithPos a) a
wpVal = lens _wpVal (\s v -> s { _wpVal = v })

instance Positioned (WithPos a) where
  getPos = view wpPos
