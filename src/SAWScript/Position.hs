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

-- Type inference info, to be used to interpret the positions of
-- inferred types.
--
-- InfFresh means that the term (or pattern) at the given position
--    caused us to generate a fresh type variable, e.g. the element
--    type of "[]".
-- InfTerm means that the term (or pattern) at the given position
--    prompted us to choose the accompanying type; e.g. "[]" has type
--    List.
-- InfContext means that the usage of the term at the given position
--    prompted us to choose the accompanying type; e.g. in "f x" f has
--    function type.
--
-- If you add an Ord instance here (there is currently no need for
-- one) be sure to take steps to avoid confusion with the comparison
-- in compareInfQuality, which is a different kind of comparison.
data Inference
  = InfFresh
  | InfTerm
  | InfContext
  deriving (Data, Eq)

-- Source position.
--
-- Mostly, this is a physical range within a file.
--
-- XXX: some logic uses Range with zero line/column numbers for end-of-file.
-- This should be replaced with an explicit end-of-file position.
--
-- FileOnlyPos is for both whole-file things (such as symbol tables in
-- executable images) and cases where we just don't have any more
-- detailed info.
--
-- FileAndFunctionPos is for cases where we have a function name in a
-- file but not a position as such (e.g. because it's compiled code
-- in an object file)
--
-- Internally generated objects use PosInternal with descriptive text.
-- (FUTURE: eliminate PosInternal in favor of explicit constructors
-- for the cases that currently generate PosInternal, so we can keep
-- track of what they are.)
--
-- PosREPL is for things typed at the repl, or in some cases (that
-- should get cleaned out) for things we assume came from the repl.
--
-- PosInferred is used for types generated by type inference; it
-- describes where and how the inference was made. This can be thought
-- of as the provenance of the inferred type.
--
-- If you add an Ord instance here (there is currently no need for
-- one) be sure to take steps to avoid confusion with the comparison
-- in comparePosQuality, which is a different kind of comparison.
--
-- XXX we should rearrange this so that either the usage is
-- "import qualified SAWScript.Position as Pos" and this type is T
-- (so the normal name of the type is Pos.T and the constructors
-- are Pos.Range, Pos.Unknown, etc.) or insert Pos in the names of
-- all the constructors instead of just some.
data Pos = Range !FilePath -- file
                 !Int !Int -- start line, col
                 !Int !Int -- end line, col
         | FileOnlyPos !FilePath
         | FileAndFunctionPos !FilePath !String
         | Unknown
         | PosInternal String
         | PosREPL
         | PosInferred Inference Pos
  deriving (Data, Generic, Eq)

renderDoc :: PP.Doc ann -> String
renderDoc doc = PP.renderString (PP.layoutPretty opts doc)
  where opts = PP.LayoutOptions (PP.AvailablePerLine 80 0.8)

fmtPos :: Pos -> String -> String
fmtPos p m = show p ++ ":\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

-- Get the empty position at the beginning of the position of
-- something else. This can be used to provide positions for implicit
-- elements, such as the not-physically-present wildcard in a
-- do-notation binding that doesn't bind anything.
leadingPos :: Pos -> Pos
leadingPos pos = case pos of
   Range f l1 c1 _l2 _c2 -> Range f l1 c1 l1 c1
   _ -> pos

-- Paste together two positions.
--
-- Note that pasting together inferred positions isn't meaningful.
-- Even if the positions are from related elements, the positions will
-- in general be wildly different and the span between them completely
-- meaningless.
--
-- I'm hesitant to make the inferred position cases crash, though.
-- Maybe in the FUTURE when we can have more faith that we won't
-- accidentally trigger them on some random code path. Or maybe we
-- should statically rule them out by having multiple layers of
-- position type. (If we do that, maybe pasting PosInternal should
-- also be disallowed.)  For now, just arbitrarily pick one and
-- discard the other. Note that inferred positions are only generated
-- by typechecking and thus only appear there and downstream, and
-- nearly but not quite all the position-pasting happens in the parser
-- upstream of that.
--
-- If we mix an inferred position and a real one, just use the real one.
--
-- Similar considerations arise from pasting FileOnlyPos and
-- FileAndFunctionPos. These should also only appear downstream of the
-- saw-script parser.
spanPos :: Pos -> Pos -> Pos
-- prefer internal and REPL to anything else
spanPos (PosInternal str) _ = PosInternal str
spanPos PosREPL _ = PosREPL
spanPos _ (PosInternal str) = PosInternal str
spanPos _ PosREPL = PosREPL
-- prefer anything else to unknown
spanPos Unknown p = p
spanPos p Unknown = p
-- if it's the same file, keep it; otherwise give up
spanPos (FileOnlyPos f) (FileOnlyPos f') | f == f' = FileOnlyPos f
spanPos (FileOnlyPos _) (FileOnlyPos _) = Unknown
-- if it's the same file and same function, keep it; otherwise if it's the
-- same file drop the function; otherwise give up
spanPos (FileAndFunctionPos f fn) (FileAndFunctionPos f' fn') | f == f' && fn == fn' =
   FileAndFunctionPos f fn
spanPos (FileAndFunctionPos f _) (FileAndFunctionPos f' _) | f == f' = FileOnlyPos f
spanPos (FileAndFunctionPos _ _) (FileAndFunctionPos _ _) = Unknown
spanPos (FileOnlyPos f) (FileAndFunctionPos f' _) | f == f' = FileOnlyPos f
spanPos (FileAndFunctionPos f _) (FileOnlyPos f') | f == f' = FileOnlyPos f
spanPos (FileOnlyPos _) (FileAndFunctionPos _ _) = Unknown
spanPos (FileAndFunctionPos _ _) (FileOnlyPos _) = Unknown
-- these cases should really not arise
spanPos (FileOnlyPos _) p = p
spanPos p (FileOnlyPos _) = p
spanPos (FileAndFunctionPos _ _) p = p
spanPos p (FileAndFunctionPos _ _) = p
-- for two inferred positions arbitrarily choose the left one;
-- otherwise defer to the real position
spanPos p@(PosInferred _ _) (PosInferred _ _) = p
spanPos (PosInferred _ _) p = p
spanPos p (PosInferred _ _) = p
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

-- Compare two type inference notes for quality of information, as per
-- comparePosQuality below. InfFresh is less, others are equal.
compareInfQuality :: Inference -> Inference -> Ordering
compareInfQuality inf1 inf2 = case (inf1, inf2) of
  (InfFresh, InfFresh) -> EQ
  (InfFresh, _) -> LT
  (_, InfFresh) -> GT
  _ -> EQ

-- Compare two positions for the same thing (e.g. two types we just
-- unified), choosing the one with higher quality information. Use the
-- following heuristics:
--    - obviously prefer any concrete position to a placeholder
--    - PosREPL is a better placeholder than Unknown
--    - prefer the position with the smaller span, as it's likely
--      to be more precise
--    - when all else fails call them equal
--
-- This could be an Ord instance but it seems dangerous to use it
-- implicitly since an EQ result doesn't imply actual equality.
--
-- This is split out from choosePos so it'll be compositional if we
-- end up with more stratification of position types.
comparePosQuality :: Pos -> Pos -> Ordering
comparePosQuality p1 p2 = case (p1, p2) of
   (Unknown, Unknown) -> EQ
   (Unknown, _) -> LT
   (_, Unknown) -> GT
   (PosREPL, PosREPL) -> EQ
   (PosREPL, _) -> LT
   (_, PosREPL) -> GT
   (PosInternal _, PosInternal _) -> EQ
   (PosInternal _, _) -> LT
   (_, PosInternal _) -> GT
   (FileOnlyPos _, FileOnlyPos _) -> EQ
   (FileOnlyPos _, FileAndFunctionPos _ _) -> LT
   (FileAndFunctionPos _ _, FileOnlyPos _) -> GT
   (FileAndFunctionPos _ _, FileAndFunctionPos _ _) -> EQ
   (FileOnlyPos _, _) -> LT
   (_, FileOnlyPos _) -> GT
   (FileAndFunctionPos _ _, _) -> LT
   (_, FileAndFunctionPos _ _) -> GT
   (PosInferred inf1 p1', PosInferred inf2 p2') ->
     case compareInfQuality inf1 inf2 of
       EQ -> comparePosQuality p1' p2'
       LT -> LT
       GT -> GT
   (PosInferred _ _, _) -> LT
   (_, PosInferred _ _) -> GT
   (Range _ sl1 _ el1 _, Range _ sl2 _ el2 _) | el2 - sl2 < el1 - sl1 -> LT
   (Range _ sl1 _ el1 _, Range _ sl2 _ el2 _) | el1 - sl1 < el2 - sl2 -> GT
   (Range _ _ sc1 _ ec1, Range _ _ sc2 _ ec2) | ec2 - sc2 < ec1 - sc1 -> LT
   (Range _ _ sc1 _ ec1, Range _ _ sc2 _ ec2) | ec1 - sc1 < ec2 - sc2 -> GT
   (Range _ _ _ _ _, Range _ _ _ _ _) -> EQ

-- Pick the better position to use going forward. If all else fails
-- pick the left one.
choosePos :: Pos -> Pos -> Pos
choosePos p1 p2 = case comparePosQuality p1 p2 of
   LT -> p2
   GT -> p1
   EQ -> p1

fmtPoss :: [Pos] -> String -> String
fmtPoss [] m = fmtPos (PosInternal "saw-script internal") m
fmtPoss ps m = "[" ++ intercalate ",\n " (map show ps) ++ "]:\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

posRelativeToCurrentDirectory :: Pos -> IO Pos
posRelativeToCurrentDirectory (Range f sl sc el ec) = makeRelativeToCurrentDirectory f >>= \f' -> return (Range f' sl sc el ec)
posRelativeToCurrentDirectory (FileOnlyPos f)       = makeRelativeToCurrentDirectory f >>= \f' -> return (FileOnlyPos f')
posRelativeToCurrentDirectory (FileAndFunctionPos f fn) = makeRelativeToCurrentDirectory f >>= \f' -> return (FileAndFunctionPos f' fn)
posRelativeToCurrentDirectory Unknown               = return Unknown
posRelativeToCurrentDirectory (PosInternal s)       = return $ PosInternal s
posRelativeToCurrentDirectory PosREPL               = return PosREPL
posRelativeToCurrentDirectory (PosInferred inf p) =
  PosInferred inf <$> posRelativeToCurrentDirectory p

posRelativeTo :: FilePath -> Pos -> Pos
posRelativeTo d (Range f sl sc el ec) = Range (makeRelative d f) sl sc el ec
posRelativeTo d (FileOnlyPos f)       = FileOnlyPos (makeRelative d f)
posRelativeTo d (FileAndFunctionPos f fn) = FileAndFunctionPos (makeRelative d f) fn
posRelativeTo _ Unknown               = Unknown
posRelativeTo _ (PosInternal s)       = PosInternal s
posRelativeTo _ PosREPL               = PosREPL
posRelativeTo d (PosInferred inf p)   = PosInferred inf $ posRelativeTo d p

routePathThroughPos :: Pos -> FilePath -> FilePath
routePathThroughPos pos fp
  | isAbsolute fp = fp
  | True = case pos of
        Range f _ _ _ _        -> takeDirectory f </> fp
        FileOnlyPos f          -> takeDirectory f </> fp
        FileAndFunctionPos f _ -> takeDirectory f </> fp
        PosInferred _inf pos'  -> routePathThroughPos pos' fp
        _ -> fp

-- Show instance for positions.
--
-- XXX: while this is adequate for basic positions, printing the
-- position information for inferred types is more complicated.  Most
-- likely, the inference information should be its own message rather
-- than being stuffed into the position field of some other message.
-- It remains to be seen exactly how that ought to work, so for now
-- just stuff things into the Show instance. It's possible that later
-- on this Show instance should be withdrawn in favor of more specific
-- tools. Note that because of limitations of Haskell we can't really
-- provide a centralized error-reporting facility, but we can at least
-- expect code that converts errors to lists of output lines to come
-- through code in this module and not be calling show on positions
-- itself.
instance Show Pos where
  -- show (Pos f 0 0)           = f ++ ":end-of-file"
  -- show (Pos f l c)           = f ++ ":" ++ show l ++ ":" ++ show c
  show (Range f 0 0 0 0) = f ++ ":end-of-file"
  show (Range f sl sc el ec) = f ++ ":" ++ show sl ++ ":" ++ show sc ++ "-" ++ show el ++ ":" ++ show ec
  show (FileOnlyPos f)          = f
  show (FileAndFunctionPos f fn)  = f ++ ":" ++ fn
  show (PosInferred InfFresh p)   = show p ++ ": Fresh type for this term"
  show (PosInferred InfTerm p)    = show p ++ ": Inferred from this term"
  show (PosInferred InfContext p) = show p ++ ": Inferred from this context"
  show Unknown               = "unknown"
  show (PosInternal s)       = "[internal:" ++ s ++ "]"
  show PosREPL               = "REPL"

toW4Loc :: Text.Text -> Pos -> W4.ProgramLoc
toW4Loc fnm =
  \case
    FileOnlyPos f -> mkLoc (fnm <> " " <> Text.pack f) W4.InternalPos
    FileAndFunctionPos f fn -> mkLoc (fnm <> " " <> Text.pack f <> " " <> Text.pack fn) W4.InternalPos
    Unknown -> mkLoc fnm W4.InternalPos
    PosREPL -> mkLoc (fnm <> " <REPL>") W4.InternalPos
    PosInternal nm -> mkLoc (fnm <> " " <> Text.pack nm) W4.InternalPos
    PosInferred _ p -> toW4Loc fnm p
    Range file sl sc _el _ec ->
      mkLoc fnm (W4.SourcePos (Text.pack file) sl sc)
  where mkLoc nm = W4.mkProgramLoc (W4.functionNameFromText nm)

-- Positioned -----------------------------------------------------------------

class Positioned a where
  getPos :: a -> Pos

instance Positioned Pos where
  getPos p = p

-- Caution: if you write maxSpan (a, b) for heterogeneous types a and b,
-- it will typecheck but not actually work correctly. Either call getPos
-- first or use maxSpan' for this case.
maxSpan :: (Functor t, Foldable t, Positioned a) => t a -> Pos
maxSpan xs = foldr spanPos Unknown (fmap getPos xs)

maxSpan' :: (Positioned a, Positioned b) => a -> b -> Pos
maxSpan' x y = spanPos (getPos x) (getPos y)

-- WithPos -----------------------------------------------------------------

data WithPos a = WithPos { _wpPos :: Pos, _wpVal :: a }
  deriving (Data, Eq, Functor, Foldable, Generic, Show, Traversable)

wpPos :: Simple Lens (WithPos a) Pos
wpPos = lens _wpPos (\s v -> s { _wpPos = v })

wpVal :: Simple Lens (WithPos a) a
wpVal = lens _wpVal (\s v -> s { _wpVal = v })

instance Positioned (WithPos a) where
  getPos = view wpPos
