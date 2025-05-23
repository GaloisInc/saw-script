{- |
Module      : SAWSupport.Pretty
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}

-- Prettyprinting infrastructure.
--
-- This module is meant to be used like this:
--    import qualified SAWSupport.Pretty as PPS
--
-- or if you like, it's reasonable to import the print functions unqualified:
--    import SAWSupport.Pretty (ppNat, ppTypeConstraint)
--    import qualified SAWSupport.Pretty as PPS
--
-- This module is a haphazard collection of prettyprinting
-- infrastructure that used to be scattered in random places around
-- the tree. Most of it came from (a) saw-core's Term prettyprinter,
-- (b) saw-script's Value prettyprinter, or (c) saw-script's AST
-- prettyprinter, none of which shared any logic other than the
-- upstream prettyprinter package.
--
-- Someone should try to systematize the naming. In particular we'd
-- like to have some kind of convention like (perhaps) "prettyFoo"
-- generates a Doc for a Foo and "ppFoo" generates a Doc and also
-- renders it to Text. (Note that in the prettyprinter package,
-- "pretty" generates Doc and there is no "pp", so this choice seems
-- preferable to the other way around.)
--
-- I'd prefer to kill off all "show"-related naming because we don't
-- want people writing or using Show instances except maybe for
-- extremely simple types.
--
-- It would also be nice in the long run to be able to do
--    import qualified Prettyprinter as PP
--    import qualified SAWSupport.Pretty as PP
-- without this causing problems.
--

module SAWSupport.Pretty (
    Doc,
    Style(..),
    MemoStyle(..),
    Opts(..),
    defaultOpts,
    PrettyPrintPrec(..),
    ppNat,
    ppTypeConstraint,
    prettyTypeSig,
    replicateDoc,
    commaSepAll,
    render,
    pShow,
    pShowText,
    commaSep,
    showBrackets,
    showBraces
 ) where

import Numeric (showIntAtBase)
import Data.Text (Text)
--import qualified Data.Text as Text
import qualified Data.Text.Lazy as TextL
import Data.List (intersperse)

import Prettyprinter (pretty, (<+>) )
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as PP
import qualified Prettyprinter.Render.Text as PPT


------------------------------------------------------------
-- Document and document style

data Style
  = PrimitiveStyle
  | ConstantStyle
  | ExtCnsStyle
  | LocalVarStyle
  | DataTypeStyle
  | CtorAppStyle
  | RecursorStyle
  | FieldNameStyle

-- TODO: assign colors for more styles
-- FUTURE: is it possible to get non-angry-fruit-salad colors?
colorStyle :: Style -> PP.AnsiStyle
colorStyle =
  \case
    PrimitiveStyle -> mempty
    ConstantStyle -> PP.colorDull PP.Blue
    ExtCnsStyle -> PP.colorDull PP.Red
    LocalVarStyle -> PP.colorDull PP.Green
    DataTypeStyle -> mempty
    CtorAppStyle -> mempty
    RecursorStyle -> mempty
    FieldNameStyle -> mempty

type Doc = PP.Doc Style


------------------------------------------------------------
-- Options

-- | Global options for pretty-printing
data Opts = Opts {
    -- | Passed to the "useAscii" setting of Cryptol's prettyprinter.
    --   Default is false.
    ppUseAscii :: Bool,

    -- | The base to print integers in; default is 10.
    ppBase :: Int,

    -- | Whether to print in color; default is false.
    ppColor :: Bool,

    -- | Whether to show the names of local variables. Default is
    --   true. If set to false, prints the deBruijn indexes instead.
    ppShowLocalNames :: Bool,

    -- | Maximum depth to recurse into terms. If not set, no limit.
    --   Default is unset.
    ppMaxDepth :: Maybe Int,

    -- | The numeric identifiers, as seen in the 'memoFresh' field of
    --   'MemoVar', of SAWCore variables that shouldn't be inlined.
    ppNoInlineMemoFresh :: [Int],

    -- | The way to display SAWCore memoization variables.
    --   Default is Incremental.
    ppMemoStyle :: MemoStyle,

    -- | Minimum sharing level required to memoize SAWCore subterms.
    --   Default is 2 (i.e., any sharing).
    ppMinSharing :: Int
 }

-- | How should memoization variables be displayed?
--
-- Note: actual text stylization is the province of 'ppMemoVar', this just
-- describes the semantic information 'ppMemoVar' should be prepared to display.
data MemoStyle
  = Incremental
  -- ^ 'Incremental' says to display a term's memoization variable with the
  -- value of a counter that increments after a term is memoized. The first
  -- term to be memoized will be displayed with '1', the second with '2', etc.
  | Hash Int
  -- ^ 'Hash i' says to display a term's memoization variable with the first 'i'
  -- digits of the term's hash.
  | HashIncremental Int
  -- ^ 'HashIncremental i' says to display a term's memoization variable with
  -- _both_ the first 'i' digits of the term's hash _and_ the value of the
  -- counter described in 'Incremental'.

-- | Default options for pretty-printing.
--
--   If the default 'ppMemoStyle' changes, be sure to update the help
--   text in the interpreter functions that control the memoization
--   style to reflect this change to users.
defaultOpts :: Opts
defaultOpts = Opts {
    ppUseAscii = False,
    ppBase = 10,
    ppColor = False,
    ppShowLocalNames = True,
    ppMaxDepth = Nothing,
    ppNoInlineMemoFresh = mempty,
    ppMemoStyle = Incremental,
    ppMinSharing = 2
 }


------------------------------------------------------------
-- Precedence prettyprinting

class PrettyPrintPrec p where
  prettyPrec :: Int -> p -> PP.Doc ann


------------------------------------------------------------
-- Common prettyprint operations
-- (for base types and common constructs not tied to any particular AST)

-- | Pretty-print an integer in the correct base
ppNat :: Opts -> Integer -> Doc
ppNat (Opts{..}) i
  | ppBase > 36 = pretty i
  | otherwise = prefix <> pretty value
  where
    prefix = case ppBase of
      2  -> "0b"
      8  -> "0o"
      10 -> mempty
      16 -> "0x"
      _  -> "0" <> pretty '<' <> pretty ppBase <> pretty '>'

    value  = showIntAtBase (toInteger ppBase) (digits !!) i ""
    digits = "0123456789abcdefghijklmnopqrstuvwxyz"

-- | Pretty-print a type constraint (also known as an ascription) @x : tp@
--   This is the formatting used by SAWCore.
ppTypeConstraint :: Doc -> Doc -> Doc
ppTypeConstraint x tp =
  PP.hang 2 $ PP.group $ PP.vsep [PP.annotate LocalVarStyle x, ":" <+> tp]

-- | Pretty-print a type signature.
--   This is the formatting used by SAWScript.
--   XXX: should probably unify with ppTypeConstraint
prettyTypeSig :: PP.Doc ann -> PP.Doc ann -> PP.Doc ann
prettyTypeSig n t = n <+> PP.pretty ':' <+> t

-- | Concatenate n copies of a doc.
replicateDoc :: Integer -> PP.Doc ann -> PP.Doc ann
replicateDoc n d
  | n < 1 = PP.emptyDoc
  | True  = d <> replicateDoc (n-1) d

-- | Add a comma to d1 and append d2.
--   (Functionally internal to commaSepAll.)
commaSepDoc :: PP.Doc ann -> PP.Doc ann -> PP.Doc ann
commaSepDoc d1 d2 = d1 <> PP.comma <+> d2

-- | Concatenate ds, appending a comma to each.
commaSepAll :: [PP.Doc ann] -> PP.Doc ann
commaSepAll ds = case ds of
  [] -> PP.emptyDoc
  _  -> foldl1 commaSepDoc ds


------------------------------------------------------------
-- Render documents

render :: Opts -> Doc -> String
render opts doc =
  TextL.unpack (PP.renderLazy (style (PP.layoutPretty layoutOpts doc)))
  where
    -- ribbon width 64, with effectively unlimited right margin
    layoutOpts = PP.LayoutOptions (PP.AvailablePerLine 8000 0.008)
    style = if ppColor opts then PP.reAnnotateS colorStyle else PP.unAnnotateS

pShow :: PrettyPrintPrec a => a -> String
pShow = show . prettyPrec 0

pShowText :: PrettyPrintPrec a => a -> Text
pShowText = PPT.renderStrict . PP.layoutPretty PP.defaultLayoutOptions . prettyPrec 0


------------------------------------------------------------
-- Show infrastructure
-- XXX: these should go away

commaSep :: [ShowS] -> ShowS
commaSep ss = foldr (.) id (intersperse (showString ",") ss)

showBrackets :: ShowS -> ShowS
showBrackets s = showString "[" . s . showString "]"

showBraces :: ShowS -> ShowS
showBraces s = showString "{" . s . showString "}"

