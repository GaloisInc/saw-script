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
-- XXX: Someone should try to systematize the naming. In particular
-- we'd like to have some kind of convention like (perhaps)
-- "prettyFoo" generates a Doc for a Foo and "ppFoo" generates a Doc
-- and also renders it to Text. (Note that in the prettyprinter
-- package, "pretty" generates Doc and there is no "pp", so this
-- choice seems preferable to the other way around.) I've done some
-- of this, but there's a lot more out in the rest of the tree that
-- ought to be updated to match it.
--
-- Update: that convention has now been adopted, but is still not
-- widely honored.
--
-- XXX: should come up with a better name for pShowText, and remove
-- pShow entirely. These shouldn't be called "show" because they
-- aren't Show instances and don't have the properties of Show
-- instances. And we don't want people writing or using Show instances
-- except maybe for extremely simple types.
--
-- XXX: The ShowS material at the bottom should go away; that requires
-- cleaning up the callers to use prettyprinting instead of Show
-- instances.
--
-- XXX: Also we should crack down on callers using "show" instead of
-- "render" to produce output text.
--
-- It would also be nice in the long run to be able to do
--    import qualified Prettyprinter as PP
--    import qualified SAWSupport.Pretty as PP
-- without this causing problems.
--
-- It may also be that this should be split into two or more modules,
-- one meant to be used qualified and one meant for selective import,
-- or something. It isn't at all clear yet what a good interface is.
--
-- FUTURE: there's also been some talk of adopting Cryptol's technique
-- of wrapping the upstream prettyprinter and exposing a monad, or
-- some other similar way of allowing options to be applied to the
-- document after it's assembled instead of needing to be threaded
-- through everywhere.
--
-- XXX: in any event, it's problematic that seemingly more than half
-- of the call sites for things that want options pass the default
-- options. If we're actually going to support the things the options
-- allows the user to set, we should make sure the user's settings
-- make it to the places that do prints. This includes errors.
--

module SAWSupport.Pretty (
    Doc,
    Style(..),
    MemoStyle(..),
    Opts(..),
    defaultOpts,
    limitMaxDepth,
    PrettyPrec(..),
    prettyNat,
    prettyTypeConstraint,
    prettyTypeSig,
    replicate,
    commaSepAll,
    squotesMatching,
    prettyLetBlock,
    render,
    renderText,
    pShow,
    pShowText,
    showCommaSep,
    showBrackets,
    showBraces
 ) where

import Prelude hiding (replicate)

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
  | VariableStyle
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
    VariableStyle -> PP.colorDull PP.Red
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

    -- | Maximum depth to recurse into SAWCore terms. If not set, no
    --   limit. Default is unset.
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
    ppMaxDepth = Nothing,
    ppNoInlineMemoFresh = mempty,
    ppMemoStyle = Incremental,
    ppMinSharing = 2
 }

limitMaxDepth :: Opts -> Int -> Opts
limitMaxDepth opts limit =
  let adjust depth = case depth of
        Nothing -> Just limit
        Just d -> Just $ if d > limit then limit else d
  in
  opts { ppMaxDepth = adjust $ ppMaxDepth opts }


------------------------------------------------------------
-- Precedence prettyprinting

class PrettyPrec p where
  prettyPrec :: Int -> p -> PP.Doc ann


------------------------------------------------------------
-- Common prettyprint operations
-- (for base types and common constructs not tied to any particular AST)

-- | Pretty-print an integer in the correct base
prettyNat :: Opts -> Integer -> Doc
prettyNat (Opts{..}) i
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
prettyTypeConstraint :: Doc -> Doc -> Doc
prettyTypeConstraint x tp =
  PP.hang 2 $ PP.group $ PP.vsep [PP.annotate LocalVarStyle x, ":" <+> tp]

-- | Pretty-print a type signature.
--   This is the formatting used by SAWScript.
--   XXX: should probably unify with prettyTypeConstraint
prettyTypeSig :: PP.Doc ann -> PP.Doc ann -> PP.Doc ann
prettyTypeSig n t = n <+> PP.pretty ':' <+> t

-- | Concatenate n copies of a doc.
replicate :: Integer -> PP.Doc ann -> PP.Doc ann
replicate n d
  | n < 1 = PP.emptyDoc
  | True  = d <> replicate (n-1) d

-- | Add a comma to d1 and append d2.
--   (Functionally internal to commaSepAll.)
commaSepDoc :: PP.Doc ann -> PP.Doc ann -> PP.Doc ann
commaSepDoc d1 d2 = d1 <> PP.comma <+> d2

-- | Concatenate ds, appending a comma to each.
commaSepAll :: [PP.Doc ann] -> PP.Doc ann
commaSepAll ds = case ds of
  [] -> PP.emptyDoc
  _  -> foldl1 commaSepDoc ds

-- | Wrap d in single quotes that match.
--   There's a PP.squotes that uses right-quote on both sides.
--   (There's also a PP.dquotes.)
squotesMatching :: PP.Doc ann -> PP.Doc ann
squotesMatching d =
  PP.enclose "`" "'" d

-- | Generalized layout for let-bindings.
prettyLetBlock :: [(PP.Doc ann, PP.Doc ann)] -> PP.Doc ann -> PP.Doc ann
prettyLetBlock defs body =
  let lets = PP.align $
        (PP.concatWith (\x y -> x <> PP.hardline <> y))
          (map ppEqn defs)
  in PP.group $ PP.vcat
        [ "let" PP.<+> PP.align (PP.lbrace PP.<+> lets <> PP.line <> PP.rbrace)
        , " in" PP.<+> body
        ]
  where
    ppEqn (var,d) = var PP.<+> "=" PP.<+> d <> ";"

------------------------------------------------------------
-- Render documents

render :: Opts -> Doc -> String
render opts doc =
  TextL.unpack (PP.renderLazy (style (PP.layoutPretty layoutOpts doc)))
  where
    -- ribbon width 64, with effectively unlimited right margin
    layoutOpts = PP.LayoutOptions (PP.AvailablePerLine 8000 0.008)
    style = if ppColor opts then PP.reAnnotateS colorStyle else PP.unAnnotateS

renderText :: Opts -> Doc -> Text
renderText opts doc =
  PP.renderStrict (style (PP.layoutPretty layoutOpts doc))
  where
    -- ribbon width 64, with effectively unlimited right margin
    layoutOpts = PP.LayoutOptions (PP.AvailablePerLine 8000 0.008)
    style = if ppColor opts then PP.reAnnotateS colorStyle else PP.unAnnotateS

pShow :: PrettyPrec a => a -> String
pShow = show . prettyPrec 0

pShowText :: PrettyPrec a => a -> Text
pShowText = PPT.renderStrict . PP.layoutPretty PP.defaultLayoutOptions . prettyPrec 0


------------------------------------------------------------
-- Show infrastructure
-- XXX: these should go away

showCommaSep :: [ShowS] -> ShowS
showCommaSep ss = foldr (.) id (intersperse (showString ",") ss)

showBrackets :: ShowS -> ShowS
showBrackets s = showString "[" . s . showString "]"

showBraces :: ShowS -> ShowS
showBraces s = showString "{" . s . showString "}"

