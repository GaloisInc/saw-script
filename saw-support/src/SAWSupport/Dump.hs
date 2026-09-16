{- |
Module      : SAWSupport.Dump
Description : Infrastructure for AST / IR dumps
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

Dump infrastructure.

Dumping is different from prettyprinting. The goal of a prettyprinter
is to recreate concrete syntax, including things like removing
unnecessary parentheses, in pursuit of generating input that's ideally
as readable as the original source text.

The goal of a dumper is somewhat different. Readability is still a
concern, but the primary goal is to make sure the output reflects
exactly what the representation contains. Prettyprinter output will
usually, for example, not distinguish the difference between
```
   Add (Add (Var x) (Var y)) (Var z)
```
and
```
   Add (Var x) (Add (Var y) (Var z))
```
Most of the time, that doesn't matter. However, when you're chasing
after a problem where your optimizing pass is failing to see `y`, it
matters a great deal. Dumps are intended to serve this debugging need.

The schematic dump format supported by this module has the general
format
```
    Heading
        Subelement
        Subelement
        Subelement
```

or

```
    Heading
        field
            Element
        field
            Element
```

where the heading is generally the AST constructor name plus any
information that reliably fits on the same line.

Small single subelements may be pulled up onto the heading line to
save vertical space. This is automatic.

This file is meant to be imported as follows:
```
    import qualified SAWSupport.Dump as Dump
    import SAWSupport.Dump (Dump)

-}
{-# LANGUAGE OverloadedStrings #-}

module SAWSupport.Dump (
    Dump,

    phantom,
    singleton,
    subelement,
    subelements,
    fields,

    bool,
    int,
    text,
    surroundText,
    surroundText',
    qstring,
    maybe,
    list,

    prepend,

    render,
    renderString
  ) where

import Prelude hiding (maybe)

import qualified Data.Char as Char
import qualified Data.Text as Text
import Data.Text (Text)

import Numeric (showHex)


------------------------------------------------------------
-- Dump representation

-- | Type for a collected but not yet printed dump, akin to a
--   prettyprinter document. But we do a lot less formatting, so it
--   can be a lot simpler.
--
--   There's nothing especially canonical about this representation;
--   it's meant to serve observed needs.
--
--   `Phantom` is empty and produces no output, except in certain
--   contexts it appears as "---".
--
--   `Line` is some text that fits on one line.
--
--   `List` is a series of dumps.
--
--   `Elements` is a heading and a series of dumps.
--
--   `Fields` is a heading and a series of labelled dumps.
--
--   `Surround` is like `Elements` but also has a footer.
--
data Dump
    = Phantom
    | Line Text
    | List [Dump]
    | Elements Text [Dump]
    | Fields Text [(Text, Dump)]
    | Surround Text [Dump] Text


------------------------------------------------------------
-- Support code

-- | Convert an arbitrary string to a printable quoted string.
--
--   This differs from using the `Show` instance for `Text` or
--   `String` (which adds quotes and escapes at least some characters)
--   at least as follows:
--      - it doesn't unpack or repack the whole string, and allocates
--        only for non-printables;
--      - it has well defined quoting and escaping behavior (the
--        `Show` instances are understood to add quotes but are
--        otherwise undocumented);
--      - experimentation indicates that the `Show` instances escape
--        at least some non-ASCII printables, which this doesn't.
--
--   Other reasons not to rely on the `Show` instances include:
--      - it's easy to forget when making changes that the `Show`
--        instances add quotes, because most analogous operations on
--        strings (e.g. @pretty@) do not, and here we rely on it;
--      - the fewer intentional uses of `Show` there are the easier it
--        is to crack down on abuse.
--
stringize :: Text -> Text
stringize txt0 =
    let visit txt results =
          let (keep, rest) = Text.span Char.isPrint txt in
          case Text.uncons rest of
              Nothing ->
                  -- reached the end
                  results
              Just (c, rest') ->
                  let again c' = visit rest' (c' : keep : results) in
                  case c of
                    '\a' -> again "\\a"
                    '\b' -> again "\\b"
                    '\t' -> again "\\t"
                    '\n' -> again "\\n"
                    '\v' -> again "\\v"
                    '\f' -> again "\\f"
                    '\r' -> again "\\r"
                    _ ->
                        let c' = Text.pack (showHex (Char.ord c) "") in
                         -- There are many ways we could print this.
                         -- This form is at least unambiguous...
                         again $ "\\(" <> c' <> ")"
    in
    Text.concat $ reverse $ ["\""] ++ visit txt0 ["\""]


------------------------------------------------------------
-- Basic dumps

-- | Completely empty dump
phantom :: Dump
phantom = Phantom

-- | Heading with no subelements. Special case of `subelements`.
singleton :: Text -> Dump
singleton heading = Elements heading []

-- | Heading with one subelement. Special case of `subelements`.
subelement :: Text -> Dump -> Dump
subelement heading elt = Elements heading [elt]
    
-- | Heading with a list of subelements.
subelements :: Text -> [Dump] -> Dump
subelements heading elts = Elements heading elts

-- | Heading with a list of subelements, but each one comes with
--   a text label.
fields :: Text -> [(Text, Dump)] -> Dump
fields heading items = Fields heading items


------------------------------------------------------------
-- Dumps for standard data types

-- | Dump a Bool.
bool :: Bool -> Dump
bool True = Line "True"
bool False = Line "False"

-- | Dump an Int, Integer, or other Num.
int :: (Show a, Num a) => a -> Dump
int k = Line $ Text.pack $ show k

-- | Dump some literal text. We don't interpret it, except to split it
--   into lines if necessary so indent works.
text :: Text -> Dump
text txt = case Text.lines txt of
    [] -> Phantom
    [l] -> Line l
    ls -> List $ map Line ls

-- | Dump some literal text, surrounding it with delimiters. We don't
--   interpret it, except to split it into lines if necessary so
--   indent works. This can be used for metasyntactic grouping symbols
--   (parens, brackets, etc.) you want to have in the dump output. You
--   don't want to use it for syntactic grouping; save that for the
--   prettyprinting logic.
surroundText :: Text -> Text -> Text -> Dump
surroundText lhs txt rhs = case Text.lines txt of
    [] -> Line (lhs <> rhs)
    [l] -> Line (lhs <> l <> rhs)
    ls -> Surround lhs (map Line ls) rhs

-- | Like `surroundText` except inserts spaces on the inside of the
--   delimiters.
surroundText' :: Text -> Text -> Text -> Dump
surroundText' lhs txt rhs = case Text.lines txt of
    [] -> Line (lhs <> " " <> rhs)
    [l] -> Line (lhs <> " " <> l <> " " <> rhs)
    ls -> Surround lhs (map Line ls) rhs

-- | Dump a string that's meant to be a quoted string literal.
qstring :: Text -> Dump
qstring txt = Line $ stringize txt

-- | Dump a Maybe value using another dumper.
maybe :: (a -> Dump) -> Maybe a -> Dump
maybe dumpX mbX = case mbX of
    Nothing -> Phantom
    Just x -> dumpX x

-- | Dump a list.
list :: [Dump] -> Dump
list xs = List xs


------------------------------------------------------------
-- Other operations

-- | Prepend some more text to the next thing. Use with discretion.
prepend :: Text -> Dump -> Dump
prepend newtxt d = case d of
    Phantom ->
        Line newtxt
    Line txt ->
        Line $ newtxt <> txt
    List ds ->
        Elements newtxt ds
    Elements txt ds ->
        Elements (newtxt <> txt) ds
    Fields txt flds ->
        Fields (newtxt <> txt) flds
    Surround lhs ds rhs ->
        Surround (newtxt <> lhs) ds rhs
        

------------------------------------------------------------
-- Rendering

-- | Guts of render.
--
--   We do the following special cases:
--
--   - If there's a single subelement and it's a single line, we pull
--     it onto the same line as the header.
--
--   - If the value of a field is a single line, we pull it onto the
--     same line as the field name.
--
--   - If the value of a field is `Phantom`, we print "---" instead of
--     just leaving the field name hanging.
--
--   - We do _not_ do any of this for `Surround` because currently the
--     only way to generate it is with a multiline text and the logic
--     there already handles the short case directly.
--
renderAt :: Text -> Dump -> [Text]
renderAt indent d = case d of
    Phantom ->
        []
    Line txt ->
        [indent <> txt]
    List ds ->
        -- List does _not_ indent any further.
        concatMap (renderAt indent) ds
    Elements header [d1] ->
        let indent' = "   " <> indent in
        case renderAt indent' d1 of
            [d1'] ->
                let d1'' = Text.dropWhile Char.isSpace d1' in
                [indent <> header <> " " <> d1'']
            ds' ->
                (indent <> header) : ds'
    Elements header ds ->
        (indent <> header) : concatMap (renderAt ("   " <> indent)) ds
    Fields header flds ->
        let indent' = "   " <> indent
            indent'' = "      " <> indent
        in
        let renderField (name, d1) =
              case renderAt indent'' d1 of
                  [] ->
                      [indent' <> name <> ": ---"]
                  [d1'] ->
                      let d1'' = Text.dropWhile Char.isSpace d1' in
                      [indent' <> name <> ": " <> d1'']
                  ds' ->
                      (indent' <> name) : ds'
        in
        (indent <> header) : concatMap renderField flds
    Surround header ds footer ->
        let ds' = concatMap (renderAt ("   " <> indent)) ds in
        (indent <> header) : ds' ++ [indent <> footer]

-- | Print to a list of (single) lines. There are no embedded newlines
--   in the result.
render :: Dump -> [Text]
render dmp =
    renderAt "" dmp

-- | `String` version of `render`, which we'll doubtless need.
renderString :: Dump -> [String]
renderString dmp = map Text.unpack $ render dmp
