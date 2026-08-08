{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : Language.Rocq.Pretty
Description : Printer for Rocq AST
License     : BSD3
Maintainer  : atomb@galois.com

Converts Rocq AST to prettyprinter documents.
-}

module Language.Rocq.Pretty (prettyDecl) where

import Data.Word
import Data.Text (Text)
import qualified Data.Text as Text
import Numeric (showHex)

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import Language.Rocq.AST


------------------------------------------------------------
-- Support

-- | Replace all occurrences of the double quote character @"@ with
--   the string @""@, i.e., two copies of it, as this is how Rocq
--   escapes double quote characters.
escapeStringLit :: Text -> Text
escapeStringLit str =
    let oneChar c = if c == '"' then "\"\"" else Text.singleton c in
    Text.concatMap oneChar str

-- | Wrapper for printing arbitrary text
text :: Text -> PP.Doc ann
text s = PP.pretty s

-- | Wrapper for printing integers
integer :: Integer -> PP.Doc ann
integer n = PP.pretty n

-- | Common code to print a name with a type
prettyNameType :: Ident -> Type -> PP.Doc ann
prettyNameType x ty =
    let x' = prettyIdent x
        ty' = prettyTerm PrecNone ty
        long = PP.nest 3 $ x' <> ":" <+> ty'
        short = PP.group $ x' <> ":" <+> ty'
    in
    PP.flatAlt long short

-- | Insert parens based on the first argument
parensIf :: Bool -> PP.Doc ann -> PP.Doc ann
parensIf p d = if p then PP.parens d else d


------------------------------------------------------------
-- Printers for AST elements

-- | Type to hold the current expression precedence while printing
data Prec
    = PrecNone
    | PrecLambda
    | PrecApp
    | PrecAtom
    deriving (Eq, Ord)

-- | Print an `Ident`
prettyIdent :: Ident -> PP.Doc ann
prettyIdent (Ident s) = text s

-- | Print a `sort`
prettySort :: Sort -> PP.Doc ann
prettySort s = case s of
    Prop -> "Prop"
    Set -> "Set"
    Type -> "Type"

-- | Print an ordinary (lambda/let) binder
prettyBinder :: Binder -> PP.Doc ann
prettyBinder b = case b of
    Binder Explicit x Nothing   -> prettyIdent x
    Binder Explicit x (Just ty) -> PP.parens $ prettyNameType x ty
    Binder Implicit x Nothing    -> PP.braces $ prettyIdent x
    Binder Implicit x (Just ty)  -> PP.braces $ prettyNameType x ty

-- | Print a pi (forall) binder
--   (we don't seem to have a representation for @exists@)
prettyPiBinder :: PiBinder -> PP.Doc ann
prettyPiBinder b = case b of
    PiBinder Explicit Nothing ty ->
        prettyTerm PrecApp ty <+> "->"
    PiBinder Explicit (Just x) ty ->
        "forall" <+> PP.parens (prettyNameType x ty) <> ","
    PiBinder Implicit Nothing ty ->
        PP.braces (prettyTerm PrecApp ty) <+> "->"
    PiBinder Implicit (Just x) ty ->
        "forall" <+> PP.braces (prettyNameType x ty) <> ","

-- | Common code for printing things shaped like function headers
--
prettyFnHeader ::
    PP.Doc ann -> [PP.Doc ann] -> Maybe (PP.Doc ann) -> PP.Doc ann ->
    PP.Doc ann
prettyFnHeader intro bindings mbRet sep =
    -- Long form
    --    fun x y z ...
    --         a b c ...
    --         : ty
    --       =>
    -- Short form:
    --    fun x : ty =>
    --
    -- (the above where intro is "fun", sep is "=>")
    --
    let firstpieces = intro : bindings
        shortHeader = case mbRet of
            Nothing -> PP.group $ PP.hsep firstpieces <+> sep
            Just ret -> PP.group $ PP.hsep firstpieces <+> ":" <+> ret <+> sep
        longBindings = case mbRet of
            Nothing -> PP.fillSep firstpieces
            Just ret -> PP.fillSep firstpieces <> PP.line <> ":" <+> ret
        longHeader = PP.nest 5 longBindings <> PP.line <> PP.indent 3 sep
    in
    PP.flatAlt longHeader shortHeader

-- | Common code for printing things shaped like functions
--   (@header@ will normally be the result of `prettyFnHeader`)
prettyFunction :: PP.Doc ann -> PP.Doc ann -> PP.Doc ann
prettyFunction header body =
    -- Long form with long argument list and long body:
    --    fun x y z ...
    --         a b c ...
    --       =>
    --       ...
    --       x + 1
    -- Long form with short argument list and long body:
    --    fun x =>
    --       ...
    --       x + 1
    -- Long form with long argument list and short body:
    --    fun x y z ...
    --         a b c ...
    --       => x + 1
    -- Short form:
    --    fun x => x + 1
    --
    let longbody = PP.line <> PP.indent 3 body <> PP.line
        shortbody = PP.group body
        body' = PP.flatAlt longbody shortbody
        long = header <> body'
        short = PP.group $ header <+> body
    in
    PP.flatAlt long short

-- | Print a term
prettyTerm :: Prec -> Term -> PP.Doc ann
prettyTerm p e0 =
  case e0 of
    Lambda binders e1 ->
        let binders' = map (\b -> PP.group $ prettyBinder b) binders
            e1' = prettyTerm PrecLambda e1
            header = prettyFnHeader "fun" binders' Nothing "=>"
        in
        parensIf (p > PrecLambda) $ prettyFunction header e1'
    Fix ident binders returnType body ->
        let ident' = prettyIdent ident
            binders' = map (\b -> PP.group $ prettyBinder b) binders
            returnType' = Just $ prettyTerm PrecNone returnType
            body' = prettyTerm PrecLambda body
            intro = "fix" <+> ident'
            header = prettyFnHeader intro binders' returnType' ":="
        in
        parensIf (p > PrecLambda) $ prettyFunction header body'
    Pi binders t ->
        let binders' = map (\b -> PP.group $ prettyPiBinder b) binders
            t' = prettyTerm PrecLambda t
            longbs = PP.nest 5 $ PP.fillSep binders'
            shortbs = PP.group $ PP.hsep binders'
            finalbs = PP.flatAlt longbs shortbs
            long = finalbs <> PP.line <> PP.indent 5 t'
            short = PP.group $ finalbs <+> t'
        in
        parensIf (p > PrecLambda) $ PP.flatAlt long short
    Let x binders mty t body ->
        let x' = prettyIdent x
            binders' = map (\b -> PP.group $ prettyBinder b) binders
            mty' = prettyTerm PrecNone <$> mty
            t' = prettyTerm PrecNone t
            body' = prettyTerm PrecLambda body
            intro = "let" <+> x'
            header = prettyFnHeader intro binders' mty' ":="
            longest = PP.vsep [header, PP.indent 3 t', "in", body']
            second = PP.vsep [PP.group (header <+> t' <+> "in"), body']
            shortest = PP.group (header <+> t' <+> "in" <+> body')
            shorter = PP.flatAlt second shortest
        in
        parensIf (p > PrecLambda) $ PP.flatAlt longest shorter
    If c t f ->
        let c' = prettyTerm PrecNone c
            t' = prettyTerm PrecNone t
            f' = prettyTerm PrecLambda f
            first = "if" <+> c' <+> "then"
            long = PP.vsep [first, PP.indent 3 t', "else", PP.indent 3 f']
            short = PP.group (first <+> t' <+> "else" <+> f')
        in
        parensIf (p > PrecLambda) $ PP.flatAlt long short
    App f [] ->
        prettyTerm p f
    App f args ->
        --
        -- The short form of this is obviously "f arg arg arg".
        --
        -- For longer forms, I'd like it to pick either
        --    blahblah
        --    blah f arg arg
        --           arg arg
        -- or
        --    blahblah
        --    blahblah blub blub blub
        --       f arg arg arg
        --         arg
        --
        -- for short f, or
        --    blahblah
        --    blah fffff arg arg
        --            arg arg
        -- or
        --    blahblah
        --    blahblah blub blub blub
        --       fffff arg arg arg
        --          arg
        --
        -- depending on how far off to the right it is. This is
        -- complicated by the fact that PP.width doesn't let you
        -- examine the width of a subdocument without emitting it,
        -- which is annoying and silly of it. (That is, the null
        -- usage of PP.width is "PP.width doc $ \_ -> PP.empty",
        -- not "PP.width doc $ \_ -> doc". The latter prints doc
        -- twice.)
        --
        -- The logic below does the following:
        --    - either indents by the width of f' (and a space) or by 3
        --      (this is in long_a)
        --    - inserts PP.line before f' if we'll be indenting the
        --      args by more than 6 spaces
        --      (this is in long)
        --
        let f' = prettyTerm PrecApp f
            args' = map (\a -> PP.group $ prettyTerm PrecAtom a) args

            short_a = PP.group $ PP.hsep (f' : args')
            short = parensIf (p > PrecApp) short_a

            long_a = PP.width f' $ \w ->
                let w' = if w <= 5 then w + 1 else 3 in
                " " <> PP.nest w' (PP.fillSep args')
            -- This must go here or the line break comes after the
            -- parens, and that's one thing for C but very weird here.
            long_b = parensIf (p > PrecApp) long_a
            long = PP.nesting $ \nest -> PP.column $ \col ->
                if col < nest + 6 then long_b
                else PP.line <> long_b
        in
        PP.flatAlt long short
    Sort s ->
        prettySort s
    Var x ->
        prettyIdent x
    ExplVar x ->
        let x' = prettyIdent x in
        parensIf (p > PrecApp) $ "@" <> x'
    Ascription tm tp ->
        let tm' = prettyTerm PrecApp tm
            tp' = prettyTerm PrecApp tp
            long = PP.nest 5 $ PP.fillSep [tm' <> ":", tp']
            short = PP.group $ tm' <> ":" <+> tp'
        in
        parensIf (p > PrecLambda) $ PP.flatAlt long short
    NatLit i ->
        if i > 1000 then
            -- Explicitly convert from Z if an integer is too big
            parensIf (p > PrecLambda) ("Z.to_nat" <+> integer i <> "%Z")
        else
            integer i
    ZLit i ->
        -- we use hex unless our integer is a positive or negative digit
        -- XXX: this cannot possibly work as intended for negative values
        if abs i > 9 then
            let ui = toInteger (fromInteger i :: Word64)
                ui' = showHex ui []
            in
            text ("0x" <> Text.pack ui' <> "%Z")
        else if i < 0 then
            text ("(" <> Text.pack (show i) <> ")%Z")
        else
            text (Text.pack (show i) <> "%Z")
    List ts ->
        let ts' = PP.punctuate ";" $ map (prettyTerm PrecNone) ts
            long = PP.brackets (PP.line <> PP.indent 3 (PP.vsep ts') <> PP.line)
            short = PP.group $ PP.brackets $ PP.hsep ts'
        in
        PP.flatAlt long short
    StringLit s ->
        PP.dquotes (text $ escapeStringLit s)
    Scope term scope ->
        let term' = prettyTerm PrecAtom term
            scope' = text scope
        in
        term' <> "%" <> scope'
    Ltac s ->
        "ltac:" <> PP.parens (text s)

-- | Print a single constructor
prettyConstructor :: Constructor -> PP.Doc ann
prettyConstructor (Constructor {..}) =
    let name' = prettyIdent constructorName
        ty' = prettyTerm PrecNone constructorType
    in
    PP.nest 5 $ "|" <+> PP.group (name' <> ":" <+> ty')

-- | Print an inductive type declaration
prettyInductive :: Inductive -> PP.Doc ann
prettyInductive (Inductive {..}) =
    let name' = prettyIdent inductiveName
        params' = map (\p -> PP.group $ prettyBinder p) inductiveParameters
        indices' = map (\i -> PP.group $ prettyPiBinder i) inductiveIndices
        sort' = prettySort inductiveSort
        ctors' = map prettyConstructor inductiveConstructors
        intro' = "Inductive" <+> name'
        lhs' = case params' of
          [] -> intro' <> ":"
          _ ->
              let short = PP.group $ intro' <+> PP.hsep params' <+> ":"
                  longparams = PP.indent 5 (PP.vsep params')
                  long = PP.vsep [intro', longparams, PP.indent 3 ":"]
              in
              PP.flatAlt long short
        rhs' = case indices' of
          [] -> sort' <+> ":="
          _ ->
              let short = PP.group $ PP.hsep indices' <+> sort' <+> ":="
                  long = PP.nest 5 $ PP.fillSep $ indices' ++ [sort' <+> ":="]
              in
              PP.flatAlt long short
        header = PP.group (lhs' <+> rhs')
    in
    PP.vsep ([header] ++ ctors' ++ ["."])

-- | Common code for the simple declarations
prettyBasicDecl :: PP.Doc ann -> Ident -> Type -> PP.Doc ann
prettyBasicDecl what nm ty =
    let nm' = prettyIdent nm
        ty' = prettyTerm PrecNone ty
        lhs' = PP.group $ what <+> nm' <> ":"
        long = PP.nest 3 $ lhs' <+> ty' <> "."
        short = PP.group $ lhs' <+> ty' <> "."
    in
    PP.flatAlt long short

-- | Print a Definition
prettyDefinition :: Ident -> [Binder] -> Maybe Type -> Term -> PP.Doc ann
prettyDefinition nm params mty body =
    let nm' = prettyIdent nm
        params' = map (\p -> PP.group $ prettyBinder p) params
        mty' = prettyTerm PrecNone <$> mty
        body' = prettyTerm PrecNone body
        intro' = "Definition" <+> nm'
        lhs' = case params' of
          [] -> intro' <> ":"
          _ ->
              let short = PP.group $ intro' <+> PP.hsep params' <+> ":"
                  longparams = PP.indent 5 (PP.vsep params')
                  long = PP.vsep [intro', longparams, PP.indent 3 ":"]
              in
              PP.flatAlt long short
        rhs' = case mty' of
          Nothing -> ":="
          Just ty' -> ty' <+> ":="
        header = PP.group (lhs' <+> rhs')
    in
    let short = PP.group $ header <+> body' <> "."
        long = PP.nest 3 $ PP.vsep [header, body' <> "."]
    in
    PP.flatAlt long short

-- | Print a top-level declaration
prettyDecl :: Decl -> PP.Doc ann
prettyDecl decl = case decl of
    Axiom nm ty ->
        prettyBasicDecl "Axiom" nm ty <> PP.hardline
    Parameter nm ty ->
        prettyBasicDecl "Parameter" nm ty <> PP.hardline
    Variable nm ty ->
        prettyBasicDecl "Variable" nm ty <> PP.hardline
    Comment s ->
        -- None of the comments we generate are multiline. If that ever
        -- changes, we'll need more logic here to print them properly.
        "(*" <+> text s <+> "*)" <> PP.hardline
    Definition nm binders mty body ->
        prettyDefinition nm binders mty body <> PP.hardline
    InductiveDecl ind ->
        prettyInductive ind <> PP.hardline
    Section nm ds ->
        let nm' = prettyIdent nm
            header = "Section" <+> nm' <> "." <> PP.hardline
            ds' = map prettyDecl ds
            footer = "End" <+> nm' <> "." <> PP.hardline
        in
        -- Note that because every declaration ends with PP.hardline (or
        -- at least PP.line, which we don't group away), we don't need
        -- another one after ds'. Except, without one, the indent for the
        -- declarations bleeds into the footer. (wut?)
        header <> PP.indent 3 (PP.vsep ds') <> PP.hardline <> footer
    Snippet s ->
        -- This assumes all the text snippets we have are multi-line blocks
        -- that include newlines, including at the end.
        --
        -- FUTURE: nothing above this code should ever call PP.group, but if
        -- that changes, we may need to go through the string and manually
        -- replace each \n with PP.hardline.
        text s
