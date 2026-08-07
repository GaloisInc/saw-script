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
import Numeric (showHex)

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import Language.Rocq.AST


------------------------------------------------------------
-- Support

-- | Replace all occurrences of the double quote character @"@ with
--   the string @""@, i.e., two copies of it, as this is how Rocq
--   escapes double quote characters.
escapeStringLit :: String -> String
escapeStringLit = concatMap (\c -> if c == '"' then "\"\"" else [c])

-- | Wrapper for printing arbitrary text
text :: String -> PP.Doc ann
text s = PP.pretty s

-- | Wrapper for printing integers
integer :: Integer -> PP.Doc ann
integer n = PP.pretty n

-- | Common code to print a name with a type
prettyNameType :: Ident -> Type -> PP.Doc ann
prettyNameType x ty = prettyIdent x <+> ":" <+> prettyTerm PrecNone ty

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

-- | Print a list of binders
prettyBinders :: [Binder] -> [PP.Doc ann]
prettyBinders bs = map prettyBinder bs

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
      let binders' = prettyBinders binders
          e1' = prettyTerm PrecLambda e1
          header = prettyFnHeader "fun" binders' Nothing "=>"
      in
      parensIf (p > PrecLambda) $ prettyFunction header e1'
    Fix ident binders returnType body ->
      let ident' = prettyIdent ident
          binders' = prettyBinders binders
          returnType' = Just $ prettyTerm PrecNone returnType
          body' = prettyTerm PrecLambda body
          intro = "fix" <+> ident'
          header = prettyFnHeader intro binders' returnType' ":="
      in
      parensIf (p > PrecLambda) $ prettyFunction header body'
    Pi bs t ->
      let bs' = map (\b -> PP.group $ prettyPiBinder b) bs
          t' = prettyTerm PrecLambda t
          longbs = PP.nest 5 $ PP.fillSep bs'
          shortbs = PP.group $ PP.hsep bs'
          finalbs = PP.flatAlt longbs shortbs
          long = finalbs <> PP.line <> t'
          short = PP.group $ finalbs <+> t'
      in
      parensIf (p > PrecLambda) $ PP.flatAlt long short
    Let x bs mty t body ->
      let x' = prettyIdent x
          bs' = prettyBinders bs
          mty' = prettyTerm PrecNone <$> mty
          t' = prettyTerm PrecNone t
          body' = prettyTerm PrecLambda body
          intro = "let" <+> x'
          header = prettyFnHeader intro bs' mty' ":="
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
      let f' = prettyTerm PrecApp f
          args' = map (prettyTerm PrecAtom) args
      in
      parensIf (p > PrecApp) $ PP.nest 5 $ PP.fillSep (f' : args')
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
          text ("0x" ++ ui' ++ "%Z")
      else if i < 0 then
          text ("(" ++ show i ++ ")%Z")
      else
          text (show i ++ "%Z")
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
      indices' = map prettyPiBinder inductiveIndices
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
  in
  PP.nest 2 (what <+> nm' <+> ":" <+> ty' <+> ".") <> PP.hardline

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
  Axiom nm ty -> prettyBasicDecl "Axiom" nm ty
  Parameter nm ty -> prettyBasicDecl "Parameter" nm ty
  Variable nm ty -> prettyBasicDecl "Variable" nm ty
  Comment s ->
    "(*" <+> text s <+> "*)" <> PP.hardline
  Definition nm binders mty body ->
    prettyDefinition nm binders mty body <> PP.hardline
  InductiveDecl ind ->
    prettyInductive ind <> PP.hardline
  Section nm ds ->
    let nm' = prettyIdent nm
        ds' = map (PP.indent 2 . prettyDecl) ds
        header = "Section" <+> nm' <+> "."
        footer = "End" <+> nm' <+> "."
    in
    -- XXX vsep issues soft newlines and there should be a hard newline
    -- after the head and after the foot. (Note that every other Decl
    -- always ends in a hard newline, so ds' is ok.)
    -- (XXX: Does `PP.vsep` on top of `PP.hardline` generate two lines?)
    PP.vsep $ [header] ++ ds' ++ [footer]
  Snippet s ->
    text s
