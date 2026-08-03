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

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import Language.Rocq.AST
import Data.Word
import Numeric (showHex)

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

-- FUTURE: Move these to SAWSupport.Pretty

-- | Like hsep, but behaves usefully for lists that might be empty:
--   returns the empty doc like hsep for empty lists, but for
--   non-empty lists prepends horizontal space. The result can then
--   be inserted like this: x <> result <+> y, and will produce
--   either "x y" or "x result y" but not "x  y", which is what
--   happens if you do x <+> hsep ... <+> y.
--
--   This baloney arises because d1 <+> emptyDoc <+> d2 prints two
--   spaces instead of one, which I'd describe as a bug. If you
--   _really_ want to accumulate multiple spaces by concatenating
--   empty docs, which seems against the concept of prettyprinting
--   layout anyway, there can be another way to do that, like the
--   latex "phantom" object.
hsep' :: [PP.Doc ann] -> PP.Doc ann
hsep' docs = case docs of
    [] -> PP.emptyDoc
    _ : _ -> PP.emptyDoc <+> PP.hsep docs


-- | Print a list separated by @sepr@.
--   Glues the separator to the end of each element.
tightSepList :: PP.Doc ann -> [PP.Doc ann] -> PP.Doc ann
tightSepList _ [] = mempty
tightSepList _ [d] = d
tightSepList sepr (d:ds) = d <> sepr <+> tightSepList sepr ds

-- | Print an `Ident`
prettyIdent :: Ident -> PP.Doc ann
prettyIdent (Ident s) = text s

-- | Common code to print a name with a type
prettyNameType :: Ident -> Type -> PP.Doc ann
prettyNameType x ty = prettyIdent x <+> ":" <+> prettyTerm PrecNone ty

-- | Print an ordinary (lambda/let) binder
prettyBinder :: Binder -> PP.Doc ann
prettyBinder b = case b of
    Binder Explicit x Nothing   -> prettyIdent x
    Binder Explicit x (Just ty) -> PP.parens $ prettyNameType x ty
    Binder Implicit x Nothing    -> PP.braces $ prettyIdent x
    Binder Implicit x (Just ty)  -> PP.braces $ prettyNameType x ty

-- | Print a pi (forall) binder
--   (we don't seem to be able to represent @exists@)
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
prettyBinders :: [Binder] -> PP.Doc ann
prettyBinders bs = PP.hsep $ map prettyBinder bs

-- | Print an optional type annotation
prettyMaybeTy :: Maybe Type -> PP.Doc ann
prettyMaybeTy Nothing = PP.emptyDoc
prettyMaybeTy (Just ty) = ":" <+> prettyTerm PrecNone ty

-- | Print a `sort`
prettySort :: Sort -> PP.Doc ann
prettySort s = case s of
    Prop -> "Prop"
    Set -> "Set"
    Type -> "Type"

-- | Print a list of pi-binders
prettyPiBinders :: [PiBinder] -> PP.Doc ann
prettyPiBinders bs = PP.hsep $ map prettyPiBinder bs

-- | Type to hold the current expression precedence while printing
data Prec
  = PrecNone
  | PrecLambda
  | PrecApp
  | PrecAtom
  deriving (Eq, Ord)

-- | Insert parens based on the first argument
parensIf :: Bool -> PP.Doc ann -> PP.Doc ann
parensIf p d = if p then PP.parens d else d

-- | Print a term
prettyTerm :: Prec -> Term -> PP.Doc ann
prettyTerm p e =
  case e of
    Lambda bs t ->
      let bs' = prettyBinders bs
          t' = prettyTerm PrecLambda t
      in
      parensIf (p > PrecLambda) $ "fun" <+> bs' <+> "=>" <+> t'
    Fix ident binders returnType body ->
      let ident' = prettyIdent ident
          binders' = prettyBinders binders
          returnType' = prettyTerm PrecNone returnType
          body' = prettyTerm PrecLambda body
      in
      parensIf (p > PrecLambda) $
          "fix" <+> ident' <+> binders' <+> ":" <+> returnType' <+> ":=" <+> body'
    Pi bs t ->
      let bs' = prettyPiBinders bs
          t' = prettyTerm PrecLambda t
      in
      parensIf (p > PrecLambda) $ bs' <+> t'
    Let x bs mty t body ->
      let x' = prettyIdent x
          bs' = prettyBinders bs
          mty' = prettyMaybeTy mty
          t' = prettyTerm PrecNone t
          body' = prettyTerm PrecLambda body
      in
      parensIf (p > PrecLambda) $ PP.fillSep [
          "let" <+> x' <+> bs' <+> mty' <+> ":=" <+> t' <+> "in",
          body'
      ]
    If c t f ->
      let c' = prettyTerm PrecNone c
          t' = prettyTerm PrecNone t
          f' = prettyTerm PrecLambda f
      in
      parensIf (p > PrecLambda) $
          "if" <+> c' <+> "then" <+> t' <+> "else" <+> f'
    App f [] ->
      prettyTerm p f
    App f args ->
      let f' = prettyTerm PrecApp f
          args' = map (prettyTerm PrecAtom) args
      in
      parensIf (p > PrecApp) $ PP.hsep (f' : args')
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
      in
      parensIf (p > PrecLambda) $ tm' <+> ":" <+> tp'
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
      let ts' = map (prettyTerm PrecNone) ts in
      PP.brackets $ tightSepList ";" ts'
    StringLit s ->
      PP.dquotes (text $ escapeStringLit s)
    Scope term scope ->
      let term' = prettyTerm PrecAtom term
          scope' = text scope
      in
      term' <> "%" <> scope'
    Ltac s ->
      "ltac:" <> PP.parens (text s)

-- | Common code for the simple declarations
prettyBasicDecl :: PP.Doc ann -> Ident -> Type -> PP.Doc ann
prettyBasicDecl what nm ty =
  let nm' = prettyIdent nm
      ty' = prettyTerm PrecNone ty
  in
  PP.nest 2 (what <+> nm' <+> ":" <+> ty' <+> ".") <> PP.hardline

-- | Print a top-level declaration
prettyDecl :: Decl -> PP.Doc ann
prettyDecl decl = case decl of
  Axiom nm ty -> prettyBasicDecl "Axiom" nm ty
  Parameter nm ty -> prettyBasicDecl "Parameter" nm ty
  Variable nm ty -> prettyBasicDecl "Variable" nm ty
  Comment s ->
    "(*" <+> text s <+> "*)" <> PP.hardline
  Definition nm bs mty body ->
    let nm' = prettyIdent nm
        bs' = hsep' $ map prettyBinder bs
        mty' = prettyMaybeTy mty
        body' = prettyTerm PrecNone body
    in
    PP.nest 2 (
      PP.vsep [
          "Definition" <+> nm' <> bs' <+> mty' <+> ":=",
          body' <> "."
      ]
    ) <> PP.hardline
  InductiveDecl ind ->
    prettyInductive ind
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

-- | Print a single constructor
prettyConstructor :: Constructor -> PP.Doc ann
prettyConstructor (Constructor {..}) =
  let name' = prettyIdent constructorName
      ty' = prettyTerm PrecNone constructorType
  in
  PP.nest 2 $ "|" <+> name' <+> ":" <+> ty'

-- | Print an inductive type declaration
prettyInductive :: Inductive -> PP.Doc ann
prettyInductive (Inductive {..}) =
  let name' = prettyIdent inductiveName
      params' = hsep' $ map prettyBinder inductiveParameters
      indices' = hsep' $ map prettyPiBinder inductiveIndices
      sort' = prettySort inductiveSort
      ctors' = map prettyConstructor inductiveConstructors
      header = "Inductive" <+> name' <> params' <+> ":" <> indices' <+> sort' <+> ":="
  in
  PP.vsep ([PP.nest 2 header] ++ ctors' ++ ["."]) <> PP.hardline

