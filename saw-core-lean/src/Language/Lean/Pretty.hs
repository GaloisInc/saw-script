{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : Language.Lean.Pretty
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable

Pretty printer for "Language.Lean.AST". Structured as a mirror of
"Language.Rocq.Pretty"; Lean-specific adjustments are documented
alongside each diverging case.
-}

module Language.Lean.Pretty (prettyDecl) where

import Prettyprinter

import Language.Lean.AST
import Prelude hiding ((<$>), (<>))

-- | Lean string literals use C-style backslash escapes, not Rocq's
-- @""@ doubling.
escapeStringLit :: String -> String
escapeStringLit = concatMap $ \c -> case c of
  '"'  -> "\\\""
  '\\' -> "\\\\"
  '\n' -> "\\n"
  _    -> [c]

text :: String -> Doc ann
text = pretty

string :: String -> Doc ann
string = pretty

integer :: Integer -> Doc ann
integer = pretty

-- FUTURE: Move these to SAWSupport.Pretty

-- | Like hsep, but behaves usefully for lists that might be empty:
--   returns the empty doc like hsep for empty lists, but for
--   non-empty lists prepends horizontal space.
hsep' :: [Doc ann] -> Doc ann
hsep' docs = case docs of
    [] -> emptyDoc
    _ : _ -> emptyDoc <+> hsep docs

-- | Glues the separator to the end of each element.
tightSepList :: Doc ann -> [Doc ann] -> Doc ann
tightSepList _ [] = mempty
tightSepList _ [d] = d
tightSepList s (d:l) = d <> s <+> tightSepList s l

prettyIdent :: Ident -> Doc ann
prettyIdent (Ident s) = pretty s

prettyNameType :: Ident -> Type -> Doc ann
prettyNameType x ty = prettyIdent x <+> colon <+> prettyTerm PrecNone ty

prettyBinder :: Binder -> Doc ann
prettyBinder b = case b of
    Binder Explicit x Nothing   -> prettyIdent x
    Binder Explicit x (Just ty) -> parens $ prettyNameType x ty
    Binder Implicit x Nothing   -> braces $ prettyIdent x
    Binder Implicit x (Just ty) -> braces $ prettyNameType x ty
    Binder Instance x Nothing   -> brackets $ prettyIdent x
    Binder Instance x (Just ty) -> brackets $ prettyNameType x ty

-- | Lean pi binders print as arrows uniformly:
--
-- * anonymous explicit: @A -> rest@
-- * named explicit:     @(x : A) -> rest@
-- * anonymous implicit: @{_ : A} -> rest@
-- * named implicit:     @{x : A} -> rest@
-- * instance:           @[x : A] -> rest@ (or @[A] -> rest@ if
--   anonymous, which is how Lean idiomatically names typeclass args)
--
-- Rocq uses @forall (x : A),@ for named binders and @->@ only for
-- anonymous ones. Lean 4 accepts @(x : A) -> rest@ and @forall (x : A),
-- rest@ interchangeably; using @->@ uniformly keeps the printer simple.
prettyPiBinder :: PiBinder -> Doc ann
prettyPiBinder b = case b of
    PiBinder Explicit Nothing ty ->
        prettyTerm PrecApp ty <+> "->"
    PiBinder Explicit (Just x) ty ->
        parens (prettyNameType x ty) <+> "->"
    PiBinder Implicit Nothing ty ->
        -- @{_ : ty}@ not @{ty}@ — the latter is valid Lean surface
        -- syntax but parses as a singleton-set literal, not an
        -- anonymous implicit binder.
        braces ("_" <+> colon <+> prettyTerm PrecNone ty) <+> "->"
    PiBinder Implicit (Just x) ty ->
        braces (prettyNameType x ty) <+> "->"
    PiBinder Instance Nothing ty ->
        brackets (prettyTerm PrecNone ty) <+> "->"
    PiBinder Instance (Just x) ty ->
        brackets (prettyNameType x ty) <+> "->"

prettyBinders :: [Binder] -> Doc ann
prettyBinders bs = hsep $ map prettyBinder bs

prettySort :: Sort -> Doc ann
prettySort s = case s of
    Prop             -> "Prop"
    TypeLvl 0        -> "Type"
    TypeLvl n        -> "Type" <+> pretty n
    SortVar u        -> "Sort" <+> pretty u
    SortMax1Var u    -> "Sort" <+> parens ("max 1" <+> pretty u)
    SortMax1Vars []  -> "Type"
    SortMax1Vars [u] -> "Sort" <+> parens ("max 1" <+> pretty u)
    SortMax1Vars us  ->
      "Sort" <+> parens ("max 1" <+> parens (foldr1 (\a b -> "max" <+> a <+> b) (map pretty us)))

data Prec
  = PrecNone
  | PrecLambda
  | PrecApp
  | PrecAtom
  deriving (Eq, Ord)

parensIf :: Bool -> Doc ann -> Doc ann
parensIf p d = if p then parens d else d

prettyTerm :: Prec -> Term -> Doc ann
prettyTerm p e =
  case e of
    Lambda bs t ->
      let bs' = prettyBinders bs
          t' = prettyTerm PrecLambda t
      in
      parensIf (p > PrecLambda) $ "fun" <+> bs' <+> "=>" <+> t'
    Pi bs t ->
      let binderDocs = map prettyPiBinder bs
          t' = prettyTerm PrecLambda t
      in
      -- @fillSep@ breaks between binders if the whole line exceeds
      -- width, @group@ lets it stay flat when it fits.
      parensIf (p > PrecLambda) $ group $ fillSep (binderDocs ++ [t'])
    Let x bs mty t body ->
      -- Lean 4 term-mode let has no @in@ keyword. @;@ separates on one
      -- line; a bare newline works across lines. Using @;@ is layout-robust.
      let x' = prettyIdent x
          binderDocs = map prettyBinder bs
          mtyDocs = maybe [] (\ty -> [colon, prettyTerm PrecNone ty]) mty
          t' = prettyTerm PrecNone t
          body' = prettyTerm PrecLambda body
          -- Build the @let x [bs] [: ty] := t;@ header by composing
          -- non-empty parts — avoids double spaces when @bs@ or @mty@
          -- are absent.
          header = hsep (["let", x'] ++ binderDocs ++ mtyDocs ++ [":=", t']) <> semi
      in
      parensIf (p > PrecLambda) $ fillSep [header, body']
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
      -- @group (hang 2 (fillSep ...))@ keeps the call on one line when
      -- it fits, otherwise breaks at arg boundaries and indents
      -- continuation lines by 2.
      parensIf (p > PrecApp) $ group $ hang 2 $ fillSep (f' : args')
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
      -- Lean's @Nat@ is arbitrary-precision and backed by machine ints,
      -- so no @Z.to_nat@ wrapper is needed for large literals.
      integer i
    IntLit i ->
      -- Emit with explicit @Int@ ascription. Always parenthesize: the
      -- surrounding context at @PrecNone@ (e.g. the RHS of @:=@) would
      -- otherwise leave the ascription @:@ syntactically ambiguous.
      parens $ integer i <+> ":" <+> "Int"
    List ts ->
      -- Lean lists use commas; Rocq uses semicolons.
      let ts' = map (prettyTerm PrecNone) ts in
      brackets $ tightSepList comma ts'
    StringLit s ->
      dquotes (string $ escapeStringLit s)
    Tactic s ->
      parensIf (p > PrecLambda) $ "by" <+> text s

-- | Lean declarations have no trailing @.@ — newlines end each decl.
-- @prettyUnivs@ renders a universe-variable list as @.{u, v, w}@
-- (comma-separated; Lean 4 rejects space-separated lists) or
-- 'mempty' when the list is empty.
prettyUnivs :: [String] -> Doc ann
prettyUnivs [] = mempty
prettyUnivs us = "." <> braces (hsep (punctuate comma (map pretty us)))

prettyDecl :: Decl -> Doc ann
prettyDecl decl = case decl of
  Axiom univs nm ty ->
    -- Lean places universe binders on the /name/, not on the keyword:
    -- @axiom foo.{u v} : …@, not @axiom.{u v} foo : …@.
    let header = "axiom" <+> prettyIdent nm <> prettyUnivs univs <+> ":"
        ty'    = prettyTerm PrecNone ty
    in
    nest 2 (header <+> ty') <> hardline
  Variable nm ty ->
    -- Lean @variable@ requires parens around the binder.
    let nm' = prettyIdent nm
        ty' = prettyTerm PrecNone ty
    in
    "variable" <+> parens (nm' <+> ":" <+> ty') <> hardline
  Comment s ->
    "/-" <+> text s <+> "-/" <> hardline
  Definition nc univs nm bs mty body ->
    let nm'        = prettyIdent nm <> prettyUnivs univs
        binderDocs = map prettyBinder bs
        mtyDocs    = maybe [] (\ty -> [colon, prettyTerm PrecNone ty]) mty
        body'      = prettyTerm PrecNone body
        keyword    = case nc of
                       Noncomputable -> ["noncomputable", "def"]
                       Computable    -> ["def"]
        -- Compose non-empty parts via @hsep@ so empty binders /
        -- missing type annotation don't produce double spaces.
        header     = hsep (keyword ++ [nm'] ++ binderDocs ++ mtyDocs ++ [":="])
    in
    nest 2 (vsep [header, body']) <> hardline
  InductiveDecl ind ->
    prettyInductive ind
  Namespace nm ds ->
    -- Rocq @Section X. ... End X.@ becomes Lean @namespace X ... end X@.
    let nm' = prettyIdent nm
        ds' = map (indent 2 . prettyDecl) ds
        header = "namespace" <+> nm'
        footer = "end" <+> nm'
    in
    vsep $ [header] ++ ds' ++ [footer]
  Snippet s ->
    text s

prettyConstructor :: Constructor -> Doc ann
prettyConstructor (Constructor {..}) =
  let name' = prettyIdent constructorName
      ty' = prettyTerm PrecNone constructorType
  in
  nest 2 $ "|" <+> name' <+> ":" <+> ty'

-- | Lean inductives use the @where@ keyword (not @:=@) and have no
-- trailing @.@ sentinel.
prettyInductive :: Inductive -> Doc ann
prettyInductive (Inductive {..}) =
  let name' = prettyIdent inductiveName <> prettyUnivs inductiveUniverses
      params' = hsep' $ map prettyBinder inductiveParameters
      indices' = hsep' $ map prettyPiBinder inductiveIndices
      sort' = prettySort inductiveSort
      ctors' = map prettyConstructor inductiveConstructors
      header = "inductive" <+> name' <> params' <+> ":" <> indices' <+> sort' <+> "where"
  in
  vsep (nest 2 header : ctors') <> hardline
