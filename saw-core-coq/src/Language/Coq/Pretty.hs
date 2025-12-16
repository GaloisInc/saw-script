{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : Language.Coq.Pretty
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Language.Coq.Pretty where

import Prettyprinter

import Language.Coq.AST
import Data.Word
import Numeric (showHex)
import Prelude hiding ((<$>), (<>))

-- | Replace all occurrences of the double quote character @"@ with the string
-- @""@, i.e., two copies of it, as this is how Coq escapes double quote
-- characters.
escapeStringLit :: String -> String
escapeStringLit = concatMap (\c -> if c == '"' then "\"\"" else [c])

text :: String -> Doc ann
text = pretty

string :: String -> Doc ann
string = pretty

integer :: Integer -> Doc ann
integer = pretty

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
hsep' :: [Doc ann] -> Doc ann
hsep' docs = case docs of
    [] -> emptyDoc
    _ : _ -> emptyDoc <+> hsep docs

-- This version glues the separator to the end of each element.
tightSepList :: Doc ann -> [Doc ann] -> Doc ann
tightSepList _ [] = mempty
tightSepList _ [d] = d
tightSepList s (d:l) = d <> s <+> tightSepList s l

-- This version issues space before the separator.
looseSepList :: Doc ann -> [Doc ann] -> Doc ann
looseSepList _ [] = mempty
looseSepList _ [d] = d
looseSepList s (d:l) = d <+> s <+> looseSepList s l

commaSepList, starSepList, semiSepList :: [Doc ann] -> Doc ann
commaSepList = tightSepList comma
starSepList = looseSepList "*"
semiSepList = tightSepList semi

period :: Doc ann
period = "."

prettyIdent :: Ident -> Doc ann
prettyIdent (Ident s) = pretty s

prettyNameType :: Ident -> Type -> Doc ann
prettyNameType x ty = prettyIdent x <+> colon <+> prettyTerm PrecNone ty

prettyBinder :: Binder -> Doc ann
prettyBinder b = case b of
    Binder False x Nothing   -> prettyIdent x
    Binder False x (Just ty) -> parens $ prettyNameType x ty
    Binder True x Nothing    -> braces $ prettyIdent x
    Binder True x (Just ty)  -> braces $ prettyNameType x ty

prettyPiBinder :: PiBinder -> Doc ann
prettyPiBinder b = case b of
    PiBinder False Nothing ty ->
        prettyTerm PrecApp ty <+> "->"
    PiBinder False (Just x) ty ->
        "forall" <+> parens (prettyNameType x ty) <> comma
    PiBinder True Nothing ty ->
        braces (prettyTerm PrecApp ty) <+> "->"
    PiBinder True (Just x) ty ->
        "forall" <+> braces (prettyNameType x ty) <> comma

prettyBinders :: [Binder] -> Doc ann
prettyBinders bs = hsep $ map prettyBinder bs

prettyMaybeTy :: Maybe Type -> Doc ann
prettyMaybeTy Nothing = mempty
prettyMaybeTy (Just ty) = colon <+> prettyTerm PrecNone ty

prettySort :: Sort -> Doc ann
prettySort s = case s of
    Prop -> "Prop"
    Set -> "Set"
    Type -> "Type"

prettyPiBinders :: [PiBinder] -> Doc ann
prettyPiBinders bs = hsep $ map prettyPiBinder bs

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
      parensIf (p > PrecLambda) $ fillSep [
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
      parensIf (p > PrecApp) $ hsep (f' : args')
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
      brackets $ semiSepList ts'
    StringLit s ->
      dquotes (string $ escapeStringLit s)
    Scope term scope ->
      let term' = prettyTerm PrecAtom term
          scope' = text scope
      in
      term' <> "%" <> scope'
    Ltac s ->
      "ltac:" <> parens (string s)

prettyBasicDecl :: Doc ann -> Ident -> Type -> Doc ann
prettyBasicDecl what nm ty =
  let nm' = prettyIdent nm
      ty' = prettyTerm PrecNone ty
  in
  nest 2 (what <+> nm' <+> ":" <+> ty' <+> period) <> hardline

prettyDecl :: Decl -> Doc ann
prettyDecl decl = case decl of
  Axiom nm ty -> prettyBasicDecl "Axiom" nm ty
  Parameter nm ty -> prettyBasicDecl "Parameter" nm ty
  Variable nm ty -> prettyBasicDecl "Variable" nm ty
  Comment s ->
    "(*" <+> text s <+> "*)" <> hardline
  Definition nm bs mty body ->
    let nm' = prettyIdent nm
        bs' = hsep' $ map prettyBinder bs
        mty' = prettyMaybeTy mty
        body' = prettyTerm PrecNone body
    in
    nest 2 (
      vsep [
          "Definition" <+> nm' <> bs' <+> mty' <+> ":=",
          body' <> period
      ]
    ) <> hardline
  InductiveDecl ind ->
    prettyInductive ind
  Section nm ds ->
    let nm' = prettyIdent nm
        ds' = map (indent 2 . prettyDecl) ds
        header = "Section" <+> nm' <+> period
        footer = "End" <+> nm' <+> period
    in
    -- XXX vsep issues soft newlines and there should be a hard newline
    -- after the head and after the foot. (Note that every other Decl
    -- always ends in a hard newline, so ds' is ok.)
    -- (XXX: Does `vsep` on top of `hardline` generate two lines?)
    vsep $ [header] ++ ds' ++ [footer]
  Snippet s ->
    text s

prettyConstructor :: Constructor -> Doc ann
prettyConstructor (Constructor {..}) =
  let name' = prettyIdent constructorName
      ty' = prettyTerm PrecNone constructorType
  in
  nest 2 $ "|" <+> name' <+> ":" <+> ty'

prettyInductive :: Inductive -> Doc ann
prettyInductive (Inductive {..}) =
  let name' = prettyIdent inductiveName
      params' = hsep' $ map prettyBinder inductiveParameters
      indices' = hsep' $ map prettyPiBinder inductiveIndices
      sort' = prettySort inductiveSort
      ctors' = map prettyConstructor inductiveConstructors
      header = "Inductive" <+> name' <> params' <+> ":" <> indices' <+> sort' <+> ":="
  in
  vsep ([nest 2 header] ++ ctors' ++ [period]) <> hardline

