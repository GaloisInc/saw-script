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
starSepList = looseSepList (text "*")
semiSepList = tightSepList semi

period :: Doc ann
period = text "."

prettyIdent :: Ident -> Doc ann
prettyIdent (Ident s) = text s

prettyNameType :: Ident -> Type -> Doc ann
prettyNameType x ty = prettyIdent x <+> colon <+> prettyTerm PrecNone ty

prettyBinder :: Binder -> Doc ann
prettyBinder b = case b of
    Binder x Nothing -> prettyIdent x
    Binder x (Just ty) -> parens $ prettyNameType x ty
    ImplicitBinder x Nothing -> braces $ prettyIdent x
    ImplicitBinder x (Just ty) -> braces $ prettyNameType x ty

prettyPiBinder :: PiBinder -> Doc ann
prettyPiBinder b = case b of
    PiBinder Nothing ty ->
        prettyTerm PrecApp ty <+> text "->"
    PiBinder (Just x) ty ->
        text "forall" <+> parens (prettyNameType x ty) <> comma
    PiImplicitBinder Nothing ty ->
        braces (prettyTerm PrecApp ty) <+> text "->"
    PiImplicitBinder (Just x) ty ->
        text "forall" <+> braces (prettyNameType x ty) <> comma

prettyBinders :: [Binder] -> Doc ann
prettyBinders bs = hsep $ map prettyBinder bs

prettyMaybeTy :: Maybe Type -> Doc ann
prettyMaybeTy Nothing = mempty
prettyMaybeTy (Just ty) = colon <+> prettyTerm PrecNone ty

prettySort :: Sort -> Doc ann
prettySort s = case s of
    Prop -> text "Prop"
    Set -> text "Set"
    Type -> text "Type"

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
      parensIf (p > PrecLambda) $
      text "fun" <+> prettyBinders bs <+> text "=>" <+> prettyTerm PrecLambda t
    Fix ident binders returnType body ->
      parensIf (p > PrecLambda) $
      text "fix" <+> prettyIdent ident <+> prettyBinders binders <+> text ":"
        <+> prettyTerm PrecNone returnType <+> text ":=" <+> prettyTerm PrecLambda body
    Pi bs t ->
      parensIf (p > PrecLambda) $
      prettyPiBinders bs <+> prettyTerm PrecLambda t
    Let x bs mty t body ->
      parensIf (p > PrecLambda) $
      fillSep
      [ text "let" <+> prettyIdent x <+> prettyBinders bs <+> prettyMaybeTy mty <+>
        text ":=" <+> prettyTerm PrecNone t <+> text "in"
      , prettyTerm PrecLambda body ]
    If c t f ->
      parensIf (p > PrecLambda) $
      text "if" <+> prettyTerm PrecNone c <+>
      text "then" <+> prettyTerm PrecNone t <+>
      text "else" <+> prettyTerm PrecLambda f
    App f [] ->
      prettyTerm p f
    App f args ->
      parensIf (p > PrecApp) $
      hsep (prettyTerm PrecApp f : map (prettyTerm PrecAtom) args)
    Sort s ->
      prettySort s
    Var x ->
      prettyIdent x
    ExplVar x ->
      parensIf (p > PrecApp) $
      string "@" <> prettyIdent x
    Ascription tm tp ->
      parensIf (p > PrecLambda)
      (prettyTerm PrecApp tm <+> text ":" <+> prettyTerm PrecApp tp)
    NatLit i ->
      if i > 1000 then
        -- Explicitly convert from Z if an integer is too big
        parensIf (p > PrecLambda) (text "Z.to_nat" <+> integer i <> text "%Z")
      else
        integer i
    ZLit i ->
      -- we use hex unless our integer is a positive or negitive digit
      if abs i > 9  then let ui = toInteger (fromInteger i :: Word64)
                          in text ("0x" ++ showHex ui [] ++ "%Z")
      else if i < 0 then text ("(" ++ show i ++ ")%Z")
                    else text (show i ++ "%Z")
    List ts ->
      brackets (semiSepList (map (prettyTerm PrecNone) ts))
    StringLit s ->
      dquotes (string $ escapeStringLit s)
    Scope term scope ->
      prettyTerm PrecAtom term <> text "%" <> text scope
    Ltac s ->
      text "ltac:" <> parens (string s)

prettyDecl :: Decl -> Doc ann
prettyDecl decl = case decl of
  Axiom nm ty ->
    nest 2 (
      hsep [text "Axiom", prettyIdent nm, text ":", prettyTerm PrecNone ty, period]
    ) <> hardline
  Parameter nm ty ->
    nest 2 (
     hsep [text "Parameter", prettyIdent nm, text ":", prettyTerm PrecNone ty, period]
    ) <> hardline
  Variable nm ty ->
    nest 2 (
      hsep [text "Variable", prettyIdent nm, text ":", prettyTerm PrecNone ty, period]
    ) <> hardline
  Comment s ->
    text "(*" <+> text s <+> text "*)" <> hardline
  Definition nm bs mty body ->
    nest 2 (
      vsep
      [ hsep ([text "Definition", prettyIdent nm] ++
             map prettyBinder bs ++
             [prettyMaybeTy mty, text ":="])
      , prettyTerm PrecNone body <> period
      ]
    ) <> hardline
  InductiveDecl ind -> prettyInductive ind
  Section nm ds ->
    vsep $ concat
     [ [ hsep [text "Section", prettyIdent nm, period] ]
     , map (indent 2 . prettyDecl) ds
     , [ hsep [text "End", prettyIdent nm, period] ]
     ]
  Snippet s -> text s

prettyConstructor :: Constructor -> Doc ann
prettyConstructor (Constructor {..}) =
  nest 2 $
  hsep [ text "|"
       , prettyIdent constructorName
       , text ":"
       , prettyTerm PrecNone constructorType
       ]

prettyInductive :: Inductive -> Doc ann
prettyInductive (Inductive {..}) =
  (vsep
   ([ nest 2 $
      hsep ([ text "Inductive"
            , prettyIdent inductiveName
            ]
            ++ map prettyBinder inductiveParameters
            ++ [ text ":" ]
            ++ map prettyPiBinder inductiveIndices
            ++ [ prettySort inductiveSort ]
            ++ [ text ":="]
           )
    ]
    <> map prettyConstructor inductiveConstructors
    <> [ period ]
   )
  ) <> hardline
