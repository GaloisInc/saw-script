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

-- TODO: import SAWCore pretty-printer?
tightSepList :: Doc ann -> [Doc ann] -> Doc ann
tightSepList _ [] = mempty
tightSepList _ [d] = d
tightSepList s (d:l) = d <> s <+> tightSepList s l

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

ppIdent :: Ident -> Doc ann
ppIdent (Ident s) = text s

ppBinder :: Binder -> Doc ann
ppBinder (Binder x Nothing)  = ppIdent x
ppBinder (Binder x (Just t)) = parens (ppIdent x <+> colon <+> ppTerm PrecNone t)
ppBinder (ImplicitBinder x Nothing)  = braces (ppIdent x)
ppBinder (ImplicitBinder x (Just t)) = braces (ppIdent x <+> colon <+> ppTerm PrecNone t)

ppPiBinder :: PiBinder -> Doc ann
ppPiBinder (PiBinder Nothing t)  = ppTerm PrecApp t <+> text "->"
ppPiBinder (PiBinder (Just x) t) =
  text "forall" <+> parens (ppIdent x <+> colon <+> ppTerm PrecNone t) <> comma
ppPiBinder (PiImplicitBinder Nothing t)  = braces (ppTerm PrecApp t) <+> text "->"
ppPiBinder (PiImplicitBinder (Just x) t) =
  text "forall" <+> braces (ppIdent x <+> colon <+> ppTerm PrecNone t) <> comma

ppBinders :: [Binder] -> Doc ann
ppBinders = hsep . map ppBinder

ppMaybeTy :: Maybe Type -> Doc ann
ppMaybeTy Nothing = mempty
ppMaybeTy (Just ty) = colon <+> ppTerm PrecNone ty

ppSort :: Sort -> Doc ann
ppSort Prop = text "Prop"
ppSort Set = text "Set"
ppSort Type = text "Type"

ppPi :: [PiBinder] -> Doc ann
ppPi bs = hsep (map ppPiBinder bs)

data Prec
  = PrecNone
  | PrecLambda
  | PrecApp
  | PrecAtom
  deriving (Eq, Ord)

parensIf :: Bool -> Doc ann -> Doc ann
parensIf p d = if p then parens d else d

ppTerm :: Prec -> Term -> Doc ann
ppTerm p e =
  case e of
    Lambda bs t ->
      parensIf (p > PrecLambda) $
      text "fun" <+> ppBinders bs <+> text "=>" <+> ppTerm PrecLambda t
    Fix ident binders returnType body ->
      parensIf (p > PrecLambda) $
      text "fix" <+> ppIdent ident <+> ppBinders binders <+> text ":"
        <+> ppTerm PrecNone returnType <+> text ":=" <+> ppTerm PrecLambda body
    Pi bs t ->
      parensIf (p > PrecLambda) $
      ppPi bs <+> ppTerm PrecLambda t
    Let x bs mty t body ->
      parensIf (p > PrecLambda) $
      fillSep
      [ text "let" <+> ppIdent x <+> ppBinders bs <+> ppMaybeTy mty <+>
        text ":=" <+> ppTerm PrecNone t <+> text "in"
      , ppTerm PrecLambda body ]
    If c t f ->
      parensIf (p > PrecLambda) $
      text "if" <+> ppTerm PrecNone c <+>
      text "then" <+> ppTerm PrecNone t <+>
      text "else" <+> ppTerm PrecLambda f
    App f [] ->
      ppTerm p f
    App f args ->
      parensIf (p > PrecApp) $
      hsep (ppTerm PrecApp f : map (ppTerm PrecAtom) args)
    Sort s ->
      ppSort s
    Var x -> ppIdent x
    ExplVar x ->
      parensIf (p > PrecApp) $
      string "@" <> ppIdent x
    Ascription tm tp ->
      parensIf (p > PrecLambda)
      (ppTerm PrecApp tm <+> text ":" <+> ppTerm PrecApp tp)
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
      brackets (semiSepList (map (ppTerm PrecNone) ts))
    StringLit s ->
      dquotes (string $ escapeStringLit s)
    Scope term scope ->
      ppTerm PrecAtom term <> text "%" <> text scope
    Ltac s ->
      text "ltac:" <> parens (string s)

ppDecl :: Decl -> Doc ann
ppDecl decl = case decl of
  Axiom nm ty ->
    nest 2 (
      hsep [text "Axiom", ppIdent nm, text ":", ppTerm PrecNone ty, period]
    ) <> hardline
  Parameter nm ty ->
    nest 2 (
     hsep [text "Parameter", ppIdent nm, text ":", ppTerm PrecNone ty, period]
    ) <> hardline
  Variable nm ty ->
    nest 2 (
      hsep [text "Variable", ppIdent nm, text ":", ppTerm PrecNone ty, period]
    ) <> hardline
  Comment s ->
    text "(*" <+> text s <+> text "*)" <> hardline
  Definition nm bs mty body ->
    nest 2 (
      vsep
      [ hsep ([text "Definition", ppIdent nm] ++
             map ppBinder bs ++
             [ppMaybeTy mty, text ":="])
      , ppTerm PrecNone body <> period
      ]
    ) <> hardline
  InductiveDecl ind -> ppInductive ind
  Section nm ds ->
    vsep $ concat
     [ [ hsep [text "Section", ppIdent nm, period] ]
     , map (indent 2 . ppDecl) ds
     , [ hsep [text "End", ppIdent nm, period] ]
     ]
  Snippet s -> text s

ppConstructor :: Constructor -> Doc ann
ppConstructor (Constructor {..}) =
  nest 2 $
  hsep [ text "|"
       , ppIdent constructorName
       , text ":"
       , ppTerm PrecNone constructorType
       ]

ppInductive :: Inductive -> Doc ann
ppInductive (Inductive {..}) =
  (vsep
   ([ nest 2 $
      hsep ([ text "Inductive"
            , ppIdent inductiveName
            ]
            ++ map ppBinder inductiveParameters
            ++ [ text ":" ]
            ++ map ppPiBinder inductiveIndices
            ++ [ ppSort inductiveSort ]
            ++ [ text ":="]
           )
    ]
    <> map ppConstructor inductiveConstructors
    <> [ period ]
   )
  ) <> hardline
