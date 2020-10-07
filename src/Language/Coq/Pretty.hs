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

import Text.PrettyPrint.ANSI.Leijen
import Language.Coq.AST
import Prelude hiding ((<$>), (<>))

-- | Replace all occurrences of the double quote character @"@ with the string
-- @""@, i.e., two copies of it, as this is how Coq escapes double quote
-- characters.
escapeStringLit :: String -> String
escapeStringLit = concat . map (\c -> if c == '"' then "\"\"" else [c])

-- TODO: import SAWCore pretty-printer?
tightSepList :: Doc -> [Doc] -> Doc
tightSepList _ [] = empty
tightSepList _ [d] = d
tightSepList s (d:l) = d <> s <+> tightSepList s l

looseSepList :: Doc -> [Doc] -> Doc
looseSepList _ [] = empty
looseSepList _ [d] = d
looseSepList s (d:l) = d <+> s <+> looseSepList s l

commaSepList, starSepList, semiSepList :: [Doc] -> Doc
commaSepList = tightSepList comma
starSepList = looseSepList (text "*")
semiSepList = tightSepList semi

period :: Doc
period = text "."

ppIdent :: Ident -> Doc
ppIdent = text

ppBinder :: Binder -> Doc
ppBinder (Binder x Nothing)  = ppIdent x
ppBinder (Binder x (Just t)) = parens (ppIdent x <+> colon <+> ppTerm t)

ppPiBinder :: PiBinder -> Doc
ppPiBinder (PiBinder Nothing t)  = parens (ppTerm t) <+> text "->"
ppPiBinder (PiBinder (Just x) t) =
  text "forall" <+> lparen <> ppIdent x <+> colon <+> ppTerm t <> rparen <> comma

ppBinders :: [Binder] -> Doc
ppBinders = hsep . map ppBinder

ppMaybeTy :: Maybe Type -> Doc
ppMaybeTy Nothing = empty
ppMaybeTy (Just ty) = colon <+> ppTerm ty

ppSort :: Sort -> Doc
ppSort Prop = text "Prop"
ppSort Set = text "Set"
ppSort Type = text "Type"

ppPi :: [PiBinder] -> Doc
ppPi bs = hsep (map ppPiBinder bs)

ppTerm :: Term -> Doc
ppTerm e =
  case e of
    Lambda bs t ->
      parens (text "fun" <+> ppBinders bs <+> text "=>" <+> ppTerm t)
    Fix ident binders returnType body ->
      parens (text "fix" <+> text ident <+> ppBinders binders <+> text ":"
             <+> ppTerm returnType <+> text ":=" <+> ppTerm body)
    Pi bs t ->
      ppPi bs <+> ppTerm t
    Let x bs mty t body ->
      text "let" <+> ppIdent x <+> ppBinders bs <+> ppMaybeTy mty <+>
      text ":=" <+> ppTerm t <+> text "in" <+> ppTerm body
    If c t f ->
      text "if" <+> ppTerm c <+>
      text "then" <+> ppTerm t <+>
      text "else" <+> ppTerm f
    App f args ->
      -- FIXME: super conservative parenthesizing because precedence is not
      -- implemented
      -- NOTE: parens around f, because (App (If c a b) d) must print as
      -- ((if c then a else b) d)
      -- or else the d is applied to b only...
      parens (hsep (parens (ppTerm f) : map (parens . ppTerm) args))
    Sort s ->
      ppSort s
    Var x ->
      ppIdent x
    NatLit i ->
      integer i
    List ts ->
      brackets (semiSepList (map ppTerm ts))
    StringLit s ->
      dquotes (string $ escapeStringLit s)
    Scope term scope ->
      parens (ppTerm term) <> text "%" <> text scope
    Ltac s ->
      text "ltac:" <> parens (string s)

ppDecl :: Decl -> Doc
ppDecl decl = case decl of
  Axiom nm ty ->
    (nest 2 $
     hsep ([text "Axiom", text nm, text ":", ppTerm ty, period])) <> hardline
  Comment s ->
    text "(*" <+> text s <+> text "*)" <> hardline
  Definition nm bs mty body ->
    (nest 2 $
     hsep ([text "Definition", text nm] ++
          map ppBinder bs ++
          [ppMaybeTy mty, text ":="]) <$>
     ppTerm body <> period) <> hardline
  InductiveDecl ind -> ppInductive ind
  Snippet s -> text s

ppConstructor :: Constructor -> Doc
ppConstructor (Constructor {..}) =
  nest 2 $
  hsep ([ text "|"
        , text constructorName
        , text ":"
        , ppTerm constructorType
        ]
       )

ppInductive :: Inductive -> Doc
ppInductive (Inductive {..}) =
  (vsep
   ([ nest 2 $
      hsep ([ text "Inductive"
            , text inductiveName
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
