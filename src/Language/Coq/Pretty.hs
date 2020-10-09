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
ppBinder (Binder x (Just t)) = parens (ppIdent x <+> colon <+> ppTerm PrecNone t)

ppPiBinder :: PiBinder -> Doc
ppPiBinder (PiBinder Nothing t)  = ppTerm PrecApp t <+> text "->"
ppPiBinder (PiBinder (Just x) t) =
  text "forall" <+> parens (ppIdent x <+> colon <+> ppTerm PrecNone t) <> comma

ppBinders :: [Binder] -> Doc
ppBinders = hsep . map ppBinder

ppMaybeTy :: Maybe Type -> Doc
ppMaybeTy Nothing = empty
ppMaybeTy (Just ty) = colon <+> ppTerm PrecNone ty

ppSort :: Sort -> Doc
ppSort Prop = text "Prop"
ppSort Set = text "Set"
ppSort Type = text "Type"

ppPi :: [PiBinder] -> Doc
ppPi bs = hsep (map ppPiBinder bs)

data Prec
  = PrecNone
  | PrecLambda
  | PrecApp
  | PrecAtom
  deriving (Eq, Ord)

parensIf :: Bool -> Doc -> Doc
parensIf p d = if p then parens d else d

ppTerm :: Prec -> Term -> Doc
ppTerm p e =
  case e of
    Lambda bs t ->
      parensIf (p > PrecLambda) $
      (text "fun" <+> ppBinders bs <+> text "=>" <+> ppTerm PrecLambda t)
    Fix ident binders returnType body ->
      parensIf (p > PrecLambda) $
      (text "fix" <+> text ident <+> ppBinders binders <+> text ":"
             <+> ppTerm PrecNone returnType <+> text ":=" <+> ppTerm PrecLambda body)
    Pi bs t ->
      parensIf (p > PrecLambda) $
      ppPi bs <+> ppTerm PrecLambda t
    Let x bs mty t body ->
      parensIf (p > PrecLambda) $
      text "let" <+> ppIdent x <+> ppBinders bs <+> ppMaybeTy mty <+>
      text ":=" <+> ppTerm PrecNone t <+> text "in" </> ppTerm PrecLambda body
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
    Var x ->
      ppIdent x
    NatLit i ->
      integer i
    List ts ->
      brackets (semiSepList (map (ppTerm PrecNone) ts))
    StringLit s ->
      dquotes (string s)
    Scope term scope ->
      ppTerm PrecAtom term <> text "%" <> text scope
    Ltac s ->
      text "ltac:" <> parens (string s)

ppDecl :: Decl -> Doc
ppDecl decl = case decl of
  Axiom nm ty ->
    (nest 2 $
     hsep ([text "Axiom", text nm, text ":", ppTerm PrecNone ty, period])) <> hardline
  Comment s ->
    text "(*" <+> text s <+> text "*)" <> hardline
  Definition nm bs mty body ->
    (nest 2 $
     hsep ([text "Definition", text nm] ++
          map ppBinder bs ++
          [ppMaybeTy mty, text ":="]) <$>
     ppTerm PrecNone body <> period) <> hardline
  InductiveDecl ind -> ppInductive ind
  Snippet s -> text s

ppConstructor :: Constructor -> Doc
ppConstructor (Constructor {..}) =
  nest 2 $
  hsep ([ text "|"
        , text constructorName
        , text ":"
        , ppTerm PrecNone constructorType
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
