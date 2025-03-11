{- |
Module      : SAWCentral.JavaPretty
Description : Pretty printer for Java Class datatype.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE OverloadedStrings #-}

module SAWCentral.JavaPretty where

import Prettyprinter

import Language.JVM.Common

import Lang.JVM.Codebase

prettyClass :: Class -> Doc ann
prettyClass cls = vcat $
  [ emptyDoc
  , "Class name:" <+> prettyClassName (className cls) <+>
    parens (commas attrs)
  , "Superclass:" <+> maybe "none" prettyClassName (superClass cls)
  , emptyDoc
  ] ++
  (if null (classInterfaces cls)
      then []
      else [ "Interfaces:"
           , indent 2 (vcat (map prettyClassName (classInterfaces cls)))
           , emptyDoc
           ]) ++
  [ "Fields:"
  , indent 2 (vcat (map prettyField (classFields cls)))
  , emptyDoc
  , "Methods:"
  , indent 2 (vcat (map prettyMethod (classMethods cls)))
  , emptyDoc
  ]
  where attrs = concat
          [ if classIsPublic cls then ["public"] else []
          , if classIsFinal cls then ["final"] else []
          , if classHasSuperAttribute cls then ["super"] else []
          , if classIsInterface cls then ["interface"] else []
          , if classIsAbstract cls then ["abstract"] else []
          ]

-- FIXME: avoid unpacking via String
prettyClassName :: ClassName -> Doc ann
prettyClassName cname = pretty (unClassName cname)

prettyField :: Field -> Doc ann
prettyField f = hsep $
  [ viaShow (fieldVisibility f) ] ++
  attrs ++
  [ ppType (fieldType f)
  , pretty (fieldName f)
  ]
  where attrs = concat
          [ if fieldIsStatic f then ["static"] else []
          , if fieldIsFinal f then ["final"] else []
          , if fieldIsVolatile f then ["volatile"] else []
          , if fieldIsTransient f then ["transient"] else []
          ]

prettyMethod :: Method -> Doc ann
prettyMethod m =
  hsep $
  (if methodIsStatic m then ["static"] else []) ++
  [ maybe "void" ppType ret
  , pretty name
  , (parens . commas . map ppType) params
  ]
  where (MethodKey name params ret) = methodKey m

commas :: [Doc ann] -> Doc ann
commas = sep . punctuate comma
