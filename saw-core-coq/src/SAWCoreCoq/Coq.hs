{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

{- |
Module      : SAWCoreCoq.Coq
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module SAWCoreCoq.Coq (
  TranslationConfiguration(..),
  moduleDeclName,
  preamble,
  TermTranslation.translateDefDoc,
  translateTermAsDeclImports,
  translateCryptolModule,
  translateSAWModule,
  ) where

import           Data.String.Interpolate                       (i)
import           Prelude                                       hiding (fail)
import           Prettyprinter

import qualified Language.Coq.AST                              as Coq
import qualified Language.Coq.Pretty                           as Coq
import           Verifier.SAW.Module
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Term.Functor
-- import Verifier.SAW.Term.CtxTerm
import qualified SAWCoreCoq.CryptolModule    as CMT
import qualified SAWCoreCoq.SAWModule        as SAWModuleTranslation
import           SAWCoreCoq.Monad
import           SAWCoreCoq.SpecialTreatment
import qualified SAWCoreCoq.Term             as TermTranslation
import           Verifier.SAW.TypedTerm
import           Verifier.SAW.Cryptol (Env)

text :: String -> Doc ann
text = pretty

-- | Generate a preamble for a Coq file, containing a list of Coq imports. This
-- includes standard imports, one of which is the @VectorNotations@ module to
-- support the vector literals used to translate SAW core array values, along
-- with any user-supplied imports in the 'postPreamble' field of the
-- supplied 'TranslationConfiguration'.
preamble :: TranslationConfiguration -> Doc ann
preamble (TranslationConfiguration { vectorModule, postPreamble }) = text [i|
(** Mandatory imports from saw-core-coq *)
From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import #{vectorModule}.
Import VectorNotations.

(** Post-preamble section specified by you *)
#{postPreamble}

(** Code generated by saw-core-coq *)
|]

translateTermAsDeclImports ::
  TranslationConfiguration -> Coq.Ident -> Term -> Term ->
  Either (TranslationError Term) (Doc ann)
translateTermAsDeclImports configuration name t tp = do
  doc <-
    TermTranslation.translateDefDoc
      configuration
      Nothing
      [] name t tp
  return $ vcat [preamble configuration, hardline <> doc]

-- | Translate a SAW core module to a Coq module
translateSAWModule :: TranslationConfiguration -> Module -> Doc ann
translateSAWModule configuration m =
  let name = show $ translateModuleName (moduleName m)
  in
  vcat $ []
  ++ [ text $ "Module " ++ name ++ "."
     , ""
     ]
  ++ [ SAWModuleTranslation.translateDecl configuration (Just $ moduleName m) decl
     | decl <- moduleDecls m ]
  ++ [ text $ "End " ++ name ++ "."
     , ""
     ]

-- | Translate a Cryptol module to a Coq module
translateCryptolModule ::
  SharedContext -> Env ->
  Coq.Ident {- ^ Section name -} ->
  TranslationConfiguration ->
  -- | List of already translated global declarations
  [String] ->
  CryptolModule ->
  IO (Either (TranslationError Term) (Doc ann))
translateCryptolModule sc env nm configuration globalDecls m = do
  translated <- CMT.translateCryptolModule sc env configuration globalDecls m
  return $ Coq.ppDecl . Coq.Section (escapeIdent nm) <$> translated

-- | Extract out the 'String' name of a declaration in a SAW core module
moduleDeclName :: ModuleDecl -> Maybe String
moduleDeclName (TypeDecl (DataType { dtName })) = Just (identName dtName)
moduleDeclName (DefDecl  (Def      { defIdent })) = Just (identName defIdent)
moduleDeclName InjectCodeDecl{} = Nothing
