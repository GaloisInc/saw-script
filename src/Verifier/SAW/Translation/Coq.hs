{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Translation.Coq
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Translation.Coq (
  TranslationConfiguration(..),
  preamble,
  preamblePlus,
  TermTranslation.translateDefDoc,
  translateTermAsDeclImports,
  translateModule,
  ) where

import Control.Monad.Reader hiding (fail)
import Prelude hiding (fail)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Language.Coq.AST as Coq
import Verifier.SAW.Module
import Verifier.SAW.SharedTerm
-- import Verifier.SAW.Term.CtxTerm
import qualified Verifier.SAW.Translation.Coq.Module as ModuleTranslation
import Verifier.SAW.Translation.Coq.Monad
import Verifier.SAW.Translation.Coq.SpecialTreatment
import qualified Verifier.SAW.Translation.Coq.Term as TermTranslation
--import Verifier.SAW.Term.Pretty
-- import qualified Verifier.SAW.UntypedAST as Un

--import Debug.Trace

-- showFTermF :: FlatTermF Term -> String
-- showFTermF = show . Unshared . FTermF

-- mkCoqIdent :: String -> String -> Ident
-- mkCoqIdent coqModule coqIdent = mkIdent (mkModuleName [coqModule]) coqIdent

{-
traceFTermF :: String -> FlatTermF Term -> a -> a
traceFTermF ctx tf = traceTerm ctx (Unshared $ FTermF tf)

traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a
-}

-- translateBinder ::
--   TermTranslationMonad m =>
--   (Ident, Term) -> m (Coq.Ident, Coq.Term)
-- translateBinder (ident, term) =
--   (,)
--   <$> pure (translateIdent ident)
--   <*> translateTerm term

-- dropModuleName :: String -> String
-- dropModuleName s =
--   case elemIndices '.' s of
--   [] -> s
--   indices ->
--     let lastIndex = last indices in
--     drop (lastIndex + 1) s

-- unqualifyTypeWithinConstructor :: Coq.Term -> Coq.Term
-- unqualifyTypeWithinConstructor = go
--   where
--     go (Coq.Pi bs t)  = Coq.Pi bs (go t)
--     go (Coq.App t as) = Coq.App (go t) as
--     go (Coq.Var v)    = Coq.Var (dropModuleName v)
--     go t              = error $ "Unexpected term in constructor: " ++ show t

-- | This is a convenient helper for when you want to add some bindings before
-- translating a term.
-- translateTermLocallyBinding :: ModuleTranslationMonad m => [String] -> Term -> m Coq.Term
-- translateTermLocallyBinding bindings term =
--   withLocalEnvironment $ do
--   modify $ over environment (bindings ++)
--   translateTerm term

-- Eventually, different modules will want different preambles, for now,
-- hardcoded.
preamblePlus :: Doc -> Doc
preamblePlus extraImports = vcat $
  [ "From Coq          Require Import Lists.List."
  , "Import            ListNotations."
  , "From Coq          Require Import String."
  , "From Coq          Require Import Vectors.Vector."
  , "From CryptolToCoq Require Import SAW."
  , "From Records      Require Import Records."
  , ""
  , extraImports
  , ""
  ]

preamble :: Doc
preamble = preamblePlus $ vcat []

translateTermAsDeclImports ::
  TranslationConfiguration -> Coq.Ident -> Term -> Either (TranslationError Term) Doc
translateTermAsDeclImports configuration name t = do
  doc <- TermTranslation.translateDefDoc configuration name t
  return (preamble <$$> hardline <> doc)

translateModule :: TranslationConfiguration -> Module -> Doc
translateModule configuration m =
  let name = show $ translateModuleName (moduleName m)
  in
  vcat $ []
  ++ [ text $ "Module " ++ name ++ "."
     , ""
     ]
  ++ [ ModuleTranslation.translateDecl configuration decl | decl <- moduleDecls m ]
  ++ [ text $ "End " ++ name ++ "."
     ]
