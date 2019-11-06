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

module Verifier.SAW.Translation.Coq.SAWModule where

import           Control.Lens                                  (makeLenses)
import qualified Control.Monad.Except                          as Except
import           Control.Monad.Reader                          hiding (fail)
import           Prelude                                       hiding (fail)
import           Text.PrettyPrint.ANSI.Leijen                  hiding ((<$>))

import qualified Language.Coq.AST                              as Coq
import qualified Language.Coq.Pretty                           as Coq
import           Verifier.SAW.Module
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Term.Functor
import           Verifier.SAW.Translation.Coq.Monad
import           Verifier.SAW.Translation.Coq.SpecialTreatment
import qualified Verifier.SAW.Translation.Coq.Term             as TermTranslation

data TranslationState = TranslationState
  { _localEnvironment  :: [String]
  }
  deriving (Show)
makeLenses ''TranslationState

type ModuleTranslationMonad m = TranslationMonad TranslationState m

runModuleTranslationMonad ::
  TranslationConfiguration ->
  (forall m. ModuleTranslationMonad m => m a) ->
  Either (TranslationError Term) (a, TranslationState)
runModuleTranslationMonad configuration =
  runTranslationMonad configuration (TranslationState [])

dropPi :: Coq.Term -> Coq.Term
dropPi (Coq.Pi (_ : t) r) = Coq.Pi t r
dropPi (Coq.Pi _       r) = dropPi r
dropPi t                  = t

translateCtor ::
  ModuleTranslationMonad m =>
  [Coq.Binder] -> -- list of parameters to drop from `ctorType`
  Ctor -> m Coq.Constructor
translateCtor inductiveParameters (Ctor {..}) = do
  constructorName <- TermTranslation.translateIdentUnqualified ctorName
  constructorType <-
    -- Unfortunately, `ctorType` qualifies the inductive type's name in the
    -- return type.
    -- dropModuleNameWithinCtor <$>
    -- Unfortunately, `ctorType` comes with the inductive parameters universally
    -- quantified.
    (\ t -> iterate dropPi t !! length inductiveParameters) <$>
    (liftTermTranslationMonad (TermTranslation.translateTerm ctorType))
  return $ Coq.Constructor
    { constructorName
    , constructorType
    }

translateDataType :: ModuleTranslationMonad m => DataType -> m Coq.Decl
translateDataType (DataType {..}) =
  atDefSite <$> findSpecialTreatment dtName >>= \case
  DefPreserve              -> translateNamed $ identName dtName
  DefRename   _ targetName -> translateNamed $ targetName
  DefReplace  str          -> return $ Coq.Snippet str
  DefSkip                  -> return $ skipped dtName
  where
    translateNamed :: ModuleTranslationMonad m => Coq.Ident -> m Coq.Decl
    translateNamed name = do
      let inductiveName = name
      let
        mkParam :: ModuleTranslationMonad m => (String, Term) -> m Coq.Binder
        mkParam (s, t) = do
          t' <- liftTermTranslationMonad (TermTranslation.translateTerm t)
          return $ Coq.Binder s (Just t')
      let mkIndex (s, t) = do
            t' <- liftTermTranslationMonad (TermTranslation.translateTerm t)
            let s' = case s of
                  "_" -> Nothing
                  _   -> Just s
            return $ Coq.PiBinder s' t'
      inductiveParameters   <- mapM mkParam dtParams
      inductiveIndices      <- mapM mkIndex dtIndices
      let inductiveSort = TermTranslation.translateSort dtSort
      inductiveConstructors <- mapM (translateCtor inductiveParameters) dtCtors
      return $ Coq.InductiveDecl $ Coq.Inductive
        { inductiveName
        , inductiveParameters
        , inductiveIndices
        , inductiveSort
        , inductiveConstructors
        }

-- translateModuleDecl :: ModuleTranslationMonad m => ModuleDecl -> m Coq.Decl
-- translateModuleDecl = \case
--   TypeDecl dataType -> translateDataType dataType
--   DefDecl definition -> translateDef definition

_mapped :: Ident -> Ident -> Coq.Decl
_mapped sawIdent newIdent =
  Coq.Comment $ show sawIdent ++ " is mapped to " ++ show newIdent

skipped :: Ident -> Coq.Decl
skipped sawIdent =
  Coq.Comment $ show sawIdent ++ " was skipped"

translateDef :: ModuleTranslationMonad m => Def -> m Coq.Decl
translateDef (Def {..}) = do
  specialTreatment <- findSpecialTreatment defIdent
  translateAccordingly (atDefSite specialTreatment)

  where

    translateAccordingly :: ModuleTranslationMonad m => DefSiteTreatment -> m Coq.Decl
    translateAccordingly  DefPreserve             = translateNamed $ identName defIdent
    translateAccordingly (DefRename _ targetName) = translateNamed $ targetName
    translateAccordingly (DefReplace  str)        = return $ Coq.Snippet str
    translateAccordingly  DefSkip                 = return $ skipped defIdent

    translateNamed :: ModuleTranslationMonad m => Coq.Ident -> m Coq.Decl
    translateNamed name = liftTermTranslationMonad (go defQualifier defBody)

      where

        go :: TermTranslation.TermTranslationMonad m => DefQualifier -> Maybe Term -> m Coq.Decl
        go NoQualifier    Nothing     = error "Terms should have a body (unless axiom/primitive)"
        go NoQualifier    (Just body) = Coq.Definition
                                        <$> pure name
                                        <*> pure []
                                        <*> (Just <$> TermTranslation.translateTerm defType)
                                        <*> TermTranslation.translateTerm body
        go AxiomQualifier _           = Coq.Axiom
                                        <$> pure name
                                        <*> TermTranslation.translateTerm defType
        go PrimQualifier  _           = Coq.Axiom
                                        <$> pure name
                                        <*> TermTranslation.translateTerm defType

liftTermTranslationMonad ::
  (forall n. TermTranslation.TermTranslationMonad   n => n a) ->
  (forall m. ModuleTranslationMonad m => m a)
liftTermTranslationMonad n = do
  configuration <- ask
  let r = TermTranslation.runTermTranslationMonad configuration [] [] n
  case r of
    Left  e      -> Except.throwError e
    Right (a, _) -> do
      return a

translateDecl :: TranslationConfiguration -> ModuleDecl -> Doc
translateDecl configuration decl =
  case decl of
  TypeDecl td -> do
    case runModuleTranslationMonad configuration (translateDataType td) of
      Left e -> error $ show e
      Right (tdecl, _) -> Coq.ppDecl tdecl
  DefDecl dd -> do
    case runModuleTranslationMonad configuration (translateDef dd) of
      Left e -> error $ show e
      Right (tdecl, _) -> Coq.ppDecl tdecl
