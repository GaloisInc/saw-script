{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : SAWCoreLean.SAWModule
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable

Walks a SAWCore 'Module' and emits each 'ModuleDecl' as a Lean
declaration. Mirrors "SAWCoreRocq.SAWModule".

The walker dispatches on the per-decl 'atDefSite' treatment:

  * 'DefPreserve' / 'DefRename'  — translate a SAWCore definition body
    to a Lean def or inductive, using the Phase 2 universe machinery.
    Axioms and primitives reject by default; support-library trust
    assumptions must be explicit, not emitted by this generic walker.
  * 'DefSkip'    — emit a one-line comment naming the skipped
    identifier (so the output is a complete record of what the
    walker saw).
-}

module SAWCoreLean.SAWModule (translateDecl) where

import qualified Control.Monad.Except         as Except
import           Control.Monad.Reader         (asks)
import qualified Data.Text                    as Text
import           Prettyprinter                (Doc, pretty, (<+>))

import qualified Language.Lean.AST            as Lean
import qualified Language.Lean.Pretty         as Lean
import           SAWCore.Module
import           SAWCore.Name
import           SAWCore.SharedTerm

import qualified SAWCoreLean.Monad            as M
import           SAWCoreLean.Monad            (TranslationError(..), ppTranslationError)
import           SAWCoreLean.SpecialTreatment
import qualified SAWCoreLean.Term             as TermTranslation
import           SAWCoreLean.Term             (mkDefinitionWith, universeVars)
import           Control.Lens                 (view)

type ModuleTranslationMonad m =
  M.TranslationMonad (Maybe ModuleName, ModuleMap) () m

runModuleTranslationMonad ::
  M.TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  (forall m. ModuleTranslationMonad m => m a) ->
  Either M.TranslationError (a, ())
runModuleTranslationMonad configuration modName mm =
  M.runTranslationMonad configuration (modName, mm) ()

-- | Bridge a 'TermTranslationMonad' action into the module-level
-- monad. The translation state created here is fresh per call —
-- universe variables allocated inside the action are local to it,
-- which matches the per-decl semantics (each Lean def has its own
-- universe-binder list).
liftTermTranslationMonad ::
  (forall n. TermTranslation.TermTranslationMonad n => n a) ->
  (forall m. ModuleTranslationMonad m => m (a, [String]))
liftTermTranslationMonad action = do
  configuration <- asks M.translationConfiguration
  (modname, mm) <- asks M.otherConfiguration
  let r = TermTranslation.runTermTranslationMonad configuration modname mm [] [] action
  case r of
    Left  e        -> Except.throwError e
    Right (a, st)  -> pure (a, view universeVars st)

skippedComment :: NameInfo -> Doc ann
skippedComment nmi =
  "--" <+> pretty (Text.unpack (toShortName nmi))
       <+> "was skipped (mapped to a hand-library equivalent)"

-- | Translate a SAWCore 'Def' (regular def, axiom, or primitive)
-- into a Lean declaration document, honoring its 'atDefSite'.
translateDef ::
  ModuleTranslationMonad m =>
  Def -> m (Doc ann)
translateDef Def{..} = do
  treatment <- findSpecialTreatment' (nameInfo defName)
  case atDefSite treatment of
    DefSkip       -> pure (skippedComment (nameInfo defName))
    DefPreserve   -> emit (Lean.Ident (Text.unpack (toShortName (nameInfo defName))))
    DefPreserveRaw ->
      emitWith TermTranslation.withRawTranslationMode
        (Lean.Ident (Text.unpack (toShortName (nameInfo defName))))
    DefRename i   -> emit i
  where
    shortName = toShortName (nameInfo defName)

    emit :: ModuleTranslationMonad m => Lean.Ident -> m (Doc ann)
    emit = emitWith id

    emitWith ::
      ModuleTranslationMonad m =>
      (forall n a. TermTranslation.TermTranslationMonad n => n a -> n a) ->
      Lean.Ident -> m (Doc ann)
    emitWith mode name = case defQualifier of
      NoQualifier -> case defBody of
        Nothing   ->
          Except.throwError $ RejectedPrimitive shortName $
            "NoQualifier def has no body — SAWCore internal contract violation"
        Just body -> do
          ((body', tp'), univs) <- liftTermTranslationMonad $ mode $ do
            b <- TermTranslation.translateTerm body
            t <- TermTranslation.translateTerm defType
            pure (b, t)
          let decl = mkDefinitionWith Lean.Noncomputable univs name body' tp'
          pure (Lean.prettyDecl decl)
      AxiomQualifier -> rejectAxiomOrPrimitive name
      PrimQualifier  -> rejectAxiomOrPrimitive name

    rejectAxiomOrPrimitive :: ModuleTranslationMonad m => Lean.Ident -> m (Doc ann)
    rejectAxiomOrPrimitive _ =
      Except.throwError $ RejectedPrimitive shortName $
        "generic Lean axiom emission is disabled. Map this SAW axiom or \
        \primitive to an explicit checked support-library declaration, skip it \
        \with a documented hand-library equivalent, or emit a proof obligation \
        \instead."

-- | Translate a SAWCore 'DataType' to a Lean inductive document.
-- Currently a stub: all SAW-Prelude data types reachable from the
-- normalized translation surface are mapped via 'mapsTo' to the
-- hand-written Lean support library, so the walker skips them.
-- A full implementation is a follow-up.
translateDataType ::
  ModuleTranslationMonad m =>
  DataType -> m (Doc ann)
translateDataType DataType{..} = do
  treatment <- findSpecialTreatment' (nameInfo dtName)
  case atDefSite treatment of
    DefSkip       -> pure (skippedComment (nameInfo dtName))
    DefPreserve   -> failUnsupported
    DefPreserveRaw -> failUnsupported
    DefRename _   -> failUnsupported
  where
    failUnsupported =
      Except.throwError $ RejectedPrimitive (toShortName (nameInfo dtName)) $
        "auto-emit of SAWCore data types is not yet implemented; \
        \map it to a hand-library equivalent via `mapsTo` in \
        \`SAWCoreLean.SpecialTreatment`."

translateDecl ::
  SharedContext ->
  M.TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  ModuleDecl ->
  IO (Doc ann)
translateDecl sc configuration modname mm decl =
  let runIt :: (forall m. ModuleTranslationMonad m => m (Doc ann)) -> IO (Doc ann)
      runIt action =
        case runModuleTranslationMonad configuration modname mm action of
          Right (d, _) -> pure d
          Left e -> do
            msg <- ppTranslationError sc e
            ioError (userError (Text.unpack msg))
  in
  case decl of
    TypeDecl td -> runIt (translateDataType td)
    DefDecl dd  -> runIt (translateDef dd)
    InjectCodeDecl ns txt
      | ns == "Lean" -> pure (pretty txt)
      | otherwise    -> pure mempty
