{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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
import qualified Prettyprinter

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
--
-- Auxiliary declarations the action pushed to 'topLevelDeclarations'
-- (currently only the Slice-6.2 constructor-order assertions a
-- recursor emission records) are returned in emission order and MUST
-- be emitted ahead of the translated decl — dropping them would
-- reopen the silent branch-swap hole the assertions close.
liftTermTranslationMonad ::
  (forall n. TermTranslation.TermTranslationMonad n => n a) ->
  (forall m. ModuleTranslationMonad m => m (a, [String], [Lean.Decl]))
liftTermTranslationMonad action = do
  configuration <- asks M.translationConfiguration
  (modname, mm) <- asks M.otherConfiguration
  let r = TermTranslation.runTermTranslationMonad configuration modname mm [] [] action
  case r of
    Left  e        -> Except.throwError e
    Right (a, st)  ->
      pure (a, view universeVars st,
            reverse (view TermTranslation.topLevelDeclarations st))

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
    emitWith mode name = checkEmittedName "a SAWCore definition" name >>
                         case defQualifier of
      NoQualifier -> case defBody of
        Nothing   ->
          Except.throwError $ RejectedPrimitive shortName
            "NoQualifier def has no body — SAWCore internal contract violation"
        Just body -> do
          -- Body position + annotation carrier from the single
          -- definition-convention authority (2026-07-18
          -- exception-hunt Finding 1: this site formerly applied NO
          -- top-level convention at all).
          ((body', tp'), univs, auxDecls) <- liftTermTranslationMonad $ mode $ do
            bodyResult <- TermTranslation.translateTermLetWithShape body
            (b, annAdj) <- TermTranslation.topLevelDefConvention
                              defType bodyResult
            t <- TermTranslation.translateTerm defType
            pure (b, TermTranslation.applyAnnotationAdjustment annAdj t)
          let decl = mkDefinitionWith Lean.Noncomputable univs name body' tp'
          pure (Prettyprinter.vcat (map Lean.prettyDecl (auxDecls ++ [decl])))
      AxiomQualifier -> rejectAxiomOrPrimitive name
      PrimQualifier  -> rejectAxiomOrPrimitive name

    rejectAxiomOrPrimitive :: ModuleTranslationMonad m => Lean.Ident -> m (Doc ann)
    rejectAxiomOrPrimitive _ =
      Except.throwError $ RejectedPrimitive shortName
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
      Except.throwError $ RejectedPrimitive (toShortName (nameInfo dtName))
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
    -- Audit-2 F-9. A SAWCore module's `injectCode "Lean" "<text>"`
    -- used to be copied into the emitted file VERBATIM: an
    -- unstructured text seam in an otherwise fully-structured
    -- emitter, with no validation and no escaping. Anything can come
    -- through it — an `axiom`, a `set_option`, a `notation` that
    -- recaptures an emitted name — and it lands in `Emitted.lean`,
    -- which the replay kernel scans LENIENTLY because it is supposed
    -- to be generator output rather than user input.
    --
    -- REFUSED as of 2026-07-25, on the same rule as the other
    -- withdrawn surfaces: the backend must be sound, and features
    -- may be deferred. Cost is zero — no public entry point reaches
    -- a generic SAWCore-module Lean writer (see
    -- `obligations/injected_lean_code`, which pins exactly that),
    -- and no shipped `.sawcore` module carries a "Lean" injection.
    --
    -- The open question the CONFORMANCE row records — are Lean
    -- injections TRUSTED declarations or PROOF-CARRYING
    -- realizations? — is answered here in the only direction that is
    -- safe by default: not trusted. Admitting them later means
    -- giving the text a checked shape (parse it, or require a
    -- declaration form the axiom audit can see), not restoring the
    -- verbatim copy.
    InjectCodeDecl ns txt
      | ns == "Lean" -> runIt $ Except.throwError $ RejectedPrimitive
          "injectCode \"Lean\""
          ("a SAWCore module asked to inject Lean source text \
           \verbatim into the emitted file. Injected text bypasses \
           \every structured emission gate and lands in the \
           \leniently-scanned generator output, so it is refused \
           \rather than trusted (audit-2 F-9). Offending text: "
           <> Text.pack (show txt))
      | otherwise    -> pure mempty
