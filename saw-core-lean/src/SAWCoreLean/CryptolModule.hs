{-# LANGUAGE FlexibleContexts #-}

{- |
Module      : SAWCoreLean.CryptolModule
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Translate a Cryptol module (as loaded into SAW) to a list of Lean
declarations. Near-mirror of "SAWCoreRocq.CryptolModule"; the only
translator-shape difference is that Rocq registers translated
globals into @globalDeclarations@ before emitting the decl, and we
do the same via the Phase-1 state-carrying refactor.
-}

module SAWCoreLean.CryptolModule (translateCryptolModule) where

import           Control.Lens              (over, view)
import           Control.Monad             (forM)
import           Control.Monad.State       (modify)
import qualified Data.Map                  as Map

import           Cryptol.ModuleSystem.Name (Name, nameIdent)
import           Cryptol.Utils.Ident       (unpackIdent)
import qualified Language.Lean.AST         as Lean

import           SAWCore.Term.Raw          (Term)
import           SAWCore.SharedTerm        (SharedContext, scGetModuleMap)

import           CryptolSAWCore.TypedTerm
import           CryptolSAWCore.Cryptol    (CryptolEnv)

import           SAWCoreLean.Monad
import qualified SAWCoreLean.Term          as TermTranslation

-- | Translate a list of named terms with their types to Lean
-- definitions. For each entry, we register the name in the
-- 'globalDeclarations' list /before/ returning the decl, so
-- subsequent entries that reference it don't re-emit the body
-- inline.
translateTypedTermMap ::
  TermTranslation.TermTranslationMonad m =>
  [(Name, Term, Term)] -> m [Lean.Decl]
translateTypedTermMap = mapM translateAndRegisterEntry
  where
    translateAndRegisterEntry (name, t, tp) = do
      let nameStr = Lean.Ident (unpackIdent (nameIdent name))
      tTrans  <- TermTranslation.translateTerm t
      tpTrans <- TermTranslation.translateTerm tp
      let decl = TermTranslation.mkDefinition nameStr tTrans tpTrans
      modify (over TermTranslation.globalDeclarations (nameStr :))
      pure decl

-- | Translate a 'CryptolModule' into a list of Lean declarations.
-- Walks the module's term map, translates each entry, and
-- accumulates every auxiliary declaration discovered along the way
-- (via 'topLevelDeclarations') ahead of the user-visible defs.
translateCryptolModule ::
  SharedContext -> CryptolEnv ->
  TranslationConfiguration ->
  [Lean.Ident] ->
    -- ^ globals already translated (from the accompanying SAWCore
    --   prelude or prior invocations).
  CryptolModule ->
  IO (Either TranslationError [Lean.Decl])
translateCryptolModule sc env configuration globalDecls (CryptolModule _ tm) = do
  defs <-
    forM (Map.assocs tm) $ \(nm, t) -> do
      tp <- ttTypeAsTerm sc env t
      pure (nm, ttTerm t, tp)
  mm <- scGetModuleMap sc
  pure $
    reverse . view TermTranslation.topLevelDeclarations . snd <$>
      TermTranslation.runTermTranslationMonad
        configuration
        Nothing
          -- No SAWCore-module context: the Cryptol module's defs
          -- translate as standalone Lean defs and reference prelude
          -- names through their usual qualified paths.
        mm
        globalDecls
        []
        (translateTypedTermMap defs)
