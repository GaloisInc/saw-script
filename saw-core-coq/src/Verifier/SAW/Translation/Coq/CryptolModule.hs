{-# LANGUAGE FlexibleContexts #-}
-- |

module Verifier.SAW.Translation.Coq.CryptolModule where

import           Control.Lens                       (over, set, view)
import           Control.Monad                      (forM)
import           Control.Monad.State                (modify)
import qualified Data.Map                           as Map

import           Cryptol.ModuleSystem.Name          (Name, nameIdent)
import           Cryptol.Utils.Ident                (unpackIdent)
import qualified Language.Coq.AST                   as Coq
import           Verifier.SAW.Term.Functor          (Term)
import           Verifier.SAW.Translation.Coq.Monad
import qualified Verifier.SAW.Translation.Coq.Term  as TermTranslation
import           Verifier.SAW.TypedTerm

translateTypedTermMap ::
  TermTranslation.TermTranslationMonad m => Map.Map Name TypedTerm -> m [Coq.Decl]
translateTypedTermMap tm = forM (Map.assocs tm) translateAndRegisterEntry
  where
    translateAndRegisterEntry (name, symbol) = do
      let t = ttTerm symbol
      let nameStr = unpackIdent (nameIdent name)
      term <- TermTranslation.withLocalTranslationState $ do
        modify $ set TermTranslation.localEnvironment [nameStr]
        TermTranslation.translateTerm t
      let decl = TermTranslation.mkDefinition nameStr term
      modify $ over TermTranslation.globalDeclarations (nameStr :)
      return decl

-- | Translates a Cryptol Module into a list of Coq declarations.  This is done
-- by going through the term map corresponding to the module, translating all
-- terms, and accumulating the translated declarations of all top-level
-- declarations encountered.
translateCryptolModule ::
  TranslationConfiguration ->
  -- | List of already translated global declarations
  [String] ->
  CryptolModule ->
  Either (TranslationError Term) [Coq.Decl]
translateCryptolModule configuration globalDecls (CryptolModule _ tm) =
  reverse . view TermTranslation.topLevelDeclarations . snd
  <$> TermTranslation.runTermTranslationMonad
      configuration
      (TermTranslation.TranslationReader Nothing) -- TODO: this should be Just no?
      globalDecls
      []
      (translateTypedTermMap tm)
