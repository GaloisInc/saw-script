{-# LANGUAGE FlexibleContexts #-}
-- |

module Verifier.SAW.Translation.Coq.CryptolModule where

import           Control.Lens                       (over, set, view)
import           Control.Monad                      (forM)
import           Control.Monad.State                (modify)
import qualified Data.Map                           as Map

import           Cryptol.ModuleSystem.Name
import           Cryptol.Utils.Ident
import qualified Language.Coq.AST                   as Coq
import           Verifier.SAW.Term.Functor
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
      term <- TermTranslation.withLocalLocalEnvironment $ do
        modify $ set TermTranslation.localEnvironment [nameStr]
        TermTranslation.translateTerm t
      let decl = TermTranslation.mkDefinition nameStr term
      modify $ over TermTranslation.globalDeclarations (nameStr :)
      return decl

translateCryptolModule ::
  TranslationConfiguration -> [String] -> CryptolModule -> Either (TranslationError Term) [Coq.Decl]
translateCryptolModule configuration globalDecls (CryptolModule _ tm) =
  case TermTranslation.runTermTranslationMonad
       configuration
       Nothing
       globalDecls
       []
       (translateTypedTermMap tm) of
  Left e -> Left e
  Right (_, st) -> Right (reverse (view TermTranslation.localDeclarations st))
