{-# LANGUAGE FlexibleContexts #-}
-- |

module Verifier.SAW.Translation.Coq.CryptolModule where

import           Control.Lens                       (over, view)
import           Control.Monad                      (forM)
import           Control.Monad.State                (modify)
import qualified Data.Map                           as Map

import           Cryptol.ModuleSystem.Name          (Name, nameIdent)
import           Cryptol.Utils.Ident                (unpackIdent)
import qualified Language.Coq.AST                   as Coq
import           Verifier.SAW.Term.Functor          (Term)
import           Verifier.SAW.SharedTerm            (SharedContext)
import           Verifier.SAW.Translation.Coq.Monad
import qualified Verifier.SAW.Translation.Coq.Term  as TermTranslation
import           Verifier.SAW.TypedTerm
import           Verifier.SAW.Cryptol (Env)


-- | Translate a list of named terms with their types to a Coq definitions
translateTypedTermMap ::
  TermTranslation.TermTranslationMonad m => [(Name,Term,Term)] -> m [Coq.Decl]
translateTypedTermMap defs = forM defs translateAndRegisterEntry
  where
    translateAndRegisterEntry (name, t, tp) = do
      let nameStr = unpackIdent (nameIdent name)
      decl <-
        do t_trans <- TermTranslation.translateTerm t
           tp_trans <- TermTranslation.translateTerm tp
           return $ TermTranslation.mkDefinition nameStr t_trans tp_trans
      modify $ over TermTranslation.globalDeclarations (nameStr :)
      return decl

-- | Translates a Cryptol Module into a list of Coq declarations.  This is done
-- by going through the term map corresponding to the module, translating all
-- terms, and accumulating the translated declarations of all top-level
-- declarations encountered.
translateCryptolModule ::
  SharedContext -> Env ->
  TranslationConfiguration ->
  -- | List of already translated global declarations
  [String] ->
  CryptolModule ->
  IO (Either (TranslationError Term) [Coq.Decl])
translateCryptolModule sc env configuration globalDecls (CryptolModule _ tm) =
  do defs <-
       forM (Map.assocs tm) $ \(nm, t) ->
       do tp <- ttTypeAsTerm sc env t
          return (nm, ttTerm t, tp)
     return
       (reverse . view TermTranslation.topLevelDeclarations . snd <$>
        TermTranslation.runTermTranslationMonad
        configuration
        Nothing -- TODO: this should be Just no?
        globalDecls
        []
        (translateTypedTermMap defs))
