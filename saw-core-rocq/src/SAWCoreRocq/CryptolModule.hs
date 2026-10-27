{-# LANGUAGE FlexibleContexts #-}
-- |

module SAWCoreRocq.CryptolModule (translateCryptolModule) where

-- base & standard modules:
import           Control.Lens              (over, view)
import           Control.Monad             (forM)
import           Control.Monad.State       (modify)
import qualified Data.Map                  as Map

-- cryptol pkg:
import           Cryptol.ModuleSystem.Exports    as Cryptol
import           Cryptol.ModuleSystem.Interface  as Cryptol
import           Cryptol.ModuleSystem.Name       (Name, nameIdent)
import qualified Cryptol.TypeCheck.AST           as Cryptol
import           Cryptol.Utils.Ident             (identText,Namespace(..))

-- local:
import           CryptolSAWCore.GlobalCryptolEnv as CSC
import           CryptolSAWCore.TypedTerm
import qualified Language.Rocq.AST         as Rocq
import           SAWCore.SharedTerm        (SharedContext, scGetModuleMap)
import           SAWCore.Term.Raw          (Term)
import           SAWCoreRocq.Monad
import qualified SAWCoreRocq.Term          as TermTranslation


-- | Translate a list of named terms with their types to a Rocq definitions
translateTypedTermMap ::
  TermTranslation.TermTranslationMonad m => [(Name,Term,Term)] -> m [Rocq.Decl]
translateTypedTermMap defs = forM defs translateAndRegisterEntry
  where
    translateAndRegisterEntry (name, t, tp) = do
      let nameStr = Rocq.Ident (identText (nameIdent name))
      decl <-
        do t_trans <- TermTranslation.translateTerm t
           tp_trans <- TermTranslation.translateTerm tp
           return $ TermTranslation.mkDefinition nameStr t_trans tp_trans
      modify $ over TermTranslation.globalDeclarations (nameStr :)
      return decl

-- | create a `Map Name TypedTerm` from the Cryptol.Module
--   - this only extracts the exported values!
--
--   - FIXME: Thus, we see why, per #3491, the Rocq exporter does not
--     export submodules. This is where (or close to) the fix should
--     be made.

cryptolModuleToMapOfTypedTerm
  :: SharedContext -> Cryptol.Module -> IO (Map.Map Name TypedTerm)
cryptolModuleToMapOfTypedTerm sc m =
  do
  modEnv   <- eModuleEnv sc
  allterms <- eAllTerms sc
  let
      ifaceDecls = CSC.getAllIfaceDecls modEnv
      types = Map.map Cryptol.ifDeclSig (Cryptol.ifDecls ifaceDecls)

      -- we're keeping only the Value exports of `m`:
      vNameSet = Cryptol.exported NSValue (Cryptol.mExports m)

  return $ Map.restrictKeys
             (Map.intersectionWith
               (\t x -> TypedTerm (TypedTermSchema t) x)
                 types
                 allterms)
             vNameSet

-- | Translates a Cryptol.Module into a list of Rocq declarations.  This is done
-- by going through the term map corresponding to the module, translating all
-- terms, and accumulating the translated declarations of all top-level
-- declarations encountered.
translateCryptolModule ::
  SharedContext ->
  TranslationConfiguration ->
  -- | List of already translated global declarations
  [Rocq.Ident] ->
  Cryptol.Module ->
  IO (Either TranslationError [Rocq.Decl])
translateCryptolModule sc configuration globalDecls cm =
  do tm <- cryptolModuleToMapOfTypedTerm sc cm
     defs <-
       forM (Map.assocs tm) $ \(nm, t) ->
         do tp <- ttTypeAsTerm sc t
            return (nm, ttTerm t, tp)
     mm <- scGetModuleMap sc
     return
       (reverse . view TermTranslation.topLevelDeclarations . snd <$>
        TermTranslation.runTermTranslationMonad
        configuration
        Nothing -- TODO: this should be Just no?
        mm
        globalDecls
        []
        (translateTypedTermMap defs))
