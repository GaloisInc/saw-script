{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module SAWServer.Yosys where

import Control.Lens (view, (%=))

import Control.Monad (forM)
import Control.Monad.IO.Class (liftIO)
import Control.Exception (throw)

import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.Text (Text)
import qualified Data.Map as Map

import Cryptol.Utils.Ident (mkIdent)

import qualified Verifier.SAW.CryptolEnv as CEnv

import qualified Argo
import qualified Argo.Doc as Doc

import CryptolServer.Data.Expression (Expression(..), getCryptolExpr)

import SAWServer (SAWState, ServerName (ServerName), sawTask, setServerVal, getYosysImport, getYosysTheorem, getYosysSequential, sawTopLevelRW)
import SAWServer.CryptolExpression (CryptolModuleException(..), getTypedTermOfCExp)
import SAWServer.Exceptions (notAtTopLevel)
import SAWServer.OK (OK, ok)
import SAWServer.ProofScript (ProofScript, interpretProofScript)
import SAWServer.TopLevel (tl)

import SAWScript.Value (getSharedContext, getTopLevelRW, rwCryptol)
import SAWCentral.Yosys (loadYosysIR, yosysIRToTypedTerms, yosys_verify, yosys_import_sequential, yosys_extract_sequential)
import SAWCentral.Yosys.Theorem (YosysImport(..))

data YosysImportParams = YosysImportParams
  { yosysImportPath :: FilePath
  , yosysImportServerName :: ServerName
  }

instance FromJSON YosysImportParams where
  parseJSON = withObject "SAW/Yosys/import params" $ \o -> do
    yosysImportServerName <- o .: "name"
    yosysImportPath <- o .: "path"
    pure YosysImportParams{..}

instance Doc.DescribedMethod YosysImportParams OK where
  parameterFieldDescription =
    [ ("name", Doc.Paragraph [Doc.Text "The name to refer to the record of Yosys modules by later."])
    , ("path", Doc.Paragraph [Doc.Text "The path to the Yosys JSON file to import."])
    ]
  resultFieldDescription = []

yosysImport :: YosysImportParams -> Argo.Command SAWState OK
yosysImport params = do
  tasks <- view sawTask <$> Argo.getState
  case tasks of
    (_:_) -> Argo.raise $ notAtTopLevel $ fst <$> tasks
    [] -> do
      imp <- tl $ do
        sc <- getSharedContext
        ir <- loadYosysIR $ yosysImportPath params
        YosysImport <$> yosysIRToTypedTerms sc ir
      setServerVal (yosysImportServerName params) imp
      ok

yosysImportDescr :: Doc.Block
yosysImportDescr =
  Doc.Paragraph [Doc.Text "Import a file produced by the Yosys \"write_json\" command"]

data YosysVerifyParams = YosysVerifyParams
  { yosysVerifyImport :: ServerName
  , yosysVerifyModule :: Text
  , yosysVerifyPreconds :: [Expression]
  , yosysVerifySpec :: Expression
  , yosysVerifyLemmas :: [ServerName]
  , yosysVerifyScript :: ProofScript
  , yosysVerifyLemmaName :: ServerName
  }

instance FromJSON YosysVerifyParams where
  parseJSON = withObject "SAW/Yosys/verify params" $ \o -> do
    yosysVerifyImport <- o .: "import"
    yosysVerifyModule <- o .: "module"
    yosysVerifyPreconds <- o .: "preconds"
    yosysVerifySpec <- o .: "spec"
    yosysVerifyLemmas <- o .: "lemmas"
    yosysVerifyScript <- o .: "script"
    yosysVerifyLemmaName <- o .: "lemma name"
    pure YosysVerifyParams{..}

instance Doc.DescribedMethod YosysVerifyParams OK where
  parameterFieldDescription =
    [ ("import", Doc.Paragraph [Doc.Text "The imported Yosys file."])
    , ("module", Doc.Paragraph [Doc.Text "The HDL module to verify."])
    , ("preconds", Doc.Paragraph [Doc.Text "Any preconditions for the verificatiion."])
    , ("spec", Doc.Paragraph [Doc.Text "The specification to verify for the module."])
    , ("lemmas", Doc.Paragraph [Doc.Text "The lemmas to use for other modules during this verification."])
    , ("script", Doc.Paragraph [Doc.Text "The script to use to prove the validity of the resulting verification conditions."])
    , ("lemma name", Doc.Paragraph [Doc.Text "The name to refer to the result by later."])
    ]
  resultFieldDescription = []

yosysVerify :: YosysVerifyParams -> Argo.Command SAWState OK
yosysVerify params = do
  tasks <- view sawTask <$> Argo.getState
  case tasks of
    (_:_) -> Argo.raise $ notAtTopLevel $ fst <$> tasks
    [] -> do
      fileReader <- Argo.getFileReader
      YosysImport imp <- getYosysImport $ yosysVerifyImport params
      let modu = yosysVerifyModule params
      modTerm <- case Map.lookup modu imp of
        Just modTerm -> pure modTerm
        Nothing -> error $ "Module " ++ show modu ++ " not found"
      lemmas <- mapM getYosysTheorem $ yosysVerifyLemmas params
      proofScript <- interpretProofScript $ yosysVerifyScript params
      cexp <- getCryptolExpr $ yosysVerifySpec params
      precondExprs <- mapM getCryptolExpr $ yosysVerifyPreconds params
      l <- tl $ do
        rw <- getTopLevelRW
        sc <- getSharedContext
        let cenv = rwCryptol rw
        preconds <- forM precondExprs $ \pc -> do
          (eterm, warnings) <- liftIO $ getTypedTermOfCExp fileReader sc cenv pc
          case eterm of
            Right (t, _) -> pure t
            Left err -> throw $ CryptolModuleException err warnings
        (eterm, warnings) <- liftIO $ getTypedTermOfCExp fileReader sc cenv cexp
        specTerm <- case eterm of
          Right (t, _) -> pure t
          Left err -> throw $ CryptolModuleException err warnings
        yosys_verify modTerm preconds specTerm lemmas proofScript
      setServerVal (yosysVerifyLemmaName params) l
      ok

yosysVerifyDescr :: Doc.Block
yosysVerifyDescr =
  Doc.Paragraph [Doc.Text "Verify that the named HDL module meets its specification"]

data YosysImportSequentialParams = YosysImportSequentialParams
  { yosysImportSequentialModuleName :: Text
  , yosysImportSequentialPath :: FilePath
  , yosysImportSequentialServerName :: ServerName
  }

instance FromJSON YosysImportSequentialParams where
  parseJSON = withObject "SAW/Yosys/import sequential params" $ \o -> do
    yosysImportSequentialServerName <- o .: "name"
    yosysImportSequentialPath <- o .: "path"
    yosysImportSequentialModuleName <- o .: "module"
    pure YosysImportSequentialParams{..}

instance Doc.DescribedMethod YosysImportSequentialParams OK where
  parameterFieldDescription =
    [ ("name", Doc.Paragraph [Doc.Text "The name to refer to the record of Yosys modules by later."])
    , ("path", Doc.Paragraph [Doc.Text "The path to the Yosys JSON file to import."])
    , ("module", Doc.Paragraph [Doc.Text "The sequential module within the Yosys JSON file to analyze."])
    ]
  resultFieldDescription = []

yosysImportSequential :: YosysImportSequentialParams -> Argo.Command SAWState OK
yosysImportSequential params = do
  tasks <- view sawTask <$> Argo.getState
  case tasks of
    (_:_) -> Argo.raise $ notAtTopLevel $ fst <$> tasks
    [] -> do
      s <- tl $ do
        yosys_import_sequential (yosysImportSequentialModuleName params) (yosysImportSequentialPath params)
      setServerVal (yosysImportSequentialServerName params) s
      ok

yosysImportSequentialDescr :: Doc.Block
yosysImportSequentialDescr =
  Doc.Paragraph [Doc.Text "Import a sequential circuit from a file produced by the Yosys \"write_json\" command"]

data YosysExtractSequentialParams = YosysExtractSequentialParams
  { yosysExtractSequentialModule :: ServerName
  , yosysExtractSequentialCycles :: Integer
  , yosysExtractSequentialServerName :: ServerName
  }

instance FromJSON YosysExtractSequentialParams where
  parseJSON = withObject "SAW/Yosys/extract sequential params" $ \o -> do
    yosysExtractSequentialServerName <- o .: "name"
    yosysExtractSequentialModule <- o .: "module"
    yosysExtractSequentialCycles <- o .: "cycles"
    pure YosysExtractSequentialParams{..}

instance Doc.DescribedMethod YosysExtractSequentialParams OK where
  parameterFieldDescription =
    [ ("name", Doc.Paragraph [Doc.Text "The name to refer extracted term by later."])
    , ("cycles", Doc.Paragraph [Doc.Text "The number of cycles over which to iterate the term."])
    , ("module", Doc.Paragraph [Doc.Text "The name of the sequential module to analyze."])
    ]
  resultFieldDescription = []

yosysExtractSequential :: YosysExtractSequentialParams -> Argo.Command SAWState OK
yosysExtractSequential params = do
  tasks <- view sawTask <$> Argo.getState
  case tasks of
    (_:_) -> Argo.raise $ notAtTopLevel $ fst <$> tasks
    [] -> do
      m <- getYosysSequential $ yosysExtractSequentialModule params
      s <- tl $ yosys_extract_sequential m (yosysExtractSequentialCycles params)
      let sn@(ServerName n) = yosysExtractSequentialServerName params
      sawTopLevelRW %= \rw -> rw { rwCryptol = CEnv.bindTypedTerm (mkIdent n, s) $ rwCryptol rw }
      setServerVal sn s
      ok

yosysExtractSequentialDescr :: Doc.Block
yosysExtractSequentialDescr =
  Doc.Paragraph [Doc.Text "Extract a term from a sequential circuit"]
