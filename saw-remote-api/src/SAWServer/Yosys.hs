{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module SAWServer.Yosys where

import Control.Lens (view)

import Control.Monad (forM)
import Control.Monad.IO.Class (liftIO)
import Control.Exception (throw)

import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.Text (Text)
import qualified Data.Map as Map

import qualified Argo
import qualified Argo.Doc as Doc

import CryptolServer.Data.Expression (Expression(..), getCryptolExpr)

import SAWServer (SAWState, ServerName, YosysImport(..), sawTask, setServerVal, getYosysImport, getYosysTheorem)
import SAWServer.CryptolExpression (CryptolModuleException(..), getTypedTermOfCExp)
import SAWServer.Exceptions (notAtTopLevel)
import SAWServer.OK (OK, ok)
import SAWServer.ProofScript (ProofScript, interpretProofScript)
import SAWServer.TopLevel (tl)

import SAWScript.Value (getSharedContext, getTopLevelRW, rwCryptol)
import SAWScript.Yosys (loadYosysIR, yosysIRToTypedTerms, yosys_verify)

-- newtype YosysModule = YosysModule (Map String ServerName)

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
      let Just modTerm = Map.lookup (yosysVerifyModule params) imp
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
