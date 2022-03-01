{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module SAWServer.Yosys where

import Control.Lens (view)

import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.Text (Text)

import qualified Argo
import qualified Argo.Doc as Doc

import SAWServer (SAWState, ServerName, sawTask, setServerVal, getTerm, getYosysTheorem)
import SAWServer.Exceptions (notAtTopLevel)
import SAWServer.OK (OK, ok)
import SAWServer.ProofScript (ProofScript, interpretProofScript)
import SAWServer.TopLevel (tl)

import SAWScript.Value (getSharedContext)
import SAWScript.Yosys (yosys_import, yosys_verify)
import SAWScript.Yosys.Theorem (cryptolRecordSelectTyped)

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
      t <- tl . yosys_import $ yosysImportPath params
      setServerVal (yosysImportServerName params) t
      ok

yosysImportDescr :: Doc.Block
yosysImportDescr =
  Doc.Paragraph [Doc.Text "Import a file produced by the Yosys \"write_json\" command"]

data YosysVerifyParams = YosysVerifyParams
  { yosysVerifyImport :: ServerName
  , yosysVerifyModule :: Text
  , yosysVerifyPreconds :: [ServerName]
  , yosysVerifySpec :: ServerName
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
    , ("lemmas", Doc.Paragraph [Doc.Text "The specifications to use for other modules during this verification."])
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
      impTerm <- getTerm $ yosysVerifyImport params
      specTerm <- getTerm $ yosysVerifySpec params
      lemmas <- mapM getYosysTheorem $ yosysVerifyLemmas params
      proofScript <- interpretProofScript $ yosysVerifyScript params
      l <- tl $ do
        sc <- getSharedContext
        modTerm <- cryptolRecordSelectTyped sc impTerm $ yosysVerifyModule params
        yosys_verify modTerm [] specTerm lemmas proofScript
      setServerVal (yosysVerifyLemmaName params) l
      ok

yosysVerifyDescr :: Doc.Block
yosysVerifyDescr =
  Doc.Paragraph [Doc.Text "Verify that the named HDL module meets its specification"]
