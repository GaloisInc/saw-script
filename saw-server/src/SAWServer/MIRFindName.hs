{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Support for finding MIR function names in SAW.
module SAWServer.MIRFindName
  ( mirFindName
  , mirFindNameDescr
  ) where

import Control.Lens (view)
import Data.Aeson (FromJSON(..), ToJSON(..), object, withObject, (.:), (.=))
import Data.Text (Text)

import CryptolServer.Data.Expression (Expression, getCryptolExpr)

import SAWCentral.Crucible.MIR.Builtins (mir_find_name)

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer.SAWServer
    ( SAWState,
      ServerName,
      sawBIC,
      sawEnv,
      sawTopLevelRW,
      getMIRModule )
import SAWServer.Data.MIRType ( JSONMIRType, mirType )
import SAWServer.TopLevel ( tl )
import SAWCentral.Value ( rwGetCryptolEnv )

-- | The parameters for the @SAW/MIR/find name@ command.
data MIRFindNameParams = MIRFindNameParams
  { mfnModule :: ServerName
  , mfnOrigName :: Text
  , mfnTypeSubstitutions :: [JSONMIRType Expression]
  }

-- | The name that the @SAW/MIR/find name@ command returns.
newtype MIRFindNameResult =
  MIRFindNameResult
  { mfnValue :: Text
  }

instance ToJSON MIRFindNameResult where
  toJSON r = object [ "value" .= mfnValue r ]

instance Doc.DescribedMethod MIRFindNameParams MIRFindNameResult where
  parameterFieldDescription =
    [ ("module",
        Doc.Paragraph [Doc.Text "The server name of the MIR module containing the function."])
    , ("original name",
        Doc.Paragraph [Doc.Text "The original (pre-monomorphized) function name."])
    , ("type substitutions",
        Doc.Paragraph [Doc.Text "The types to substitute the function's type parameters with."])
    ]
  resultFieldDescription =
    [ ("value",
      Doc.Paragraph [Doc.Text "The monomorphized function name."])
    ]

instance FromJSON MIRFindNameParams where
  parseJSON =
    withObject "SAW/MIR/find name params" $ \o ->
    MIRFindNameParams <$> o .: "module"
                      <*> o .: "original name"
                      <*> o .: "type substitutions"

-- | The implementation of the @SAW/MIR/find name@ command.
mirFindName :: MIRFindNameParams -> Argo.Command SAWState MIRFindNameResult
mirFindName params = do
  state <- Argo.getState
  fileReader <- Argo.getFileReader
  let cenv = rwGetCryptolEnv (view sawTopLevelRW state)
      bic = view sawBIC state
      sawenv = view sawEnv state
  mod' <- getMIRModule $ mfnModule params
  let substs0 = mfnTypeSubstitutions params
  substs1 <- traverse (traverse getCryptolExpr) substs0
  substs2 <-
    tl $ traverse (mirType fileReader bic cenv sawenv) substs1
  name <- tl $ mir_find_name mod' (mfnOrigName params) substs2
  pure $ MIRFindNameResult name

mirFindNameDescr :: Doc.Block
mirFindNameDescr =
  Doc.Paragraph
    [ Doc.Text "Consult the a MIR module to find a function with the supplied "
    , Doc.Text "identifier and type parameter substitutions. If such a "
    , Doc.Text "function cannot be found in the module, this will raise an "
    , Doc.Text "error."
    ]
