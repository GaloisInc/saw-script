{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module SAWServer.Eval
  ( evalInt
  , evalIntDescr
  ) where

import Control.Exception ( throw )
import Control.Lens ( view )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Aeson
    ( (.:),
      withObject,
      object,
      FromJSON(parseJSON),
      KeyValue((.=)),
      ToJSON(toJSON) )

import qualified Argo
import qualified Argo.Doc as Doc
import CryptolServer.Data.Expression ( Expression(..), getCryptolExpr )
import qualified SAWScript.Builtins as SB
import qualified SAWScript.Value as SV
import SAWServer
    ( SAWState,
      sawBIC,
      sawTopLevelRW)
import SAWServer.CryptolExpression ( CryptolModuleException(..), getTypedTermOfCExp )
import SAWServer.TopLevel ( tl )

data EvalIntParams cryptolExpr =
  EvalIntParams
  { evalIntExpr :: cryptolExpr
  }

instance (FromJSON cryptolExpr) => FromJSON (EvalIntParams cryptolExpr) where
  parseJSON =
    withObject "SAW/eval int params" $ \o ->
    EvalIntParams <$> o .: "expr"

data EvalIntResult =
  EvalIntResult
  { evalIntValue :: Integer
  }

instance ToJSON EvalIntResult where
  toJSON r = object [ "value" .= evalIntValue r ]

evalIntDescr :: Doc.Block
evalIntDescr =
  Doc.Paragraph [ Doc.Text "Attempt to evaluate the given term to a concrete integer." ]

instance Doc.DescribedMethod (EvalIntParams cryptolExpr) EvalIntResult where
  parameterFieldDescription =
    [ ("expr",
       Doc.Paragraph [Doc.Text "The Cryptol expression to evaluate."])
    ]
  resultFieldDescription =
    [ ("value",
      Doc.Paragraph [Doc.Text "The integer value of the expresssion."])
    ]

evalInt :: EvalIntParams Expression -> Argo.Command SAWState EvalIntResult
evalInt params = do
  state <- Argo.getState
  fileReader <- Argo.getFileReader
  let cenv = SV.rwCryptol (view sawTopLevelRW state)
      bic = view sawBIC state
  cexp <- getCryptolExpr $ evalIntExpr params
  (eterm, warnings) <- liftIO $ getTypedTermOfCExp fileReader (SV.biSharedContext bic) cenv cexp
  t <- case eterm of
         Right (t, _) -> return t -- TODO: report warnings
         Left err -> throw $ CryptolModuleException err warnings
  i <- tl $ SB.eval_int t
  pure $ EvalIntResult i
