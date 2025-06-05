{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module SAWServer.Eval
  ( evalInt
  , evalIntDescr
  , evalBool
  , evalBoolDescr
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
import CryptolSAWCore.TypedTerm (TypedTerm)
import qualified SAWCentral.Builtins as SB
import qualified SAWCentral.Value as SV
import SAWServer.SAWServer
    ( SAWState,
      sawBIC,
      sawTopLevelRW)
import SAWServer.CryptolExpression ( CryptolModuleException(..), getTypedTermOfCExp )
import SAWServer.TopLevel ( tl )

-- The phantom type here is used to prevent a functional dependency conflict when
-- writing instances of Doc.DescribedMethod, and should match the type parameter
-- of EvalResult
newtype EvalParams evalty cryptolExpr =
  EvalParams
  { evalExpr :: cryptolExpr
  }

instance (FromJSON cryptolExpr) => FromJSON (EvalParams a cryptolExpr) where
  parseJSON =
    withObject "SAW/eval params" $ \o ->
    EvalParams <$> o .: "expr"

newtype EvalResult evalty =
  EvalResult
  { evalValue :: evalty
  }

instance ToJSON a => ToJSON (EvalResult a) where
  toJSON r = object [ "value" .= evalValue r ]

instance Doc.DescribedMethod (EvalParams Integer cryptolExpr) (EvalResult Integer) where
  parameterFieldDescription =
    [ ("expr",
       Doc.Paragraph [Doc.Text "The Cryptol expression to evaluate."])
    ]
  resultFieldDescription =
    [ ("value",
      Doc.Paragraph [Doc.Text "The integer value of the expresssion."])
    ]

instance Doc.DescribedMethod (EvalParams Bool cryptolExpr) (EvalResult Bool) where
  parameterFieldDescription =
    [ ("expr",
       Doc.Paragraph [Doc.Text "The Cryptol expression to evaluate."])
    ]
  resultFieldDescription =
    [ ("value",
      Doc.Paragraph [Doc.Text "The boolean value of the expresssion."])
    ]

eval ::
  (TypedTerm -> SV.TopLevel a) -> EvalParams a Expression -> Argo.Command SAWState (EvalResult a)
eval f params = do
  state <- Argo.getState
  fileReader <- Argo.getFileReader
  let cenv = SV.rwCryptol (view sawTopLevelRW state)
      bic = view sawBIC state
  cexp <- getCryptolExpr $ evalExpr params
  (eterm, warnings) <- liftIO $ getTypedTermOfCExp fileReader (SV.biSharedContext bic) cenv cexp
  t <- case eterm of
         Right (t, _) -> return t -- TODO: report warnings
         Left err -> throw $ CryptolModuleException err warnings
  i <- tl $ f t
  pure $ EvalResult i

evalIntDescr :: Doc.Block
evalIntDescr =
  Doc.Paragraph [ Doc.Text "Attempt to evaluate the given term to a concrete integer." ]

evalInt :: EvalParams Integer Expression -> Argo.Command SAWState (EvalResult Integer)
evalInt = eval SB.eval_int

evalBoolDescr :: Doc.Block
evalBoolDescr =
  Doc.Paragraph [ Doc.Text "Attempt to evaluate the given term to a concrete boolean." ]

evalBool :: EvalParams Bool Expression -> Argo.Command SAWState (EvalResult Bool)
evalBool = eval SB.eval_bool
