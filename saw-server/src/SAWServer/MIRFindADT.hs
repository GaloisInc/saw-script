{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Support for finding MIR ADT definitions in SAW.
module SAWServer.MIRFindADT
  ( mirFindADT
  , mirFindADTDescr
  ) where

import Control.Lens (view)
import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.Text (Text)

import SAWCentral.Crucible.MIR.Builtins (mir_find_adt)

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer.SAWServer
    ( SAWState,
      ServerName,
      sawEnv,
      sawTask,
      setServerVal,
      getMIRModule )
import SAWServer.Data.MIRType ( JSONMIRType, mirType )
import SAWServer.Exceptions ( notAtTopLevel )
import SAWServer.OK ( OK, ok )
import SAWServer.TopLevel ( tl )

-- | The parameters for the @SAW/MIR/find ADT@ command.
data MIRFindADTParams = MIRFindADTParams
  { mfaModule :: ServerName
  , mfaADTOrigName :: Text
  , mfaTypeSubstitutions :: [JSONMIRType]
  , mfaADTServerName :: ServerName
  }

instance Doc.DescribedMethod MIRFindADTParams OK where
  parameterFieldDescription =
    [ ("module",
        Doc.Paragraph [Doc.Text "The server name of the MIR module containing the ADT."])
    , ("ADT original name",
        Doc.Paragraph [Doc.Text "The original (pre-monomorphized) ADT name."])
    , ("type substitutions",
        Doc.Paragraph [Doc.Text "The types to substitute the ADT's type parameters with."])
    , ("ADT server name",
        Doc.Paragraph [Doc.Text "The server name to refer to the ADT by later."])
    ]
  resultFieldDescription = []

instance FromJSON MIRFindADTParams where
  parseJSON =
    withObject "SAW/MIR/find ADT params" $ \o ->
    MIRFindADTParams <$> o .: "module"
                     <*> o .: "ADT original name"
                     <*> o .: "type substitutions"
                     <*> o .: "ADT server name"

-- | The implementation of the @SAW/MIR/find ADT@ command.
mirFindADT :: MIRFindADTParams -> Argo.Command SAWState OK
mirFindADT params = do
  state <- Argo.getState
  let tasks = view sawTask state
      sawenv = view sawEnv state
  case tasks of
    (_:_) -> Argo.raise $ notAtTopLevel $ fst <$> tasks
    [] -> do
      mod' <- getMIRModule $ mfaModule params
      adt <- tl $ mir_find_adt
                    mod'
                    (mfaADTOrigName params)
                    (map (mirType sawenv) $ mfaTypeSubstitutions params)
      let sn = mfaADTServerName params
      setServerVal sn adt
      ok

mirFindADTDescr :: Doc.Block
mirFindADTDescr =
  Doc.Paragraph
    [ Doc.Text "Consult the a MIR module to find an algebraic data type (ADT) "
    , Doc.Text "with the supplied identifier and type parameter substitutions. "
    , Doc.Text "If such an ADT cannot be found in the module, this will raise "
    , Doc.Text "an error."
    ]
