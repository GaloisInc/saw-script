{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Support for looking up MIR ADT definitions in SAW from mangled
-- identifiers.
module SAWServer.MIRFindMangledADT
  ( mirFindMangledADT
  , mirFindMangledADTDescr
  ) where

import Control.Lens (view)
import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.Text (Text)

import SAWCentral.Crucible.MIR.Builtins (mir_find_mangled_adt)

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer.SAWServer
    ( SAWState,
      ServerName,
      sawTask,
      setServerVal,
      getMIRModule )
import SAWServer.Exceptions ( notAtTopLevel )
import SAWServer.OK ( OK, ok )
import SAWServer.TopLevel ( tl )

-- | The parameters for the @SAW/MIR/find mangled ADT@ command.
data MIRFindMangledADTParams = MIRFindMangledADTParams
  { mfmaModule :: ServerName
  , mfmaADTName :: Text
  , mfmaADTServerName :: ServerName
  }

instance Doc.DescribedMethod MIRFindMangledADTParams OK where
  parameterFieldDescription =
    [ ("module",
        Doc.Paragraph [Doc.Text "The server name of the MIR module containing the ADT."])
    , ("ADT mangled name",
        Doc.Paragraph [Doc.Text "The ADT name, which should be a mangled identifier."])
    , ("ADT server name",
        Doc.Paragraph [Doc.Text "The server name to refer to the ADT by later."])
    ]
  resultFieldDescription = []

instance FromJSON MIRFindMangledADTParams where
  parseJSON =
    withObject "SAW/MIR/find mangled ADT params" $ \o ->
    MIRFindMangledADTParams
      <$> o .: "module"
      <*> o .: "ADT mangled name"
      <*> o .: "ADT server name"

-- | The implementation of the @SAW/MIR/find mangled ADT@ command.
mirFindMangledADT :: MIRFindMangledADTParams -> Argo.Command SAWState OK
mirFindMangledADT params = do
  state <- Argo.getState
  let tasks = view sawTask state
  case tasks of
    (_:_) -> Argo.raise $ notAtTopLevel $ fst <$> tasks
    [] -> do
      mod' <- getMIRModule $ mfmaModule params
      adt <- tl $ mir_find_mangled_adt mod' $ mfmaADTName params
      let sn = mfmaADTServerName params
      setServerVal sn adt
      ok

mirFindMangledADTDescr :: Doc.Block
mirFindMangledADTDescr =
  Doc.Paragraph
    [ Doc.Text "Consult the a MIR module to find an algebraic data type (ADT) "
    , Doc.Text "with the supplied mangled identifier. A mangled identifier is "
    , Doc.Text "one that refers to an ADT that is already instantiated with "
    , Doc.Text "its type arguments (e.g., foo::Bar::_adt123456789 is a "
    , Doc.Text "mangled identifier, but foo::Bar is not). If such an ADT "
    , Doc.Text "cannot be found in the module, this will raise an error. "
    , Doc.Text ""
    , Doc.Text "Due to the fact that mangled identifiers can change easily "
    , Doc.Text "when recompiling Rust code, this command's use is discouraged "
    , Doc.Text "in favor of using 'SAW/MIR/find ADT' whenever possible."
    ]
