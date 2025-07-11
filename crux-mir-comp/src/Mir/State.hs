{-# Language ImplicitParams #-}
{-# Language TemplateHaskell #-}

-- | Custom state we maintin during symbolic simulation.
module Mir.State where

import Control.Lens (makeLenses,(^.))
import Data.Text(Text)
import qualified Data.ByteString as BS

import qualified SAWCore.SharedTerm as SAW
import qualified CryptolSAWCore.CryptolEnv as SAW
import qualified CryptolSAWCore.Prelude as SAW
import qualified CryptolSAWCore.Cryptol as SAW


data CompMirState = CompMirState {
  _crySharedContext :: SAW.SharedContext,
  _cryEnv           :: SAW.CryptolEnv
}

makeLenses ''CompMirState

newMirState :: IO CompMirState
newMirState =
  do
    sc <- SAW.mkSharedContext
    SAW.scLoadPreludeModule sc
    SAW.scLoadCryptolModule sc
    let ?fileReader = BS.readFile
    env <- SAW.initCryptolEnv sc
    pure CompMirState {
      _crySharedContext = sc,
      _cryEnv = env
    }

-- | This is a modified version of `resolveName` in `SAWCentral.Builtins`
-- Given a user supplied name, we try to figure out SAW Core variable
-- it might refere to.
resolveName :: CompMirState -> Text -> IO [SAW.VarIndex]
resolveName s nm =
  do
    let cenv = s ^. cryEnv
    let sc   = s ^. crySharedContext
    scnms <- SAW.scResolveName sc nm
    let ?fileReader = BS.readFile
    res <- SAW.resolveIdentifier cenv nm
    case res of
      Just cnm ->
        do importedName <- SAW.importName cnm
           case importedName of
             SAW.ImportedName uri _ ->
               do resolvedName <- SAW.scResolveNameByURI sc uri
                  case resolvedName of
                    Just vi -> pure (vi : scnms)
                    Nothing -> pure scnms
             _ -> pure []
      Nothing -> pure []
