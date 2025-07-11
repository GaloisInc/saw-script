{-# Language ImplicitParams #-}
{-# Language TemplateHaskell #-}

-- | Custom state we maintin during symbolic simulation.
module Mir.State where

import Control.Lens (makeLenses,(^.))
import Control.Monad(foldM)
import qualified Data.ByteString as BS
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Text(Text)
import qualified Data.Text as Text


import qualified SAWCentral.Builtins as SAW
import qualified SAWCore.SharedTerm as SAW
import qualified CryptolSAWCore.CryptolEnv as SAW
import qualified CryptolSAWCore.Prelude as SAW


data CompMirState = CompMirState {
  _crySharedContext :: SAW.SharedContext,
  _cryEnv           :: SAW.CryptolEnv,
  _keepUninterp     :: Set Text
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
      _cryEnv = env,
      _keepUninterp = mempty
    }


-- | Resolve the given name and add it mark it as an uninterpreted function.
-- Throws an exception if the name does not refer to anything.  If it
-- refers to multiple things, they are all uninterpreted.
resolveUninterp :: CompMirState -> IO (Set SAW.VarIndex)
resolveUninterp s = foldM resolve Set.empty (s ^. keepUninterp)
  where
  resolve done nm =
    do
      vars <- SAW.resolveNameIO (s ^. crySharedContext) (s ^. cryEnv) nm
      case vars of
        [] -> fail ("uninterp: unndefined name `" ++ Text.unpack nm ++ "`")
        _  -> pure (Set.union (Set.fromList vars) done)