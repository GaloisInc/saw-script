module SAWServer.TrackFile (trackFile, forgetFile) where

import Control.Lens
import qualified Data.Map as M
import qualified Crypto.Hash.Conduit as Hash

import Argo
import SAWServer

-- | Add a filepath to the list of filepaths tracked by the server. Any change
-- to the SHA256 hash of this file will invalidate any cached state which is
-- causally descended from the moment this method is invoked, unless
-- @forgetFile@ is used to remove tracking of this file.
trackFile :: FilePath -> Method SAWState ()
trackFile path =
  do hash <- Hash.hashFile path
     modifyState $ over trackedFiles (M.insert path hash)

-- | Stop tracking a given file. Any state that causally descends from the
-- moment this method is invoked will not be invalidated by changes to the file
-- on disk, even if this file was previously tracked via @trackFile@.
forgetFile :: FilePath -> Method SAWState ()
forgetFile path =
  modifyState $ over trackedFiles (M.delete path)
