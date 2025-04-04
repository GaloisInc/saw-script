module SAWServer.TrackFile (trackFile, forgetFile) where

import Control.Lens
import qualified Data.Map as M
import qualified Crypto.Hash.Conduit as Hash

import qualified Argo

-- XXX why are we importing what's theoretically the top-level interface from inside?
import SAWServer.SAWServer ( SAWState, trackedFiles )

-- | Add a filepath to the list of filepaths tracked by the server. Any change
-- to the SHA256 hash of this file will invalidate any cached state which is
-- causally descended from the moment this method is invoked, unless
-- @forgetFile@ is used to remove tracking of this file.
trackFile :: FilePath -> Argo.Command SAWState ()
trackFile path =
  do hash <- Hash.hashFile path
     Argo.modifyState $ over trackedFiles (M.insert path hash)

-- | Stop tracking a given file. Any state that causally descends from the
-- moment this method is invoked will not be invalidated by changes to the file
-- on disk, even if this file was previously tracked via @trackFile@.
forgetFile :: FilePath -> Argo.Command SAWState ()
forgetFile path =
  Argo.modifyState $ over trackedFiles (M.delete path)
