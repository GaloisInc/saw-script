


module CryptolSAWCore.FileReader 
  ( withFileReader
  , scFileReader 
  ) where

import Control.Monad.IO.Class
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Typeable

import SAWCore.SharedTerm (SharedContext, IsMetadata(..), scGetData, scWithData)

newtype FileReader = FileReader (FilePath -> IO ByteString)
  deriving Typeable

instance IsMetadata FileReader where
  initMetadata = return $ FileReader BS.readFile

-- Override the result of 'scFileReader' with the given function for
-- the duration of an action.
withFileReader :: (MonadIO m) => SharedContext -> (FilePath -> IO ByteString) -> m a -> m a
withFileReader sc fileReader = scWithData sc (\_ -> FileReader fileReader)

-- | Get the file reader from the 'SharedContext'. Returns
-- 'Data.ByteString.readFile' unless overridden by 'withFileReader'.
scFileReader :: (MonadIO m) => SharedContext -> m (FilePath -> IO ByteString)
scFileReader sc = do
  FileReader fileReader <- liftIO $ scGetData sc
  return fileReader
