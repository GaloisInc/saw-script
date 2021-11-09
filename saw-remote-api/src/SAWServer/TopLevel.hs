{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWServer.TopLevel (tl) where

import Control.Exception ( try, SomeException(..) )
import Control.Lens ( view, set )
import Control.Monad.State ( MonadIO(liftIO) )
import Data.IORef
import Data.Typeable (cast)

import SAWScript.Value ( TopLevel, runTopLevel )

import qualified Argo
import CryptolServer.Exceptions (cryptolError)
import SAWServer ( SAWState, sawTopLevelRO, sawTopLevelRW )
import SAWServer.CryptolExpression (CryptolModuleException(..))
import SAWServer.Exceptions ( verificationException )

tl :: TopLevel a -> Argo.Command SAWState a
tl act =
  do st <- Argo.getState
     let ro = view sawTopLevelRO st
         rw = view sawTopLevelRW st
     ref <- liftIO (newIORef rw)
     liftIO (try (runTopLevel act ro ref)) >>=
       \case
         Left e@(SomeException e')
           |  Just (CryptolModuleException err warnings) <- cast e'
           -> Argo.raise (cryptolError err warnings)
           |  otherwise
           -> Argo.raise (verificationException e)
         Right res ->
           do rw' <- liftIO (readIORef ref)
              Argo.modifyState $ set sawTopLevelRW rw'
              return res
