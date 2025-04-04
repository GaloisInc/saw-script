{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWServer.TopLevel (tl) where

import Control.Exception ( try, SomeException(..) )
import Control.Lens ( view, set )
import Control.Monad.State ( MonadIO(liftIO) )
import Data.Typeable (cast)

import SAWCentral.Value ( TopLevel, runTopLevel, IsValue(..), FromValue(..) )

import qualified Argo
import CryptolServer.Exceptions (cryptolError)
import SAWServer ( SAWState, sawTopLevelRO, sawTopLevelRW )
import SAWServer.CryptolExpression (CryptolModuleException(..))
import SAWServer.Exceptions ( verificationException )

tl :: (FromValue a, IsValue a) => TopLevel a -> Argo.Command SAWState a
tl act =
  do st <- Argo.getState
     let ro = view sawTopLevelRO st
         rw = view sawTopLevelRW st
     liftIO (try (runTopLevel act ro rw)) >>=
       \case
         Left e@(SomeException e')
           |  Just (CryptolModuleException err warnings) <- cast e'
           -> Argo.raise (cryptolError err warnings)
           |  otherwise
           -> Argo.raise (verificationException e)
         Right (res, rw') ->
           do Argo.modifyState $ set sawTopLevelRW rw'
              return (fromValue res)
