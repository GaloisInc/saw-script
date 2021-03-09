{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWServer.TopLevel (tl) where

import Control.Exception ( try, SomeException )
import Control.Lens ( view, set )
import Control.Monad.State ( MonadIO(liftIO) )

import SAWScript.Value ( TopLevel, runTopLevel )

import qualified Argo
import SAWServer ( SAWState, sawTopLevelRO, sawTopLevelRW )
import SAWServer.Exceptions ( verificationException )

tl :: TopLevel a -> Argo.Command SAWState a
tl act =
  do st <- Argo.getState
     let ro = view sawTopLevelRO st
         rw = view sawTopLevelRW st
     liftIO (try (runTopLevel act ro rw)) >>=
       \case
         Left (e :: SomeException) ->
           Argo.raise (verificationException e)
         Right (res, rw') ->
           do Argo.modifyState $ set sawTopLevelRW rw'
              return res
