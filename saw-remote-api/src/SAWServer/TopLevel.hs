{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWServer.TopLevel (tl) where

import Control.Exception
import Control.Lens
import Control.Monad.State

import SAWScript.Value

import Argo
import SAWServer
import SAWServer.Exceptions

tl :: TopLevel a -> Method SAWState a
tl act =
  do st <- getState
     let ro = view sawTopLevelRO st
         rw = view sawTopLevelRW st
     liftIO (try (runTopLevel act ro rw)) >>=
       \case
         Left (e :: SomeException) ->
           raise (verificationException e)
         Right (res, rw') ->
           do modifyState $ set sawTopLevelRW rw'
              return res
