{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Exceptions (
  -- * Environment errors
    serverValNotFound
  , notACryptolEnv
  , notAnLLVMModule
  , notAnLLVMSetup
  , notACrucibleSetupVal
  , notAJVMMethodSpecIR
  , notAnLLVMMethodSpecIR
  , notASimpset
  , notATerm
  , notAJVMClass
  , notAYosysTheorem
  , notAYosysImport
  , notAYosysSequential
  , notAMIRModule
  , notAMIRMethodSpecIR
  , notAMIRAdt
  -- * Wrong monad errors
  , notSettingUpCryptol
  , notSettingUpLLVMCrucible
  , notAtTopLevel
  -- * Cryptol errors
  , cryptolError
  -- * LLVM errors
  , cantLoadLLVMModule
  -- * Verification
  , verificationException
  ) where

import Control.Exception ( Exception(displayException) )
import Data.Aeson as JSON ( object, KeyValue((.=)), ToJSON )
import qualified Data.Text as T

import Argo ( makeJSONRPCException, JSONRPCException )

--------------------------------------------------------------------------------
-- NOTE: IF YOU MODIFY EXCEPTION CODES OR ADD NEW ONES, THESE CHANGES MUST BE
--       SYNCHRONIZED WITH ANY CLIENTS (such as argo/python/saw/exceptions.py)
--------------------------------------------------------------------------------

serverValNotFound ::
  (ToJSON name, Show name) =>
  name {- ^ the name that was not found -}->
  JSONRPCException
serverValNotFound name =
  makeJSONRPCException 10000 ("No server value with name " <> T.pack (show name))
    (Just $ object ["name" .= name])

notACryptolEnv ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a Cryptol environment -}->
  JSONRPCException
notACryptolEnv name =
  makeJSONRPCException 10010
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a Cryptol environment")
    (Just $ object ["name" .= name])

notAnLLVMModule ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to an LLVM module -}->
  JSONRPCException
notAnLLVMModule name =
  makeJSONRPCException 10020
    ("The server value with name " <>
     T.pack (show name) <>
     " is not an LLVM module")
    (Just $ object ["name" .= name])

notAnLLVMSetup ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to an LLVM setup script -}->
  JSONRPCException
notAnLLVMSetup name =
  makeJSONRPCException 10030
    ("The server value with name " <>
     T.pack (show name) <>
     " is not an LLVM setup script")
    (Just $ object ["name" .= name])

notACrucibleSetupVal ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a Crucible setup value -}->
  JSONRPCException
notACrucibleSetupVal name =
  makeJSONRPCException 10040
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a Crucible setup value")
    (Just $ object ["name" .= name])

notAnLLVMMethodSpecIR ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a method specification IR -}->
  JSONRPCException
notAnLLVMMethodSpecIR name =
  makeJSONRPCException 10050
    ("The server value with name " <>
     T.pack (show name) <>
     " is not an LLVM method specification")
    (Just $ object ["name" .= name])

notASimpset ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a simpset -}->
  JSONRPCException
notASimpset name =
  makeJSONRPCException 10060
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a simpset")
    (Just $ object ["name" .= name])

notATerm ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a term -}->
  JSONRPCException
notATerm name =
  makeJSONRPCException 10070
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a term")
    (Just $ object ["name" .= name])

notAJVMClass ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a JVM class -}->
  JSONRPCException
notAJVMClass name =
  makeJSONRPCException 10080
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a JVM class")
    (Just $ object ["name" .= name])

notAJVMMethodSpecIR ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a method specification IR -}->
  JSONRPCException
notAJVMMethodSpecIR name =
  makeJSONRPCException 10090
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a JVM method specification")
    (Just $ object ["name" .= name])

notSettingUpCryptol :: JSONRPCException
notSettingUpCryptol =
  makeJSONRPCException 10100 "Not currently setting up Cryptol" noData

notSettingUpLLVMCrucible :: JSONRPCException
notSettingUpLLVMCrucible =
  makeJSONRPCException
    10110 "Not currently setting up Crucible/LLVM" noData

notAtTopLevel :: ToJSON a => [a] -> JSONRPCException
notAtTopLevel tasks =
  makeJSONRPCException
    10120 "Not at top level"
    (Just (JSON.object ["tasks" .= tasks]))

notAYosysTheorem ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a Yosys theorem -}->
  JSONRPCException
notAYosysTheorem name =
  makeJSONRPCException 10130
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a Yosys theorem")
    (Just $ object ["name" .= name])

notAYosysImport ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a Yosys import -}->
  JSONRPCException
notAYosysImport name =
  makeJSONRPCException 10131
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a Yosys import")
    (Just $ object ["name" .= name])

notAYosysSequential ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a Yosys sequential module -}->
  JSONRPCException
notAYosysSequential name =
  makeJSONRPCException 10132
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a Yosys sequential module")
    (Just $ object ["name" .= name])

notAMIRModule ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a MIR module -}->
  JSONRPCException
notAMIRModule name =
  makeJSONRPCException 10140
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a MIR module")
    (Just $ object ["name" .= name])

notAMIRMethodSpecIR ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a method specification IR -}->
  JSONRPCException
notAMIRMethodSpecIR name =
  makeJSONRPCException 10150
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a MIR method specification")
    (Just $ object ["name" .= name])

notAMIRAdt ::
  (ToJSON name, Show name) =>
  name {- ^ the name that should have been mapped to a MIR ADT -}->
  JSONRPCException
notAMIRAdt name =
  makeJSONRPCException 10150
    ("The server value with name " <>
     T.pack (show name) <>
     " is not a MIR ADT")
    (Just $ object ["name" .= name])

cantLoadLLVMModule :: String -> JSONRPCException
cantLoadLLVMModule err =
  makeJSONRPCException
    10200 "Can't load LLVM module"
    (Just (JSON.object ["error" .= err]))

verificationException :: Exception e => e -> JSONRPCException
verificationException e =
  makeJSONRPCException
    10300 "Verification exception"
    (Just (JSON.object ["error" .= displayException e]))

cryptolError :: String -> JSONRPCException
cryptolError message =
  makeJSONRPCException
    11000 "Cryptol exception"
    (Just (JSON.object ["error" .= message]))

noData :: Maybe ()
noData = Nothing
