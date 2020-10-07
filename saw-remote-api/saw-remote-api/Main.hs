{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.Aeson as JSON
import Data.Text (Text)

import Argo
import Argo.DefaultMain

import SAWServer
import SAWServer.CryptolSetup
import SAWServer.JVMCrucibleSetup
import SAWServer.JVMVerify
import SAWServer.LLVMCrucibleSetup
import SAWServer.LLVMVerify
import SAWServer.ProofScript
import SAWServer.SaveTerm
import SAWServer.SetOption


main :: IO ()
main =
  do theApp <- mkApp initialState sawMethods
     defaultMain description theApp

description :: String
description =
  "An RPC server for SAW."

sawMethods :: [(Text, MethodType, JSON.Value -> Method SAWState JSON.Value)]
sawMethods =
  -- Cryptol
  [ ("SAW/Cryptol/load module",  Command, method cryptolLoadModule)
  , ("SAW/Cryptol/load file",    Command, method cryptolLoadFile)
  , ("SAW/Cryptol/save term",    Command, method saveTerm)
  -- JVM
  , ("SAW/JVM/load class",       Command, method jvmLoadClass)
  , ("SAW/JVM/verify",           Command, method jvmVerify)
  , ("SAW/JVM/assume",           Command, method jvmAssume)
  -- LLVM
  , ("SAW/LLVM/load module",     Command, method llvmLoadModule)
  , ("SAW/LLVM/verify",          Command, method llvmVerify)
  , ("SAW/LLVM/verify x86",      Command, method llvmVerifyX86)
  , ("SAW/LLVM/assume",          Command, method llvmAssume)
  -- General
  , ("SAW/make simpset",         Command, method makeSimpset)
  , ("SAW/prove",                Command, method prove)
  , ("SAW/set option",           Command, method setOption)
  ]
