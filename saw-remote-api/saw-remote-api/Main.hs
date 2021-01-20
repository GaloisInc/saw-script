{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Argo
import Argo.DefaultMain
import qualified Argo.Doc as Doc

import SAWServer
import SAWServer.CryptolSetup
--import SAWServer.JVMCrucibleSetup
--import SAWServer.JVMVerify
import SAWServer.LLVMCrucibleSetup
import SAWServer.LLVMVerify
import SAWServer.ProofScript
import SAWServer.SaveTerm
import SAWServer.SetOption


main :: IO ()
main =
  do theApp <- mkApp "SAW RPC Server" serverDocs initialState sawMethods
     defaultMain description theApp

serverDocs :: [Doc.Block]
serverDocs =
  [ Doc.Section "Summary" $ [ Doc.Paragraph
    [Doc.Text "A remote server for ",
     Doc.Link (Doc.URL "https://saw.galois.com/") "SAW",
     Doc.Text " for verifying programs with a featureset similar to SAWScript."]]]

description :: String
description =
  "An RPC server for SAW."

sawMethods :: [AppMethod SAWState]
sawMethods =
  -- Cryptol
  [ method
     "SAW/Cryptol/load module"
     Command
     cryptolLoadModuleDescr
     cryptolLoadModule
  , method
     "SAW/Cryptol/load file"
     Command
     cryptolLoadFileDescr
     cryptolLoadFile
  , method
     "SAW/Cryptol/save term"
     Command
     saveTermDescr
     saveTerm
  -- JVM
  {-
  , method "SAW/JVM/load class" Command (Doc.Paragraph [Doc.Text "TODO"]) jvmLoadClass
  , method "SAW/JVM/verify"     Command (Doc.Paragraph [Doc.Text "TODO"]) jvmVerify
  , method "SAW/JVM/assume"     Command (Doc.Paragraph [Doc.Text "TODO"]) jvmAssume
  -}
  -- LLVM
  , method
     "SAW/LLVM/load module"
     Command
     llvmLoadModuleDescr
     llvmLoadModule
  , method
     "SAW/LLVM/verify"
     Command
     llvmVerifyDescr
     llvmVerify
  , method
     "SAW/LLVM/verify x86"
     Command
     llvmVerifyX86Descr
     llvmVerifyX86
  , method
     "SAW/LLVM/assume"
     Command
     llvmAssumeDescr
     llvmAssume
  -- General
  , method
     "SAW/make simpset"
     Command
     makeSimpsetDescr
     makeSimpset
  , method
     "SAW/prove"
     Command
     proveDescr
     prove
  , method
     "SAW/set option"
     Command
     setOptionDescr
     setOption
  ]
