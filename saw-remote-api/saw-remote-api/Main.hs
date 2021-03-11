{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Argo
import qualified Argo.DefaultMain as Argo (defaultMain)
import qualified Argo.Doc as Doc

import SAWServer ( SAWState, initialState )
import SAWServer.CryptolSetup
    ( cryptolLoadModuleDescr,
      cryptolLoadModule,
      cryptolLoadFileDescr,
      cryptolLoadFile )
--import SAWServer.JVMCrucibleSetup
--import SAWServer.JVMVerify
import SAWServer.LLVMCrucibleSetup
    ( llvmLoadModuleDescr, llvmLoadModule )
import SAWServer.LLVMVerify
    ( llvmVerifyDescr,
      llvmVerify,
      llvmAssumeDescr,
      llvmAssume,
      llvmVerifyX86Descr,
      llvmVerifyX86 )
import SAWServer.ProofScript
    ( makeSimpsetDescr, makeSimpset, proveDescr, prove )
import SAWServer.SaveTerm ( saveTermDescr, saveTerm )
import SAWServer.SetOption ( setOptionDescr, setOption )


main :: IO ()
main = do
  theApp <- Argo.mkApp
               "SAW RPC Server"
               serverDocs
               (Argo.defaultAppOpts
               Argo.MutableState)
               initialState
               sawMethods
  Argo.defaultMain description theApp

serverDocs :: [Doc.Block]
serverDocs =
  [ Doc.Section "Summary" $ [ Doc.Paragraph
    [Doc.Text "A remote server for ",
     Doc.Link (Doc.URL "https://saw.galois.com/") "SAW",
     Doc.Text " for verifying programs with a featureset similar to SAWScript."]]]

description :: String
description =
  "An RPC server for SAW."

sawMethods :: [Argo.AppMethod SAWState]
sawMethods =
  -- Cryptol
  [ Argo.command
     "SAW/Cryptol/load module"
     cryptolLoadModuleDescr
     cryptolLoadModule
  , Argo.command
     "SAW/Cryptol/load file"
     cryptolLoadFileDescr
     cryptolLoadFile
  , Argo.command
     "SAW/Cryptol/save term"
     saveTermDescr
     saveTerm
  -- JVM
  {-
  , Argo.command "SAW/JVM/load class" (Doc.Paragraph [Doc.Text "TODO"]) jvmLoadClass
  , Argo.command "SAW/JVM/verify"     (Doc.Paragraph [Doc.Text "TODO"]) jvmVerify
  , Argo.command "SAW/JVM/assume"     (Doc.Paragraph [Doc.Text "TODO"]) jvmAssume
  -}
  -- LLVM
  , Argo.command
     "SAW/LLVM/load module"
     llvmLoadModuleDescr
     llvmLoadModule
  , Argo.command
     "SAW/LLVM/verify"
     llvmVerifyDescr
     llvmVerify
  , Argo.command
     "SAW/LLVM/verify x86"
     llvmVerifyX86Descr
     llvmVerifyX86
  , Argo.command
     "SAW/LLVM/assume"
     llvmAssumeDescr
     llvmAssume
  -- General
  , Argo.command
     "SAW/make simpset"
     makeSimpsetDescr
     makeSimpset
  , Argo.command
     "SAW/prove"
     proveDescr
     prove
  , Argo.command
     "SAW/set option"
     setOptionDescr
     setOption
  ]
