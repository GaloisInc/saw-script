{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.Text as T

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
  [ Doc.Paragraph [Doc.Text "A remote server for SAW."]
  ]

description :: String
description =
  "An RPC server for SAW."

sawMethods :: [AppMethod SAWState]
sawMethods =
  -- Cryptol
  [ method
     "SAW/Cryptol/load module"
     Command
     (Doc.Paragraph [Doc.Text "Load the specified Cryptol module."])
     cryptolLoadModule
  , method
     "SAW/Cryptol/load file"
     Command
     (Doc.Paragraph [Doc.Text "Load the given file as a Cryptol module."])
     cryptolLoadFile
  , method
     "SAW/Cryptol/save term"
     Command
     (Doc.Paragraph [Doc.Text "Save a term to be referenced later by name."])
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
     (Doc.Paragraph [Doc.Text "Load the specified LLVM module."])
     llvmLoadModule
  , method
     "SAW/LLVM/verify"
     Command
     (Doc.Paragraph [Doc.Text "Verify the named LLVM function meets its specification."])
     llvmVerify
  , method
     "SAW/LLVM/verify x86"
     Command
     (Doc.Paragraph [Doc.Text $ T.pack
                              $ "Verify an x86 function from an ELF file for use as "
                                ++ "an override in an LLVM verification meets its specification."])
     llvmVerifyX86
  , method
     "SAW/LLVM/assume"
     Command
     (Doc.Paragraph [Doc.Text $ "Assume the function meets its specification."])
     llvmAssume
  -- General
  , method
     "SAW/make simpset"
     Command
     (Doc.Paragraph [Doc.Text "Create a simplification rule from the given rules."])
     makeSimpset
  , method
     "SAW/prove"
     Command
     (Doc.Paragraph [Doc.Text $ T.pack
                              $ "Attempt to prove the given term representing a "
                                ++ "theorem, given a proof script context."])
     prove
  , method
     "SAW/set option"
     Command
     (Doc.Paragraph [Doc.Text "Set a SAW option in the server."])
     setOption
  ]
