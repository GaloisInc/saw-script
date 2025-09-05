{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Options.Applicative
    ( Parser, help, hidden, infoOption, long, short )

import qualified Argo
import qualified Argo.DefaultMain as Argo (customMain, parseNoOpts)
import qualified Argo.Doc as Doc

import SAWVersion.Version (shortVersionText)

import SAWServer.SAWServer ( SAWState, initialState )
import SAWServer.ClearState
    ( clearStateDescr,
      clearState,
      clearAllStatesDescr,
      clearAllStates )
import SAWServer.CryptolSetup
    ( cryptolLoadModuleDescr,
      cryptolLoadModule,
      cryptolLoadFileDescr,
      cryptolLoadFile )
import SAWServer.Data.JVMType()
import SAWServer.Eval
    ( evalIntDescr,
      evalInt,
      evalBoolDescr,
      evalBool )
import SAWServer.Ghost
    ( createGhostVariableDescr,
      createGhostVariable )
import SAWServer.JVMCrucibleSetup
import SAWServer.JVMVerify
import SAWServer.LLVMCrucibleSetup
    ( llvmLoadModuleDescr, llvmLoadModule )
import SAWServer.LLVMVerify
    ( llvmVerifyDescr,
      llvmVerify,
      llvmAssumeDescr,
      llvmAssume,
      llvmVerifyX86Descr,
      llvmVerifyX86 )
import SAWServer.MIRCrucibleSetup
    ( mirLoadModuleDescr, mirLoadModule )
import SAWServer.MIRFindADT
    ( mirFindADTDescr, mirFindADT )
import SAWServer.MIRVerify
    ( mirAssumeDescr, mirAssume,
      mirVerifyDescr, mirVerify )
import SAWServer.ProofScript
    ( makeSimpsetDescr, makeSimpset, proveDescr, prove )
import SAWServer.SaveTerm ( saveTermDescr, saveTerm )
import SAWServer.SetOption ( setOptionDescr, setOption )
import SAWServer.Yosys
    ( yosysImportDescr, yosysImport,
      yosysVerifyDescr, yosysVerify,
      yosysImportSequentialDescr, yosysImportSequential,
      yosysExtractSequentialDescr, yosysExtractSequential )


main :: IO ()
main = do
  setLocaleEncoding utf8
  theApp <- Argo.mkApp
               "SAW RPC Server"
               serverDocs
               (Argo.defaultAppOpts
               Argo.MutableState)
               initialState
               sawMethods
  Argo.customMain
    Argo.parseNoOpts
    Argo.parseNoOpts
    Argo.parseNoOpts
    Argo.parseNoOpts
    versionParser
    description
    (const (pure theApp))

-- | Display the version number when the @--version@/@-v@ option is supplied.
versionParser :: Parser (a -> a)
versionParser =
  infoOption shortVersionText $
  mconcat
    [ long "version"
    , short 'v'
    , help "Display version number"
    , hidden
    ]

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
  , Argo.command
     "SAW/JVM/load class"
     jvmLoadClassDescr
     jvmLoadClass
  , Argo.command
     "SAW/JVM/verify"
     jvmVerifyDescr
     jvmVerify
  , Argo.command
     "SAW/JVM/assume"
     jvmAssumeDescr
     jvmAssume
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
  -- MIR
  , Argo.command
      "SAW/MIR/load module"
      mirLoadModuleDescr
      mirLoadModule
  , Argo.command
     "SAW/MIR/verify"
     mirVerifyDescr
     mirVerify
  , Argo.command
     "SAW/MIR/assume"
     mirAssumeDescr
     mirAssume
  , Argo.command
     "SAW/MIR/find ADT"
     mirFindADTDescr
     mirFindADT
  -- Yosys
  , Argo.command
     "SAW/Yosys/import"
     yosysImportDescr
     yosysImport
  , Argo.command
     "SAW/Yosys/verify"
     yosysVerifyDescr
     yosysVerify
  , Argo.command
     "SAW/Yosys/import sequential"
     yosysImportSequentialDescr
     yosysImportSequential
  , Argo.command
     "SAW/Yosys/extract sequential"
     yosysExtractSequentialDescr
     yosysExtractSequential
  -- General
  , Argo.command
     "SAW/create ghost variable"
     createGhostVariableDescr
     createGhostVariable
  , Argo.command
     "SAW/make simpset"
     makeSimpsetDescr
     makeSimpset
  , Argo.command
     "SAW/prove"
     proveDescr
     prove
  , Argo.command
     "SAW/eval int"
     evalIntDescr
     evalInt
  , Argo.command
     "SAW/eval bool"
     evalBoolDescr
     evalBool
  , Argo.command
     "SAW/set option"
     setOptionDescr
     setOption
  , Argo.notification
     "SAW/clear state"
     clearStateDescr
     clearState
  , Argo.notification
     "SAW/clear all states"
     clearAllStatesDescr
     clearAllStates
  ]
