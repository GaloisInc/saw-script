{-# LANGUAGE OverloadedStrings #-}

module SAWServer.LLVMVerify
  ( llvmVerify
  , llvmVerifyDescr
  , llvmVerifyX86
  , llvmVerifyX86Descr
  , llvmAssume
  , llvmAssumeDescr
  ) where

import Prelude hiding (mod)
import Control.Lens

import SAWScript.Crucible.LLVM.Builtins
import SAWScript.Crucible.LLVM.X86
import SAWScript.Value (rwCryptol)

import Argo
import qualified Argo.Doc as Doc
import CryptolServer.Data.Expression
import SAWServer
import SAWServer.Data.Contract
import SAWServer.Data.LLVMType
import SAWServer.Exceptions
import SAWServer.LLVMCrucibleSetup
import SAWServer.OK
import SAWServer.ProofScript
import SAWServer.TopLevel
import SAWServer.VerifyCommon

llvmVerifyAssume :: ContractMode -> VerifyParams JSONLLVMType -> Method SAWState OK
llvmVerifyAssume mode (VerifyParams modName fun lemmaNames checkSat contract script lemmaName) =
  do tasks <- view sawTask <$> getState
     case tasks of
       (_:_) -> raise $ notAtTopLevel $ map fst tasks
       [] ->
         do pushTask (LLVMCrucibleSetup lemmaName [])
            state <- getState
            mod <- getLLVMModule modName
            let bic = view sawBIC state
                cenv = rwCryptol (view sawTopLevelRW state)
            fileReader <- getFileReader
            setup <- compileLLVMContract fileReader bic cenv <$> traverse getExpr contract
            res <- case mode of
              VerifyContract -> do
                lemmas <- mapM getLLVMMethodSpecIR lemmaNames
                proofScript <- interpretProofScript script
                tl $ llvm_verify mod fun lemmas checkSat setup proofScript
              AssumeContract ->
                tl $ llvm_unsafe_assume_spec mod fun setup
            dropTask
            setServerVal lemmaName res
            ok



llvmVerifyDescr :: Doc.Block
llvmVerifyDescr =
  Doc.Paragraph [Doc.Text "Verify the named LLVM function meets its specification."]

llvmVerify :: VerifyParams JSONLLVMType -> Method SAWState OK
llvmVerify = llvmVerifyAssume VerifyContract





llvmAssumeDescr :: Doc.Block
llvmAssumeDescr =
  Doc.Paragraph [Doc.Text $ "Assume the function meets its specification."]

llvmAssume :: AssumeParams JSONLLVMType -> Method SAWState OK
llvmAssume (AssumeParams modName fun contract lemmaName) =
  llvmVerifyAssume AssumeContract (VerifyParams modName fun [] False contract (ProofScript []) lemmaName)





llvmVerifyX86Descr :: Doc.Block
llvmVerifyX86Descr =
  Doc.Paragraph [ Doc.Text "Verify an x86 function from an ELF file for use as"
                , Doc.Text " an override in an LLVM verification meets its specification."]

llvmVerifyX86 :: X86VerifyParams JSONLLVMType -> Method SAWState OK
llvmVerifyX86 (X86VerifyParams modName objName fun globals _lemmaNames checkSat contract script lemmaName) =
  do tasks <- view sawTask <$> getState
     case tasks of
       (_:_) -> raise $ notAtTopLevel $ map fst tasks
       [] ->
         do pushTask (LLVMCrucibleSetup lemmaName [])
            state <- getState
            mod <- getLLVMModule modName
            let bic = view  sawBIC state
                cenv = rwCryptol (view sawTopLevelRW state)
                allocs = map (\(X86Alloc name size) -> (name, size)) globals
            proofScript <- interpretProofScript script
            fileReader <- getFileReader
            setup <- compileLLVMContract fileReader bic cenv <$> traverse getExpr contract
            res <- tl $ llvm_verify_x86 mod objName fun allocs checkSat setup proofScript
            dropTask
            setServerVal lemmaName res
            ok
