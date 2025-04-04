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
import Control.Lens ( view )
import qualified Data.Map as Map

import SAWCentral.Crucible.LLVM.Builtins
    ( llvm_unsafe_assume_spec, llvm_verify )
import SAWCentral.Crucible.LLVM.X86 ( llvm_verify_x86 )
import SAWCentral.Value (rwCryptol)

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer.SAWServer
    ( SAWState,
      SAWTask(LLVMCrucibleSetup),
      sawBIC,
      sawTask,
      sawTopLevelRW,
      pushTask,
      dropTask,
      setServerVal,
      getGhosts,
      getLLVMModule,
      getLLVMMethodSpecIR )
import SAWServer.CryptolExpression (getCryptolExpr)
import SAWServer.Data.Contract ( ContractMode(..) )
import SAWServer.Data.LLVMType ( JSONLLVMType )
import SAWServer.Exceptions ( notAtTopLevel )
import SAWServer.LLVMCrucibleSetup ( compileLLVMContract )
import SAWServer.OK ( OK, ok )
import SAWServer.ProofScript
    ( ProofScript(ProofScript), interpretProofScript )
import SAWServer.TopLevel ( tl )
import SAWServer.VerifyCommon
    ( AssumeParams(AssumeParams),
      X86VerifyParams(X86VerifyParams),
      X86Alloc(X86Alloc),
      VerifyParams(VerifyParams) )

llvmVerifyAssume :: ContractMode -> VerifyParams JSONLLVMType -> Argo.Command SAWState OK
llvmVerifyAssume mode (VerifyParams modName fun lemmaNames checkSat contract script lemmaName) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do pushTask (LLVMCrucibleSetup lemmaName)
            state <- Argo.getState
            mod <- getLLVMModule modName
            let bic = view sawBIC state
                cenv = rwCryptol (view sawTopLevelRW state)
            fileReader <- Argo.getFileReader
            ghostEnv <- Map.fromList <$> getGhosts
            setup <- compileLLVMContract fileReader bic ghostEnv cenv <$>
                     traverse getCryptolExpr contract
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

llvmVerify :: VerifyParams JSONLLVMType -> Argo.Command SAWState OK
llvmVerify = llvmVerifyAssume VerifyContract





llvmAssumeDescr :: Doc.Block
llvmAssumeDescr =
  Doc.Paragraph [Doc.Text $ "Assume the function meets its specification."]

llvmAssume :: AssumeParams JSONLLVMType -> Argo.Command SAWState OK
llvmAssume (AssumeParams modName fun contract lemmaName) =
  llvmVerifyAssume AssumeContract (VerifyParams modName fun [] False contract (ProofScript []) lemmaName)





llvmVerifyX86Descr :: Doc.Block
llvmVerifyX86Descr =
  Doc.Paragraph [ Doc.Text "Verify an x86 function from an ELF file for use as"
                , Doc.Text " an override in an LLVM verification meets its specification."]

llvmVerifyX86 :: X86VerifyParams JSONLLVMType -> Argo.Command SAWState OK
llvmVerifyX86 (X86VerifyParams modName objName fun globals _lemmaNames checkSat contract script lemmaName) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do pushTask (LLVMCrucibleSetup lemmaName)
            state <- Argo.getState
            mod <- getLLVMModule modName
            let bic = view  sawBIC state
                cenv = rwCryptol (view sawTopLevelRW state)
                allocs = map (\(X86Alloc name size) -> (name, size)) globals
            proofScript <- interpretProofScript script
            fileReader <- Argo.getFileReader
            ghostEnv <- Map.fromList <$> getGhosts
            setup <- compileLLVMContract fileReader bic ghostEnv cenv <$>
                     traverse getCryptolExpr contract
            res <- tl $ llvm_verify_x86 mod objName fun allocs checkSat setup proofScript
            dropTask
            setServerVal lemmaName res
            ok
