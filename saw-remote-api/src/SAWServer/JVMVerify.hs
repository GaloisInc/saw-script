{-# LANGUAGE OverloadedStrings #-}

module SAWServer.JVMVerify
  ( jvmVerify
  , jvmAssume
  ) where

import Prelude hiding (mod)
import Control.Lens

import qualified Language.JVM.Common as JVM

import SAWScript.Crucible.JVM.Builtins
import SAWScript.JavaExpr (JavaType(..))
import SAWScript.Value (rwCryptol)

import Argo
import CryptolServer.Data.Expression
import SAWServer
import SAWServer.Data.Contract
import SAWServer.Data.JVMType
import SAWServer.Exceptions
import SAWServer.JVMCrucibleSetup
import SAWServer.OK
import SAWServer.ProofScript
import SAWServer.TopLevel
import SAWServer.VerifyCommon

jvmVerifyAssume :: ContractMode -> VerifyParams JavaType -> Method SAWState OK
jvmVerifyAssume mode (VerifyParams className fun lemmaNames checkSat contract script lemmaName) =
  do tasks <- view sawTask <$> getState
     case tasks of
       (_:_) -> raise $ notAtTopLevel $ map fst tasks
       [] ->
         do pushTask (JVMSetup lemmaName [])
            state <- getState
            cls <- getJVMClass className
            let bic = view sawBIC state
                cenv = rwCryptol (view sawTopLevelRW state)
            fileReader <- getFileReader
            setup <- compileJVMContract fileReader bic cenv <$> traverse getExpr contract
            res <- case mode of
              VerifyContract -> do
                lemmas <- mapM getJVMMethodSpecIR lemmaNames
                proofScript <- interpretProofScript script
                tl $ crucible_jvm_verify cls fun lemmas checkSat setup proofScript
              AssumeContract ->
                tl $ crucible_jvm_unsafe_assume_spec cls fun setup
            dropTask
            setServerVal lemmaName res
            ok

jvmVerify :: VerifyParams JavaType -> Method SAWState OK
jvmVerify = jvmVerifyAssume VerifyContract


jvmAssume :: AssumeParams JavaType -> Method SAWState OK
jvmAssume (AssumeParams className fun contract lemmaName) =
  jvmVerifyAssume AssumeContract (VerifyParams className fun [] False contract (ProofScript []) lemmaName)
