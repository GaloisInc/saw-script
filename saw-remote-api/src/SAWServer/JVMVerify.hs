{-# LANGUAGE OverloadedStrings #-}

module SAWServer.JVMVerify
  ( jvmVerify
  , jvmAssume
  ) where

import Prelude hiding (mod)
import Control.Lens

import SAWScript.Crucible.JVM.Builtins
    ( jvm_unsafe_assume_spec, jvm_verify )
import SAWScript.JavaExpr (JavaType(..))
import SAWScript.Value (rwCryptol)

import qualified Argo
import SAWServer
    ( SAWState,
      SAWTask(JVMSetup),
      sawBIC,
      sawTask,
      sawTopLevelRW,
      pushTask,
      dropTask,
      setServerVal,
      getJVMClass,
      getJVMMethodSpecIR )
import SAWServer.CryptolExpression (getCryptolExpr)
import SAWServer.Data.Contract ( ContractMode(..) )
import SAWServer.Exceptions ( notAtTopLevel )
import SAWServer.JVMCrucibleSetup ( compileJVMContract )
import SAWServer.OK ( OK, ok )
import SAWServer.ProofScript
    ( ProofScript(ProofScript), interpretProofScript )
import SAWServer.TopLevel ( tl )
import SAWServer.VerifyCommon
    ( AssumeParams(AssumeParams), VerifyParams(VerifyParams) )

jvmVerifyAssume :: ContractMode -> VerifyParams JavaType -> Argo.Command SAWState OK
jvmVerifyAssume mode (VerifyParams className fun lemmaNames checkSat contract script lemmaName) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do pushTask (JVMSetup lemmaName [])
            state <- Argo.getState
            cls <- getJVMClass className
            let bic = view sawBIC state
                cenv = rwCryptol (view sawTopLevelRW state)
            fileReader <- Argo.getFileReader
            setup <- compileJVMContract fileReader bic cenv <$> traverse getCryptolExpr contract
            res <- case mode of
              VerifyContract -> do
                lemmas <- mapM getJVMMethodSpecIR lemmaNames
                proofScript <- interpretProofScript script
                tl $ jvm_verify cls fun lemmas checkSat setup proofScript
              AssumeContract ->
                tl $ jvm_unsafe_assume_spec cls fun setup
            dropTask
            setServerVal lemmaName res
            ok

jvmVerify :: VerifyParams JavaType -> Argo.Command SAWState OK
jvmVerify = jvmVerifyAssume VerifyContract


jvmAssume :: AssumeParams JavaType -> Argo.Command SAWState OK
jvmAssume (AssumeParams className fun contract lemmaName) =
  jvmVerifyAssume AssumeContract (VerifyParams className fun [] False contract (ProofScript []) lemmaName)
