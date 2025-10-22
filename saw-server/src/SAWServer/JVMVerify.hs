{-# LANGUAGE OverloadedStrings #-}

module SAWServer.JVMVerify
  ( jvmVerify
  , jvmVerifyDescr
  , jvmAssume
  , jvmAssumeDescr
  ) where

import Prelude hiding (mod)
import Control.Lens
import qualified Data.Map as Map

import SAWCentral.Crucible.JVM.Builtins
    ( jvm_unsafe_assume_spec, jvm_verify )
import SAWCentral.JavaExpr (JavaType(..))
import SAWCentral.Value (rwGetCryptolEnv)

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer.SAWServer
    ( SAWState,
      SAWTask(JVMSetup),
      sawBIC,
      sawTask,
      sawTopLevelRW,
      pushTask,
      dropTask,
      setServerVal,
      getGhosts,
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
         do pushTask (JVMSetup lemmaName)
            state <- Argo.getState
            cls <- getJVMClass className
            let bic = view sawBIC state
                cenv = rwGetCryptolEnv (view sawTopLevelRW state)
            fileReader <- Argo.getFileReader
            ghostEnv <- Map.fromList <$> getGhosts
            setup <- compileJVMContract fileReader bic ghostEnv cenv <$> traverse getCryptolExpr contract
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

jvmVerifyDescr :: Doc.Block
jvmVerifyDescr =
  Doc.Paragraph [Doc.Text "Verify the named JVM method meets its specification."]

jvmAssume :: AssumeParams JavaType -> Argo.Command SAWState OK
jvmAssume (AssumeParams className fun contract lemmaName) =
  jvmVerifyAssume AssumeContract (VerifyParams className fun [] False contract (ProofScript []) lemmaName)

jvmAssumeDescr :: Doc.Block
jvmAssumeDescr =
  Doc.Paragraph [Doc.Text "Assume the named JVM method meets its specification."]
