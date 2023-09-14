{-# LANGUAGE OverloadedStrings #-}
-- | Support for the MIR @verify@ and @assume@ commands.
module SAWServer.MIRVerify
  ( mirVerify
  , mirVerifyDescr
  , mirAssume
  , mirAssumeDescr
  ) where

import Prelude hiding (mod)
import Control.Lens

import SAWScript.Crucible.MIR.Builtins
    ( mir_verify )
import SAWScript.Value (rwCryptol)

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer
    ( SAWState,
      SAWTask(MIRSetup),
      sawBIC,
      sawEnv,
      sawTask,
      sawTopLevelRW,
      pushTask,
      dropTask,
      setServerVal,
      getMIRModule,
      getMIRMethodSpecIR )
import SAWServer.CryptolExpression (getCryptolExpr)
import SAWServer.Data.Contract ( ContractMode(..) )
import SAWServer.Data.MIRType ( JSONMIRType )
import SAWServer.Exceptions ( notAtTopLevel )
import SAWServer.MIRCrucibleSetup ( compileMIRContract )
import SAWServer.OK ( OK, ok )
import SAWServer.ProofScript
    ( ProofScript(ProofScript), interpretProofScript )
import SAWServer.TopLevel ( tl )
import SAWServer.VerifyCommon
    ( AssumeParams(AssumeParams), VerifyParams(VerifyParams) )

mirVerifyAssume :: ContractMode -> VerifyParams JSONMIRType -> Argo.Command SAWState OK
mirVerifyAssume mode (VerifyParams modName fun lemmaNames checkSat contract script lemmaName) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do pushTask (MIRSetup lemmaName)
            state <- Argo.getState
            rm <- getMIRModule modName
            let bic = view sawBIC state
                cenv = rwCryptol (view sawTopLevelRW state)
                sawenv = view sawEnv state
            fileReader <- Argo.getFileReader
            setup <- compileMIRContract fileReader bic cenv sawenv <$>
                     traverse getCryptolExpr contract
            res <- case mode of
              VerifyContract -> do
                lemmas <- mapM getMIRMethodSpecIR lemmaNames
                proofScript <- interpretProofScript script
                tl $ mir_verify rm fun lemmas checkSat setup proofScript
              AssumeContract ->
                tl $ error "mir_unsafe_assume_spec not yet supported"
            dropTask
            setServerVal lemmaName res
            ok

mirVerify :: VerifyParams JSONMIRType -> Argo.Command SAWState OK
mirVerify = mirVerifyAssume VerifyContract

mirVerifyDescr :: Doc.Block
mirVerifyDescr =
  Doc.Paragraph [Doc.Text "Verify the named MIR method meets its specification."]

mirAssume :: AssumeParams JSONMIRType -> Argo.Command SAWState OK
mirAssume (AssumeParams modName fun contract lemmaName) =
  mirVerifyAssume AssumeContract (VerifyParams modName fun [] False contract (ProofScript []) lemmaName)

mirAssumeDescr :: Doc.Block
mirAssumeDescr =
  Doc.Paragraph [Doc.Text "Assume the named MIR method meets its specification."]
