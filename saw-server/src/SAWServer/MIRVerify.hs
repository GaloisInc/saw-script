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
import Data.Bitraversable (Bitraversable(bitraverse))
import qualified Data.Map as Map

import CryptolServer.Data.Expression (Expression)

import SAWCentral.Crucible.MIR.Builtins
    ( mir_unsafe_assume_spec, mir_verify )
import SAWCentral.Value (rwGetCryptolEnv)

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer.SAWServer
    ( SAWState,
      SAWTask(MIRSetup),
      sawBIC,
      sawEnv,
      sawTask,
      sawTopLevelRW,
      pushTask,
      dropTask,
      setServerVal,
      getGhosts,
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

mirVerifyAssume :: ContractMode -> VerifyParams (JSONMIRType Expression) -> Argo.Command SAWState OK
mirVerifyAssume mode (VerifyParams modName fun lemmaNames checkSat contract script lemmaName) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do pushTask (MIRSetup lemmaName)
            state <- Argo.getState
            rm <- getMIRModule modName
            let bic = view sawBIC state
                cenv = rwGetCryptolEnv (view sawTopLevelRW state)
                sawenv = view sawEnv state
            fileReader <- Argo.getFileReader
            ghostEnv <- Map.fromList <$> getGhosts
            setup <- compileMIRContract fileReader bic ghostEnv cenv sawenv <$>
                     bitraverse (traverse getCryptolExpr) getCryptolExpr contract
            res <- case mode of
              VerifyContract -> do
                lemmas <- mapM getMIRMethodSpecIR lemmaNames
                proofScript <- interpretProofScript script
                tl $ mir_verify rm fun lemmas checkSat setup proofScript
              AssumeContract ->
                tl $ mir_unsafe_assume_spec rm fun setup
            dropTask
            setServerVal lemmaName res
            ok

mirVerify :: VerifyParams (JSONMIRType Expression) -> Argo.Command SAWState OK
mirVerify = mirVerifyAssume VerifyContract

mirVerifyDescr :: Doc.Block
mirVerifyDescr =
  Doc.Paragraph [Doc.Text "Verify the named MIR method meets its specification."]

mirAssume :: AssumeParams (JSONMIRType Expression) -> Argo.Command SAWState OK
mirAssume (AssumeParams modName fun contract lemmaName) =
  mirVerifyAssume AssumeContract (VerifyParams modName fun [] False contract (ProofScript []) lemmaName)

mirAssumeDescr :: Doc.Block
mirAssumeDescr =
  Doc.Paragraph [Doc.Text "Assume the named MIR method meets its specification."]
