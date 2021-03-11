{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWServer.ProofScript
  ( ProofScript(..)
  , interpretProofScript
  , makeSimpset
  , makeSimpsetDescr
  , prove
  , proveDescr
  ) where

import Control.Applicative ( Alternative(empty) )
import Control.Monad (foldM)
import Data.Aeson
    ( (.:), (.:?),
      withObject,
      object,
      FromJSON(parseJSON),
      KeyValue((.=)),
      ToJSON(toJSON) )
import Data.Maybe (maybeToList)
import Data.Text (Text)

import qualified Argo
import qualified Argo.Doc as Doc
import qualified SAWScript.Builtins as SB
import qualified SAWScript.Value as SV
import qualified SAWScript.Proof as PF
import SAWServer
    ( ServerVal(VTerm, VSimpset),
      ServerName,
      SAWState,
      setServerVal,
      getServerVal,
      getSimpset,
      getTerm )
import SAWServer.Exceptions ( notASimpset )
import SAWServer.OK ( OK, ok )
import SAWServer.TopLevel ( tl )
import Verifier.SAW.Rewriter (addSimp, emptySimpset)
import Verifier.SAW.TermNet (merge)
import Verifier.SAW.TypedTerm (TypedTerm(..))

data Prover
  = ABC_Internal
  | RME
  | SBV_ABC_SMTLib
  | SBV_Boolector [String]
  | SBV_CVC4 [String]
  | SBV_MathSAT [String]
  | SBV_Yices [String]
  | SBV_Z3 [String]
  | W4_ABC_SMTLib
  | W4_ABC_Verilog
  | W4_Boolector [String]
  | W4_CVC4 [String]
  | W4_Yices [String]
  | W4_Z3 [String]

data ProofTactic
  = UseProver Prover
  | Unfold [String]
  | BetaReduceGoal
  | EvaluateGoal [String]
  | Simplify ServerName
  | AssumeUnsat
  | Trivial

newtype ProofScript = ProofScript [ProofTactic]

instance FromJSON Prover where
  parseJSON =
    withObject "prover" $ \o -> do
      (name :: String) <- o .: "name"
      let unints = maybeToList <$> o .:? "uninterpreted functions"
      case name of
        "abc"            -> pure ABC_Internal
        "internal-abc"   -> pure ABC_Internal
        "rme"            -> pure RME
        "sbv-abc"        -> pure SBV_ABC_SMTLib
        "sbv-boolector"  -> SBV_Boolector <$> unints
        "sbv-cvc4"       -> SBV_CVC4  <$> unints
        "cvc4"           -> SBV_CVC4  <$> unints
        "sbv-mathsat"    -> SBV_MathSAT <$> unints
        "mathsat"        -> SBV_MathSAT <$> unints
        "sbv-yices"      -> SBV_Yices <$> unints
        "yices"          -> SBV_Yices <$> unints
        "sbv-z3"         -> SBV_Z3    <$> unints
        "z3"             -> SBV_Z3    <$> unints
        "w4-abc-verilog" -> pure W4_ABC_Verilog
        "w4-abc-smtlib"  -> pure W4_ABC_SMTLib
        "w4-boolector"   -> W4_Boolector <$> unints
        "w4-cvc4"        -> W4_CVC4   <$> unints
        "w4-yices"       -> W4_Yices  <$> unints
        "w4-z3"          -> W4_Z3     <$> unints
        _                -> empty

instance FromJSON ProofTactic where
  parseJSON =
    withObject "proof tactic" $ \o -> do
      (tac :: String) <- o .: "tactic"
      case tac of
        "use prover"       -> UseProver <$> o .: "prover"
        "unfold"           -> Unfold <$> o .: "names"
        "beta reduce goal" -> pure BetaReduceGoal
        "evalute goal"     -> EvaluateGoal <$> o .: "uninterpreted functions"
        "simplify"         -> Simplify <$> o .: "rules"
        "assume unsat"     -> pure AssumeUnsat
        "trivial"          -> pure Trivial
        _                  -> empty

instance FromJSON ProofScript where
  parseJSON =
    withObject "proof script" $ \o -> ProofScript <$> o .: "tactics"

data MakeSimpsetParams =
  MakeSimpsetParams
  { ssElements :: [ServerName]
  , ssResult :: ServerName
  }

instance FromJSON MakeSimpsetParams where
  parseJSON =
    withObject "SAW/make simpset params" $ \o ->
    MakeSimpsetParams <$> o .: "elements"
                      <*> o .: "result"

instance Doc.DescribedParams MakeSimpsetParams where
  parameterFieldDescription =
    [ ("elements",
       Doc.Paragraph [Doc.Text "The items to include in the simpset."])
    , ("result",
       Doc.Paragraph [Doc.Text "The name to assign to this simpset."])
    ]


makeSimpsetDescr :: Doc.Block
makeSimpsetDescr =
  Doc.Paragraph [Doc.Text "Create a simplification rule set from the given rules."]

makeSimpset :: MakeSimpsetParams -> Argo.Command SAWState OK
makeSimpset params = do
  let add ss n = do
        v <- getServerVal n
        case v of
          VSimpset ss' -> return (merge ss ss')
          VTerm t -> return (addSimp (ttTerm t) ss)
          _ -> Argo.raise (notASimpset n)
  ss <- foldM add emptySimpset (ssElements params)
  setServerVal (ssResult params) ss
  ok

data ProveParams =
  ProveParams
  { ppScript   :: ProofScript
  , ppTermName :: ServerName
  }

instance FromJSON ProveParams where
  parseJSON =
    withObject "SAW/prove params" $ \o ->
    ProveParams <$> o .: "script"
                <*> o .: "term"

instance Doc.DescribedParams ProveParams where
  parameterFieldDescription =
    [ ("script",
       Doc.Paragraph [Doc.Text "Script to use to prove the term."])
    , ("term",
       Doc.Paragraph [Doc.Text "The term to interpret as a theorm and prove."])
    ]

--data CexValue = CexValue String TypedTerm

data ProveResult
  = ProofValid
  | ProofInvalid -- [CexValue]

--instance ToJSON CexValue where
--  toJSON (CexValue n t) = object [ "name" .= n, "value" .= t ]

instance ToJSON ProveResult where
  toJSON ProofValid = object [ "status" .= ("valid" :: Text)]
  toJSON ProofInvalid {-cex-} =
    object [ "status" .= ("invalid" :: Text) ] -- , "counterexample" .= cex]


proveDescr :: Doc.Block
proveDescr =
  Doc.Paragraph [ Doc.Text "Attempt to prove the given term representing a"
                , Doc.Text " theorem, given a proof script context."]

prove :: ProveParams -> Argo.Command SAWState ProveResult
prove params = do
  t <- getTerm (ppTermName params)
  proofScript <- interpretProofScript (ppScript params)
  res <- tl $ SB.provePrim proofScript t
  case res of
    PF.ValidProof{}      -> return ProofValid
    PF.InvalidProof{}    -> return ProofInvalid
    PF.UnfinishedProof{} -> return ProofInvalid

interpretProofScript :: ProofScript -> Argo.Command SAWState (SV.ProofScript ())
interpretProofScript (ProofScript ts) = go ts
  where go [UseProver p]            =
          case p of
            ABC_Internal          -> return $ SB.proveABC
            RME                   -> return $ SB.proveRME
            SBV_ABC_SMTLib        -> return $ SB.proveABC_SBV
            SBV_Boolector unints  -> return $ SB.proveUnintBoolector unints
            SBV_CVC4 unints       -> return $ SB.proveUnintCVC4 unints
            SBV_MathSAT unints    -> return $ SB.proveUnintMathSAT unints
            SBV_Yices unints      -> return $ SB.proveUnintYices unints
            SBV_Z3 unints         -> return $ SB.proveUnintZ3 unints
            W4_ABC_SMTLib         -> return $ SB.w4_abc_smtlib2
            W4_ABC_Verilog        -> return $ SB.w4_abc_verilog
            W4_Boolector unints   -> return $ SB.w4_unint_boolector unints
            W4_CVC4 unints        -> return $ SB.w4_unint_cvc4 unints
            W4_Yices unints       -> return $ SB.w4_unint_yices unints
            W4_Z3 unints          -> return $ SB.w4_unint_z3 unints
        go [Trivial]                  = return $ SB.trivial
        go [AssumeUnsat]              = return $ SB.assumeUnsat
        go (BetaReduceGoal : rest)    = do
          m <- go rest
          return (SB.beta_reduce_goal >> m)
        go (EvaluateGoal fns : rest)  = do
          m <- go rest
          return (SB.goal_eval fns >> m)
        go (Unfold fns : rest)        = do
          m <- go rest
          return (SB.unfoldGoal fns >> m)
        go (Simplify sn : rest)       = do
          ss <- getSimpset sn
          m <- go rest
          return (SB.simplifyGoal ss >> m)
        go _ = error "malformed proof script"
