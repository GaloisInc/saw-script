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
    ( (.:),
      withObject,
      object,
      FromJSON(parseJSON),
      KeyValue((.=)),
      ToJSON(toJSON) )
import Data.Text (Text)

import qualified Argo
import qualified Argo.Doc as Doc
import qualified SAWScript.Builtins as SB
import qualified SAWScript.Value as SV
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
  = ABC
  | CVC4 [String]
  | RME
  | Yices [String]
  | Z3 [String]

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
      case name of
        "abc"   -> pure ABC
        "cvc4"  -> CVC4 <$> o .: "uninterpreted functions"
        "rme"   -> pure RME
        "yices" -> Yices <$> o .: "uninterpreted functions"
        "z3"    -> Z3 <$> o .: "uninterpreted functions"
        _       -> empty

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
    SV.Valid _ -> return ProofValid
    SV.InvalidMulti _  _ -> return ProofInvalid

interpretProofScript :: ProofScript -> Argo.Command SAWState (SV.ProofScript SV.SatResult)
interpretProofScript (ProofScript ts) = go ts
  where go [UseProver ABC]            = return $ SB.proveABC
        go [UseProver (CVC4 unints)]  = return $ SB.proveUnintCVC4 unints
        go [UseProver RME]            = return $ SB.proveRME
        go [UseProver (Yices unints)] = return $ SB.proveUnintYices unints
        go [UseProver (Z3 unints)]    = return $ SB.proveUnintZ3 unints
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
