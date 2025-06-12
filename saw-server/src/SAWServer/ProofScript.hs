{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module SAWServer.ProofScript
  ( ProofScript(..)
  , interpretProofScript
  , makeSimpset
  , makeSimpsetDescr
  , prove
  , proveDescr
  ) where

import Control.Applicative ( Alternative(empty) )
import Control.Exception ( Exception, throw )
import Control.Lens ( view )
import Control.Monad (foldM, forM)
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Aeson
    ( (.:), (.:?),
      withObject,
      object,
      FromJSON(parseJSON),
      KeyValue((.=)),
      ToJSON(toJSON) )
import Data.Maybe ( fromMaybe )
import Data.Text (Text, pack)
import Data.Typeable (Proxy(..), typeRep)
import Numeric (showHex)

import qualified Argo
import qualified Argo.Doc as Doc
import CryptolServer.Data.Expression ( Expression(..), Encoding(..), getCryptolExpr )
import qualified SAWCentral.Builtins as SB
import qualified SAWCentral.Value as SV
import qualified SAWCentral.Proof as PF
import SAWServer.SAWServer
    ( ServerVal(VSimpset),
      ServerName,
      SAWState,
      setServerVal,
      getServerVal,
      getSimpset,
      sawBIC,
      sawTopLevelRW)
import SAWServer.CryptolExpression ( CryptolModuleException(..), getTypedTermOfCExp )
import SAWServer.Exceptions ( notASimpset )
import SAWServer.OK ( OK, ok )
import SAWServer.TopLevel ( tl )
import SAWCore.FiniteValue (FirstOrderValue(..))
import SAWCore.Name (ecName, toShortName)
import SAWCore.Rewriter (emptySimpset)
import SAWCore.TermNet (merge)

data Prover
  = RME
  | SBV_ABC_SMTLib
  | SBV_Bitwuzla [Text]
  | SBV_Boolector [Text]
  | SBV_CVC4 [Text]
  | SBV_CVC5 [Text]
  | SBV_MathSAT [Text]
  | SBV_Yices [Text]
  | SBV_Z3 [Text]
  | W4_ABC_SMTLib
  | W4_ABC_Verilog
  | W4_Bitwuzla [Text]
  | W4_Boolector [Text]
  | W4_CVC4 [Text]
  | W4_CVC5 [Text]
  | W4_Yices [Text]
  | W4_Z3 [Text]

data ProofTactic
  = UseProver Prover
  | Unfold [Text]
  | BetaReduceGoal
  | EvaluateGoal [Text]
  | Simplify ServerName
  | Admit
  | Trivial
  | Quickcheck Integer

newtype ProofScript = ProofScript [ProofTactic]

instance FromJSON Prover where
  parseJSON =
    withObject "prover" $ \o -> do
      (name :: Text) <- o .: "name"
      let unints = fromMaybe [] <$> o .:? "uninterpreted functions"
      case name of
        "abc"            -> pure W4_ABC_SMTLib
        "bitwuzla"       -> SBV_Bitwuzla <$> unints
        "boolector"      -> SBV_Boolector <$> unints
        "cvc4"           -> SBV_CVC4  <$> unints
        "cvc5"           -> SBV_CVC5  <$> unints
        "mathsat"        -> SBV_MathSAT <$> unints
        "rme"            -> pure RME
        "sbv-abc"        -> pure SBV_ABC_SMTLib
        "sbv-bitwuzla"   -> SBV_Bitwuzla <$> unints
        "sbv-boolector"  -> SBV_Boolector <$> unints
        "sbv-cvc4"       -> SBV_CVC4  <$> unints
        "sbv-cvc5"       -> SBV_CVC5  <$> unints
        "sbv-mathsat"    -> SBV_MathSAT <$> unints
        "sbv-yices"      -> SBV_Yices <$> unints
        "sbv-z3"         -> SBV_Z3    <$> unints
        "w4-abc-smtlib"  -> pure W4_ABC_SMTLib
        "w4-abc-verilog" -> pure W4_ABC_Verilog
        "w4-bitwuzla"    -> W4_Bitwuzla <$> unints
        "w4-boolector"   -> W4_Boolector <$> unints
        "w4-cvc4"        -> W4_CVC4   <$> unints
        "w4-cvc5"        -> W4_CVC5   <$> unints
        "w4-yices"       -> W4_Yices  <$> unints
        "w4-z3"          -> W4_Z3     <$> unints
        "yices"          -> SBV_Yices <$> unints
        "z3"             -> SBV_Z3    <$> unints
        _                -> empty

instance FromJSON ProofTactic where
  parseJSON =
    withObject "proof tactic" $ \o -> do
      (tac :: Text) <- o .: "tactic"
      case tac of
        "use prover"       -> UseProver <$> o .: "prover"
        "unfold"           -> Unfold <$> o .: "names"
        "beta reduce goal" -> pure BetaReduceGoal
        -- The "evaluate" was misspelled "evalute" until 20250329;
        -- since the python side has the correct spelling, it wouldn't
        -- have worked and probably hasn't been used; therefore, I'm
        -- going to just fix it and not worry about backwards compat.
        "evaluate goal"    -> EvaluateGoal <$> o .: "uninterpreted functions"
        "simplify"         -> Simplify <$> o .: "rules"
        "admit"            -> pure Admit
        "trivial"          -> pure Trivial
        "quickcheck"       -> Quickcheck <$> o .: "number of inputs"
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

instance Doc.DescribedMethod MakeSimpsetParams OK where
  parameterFieldDescription =
    [ ("elements",
       Doc.Paragraph [Doc.Text "The items to include in the simpset."])
    , ("result",
       Doc.Paragraph [Doc.Text "The name to assign to this simpset."])
    ]
  resultFieldDescription = []


makeSimpsetDescr :: Doc.Block
makeSimpsetDescr =
  Doc.Paragraph [Doc.Text "Create a simplification rule set from the given rules."]

makeSimpset :: MakeSimpsetParams -> Argo.Command SAWState OK
makeSimpset params = do
  let add ss n = do
        v <- getServerVal n
        case v of
          VSimpset ss' -> return (merge ss ss')
          _ -> Argo.raise (notASimpset n)
  ss <- foldM add emptySimpset (ssElements params)
  setServerVal (ssResult params) ss
  ok

data ProveParams cryptolExpr =
  ProveParams
  { ppScript :: ProofScript
  , ppGoal   :: cryptolExpr
  }

instance (FromJSON cryptolExpr) => FromJSON (ProveParams cryptolExpr) where
  parseJSON =
    withObject "SAW/prove params" $ \o ->
    ProveParams <$> o .: "script"
                <*> o .: "goal"

instance Doc.DescribedMethod (ProveParams cryptolExpr) ProveResult where
  parameterFieldDescription =
    [ ("script",
       Doc.Paragraph [Doc.Text "Script to use to prove the term."])
    , ("goal",
       Doc.Paragraph [Doc.Text "The goal to interpret as a theorm and prove."])
    ]
  resultFieldDescription =
    [ ("status",
      Doc.Paragraph [ Doc.Text "A string (one of "
                    , Doc.Literal "valid", Doc.Literal ", ", Doc.Literal "invalid"
                    , Doc.Text ", or ", Doc.Literal "unknown"
                    , Doc.Text ") indicating whether the proof went through successfully or not."
                    ])
    , ("counterexample",
      Doc.Paragraph [ Doc.Text "Only used if the ", Doc.Literal "status"
                    , Doc.Text " is ", Doc.Literal "invalid"
                    , Doc.Text ". An array of objects where each object has a ", Doc.Literal "name"
                    , Doc.Text " string and a "
                    , Doc.Link (Doc.TypeDesc (typeRep (Proxy @Expression))) "JSON Cryptol expression"
                    , Doc.Text " ", Doc.Literal "value", Doc.Text "."
                    ])
    ]

data CexValue = CexValue Text Expression

data ProveResult
  = ProofValid
  | ProofInvalid [CexValue]
  | ProofUnknown

instance ToJSON CexValue where
  toJSON (CexValue n t) = object [ "name" .= n, "value" .= t ]

instance ToJSON ProveResult where
  toJSON ProofValid = object [ "status" .= ("valid" :: Text)]
  toJSON ProofUnknown = object [ "status" .= ("unknown" :: Text)]
  toJSON (ProofInvalid cex) =
    object [ "status" .= ("invalid" :: Text), "counterexample" .= cex]


proveDescr :: Doc.Block
proveDescr =
  Doc.Paragraph [ Doc.Text "Attempt to prove the given term representing a"
                , Doc.Text " theorem, given a proof script context."]

exportFirstOrderExpression :: FirstOrderValue -> Either String Expression
exportFirstOrderExpression fv =
  case fv of
    FOVBit b    -> return $ Bit b
    FOVInt i    -> return $ Integer i
    FOVIntMod m i -> return $ IntegerModulo i (toInteger m)
    FOVWord w x -> return $ Num Hex (pack (showHex x "")) (toInteger w)
    FOVVec _t vs -> Sequence <$> mapM exportFirstOrderExpression vs
    FOVArray{} -> Left "exportFirstOrderExpression: unsupported type: Array (concrete case)"
    FOVOpaqueArray{} -> Left "exportFirstOrderExpression: unsupported type: Array (opaque case)"
    FOVTuple vs -> Tuple <$> mapM exportFirstOrderExpression vs
    FOVRec _vm  -> Left "exportFirstOrderExpression: unsupported type: Record"


data ProveException = ProveException String

instance Show ProveException where
    show (ProveException msg) = "Exception in `prove` command: " ++ msg

instance Exception ProveException

prove :: ProveParams Expression -> Argo.Command SAWState ProveResult
prove params = do
  state <- Argo.getState
  fileReader <- Argo.getFileReader
  let cenv = SV.rwCryptol (view sawTopLevelRW state)
      bic = view sawBIC state
  cexp <- getCryptolExpr (ppGoal params)
  (eterm, warnings) <- liftIO $ getTypedTermOfCExp fileReader (SV.biSharedContext bic) cenv cexp
  t <- case eterm of
         Right (t, _) -> return t -- TODO: report warnings
         Left err -> throw $ CryptolModuleException err warnings
  proofScript <- interpretProofScript (ppScript params)
  res <- tl $ SB.provePrim proofScript t
  case res of
    PF.ValidProof{} ->
      return ProofValid
    PF.InvalidProof _ cex _ ->
      do cexVals <- forM cex $
                      \(ec, v) ->
                         do e <- case exportFirstOrderExpression v of
                                   Left err -> throw $ ProveException err
                                   Right e -> return e
                            return $ CexValue (toShortName (ecName ec)) e
         return $ ProofInvalid $ cexVals
    PF.UnfinishedProof{} ->
      return ProofUnknown

interpretProofScript :: ProofScript -> Argo.Command SAWState (SV.ProofScript ())
interpretProofScript (ProofScript ts) = go ts
  where go [UseProver p]            =
          case p of
            RME                   -> return $ SB.proveRME
            SBV_ABC_SMTLib        -> return $ SB.proveABC_SBV
            SBV_Bitwuzla unints   -> return $ SB.proveUnintBitwuzla unints
            SBV_Boolector unints  -> return $ SB.proveUnintBoolector unints
            SBV_CVC4 unints       -> return $ SB.proveUnintCVC4 unints
            SBV_CVC5 unints       -> return $ SB.proveUnintCVC5 unints
            SBV_MathSAT unints    -> return $ SB.proveUnintMathSAT unints
            SBV_Yices unints      -> return $ SB.proveUnintYices unints
            SBV_Z3 unints         -> return $ SB.proveUnintZ3 unints
            W4_ABC_SMTLib         -> return $ SB.w4_abc_smtlib2
            W4_ABC_Verilog        -> return $ SB.w4_abc_verilog
            W4_Bitwuzla unints    -> return $ SB.w4_unint_bitwuzla unints
            W4_Boolector unints   -> return $ SB.w4_unint_boolector unints
            W4_CVC4 unints        -> return $ SB.w4_unint_cvc4 unints
            W4_CVC5 unints        -> return $ SB.w4_unint_cvc5 unints
            W4_Yices unints       -> return $ SB.w4_unint_yices unints
            W4_Z3 unints          -> return $ SB.w4_unint_z3 unints
        go [Trivial]                  = return $ SB.trivial
        go [Admit]                    = return $ SB.assumeUnsat -- TODO: admit
        go [Quickcheck n]             = tl $ do
          sc <- SV.getSharedContext
          return $ SB.quickcheckGoal sc n
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
        go _ = throw $ ProveException "malformed proof script"
