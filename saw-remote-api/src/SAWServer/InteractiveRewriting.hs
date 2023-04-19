{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module SAWServer.InteractiveRewriting where

import Control.Lens (over)
import Control.Exception (Exception)

import Data.Aeson

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Map as Map

import qualified Argo
import qualified Argo.Doc as Doc

import SAWServer
import SAWServer.OK (OK, ok)
import SAWServer.TopLevel (tl)
import SAWServer.Exceptions (verificationException)

import qualified Verifier.SAW.TypedTerm as SC
import qualified Verifier.SAW.ExternalFormat as SC

import qualified SAWScript.AST as AST
import SAWScript.Interpreter (include_value)
import SAWScript.Builtins (readCore, rewritePrim, addsimps, provePropPrim, prop_eval, unfold_term)
import SAWScript.Value (TopLevelRW(..), Value(..))
import SAWScript.TopLevel (getTopLevelRW) 
import Control.Monad (void)

newtype InteractiveRewritingException = InteractiveRewritingException Text
  deriving (Show, Eq, Ord)
instance Exception InteractiveRewritingException

includeSAWScriptDescr :: Doc.Block
includeSAWScriptDescr =
  Doc.Paragraph [Doc.Text "Include a SAWScript file."]

includeSAWScript :: IncludeSAWScriptParams -> Argo.Command SAWState OK
includeSAWScript (IncludeSAWScriptParams path) = do
  tl . include_value $ Text.unpack path
  ok

newtype IncludeSAWScriptParams = IncludeSAWScriptParams Text

instance FromJSON IncludeSAWScriptParams where
  parseJSON = withObject "parameters for including SAWScript source" $ \o ->
    IncludeSAWScriptParams <$> o .: "path"

instance Doc.DescribedMethod IncludeSAWScriptParams OK where
  parameterFieldDescription =
    [ ( "path"
      , Doc.Paragraph [Doc.Text "The path to the SAWScript pile to import."]
      )
    ]
  resultFieldDescription = []

readExtcoreDescr :: Doc.Block
readExtcoreDescr =
  Doc.Paragraph [Doc.Text "Read a SAWCore external term."]

readExtcore :: ReadExtcoreParams -> Argo.Command SAWState OK
readExtcore (ReadExtcoreParams nm path) = do
  val <- tl . readCore $ Text.unpack path
  setServerVal nm val
  ok

data ReadExtcoreParams = ReadExtcoreParams ServerName Text

instance FromJSON ReadExtcoreParams where
  parseJSON = withObject "parameters for reading a SAWCore external term" $ \o ->
    ReadExtcoreParams
    <$> o .: "nm"
    <*> o .: "path"

instance Doc.DescribedMethod ReadExtcoreParams OK where
  parameterFieldDescription =
    [ ( "nm"
      , Doc.Paragraph [Doc.Text "The name to use for the term."]
      )
    , ( "path"
      , Doc.Paragraph [Doc.Text "The path to the SAWCore external file to read."]
      )
    ]
  resultFieldDescription = []

copyTermDescr :: Doc.Block
copyTermDescr =
  Doc.Paragraph [Doc.Text "Copy a term."]

copyTerm :: CopyTermParams -> Argo.Command SAWState OK
copyTerm (CopyTermParams from to) = do
  val <- getServerVal from
  Argo.modifyState $
    over sawEnv $ \(SAWEnv env) -> SAWEnv (Map.insert to val env)
  ok

data CopyTermParams = CopyTermParams ServerName ServerName

instance FromJSON CopyTermParams where
  parseJSON = withObject "parameters for copying a term" $ \o ->
    CopyTermParams
    <$> o .: "from"
    <*> o .: "to"

instance Doc.DescribedMethod CopyTermParams OK where
  parameterFieldDescription =
    [ ( "from"
      , Doc.Paragraph [Doc.Text "The name of the source term."]
      )
    , ( "to"
      , Doc.Paragraph [Doc.Text "The destination name."]
      )
    ]
  resultFieldDescription = []

simplifyTermDescr :: Doc.Block
simplifyTermDescr =
  Doc.Paragraph [Doc.Text "Simplify a term using named SAWScript rewrite rules."]

simplifyTerm :: SimplifyTermParams -> Argo.Command SAWState OK
simplifyTerm (SimplifyTermParams nm rewriteNms simpsetNm) = do
  rw <- tl getTopLevelRW
  simpset <- case Map.lookup simpsetNm $ Map.mapKeys (Text.pack . AST.getVal) $ rwValues rw of
    Just (SAWScript.Value.VSimpset ss) -> pure ss
    Just (SAWScript.Value.VLambda fun) -> tl (fun $ VTuple []) >>= \case
      SAWScript.Value.VSimpset ss -> pure ss
      _ -> Argo.raise . verificationException . InteractiveRewritingException $ mconcat
        [ "Function does not yield simpset: "
        , simpsetNm
        ]
    _ -> Argo.raise . verificationException . InteractiveRewritingException $ mconcat
      [ "Could not find simpset: "
      , simpsetNm
      ]
  let lookupRewrite rnm =
        case Map.lookup rnm $ Map.mapKeys (Text.pack . AST.getVal) $ rwValues rw of
          Just (VTheorem thm) -> pure thm
          _ -> Argo.raise . verificationException . InteractiveRewritingException $ mconcat
            [ "Could not find theorem: "
            , rnm
            ]
  t <- getTerm nm
  rewrites <- mapM lookupRewrite rewriteNms
  ss <- tl $ addsimps rewrites simpset
  t' <- tl $ rewritePrim ss t
  setServerVal nm t'
  ok

data SimplifyTermParams = SimplifyTermParams ServerName [Text] Text

instance FromJSON SimplifyTermParams where
  parseJSON = withObject "parameters for simplifying SAWCore term" $ \o ->
    SimplifyTermParams
    <$> o .: "nm"
    <*> o .: "rewrites"
    <*> o .: "simpset"

instance Doc.DescribedMethod SimplifyTermParams OK where
  parameterFieldDescription =
    [ ( "nm"
      , Doc.Paragraph [Doc.Text "The name of the term."]
      )
    , ( "rewrites"
      , Doc.Paragraph [Doc.Text "A list of rewrite rules (as SAWScript toplevel names)."]
      )
    , ( "simpset"
      , Doc.Paragraph [Doc.Text "The base simpset to use"]
      )
    ]
  resultFieldDescription = []

runSolverDescr :: Doc.Block
runSolverDescr =
  Doc.Paragraph [Doc.Text "Run the given solver on a term."]

runSolver :: RunSolverParams -> Argo.Command SAWState OK
runSolver (RunSolverParams nm solverNm unintNms) = do
  rw <- tl getTopLevelRW
  t <- getTerm nm
  solver <- case Map.lookup solverNm $ Map.mapKeys (Text.pack . AST.getVal) $ rwValues rw of
    Just (VProofScript ps) -> pure ps
    Just (VLambda fun) -> tl (fun . VArray $ VString <$> unintNms) >>= \case
      VProofScript ps -> pure ps
      _ -> Argo.raise . verificationException . InteractiveRewritingException $ mconcat
        [ "Solver function does not yield proof script: "
        , solverNm
        ]
    _ -> Argo.raise . verificationException . InteractiveRewritingException $ mconcat
      [ "Could not find solver: "
      , solverNm
      ]
  _ <- tl $ provePropPrim (void solver) t
  ok

data RunSolverParams = RunSolverParams ServerName Text [Text]

instance FromJSON RunSolverParams where
  parseJSON = withObject "parameters for running solvers on terms" $ \o ->
    RunSolverParams
    <$> o .: "nm"
    <*> o .: "solver"
    <*> o .: "unints"

instance Doc.DescribedMethod RunSolverParams OK where
  parameterFieldDescription =
    [ ( "nm"
      , Doc.Paragraph [Doc.Text "The name of the term."]
      )
    , ( "solver"
      , Doc.Paragraph [Doc.Text "The name of the solver."]
      )
    , ( "unints"
      , Doc.Paragraph [Doc.Text "A list of uninterpreted names."]
      )
    ]
  resultFieldDescription = []

inspectTermDescr :: Doc.Block
inspectTermDescr =
  Doc.Paragraph [Doc.Text "Obtain the external SAWCore representation of a term."]

inspectTerm :: InspectTermParams -> Argo.Command SAWState InspectTermResult
inspectTerm (InspectTermParams nm) = do
  t <- getTerm nm
  pure . InspectTermResult . Text.pack . SC.scWriteExternal $ SC.ttTerm t

newtype InspectTermParams = InspectTermParams ServerName

instance FromJSON InspectTermParams where
  parseJSON = withObject "parameters for inspecting a term" $ \o ->
    InspectTermParams
    <$> o .: "nm"

newtype InspectTermResult = InspectTermResult Text

instance ToJSON InspectTermResult where
  toJSON (InspectTermResult t) = object [ "extcore" .= t ]

instance Doc.DescribedMethod InspectTermParams InspectTermResult where
  parameterFieldDescription =
    [ ( "nm"
      , Doc.Paragraph [Doc.Text "The name of the term."]
      )
    ]
  resultFieldDescription =
    [ ( "extcore"
      , Doc.Paragraph [Doc.Text "The external SAWCore representation of the term."]
      )
    ]

evalTermDescr :: Doc.Block
evalTermDescr =
  Doc.Paragraph [Doc.Text "Simplify a term via What4."]

evalTerm :: EvalTermParams -> Argo.Command SAWState OK
evalTerm (EvalTermParams nm unints) = do
  t <- getTerm nm
  t' <- tl $ prop_eval (Text.unpack <$> unints) t
  setServerVal nm t'
  ok

data EvalTermParams = EvalTermParams ServerName [Text]

instance FromJSON EvalTermParams where
  parseJSON = withObject "parameters for simplifying a term via What4" $ \o ->
    EvalTermParams
    <$> o .: "nm"
    <*> o .: "unints"

instance Doc.DescribedMethod EvalTermParams OK where
  parameterFieldDescription =
    [ ( "nm"
      , Doc.Paragraph [Doc.Text "The name of the term."]
      )
    , ( "unints"
      , Doc.Paragraph [Doc.Text "A list of uninterpreted names."]
      )
    ]
  resultFieldDescription = []

unfoldTermDescr :: Doc.Block
unfoldTermDescr =
  Doc.Paragraph [Doc.Text "Unfold names within a term."]

unfoldTerm :: UnfoldTermParams -> Argo.Command SAWState OK
unfoldTerm (UnfoldTermParams nm names) = do
  t <- getTerm nm
  t' <- tl $ unfold_term (Text.unpack <$> names) t
  setServerVal nm t'
  ok

data UnfoldTermParams = UnfoldTermParams ServerName [Text]

instance FromJSON UnfoldTermParams where
  parseJSON = withObject "parameters for unfolding names within a term" $ \o ->
    UnfoldTermParams
    <$> o .: "nm"
    <*> o .: "names"

instance Doc.DescribedMethod UnfoldTermParams OK where
  parameterFieldDescription =
    [ ( "nm"
      , Doc.Paragraph [Doc.Text "The name of the term."]
      )
    , ( "names"
      , Doc.Paragraph [Doc.Text "A list of names to unfold."]
      )
    ]
  resultFieldDescription = []
