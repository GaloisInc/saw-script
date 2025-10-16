{- |
Module      : SAWCentral.Yosys
Description : Loading and manipulating HDL programs
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ViewPatterns #-}
{-# Language LambdaCase #-}
{-# Language MultiWayIf #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}

module SAWCentral.Yosys
  ( YosysIR
  , yosys_import
  , yosys_verify
  , yosys_import_sequential
  , yosys_extract_sequential
  , yosys_extract_sequential_with_state
  , yosys_extract_sequential_raw
  , yosys_verify_sequential_sally
  , loadYosysIR
  , yosysIRToTypedTerms
  ) where

import Control.Lens.TH (makeLenses)

import Control.Lens (view, (^.))
import Control.Exception (throw)
import Control.Monad (foldM)
import Control.Monad.IO.Class (MonadIO(..))

import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph as Graph

import qualified Text.URI as URI

import qualified Data.Parameterized.Nonce as Nonce

import qualified SAWCore.SharedTerm as SC
import qualified CryptolSAWCore.TypedTerm as SC

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

import SAWCentral.Value
import qualified SAWCentral.Builtins as Builtins
import qualified SAWCentral.Crucible.Common as Common

import SAWCentral.Yosys.Utils
import SAWCentral.Yosys.IR
import SAWCentral.Yosys.State
import SAWCentral.Yosys.Theorem
import SAWCentral.Yosys.TransitionSystem
import SAWCentral.Yosys.Netgraph

--------------------------------------------------------------------------------
-- ** Building the module graph from Yosys IR

data Modgraph = Modgraph
  { _modgraphGraph :: Graph.Graph
  , _modgraphNodeFromVertex :: Graph.Vertex -> (Module, Text, [Text])
  -- , _modgraphVertexFromKey :: Text -> Maybe Graph.Vertex
  }
makeLenses ''Modgraph

-- | Given a Yosys IR, construct a graph of intermodule dependencies.
yosysIRModgraph :: YosysIR -> Modgraph
yosysIRModgraph ir =
  let
    moduleToNode :: (Text, Module) -> (Module, Text, [Text])
    moduleToNode (nm, m) = (m, nm, deps)
      where
        deps = Text.pack . show . view cellType <$> Map.elems (m ^. moduleCells)
    nodes = moduleToNode <$> Map.assocs (ir ^. yosysModules)
    (_modgraphGraph, _modgraphNodeFromVertex, _modgraphVertexFromKey)
      = Graph.graphFromEdges nodes
  in Modgraph{..}

-- | Given a Yosys IR, construct a map from module names to SAWCore terms alongside SAWCore and Cryptol types
convertYosysIR ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  m (Map Text ConvertedModule)
convertYosysIR sc ir = do
  let mg = yosysIRModgraph ir
  let sorted = reverseTopSort $ mg ^. modgraphGraph
  foldM
    (\env v -> do
        let (m, nm, _) = mg ^. modgraphNodeFromVertex $ v
        cm <- convertModule sc env m
        _ <- validateTerm sc ("translating the combinational circuit \"" <> nm <> "\"") $ cm ^. convertedModuleTerm
        n <- liftIO $ Nonce.freshNonce Nonce.globalNonceGenerator
        let frag = Text.pack . show $ Nonce.indexValue n
        let uri = URI.URI
              { URI.uriScheme = URI.mkScheme "yosys"
              , URI.uriAuthority = Left True
              , URI.uriPath = (False,) <$> mapM URI.mkPathPiece (nm NE.:| [])
              , URI.uriQuery = []
              , URI.uriFragment = URI.mkFragment frag
              }
        let ni = SC.ImportedName uri [nm]
        tc <- liftIO $ SC.scDefineConstant sc ni (cm ^. convertedModuleTerm) (cm ^. convertedModuleType)
        let cm' = cm { _convertedModuleTerm = tc }
        pure $ Map.insert nm cm' env
    )
    Map.empty
    sorted

-- | Given a Yosys IR, construct a map from module names to TypedTerms
yosysIRToTypedTerms ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  m (Map Text SC.TypedTerm)
yosysIRToTypedTerms sc ir = do
  env <- convertYosysIR sc ir
  pure . flip fmap env $ \cm ->
    SC.TypedTerm
    (SC.TypedTermSchema $ C.tMono $ cm ^. convertedModuleCryptolType)
    $ cm ^. convertedModuleTerm

-- | Given a Yosys IR, construct a SAWCore record containing terms for each module
yosysIRToRecordTerm ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  m SC.TypedTerm
yosysIRToRecordTerm sc ir = do
  env <- convertYosysIR sc ir
  record <- cryptolRecord sc $ view convertedModuleTerm <$> env
  let cty = C.tRec . C.recordFromFields $ (\(nm, cm) -> (C.mkIdent nm, cm ^. convertedModuleCryptolType)) <$> Map.assocs env
  let tt = SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) record
  pure tt

-- | Given a Yosys IR, construct a value representing a specific module with all submodules inlined
yosysIRToSequential ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  Text ->
  m YosysSequential
yosysIRToSequential sc ir nm = do
  case Map.lookup nm $ ir ^. yosysModules of
    Nothing -> throw . YosysError $ mconcat
      [ "Could not find module: "
      , nm
      ]
    Just m -> convertModuleInline sc m

--------------------------------------------------------------------------------
-- ** Functions visible from SAWScript REPL

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

-- | Produces a Term given the path to a JSON file produced by the
-- Yosys write_json command. The resulting term is a Cryptol record,
-- where each field corresponds to one HDL module exported by Yosys.
-- Each HDL module is in turn represented by a function from a record
-- of input port values to a record of output port values.
yosys_import :: FilePath -> TopLevel SC.TypedTerm
yosys_import path = do
  sc <- getSharedContext
  ir <- loadYosysIR path
  tt <- yosysIRToRecordTerm sc ir
  _ <- validateTerm sc "translating combinational circuits" $ SC.ttTerm tt
  pure tt

-- | Proves equality between a combinational HDL module and a
-- specification. Note that terms derived from HDL modules are first
-- class, and are not restricted to yosys_verify: they may also be
-- used with SAW's typical Term infrastructure like sat, prove_print,
-- term rewriting, etc. yosys_verify simply provides a convenient and
-- familiar interface, similar to llvm_verify or jvm_verify.
yosys_verify ::
  SC.TypedTerm {- ^ Term corresponding to the HDL module -} ->
  [SC.TypedTerm] {- ^ Preconditions for the equality -} ->
  SC.TypedTerm {- ^ Specification term of the same type as the HDL module -} ->
  [YosysTheorem] {- ^ Overrides to apply -} ->
  ProofScript () ->
  TopLevel YosysTheorem
yosys_verify ymod preconds other specs tactic = do
  sc <- getSharedContext
  newmod <- foldM (flip $ applyOverride sc)
    (SC.ttTerm ymod)
    specs
  mpc <- case preconds of
    [] -> pure Nothing
    (pc:pcs) -> do
      t <- foldM (\a b -> liftIO $ SC.scAnd sc a b) (SC.ttTerm pc) (SC.ttTerm <$> pcs)
      pure . Just $ SC.TypedTerm (SC.ttType pc) t
  thm <- buildTheorem sc ymod newmod mpc other
  prop <- theoremProp sc thm
  _ <- Builtins.provePrintPrim tactic prop
  pure thm

-- | Import a single sequential HDL module. N.B. SAW expects the
-- sequential module to exist entirely within a single Yosys module.
yosys_import_sequential ::
  Text {- ^ Name of the HDL module -} ->
  FilePath {- ^ Path to the Yosys JSON file -} ->
  TopLevel YosysSequential
yosys_import_sequential nm path = do
  sc <- getSharedContext
  ir <- loadYosysIR path
  yosysIRToSequential sc ir nm

-- | Extracts a term from the given sequential module with the state
-- eliminated by iterating the term over the given concrete number of
-- cycles. The resulting term has no state field in the inputs or
-- outputs. Each input and output field is replaced with an array of
-- that field's type (array length being the number of cycles
-- specified).
yosys_extract_sequential ::
  YosysSequential ->
  Integer {- ^ Number of cycles to iterate term -} ->
  TopLevel SC.TypedTerm
yosys_extract_sequential s n = do
  sc <- getSharedContext
  tt <- composeYosysSequential sc s n
  _ <- validateTerm sc "composing a sequential term" $ SC.ttTerm tt
  pure tt

-- | Like `yosys_extract_sequential`, but the resulting term has an
-- additional parameter to specify the initial state.
yosys_extract_sequential_with_state ::
  YosysSequential ->
  Integer {- ^ Number of cycles to iterate term -} ->
  TopLevel SC.TypedTerm
yosys_extract_sequential_with_state s n = do
  sc <- getSharedContext
  tt <- composeYosysSequentialWithState sc s n
  _ <- validateTerm sc "composing a sequential term with state" $ SC.ttTerm tt
  pure tt

-- | Extracts a term from the given sequential module. This term has
-- explicit fields for the state of the circuit in the input and
-- output record types.
yosys_extract_sequential_raw :: YosysSequential -> TopLevel SC.TypedTerm
yosys_extract_sequential_raw s = pure $ s ^. yosysSequentialTerm

-- | Export a query over the given sequential module to an input file for the Sally model checker.
yosys_verify_sequential_sally ::
  YosysSequential ->
  FilePath {- ^ Path to write the resulting Sally input -} ->
  SC.TypedTerm {- ^ A boolean function of three parameters: an 8-bit cycle counter, a record of "fixed" inputs, and a record of circuit outputs -} ->
  [Text] {- ^ Names of circuit inputs that are fixed -} ->
  TopLevel ()
yosys_verify_sequential_sally s path q fixed = do
  sc <- getSharedContext
  sym <- liftIO $ Common.newSAWCoreExprBuilder sc False
  queryModelChecker sym sc s path q $ Set.fromList fixed
