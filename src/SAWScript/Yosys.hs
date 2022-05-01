{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ViewPatterns #-}
{-# Language LambdaCase #-}
{-# Language MultiWayIf #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}

module SAWScript.Yosys
  ( YosysIR
  , yosys_import
  , yosys_verify
  , loadYosysIR
  , yosysIRToTypedTerms
  ) where

import Control.Lens.TH (makeLenses)

import Control.Lens (view, (^.))
import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))

import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph as Graph

import qualified Text.URI as URI

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedTerm as SC

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

import SAWScript.Value
import qualified SAWScript.Builtins as Builtins

import SAWScript.Yosys.Utils
import SAWScript.Yosys.IR
import SAWScript.Yosys.Netgraph
import SAWScript.Yosys.State
import SAWScript.Yosys.Theorem

--------------------------------------------------------------------------------
-- ** Building the module graph from Yosys IR

data Modgraph = Modgraph
  { _modgraphGraph :: Graph.Graph
  , _modgraphNodeFromVertex :: Graph.Vertex -> (Module, Text, [Text])
  -- , _modgraphVertexFromKey :: Text -> Maybe Graph.Vertex
  }
makeLenses ''Modgraph

yosysIRModgraph :: YosysIR -> Modgraph
yosysIRModgraph ir =
  let
    moduleToNode :: (Text, Module) -> (Module, Text, [Text])
    moduleToNode (nm, m) = (m, nm, deps)
      where
        deps = view cellType <$> Map.elems (m ^. moduleCells)
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
  let sorted = Graph.reverseTopSort $ mg ^. modgraphGraph
  foldM
    (\env v -> do
        let (m, nm, _) = mg ^. modgraphNodeFromVertex $ v
        -- liftIO . putStrLn . Text.unpack $ mconcat ["Converting module: ", nm]
        cm <- convertModule sc env m
        let uri = URI.URI
              { URI.uriScheme = URI.mkScheme "yosys"
              , URI.uriAuthority = Left True
              , URI.uriPath = (False,) <$> mapM URI.mkPathPiece (nm NE.:| [])
              , URI.uriQuery = []
              , URI.uriFragment = Nothing
              }
        let ni = SC.ImportedName uri [nm]
        tc <- liftIO $ SC.scConstant' sc ni (cm ^. convertedModuleTerm) (cm ^. convertedModuleType)
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

-- | Given a Yosys IR, construct a map from module names to SAWCore terms alongside SAWCore and Cryptol types
convertYosysIRInline ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  m (Map Text ConvertedModule)
convertYosysIRInline sc ir = do
  res <- forM (Map.assocs $ ir ^. yosysModules) $ \(nm, m) -> do
    -- liftIO $ putStrLn $ "Converting: " <> Text.unpack nm
    cm <- convertModuleInline sc (ir ^. yosysModules) m
    let uri = URI.URI
          { URI.uriScheme = URI.mkScheme "yosys"
          , URI.uriAuthority = Left True
          , URI.uriPath = (False,) <$> mapM URI.mkPathPiece (nm NE.:| [])
          , URI.uriQuery = []
          , URI.uriFragment = Nothing
          }
    let ni = SC.ImportedName uri [nm]
    tc <- liftIO $ SC.scConstant' sc ni (cm ^. convertedModuleTerm) (cm ^. convertedModuleType)
    let cm' = cm { _convertedModuleTerm = tc }
    pure (nm, cm')
  pure $ Map.fromList res

-- | Given a Yosys IR, construct a SAWCore record containing terms for each module
yosysIRToRecordTermInline ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  m SC.TypedTerm
yosysIRToRecordTermInline sc ir = do
  env <- convertYosysIRInline sc ir
  record <- cryptolRecord sc $ view convertedModuleTerm <$> env
  let cty = C.tRec . C.recordFromFields $ (\(nm, cm) -> (C.mkIdent nm, cm ^. convertedModuleCryptolType)) <$> Map.assocs env
  let tt = SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) record
  pure tt

--------------------------------------------------------------------------------
-- ** Functions visible from SAWScript REPL

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

yosys_import :: FilePath -> TopLevel SC.TypedTerm
yosys_import path = do
  sc <- getSharedContext
  ir <- loadYosysIR path
  yosysIRToRecordTermInline sc ir

yosys_verify :: SC.TypedTerm -> [SC.TypedTerm] -> SC.TypedTerm -> [YosysTheorem] -> ProofScript () -> TopLevel YosysTheorem
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
