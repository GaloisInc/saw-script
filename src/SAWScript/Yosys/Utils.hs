{-# Language CPP #-}
{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}

module SAWScript.Yosys.Utils where

import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (Exception, throw)
import Control.Monad.Catch (MonadThrow)

import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Graph as Graph

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedTerm as SC

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

reportBugText :: Text
reportBugText = "You should report this issue at: https://github.com/GaloisInc/saw-script/issues"

consultYosysManual :: Text
consultYosysManual = "More information is available in the Yosys manual, at: https://yosyshq.net/yosys/documentation.html"

data YosysBitvecConsumer
  = YosysBitvecConsumerOutputPort Text
  | YosysBitvecConsumerCell Text Text

data YosysError
  = YosysError Text
  | YosysErrorNoSuchOutputBitvec Text YosysBitvecConsumer
  | YosysErrorNoSuchCellType Text Text
  | YosysErrorUnsupportedPmux
  | YosysErrorUnsupportedFF Text
instance Exception YosysError
instance Show YosysError where
  show (YosysError msg) = Text.unpack $ "Error: " <> msg <> "\n" <> reportBugText
  show (YosysErrorNoSuchOutputBitvec bvec (YosysBitvecConsumerOutputPort onm)) = Text.unpack $ mconcat
    [ "Error: Could not find the output bitvector ", bvec
    , ", which is connected to a module output port \"", onm
    , "\".\n"
    , "This may represent a bug in SAW.\n"
    , reportBugText
    ]
  show (YosysErrorNoSuchOutputBitvec bvec (YosysBitvecConsumerCell cnm inm)) = Text.unpack $ mconcat
    [ "Error: Could not find the output bitvector ", bvec
    , ", which is connected to the input \"", inm
    , "\" of the cell with name \"", cnm
    , "\".\n"
    , "It is possible that this represents an undetected cycle in the netgraph.\n"
    , reportBugText
    ]
  show (YosysErrorNoSuchCellType mnm cnm)
    | Just ('$', _) <- Text.uncons mnm
    = Text.unpack $ mconcat
      [ "Error: The cell type \"", mnm
      , "\", which is the type of the cell with name \"", cnm
      , "\", is not a supported primitive cell type.\n"
      , reportBugText
      ]
    | otherwise = Text.unpack $ mconcat
      [ "Error: The cell type \"", mnm
      , "\", which is the type of the cell with name \"", cnm
      , "\", refers to a submodule of the circuit.\n"
      , "Using such submodules during translation of sequential circuits is not currently supported by SAW.\n"
      , "It may be helpful to use the \"flatten\" tactic within Yosys.\n"
      , consultYosysManual
      ]
  show YosysErrorUnsupportedPmux = Text.unpack $ mconcat
    [ "Error: The circuit contains cells with type \"$pmux\".\n"
    , "These cells are not currently supported by SAW.\n"
    , "It may be helpful to replace $pmux cells using the \"pmuxtree\" tactic within Yosys.\n"
    , consultYosysManual
    ]
  show (YosysErrorUnsupportedFF mnm) = Text.unpack $ mconcat
    [ "Error: The circuit contains cells with type \"", mnm, "\".\n"
    , "These cells are not currently supported by SAW.\n"
    , "It may be helpful to replace certain stateful cells using the \"memory\", \"dffunmap\", and \"async2sync\" tactics within Yosys.\n"
    , consultYosysManual
    ]

mapForWithKeyM :: Monad m => Map k a -> (k -> a -> m b) -> m (Map k b)
mapForWithKeyM m f = sequence $ Map.mapWithKey f m

reverseTopSort :: Graph.Graph -> [Graph.Vertex]
reverseTopSort =
#if MIN_VERSION_containers(6,4,1)
  Graph.reverseTopSort
#else
  reverse . Graph.topSort
#endif

cryptolRecordType ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term ->
  m SC.Term
cryptolRecordType sc fields =
  liftIO $ SC.scTupleType sc (fmap snd . C.canonicalFields . C.recordFromFields $ Map.assocs fields)

cryptolRecord ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term ->
  m SC.Term
cryptolRecord sc fields =
  liftIO $ SC.scTuple sc (fmap snd . C.canonicalFields . C.recordFromFields $ Map.assocs fields)

cryptolRecordSelect ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text a ->
  SC.Term ->
  Text ->
  m SC.Term
cryptolRecordSelect sc fields r nm =
  case List.elemIndex nm ord of
    Just i -> liftIO $ SC.scTupleSelector sc r (i + 1) (length ord)
    Nothing -> throw . YosysError $ mconcat
      [ "Could not build record selector term for field name \""
      , nm
      , "\" on record term: "
      , Text.pack $ SC.showTerm r
      , "\nFields are: "
      , Text.pack . show $ Map.keys fields
      ]
  where ord = fmap fst . C.canonicalFields . C.recordFromFields $ Map.assocs fields

cryptolRecordSelectTyped ::
  MonadIO m =>
  SC.SharedContext ->
  SC.TypedTerm ->
  Text ->
  m SC.TypedTerm
cryptolRecordSelectTyped sc r nm = do
  fields <- Map.mapKeys C.identText . Map.fromList . C.canonicalFields <$> case SC.ttType r of
    SC.TypedTermSchema (C.Forall [] [] (C.TRec fs)) -> pure fs
    _ -> throw . YosysError $ mconcat
      [ "Type\n"
      , Text.pack . show $ SC.ttType r
      , "\nis not a record type"
      ]
  cty <- case Map.lookup nm fields of
    Just cty -> pure cty
    _ -> throw . YosysError $ mconcat
      [ "Record type\n"
      , Text.pack . show $ SC.ttType r
      , "\ndoes not have field "
      , nm
      ]
  t <- cryptolRecordSelect sc fields (SC.ttTerm r) nm
  pure $ SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) t

eqBvRecords ::
  (MonadIO m, MonadThrow m) =>
  SC.SharedContext ->
  C.Type ->
  SC.Term ->
  SC.Term ->
  m SC.Term
eqBvRecords sc cty a b = do
  fields <- Map.mapKeys C.identText . Map.fromList . C.canonicalFields <$> case cty of
    C.TRec fs -> pure fs
    _ -> throw . YosysError $ mconcat
      [ "Type\n"
      , Text.pack $ show cty
      , "\nis not a record type"
      ]
  eqs <- forM (Map.assocs fields) $ \(nm, fcty) -> do
    w <- case fcty of
      C.TCon (C.TC C.TCSeq) [C.TCon (C.TC (C.TCNum wint)) [], C.TCon (C.TC C.TCBit) []] ->
        liftIO . SC.scNat sc $ fromIntegral wint
      _ -> throw . YosysError $ mconcat
        [ "Type\n"
        , Text.pack $ show fcty
        , "\nis not a bitvector type"
        ]
    fa <- cryptolRecordSelect sc fields a nm
    fb <- cryptolRecordSelect sc fields b nm
    liftIO $ SC.scBvEq sc w fa fb
  case eqs of
    [] -> throw . YosysError $ mconcat
      [ "Record type\n"
      , Text.pack $ show cty
      , "\nhas no fields"
      ]
    (e:es) -> foldM (\x y -> liftIO $ SC.scAnd sc x y) e es
