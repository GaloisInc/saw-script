{- |
Module      : SAWCentral.Yosys.Utils
Description : Miscellaneous utilities used when working with HDL
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language CPP #-}
{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}

module SAWCentral.Yosys.Utils where

import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (Exception, throw)
import Control.Monad.Catch (MonadThrow)

import Data.Bifunctor (bimap)
import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Graph as Graph

import Text.Encoding.Z (zEncodeString)

import qualified Verifier.SAW.SharedTerm as SC
import qualified CryptolSAWCore.TypedTerm as SC
import qualified Verifier.SAW.SCTypeCheck as SC.TC

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
  | YosysErrorTypeError Text Text
  | YosysErrorNoSuchOutputBitvec Text YosysBitvecConsumer
  | YosysErrorNoSuchSubmodule Text Text
  | YosysErrorUnsupportedFF Text
  | YosysErrorInvalidOverrideTarget
  | YosysErrorOverrideNameNotFound Text
  | YosysErrorInvalidStateFieldWidth Text
  | YosysErrorTransitionSystemMissingField Text
  | YosysErrorTransitionSystemBadType
instance Exception YosysError
instance Show YosysError where
  show (YosysError msg) = Text.unpack $ "Error: " <> msg <> "\n" <> reportBugText
  show (YosysErrorTypeError msg err) = Text.unpack $ mconcat
    [ "Error: An internal term failed to type-check.\n"
    , "This occured while ", msg, ".\n"
    , "The type error was:\n", err
    , "This may represent a bug in SAW.\n"
    , reportBugText
    ]
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
  show (YosysErrorNoSuchSubmodule submoduleName cellName) =
    Text.unpack $ mconcat
      [ "Error: Encountered a cell \""
      , cellName
      , "\" with type \""
      , submoduleName
      , "\", but could not find a submodule named \""
      , submoduleName
      , "\"."
      ]
  show (YosysErrorUnsupportedFF mnm) = Text.unpack $ mconcat
    [ "Error: The circuit contains cells with type \"", mnm, "\".\n"
    , "These cells are not currently supported by SAW.\n"
    , "It may be helpful to replace certain stateful cells using the \"memory\", \"dffunmap\", and \"async2sync\" tactics within Yosys.\n"
    , consultYosysManual
    ]
  show YosysErrorInvalidOverrideTarget = Text.unpack $ mconcat
    [ "Error: The first argument to \"yosys_verify\" could not be identified as a Yosys module.\n"
    , "This argument should typically take the form {{ m.module_name }}, where \"m\" is a record term returned by \"yosys_import\""
    ]
  show (YosysErrorOverrideNameNotFound nm) = Text.unpack $ mconcat
    [ "Error: The name \"", nm, "\" could not be found while applying overrides.\n"
    , "This may represent a bug in SAW.\n"
    , reportBugText
    ]
  show (YosysErrorInvalidStateFieldWidth nm) = Text.unpack $ mconcat
    [ "Error: The state field \"", nm, "\" has an invalid width.\n"
    , "This may represent a bug in SAW.\n"
    , reportBugText
    ]
  show (YosysErrorTransitionSystemMissingField nm) = Text.unpack $ mconcat
    [ "Error: While translating a sequential circuit to a Sally transition system, could not find the field \"", nm, "\".\n"
    , "This may represent a bug in SAW.\n"
    , reportBugText
    ]
  show YosysErrorTransitionSystemBadType = Text.unpack $ mconcat
    [ "Error: While translating a sequential circuit to a Sally transition system, an intermediate What4 predicate was not a boolean.\n"
    , "This may represent a bug in SAW.\n"
    , reportBugText
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

-- | Check that a SAWCore term is well-typed, throwing an exception otherwise.
validateTerm :: MonadIO m => SC.SharedContext -> Text -> SC.Term -> m SC.Term
validateTerm sc msg t = liftIO (SC.TC.scTypeCheck sc Nothing t) >>= \case
  Right _ -> pure t
  Left err ->
    throw
    . YosysErrorTypeError msg
    . Text.pack
    . unlines
    $ SC.TC.prettyTCError err

-- | Check that a SAWCore term is well-typed and has a specific type
validateTermAtType :: MonadIO m => SC.SharedContext -> Text ->
                      SC.Term -> SC.Term -> m ()
validateTermAtType sc msg trm tp =
  liftIO (SC.TC.runTCM (SC.TC.typeInferComplete trm >>= \tp_trm ->
                         SC.TC.checkSubtype tp_trm tp) sc Nothing []) >>= \case
  Right _ -> return ()
  Left err ->
    throw
    . YosysErrorTypeError msg
    . Text.pack
    . unlines
    $ SC.TC.prettyTCError err

-- | Produce a SAWCore tuple type corresponding to a Cryptol record type with the given fields.
cryptolRecordType ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term ->
  m SC.Term
cryptolRecordType sc fields =
  liftIO $ SC.scTupleType sc (fmap snd . C.canonicalFields . C.recordFromFields $ Map.assocs fields)

-- | Produce a SAWCore tuple corresponding to a Cryptol record with the given fields.
cryptolRecord ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term ->
  m SC.Term
cryptolRecord sc fields =
  liftIO $ SC.scTuple sc (fmap snd . C.canonicalFields . C.recordFromFields $ Map.assocs fields)

-- | Produce a SAWCore tuple index corresponding to a lookup in a Cryptol record with the given fields.
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

-- | Produce a SAWCore tuple index corresponding to a lookup in a Cryptol record.
-- The record fields are inferred from the Cryptol type attached to the `TypedTerm`.
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

-- | Construct a SAWCore expression asserting equality between each field of two records.
-- Both records should be tuples corresponding to the specified Cryptol record type.
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

-- | Encode the given string such that is a valid Cryptol identifier. 
-- Since Yosys cell names often look like "\42", this makes it much easier to manipulate state records,
-- which are keyed by cell name.
cellIdentifier :: Text -> Text
cellIdentifier = Text.pack . zEncodeString . Text.unpack

-- | Build a SAWCore type corresponding to the Cryptol record type with the given field types
fieldsToType ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text (SC.Term, C.Type) ->
  m SC.Term
fieldsToType sc = cryptolRecordType sc . fmap fst

-- | Build a Cryptol record type with the given field types
fieldsToCryptolType ::
  MonadIO m =>
  Map Text (SC.Term, C.Type) ->
  m C.Type
fieldsToCryptolType fields = pure . C.tRec . C.recordFromFields $ bimap C.mkIdent snd <$> Map.assocs fields

-- | Given a bit pattern ([b]) and a term, construct a map associating that output pattern with
-- the term, and each bit of that pattern with the corresponding bit of the term.
deriveTermsByIndices :: (MonadIO m, Ord b) => SC.SharedContext -> [b] -> SC.Term -> m (Map [b] SC.Term)
deriveTermsByIndices sc rep t = do
  boolty <- liftIO $ SC.scBoolType sc
  telems <- forM [0..length rep - 1] $ \index -> do
    tlen <- liftIO . SC.scNat sc . fromIntegral $ length rep
    idx <- liftIO . SC.scNat sc $ fromIntegral index
    bit <- liftIO $ SC.scAt sc tlen boolty t idx
    liftIO $ SC.scSingle sc boolty bit
  pure . Map.fromList $ mconcat
    [ [(rep, t)]
    , zip ((:[]) <$> rep) telems
    ]
