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
import Control.Exception (Exception, throwIO)

import Data.Bifunctor (bimap)
import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Graph as Graph

import Numeric.Natural (Natural)

import Text.Encoding.Z (zEncodeString)

import qualified SAWCore.SharedTerm as SC
import qualified CryptolSAWCore.TypedTerm as SC
import qualified SAWCore.SCTypeCheck as SC.TC
import qualified SAWCore.Term.Pretty as SC (showTerm)

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
validateTerm :: SC.SharedContext -> Text -> SC.Term -> IO SC.Term
validateTerm sc msg t =
  do result <- SC.TC.scTypeCheck sc t
     case result of
       Right _ -> pure t
       Left err ->
         throwIO $
         YosysErrorTypeError msg $
         Text.pack $ unlines $ SC.TC.prettyTCError err

-- | Check that a SAWCore term is well-typed and has a specific type
validateTermAtType :: SC.SharedContext -> Text -> SC.Term -> SC.Term -> IO ()
validateTermAtType sc msg trm tp =
  do let check =
           do tp_trm <- SC.TC.typeInferComplete trm
              SC.TC.checkSubtype tp_trm tp
     result <- SC.TC.runTCM check sc
     case result of
       Right _ -> pure ()
       Left err ->
         throwIO $
         YosysErrorTypeError msg $
         Text.pack $ unlines $ SC.TC.prettyTCError err

-- | Produce a SAWCore tuple type corresponding to a Cryptol record type with the given fields.
cryptolRecordType ::
  SC.SharedContext ->
  Map Text SC.Term ->
  IO SC.Term
cryptolRecordType sc fields =
  SC.scTupleType sc (fmap snd . C.canonicalFields . C.recordFromFields $ Map.assocs fields)

-- | Produce a SAWCore tuple corresponding to a Cryptol record with the given fields.
cryptolRecord ::
  SC.SharedContext ->
  Map Text SC.Term ->
  IO SC.Term
cryptolRecord sc fields =
  SC.scTuple sc (fmap snd . C.canonicalFields . C.recordFromFields $ Map.assocs fields)

-- | Produce a SAWCore tuple index corresponding to a lookup in a Cryptol record with the given fields.
cryptolRecordSelect ::
  SC.SharedContext ->
  Map Text a ->
  SC.Term ->
  Text ->
  IO SC.Term
cryptolRecordSelect sc fields r nm =
  case List.elemIndex nm ord of
    Just i -> SC.scTupleSelector sc r (i + 1) (length ord)
    Nothing -> throwIO $ YosysError $ mconcat
      [ "Could not build record selector term for field name \""
      , nm
      , "\" on record term: "
      , Text.pack $ SC.showTerm r
      , "\nFields are: "
      , Text.pack . show $ Map.keys fields
      ]
  where ord = fmap fst . C.canonicalFields . C.recordFromFields $ Map.assocs fields

-- | Produce a SAWCore tuple index corresponding to a lookup in a
-- Cryptol record. The record fields are inferred from the Cryptol
-- type attached to the `TypedTerm`.
cryptolRecordSelectTyped ::
  SC.SharedContext ->
  SC.TypedTerm ->
  Text ->
  IO SC.TypedTerm
cryptolRecordSelectTyped sc r nm = do
  fields <- Map.mapKeys C.identText . Map.fromList . C.canonicalFields <$> case SC.ttType r of
    SC.TypedTermSchema (C.Forall [] [] (C.TRec fs)) -> pure fs
    _ -> throwIO $ YosysError $ mconcat
      [ "Type\n"
      , Text.pack . show $ SC.ttType r
      , "\nis not a record type"
      ]
  cty <- case Map.lookup nm fields of
    Just cty -> pure cty
    _ -> throwIO $ YosysError $ mconcat
      [ "Record type\n"
      , Text.pack . show $ SC.ttType r
      , "\ndoes not have field "
      , nm
      ]
  t <- cryptolRecordSelect sc fields (SC.ttTerm r) nm
  pure $ SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) t

-- | Construct a SAWCore expression asserting equality between each
-- field of two records. Both records should be tuples corresponding
-- to the specified Cryptol record type.
eqBvRecords ::
  SC.SharedContext ->
  C.Type ->
  SC.Term ->
  SC.Term ->
  IO SC.Term
eqBvRecords sc cty a b = do
  fields <- Map.mapKeys C.identText . Map.fromList . C.canonicalFields <$> case cty of
    C.TRec fs -> pure fs
    _ -> throwIO $ YosysError $ mconcat
      [ "Type\n"
      , Text.pack $ show cty
      , "\nis not a record type"
      ]
  eqs <- forM (Map.assocs fields) $ \(nm, fcty) -> do
    w <- case fcty of
      C.TCon (C.TC C.TCSeq) [C.TCon (C.TC (C.TCNum wint)) [], C.TCon (C.TC C.TCBit) []] ->
        SC.scNat sc $ fromIntegral wint
      _ -> throwIO $  YosysError $ mconcat
        [ "Type\n"
        , Text.pack $ show fcty
        , "\nis not a bitvector type"
        ]
    fa <- cryptolRecordSelect sc fields a nm
    fb <- cryptolRecordSelect sc fields b nm
    SC.scBvEq sc w fa fb
  case eqs of
    [] -> throwIO $ YosysError $ mconcat
      [ "Record type\n"
      , Text.pack $ show cty
      , "\nhas no fields"
      ]
    (e:es) -> foldM (\x y -> SC.scAnd sc x y) e es

-- | Encode the given string such that is a valid Cryptol identifier.
-- Since Yosys cell names often look like "\42", this makes it much
-- easier to manipulate state records, which are keyed by cell name.
cellIdentifier :: Text -> Text
cellIdentifier = Text.pack . zEncodeString . Text.unpack

-- | Build a SAWCore type corresponding to the Cryptol record type
-- with the given field types.
fieldsToType ::
  SC.SharedContext ->
  Map Text (SC.Term, C.Type) ->
  IO SC.Term
fieldsToType sc = cryptolRecordType sc . fmap fst

-- | Build a Cryptol record type with the given field types
fieldsToCryptolType ::
  Map Text (SC.Term, C.Type) -> IO C.Type
fieldsToCryptolType fields = pure . C.tRec . C.recordFromFields $ bimap C.mkIdent snd <$> Map.assocs fields

-- | Given a bit pattern ([b]) and a term, construct a map associating
-- that output pattern with the term, and each bit of that pattern
-- with the corresponding bit of the term.
deriveTermsByIndices :: (Ord b) => SC.SharedContext -> [b] -> SC.Term -> IO (Map [b] Preterm)
deriveTermsByIndices _sc rep t = do
  let len = length rep
  let bit i = PretermSlice (fromIntegral (len - 1 - i)) 1 (fromIntegral i) t
  let telems = map bit [0..len-1]
  pure . Map.fromList $ mconcat
    [ [(rep, PretermSlice 0 (fromIntegral len) 0 t)]
    , zip ((:[]) <$> rep) telems
    ]

--------------------------------------------------------------------------------
-- ** Pre-terms

data Preterm
  = PretermSlice Natural Natural Natural SC.Term
    -- ^ @PretermSlice i j k t@ selects bits @k..k+j-1@ from @t@.
  | PretermBvNat Natural Natural
    -- ^ @PretermBvNat n x@ is @x@ as an @n@-bit binary number.

widthPreterm :: Preterm -> Natural
widthPreterm p =
  case p of
    PretermSlice _ j _ _ -> j
    PretermBvNat n _ -> n

-- | Rewrite the concatenation of two 'Preterm' expressions into a
-- single 'Preterm', if possible.
fusePreterm :: Preterm -> Preterm -> Maybe Preterm
fusePreterm (PretermSlice a b c t) (PretermSlice i j k t')
  | t == t' && a + b == i && c == j + k =
    Just (PretermSlice a (b + j) k t)
fusePreterm (PretermBvNat m x) (PretermBvNat n y) =
  Just (PretermBvNat (m + n) (x * 2^n + y))
fusePreterm _ _ = Nothing

-- | Concatenate a 'Preterm' expression onto a list of 'Preterm's,
-- fusing expressions if possible.
consPreterm :: Preterm -> [Preterm] -> [Preterm]
consPreterm x [] = [x]
consPreterm x (y : ys) =
  case fusePreterm x y of
    Nothing -> x : y : ys
    Just xy -> xy : ys

-- | Rewrite a sequence of 'Preterm' expressions, combining adjacent
-- expressions wherever possible.
fusePreterms :: [Preterm] -> [Preterm]
fusePreterms = foldr consPreterm []

-- | Build a 'SC.Term' from a 'Preterm'.
scPreterm :: SC.SharedContext -> Preterm -> IO SC.Term
scPreterm sc p =
  case p of
    PretermSlice 0 _ 0 t ->
      pure t
    PretermSlice 0 j k t ->
      do boolty <- SC.scBoolType sc
         j' <- SC.scNat sc j
         k' <- SC.scNat sc k
         SC.scGlobalApply sc "Prelude.take" [boolty, j', k', t]
    PretermSlice i j 0 t ->
      do boolty <- SC.scBoolType sc
         i' <- SC.scNat sc i
         j' <- SC.scNat sc j
         SC.scGlobalApply sc "Prelude.drop" [boolty, i', j', t]
    PretermSlice i 1 k t ->
      do boolty <- SC.scBoolType sc
         n' <- SC.scNat sc (i + 1 + k)
         i' <- SC.scNat sc i
         SC.scSingle sc boolty =<< SC.scAt sc n' boolty t i'
    PretermSlice i j k t ->
      do boolty <- SC.scBoolType sc
         i' <- SC.scNat sc i
         j' <- SC.scNat sc j
         k' <- SC.scNat sc k
         SC.scSlice sc boolty i' j' k' t
    PretermBvNat i x ->
      do i' <- SC.scNat sc i
         x' <- SC.scNat sc x
         SC.scBvNat sc i' x'

-- | Build a 'SC.Term' from a concatenated sequence of 'Preterm's.
scPreterms :: SC.SharedContext -> [Preterm] -> IO SC.Term
scPreterms sc preterms = snd <$> go preterms
  where
    append :: (Natural, SC.Term) -> (Natural, SC.Term) -> IO (Natural, SC.Term)
    append (i, x) (j, y)
      | i == 0 = pure (j, y)
      | j == 0 = pure (i, x)
      | otherwise =
        do i' <- SC.scNat sc i
           j' <- SC.scNat sc j
           boolty <- SC.scBoolType sc
           t <- SC.scAppend sc i' j' boolty x y
           pure (i + j, t)

    go :: [Preterm] -> IO (Natural, SC.Term)
    go [] =
      do z <- SC.scNat sc 0
         t <- SC.scBvNat sc z z
         pure (0, t)
    go (p : ps) =
      do let i = widthPreterm p
         p' <- scPreterm sc p
         let (ps1, ps2) = span ((==i) . widthPreterm) ps
         if length ps1 > 1 then
           -- Use `join` to concatenate same-length preterms
           do i' <- SC.scNat sc i
              boolty <- SC.scBoolType sc
              ety <- SC.scVecType sc i' boolty
              ps1' <- traverse (scPreterm sc) ps1
              v <- SC.scVector sc ety (p' : ps1')
              let len = List.genericLength ps1 + 1 :: Natural
              len' <- SC.scNat sc len
              x <- SC.scJoin sc len' i' boolty v
              (j, y) <- go ps2
              append (len * i, x) (j, y)
           else
           do x <- scPreterm sc p
              (j, y) <- go ps
              append (i, x) (j, y)
