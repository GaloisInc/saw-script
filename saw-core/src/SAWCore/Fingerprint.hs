{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : SAWCore.Fingerprint
Description : SATQuery fingerprinting, intended for solver cache key.
Copyright   : Galois, Inc. 2026
License     : BSD3
Stability   : experimental
-}

module SAWCore.Fingerprint
  ( fingerprintSATQuery
  ) where

import Control.Monad.Reader (ReaderT, MonadReader, runReaderT, ask)
import Control.Monad.State.Strict (State, MonadState, state, gets, modify', evalState)
import qualified Crypto.Hash.SHA256 as SHA256
import Data.Binary (encode)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BS
import Data.ByteString.Lazy (ByteString, singleton)
import Data.Foldable (foldl')
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import qualified Data.Vector as V
import Data.Word (Word8)
import GHC.Num.Natural (Natural)


import SAWCore.FiniteValue (FirstOrderType(..))
import SAWCore.Module (ModuleMap, ResolvedName(..), Def(..), DataType(..), Ctor(..), lookupVarIndexInMap)
import SAWCore.Name (Name(..), VarCtx, pattern ImportedName, NameInfo, pattern ModuleIdentifier,
                     emptyVarCtx, consVarCtx, lookupVarCtx, VarName(..), VarIndex,
                     moduleIdentToQualName)
import qualified SAWCore.QualName as QN
import SAWCore.SATQuery (SATQuery, SATAssert(..), satVariables, satUninterp, satAsserts)
import SAWCore.Term.Functor (FlatTermF(..), TermF(..), Sort(..), CompiledRecursor(..))
import SAWCore.Term.Raw (Term, unwrapTermF, termIndex)

type FP = ReaderT FPCfg (State FPSt)

-- | Read-only bits of state.
data FPCfg = FPCfg
  { fpModuleMap :: !ModuleMap
    -- ^ The module map for looking up definitions.
  , fpUninterp  :: !(Set VarIndex)
    -- ^ The set of uninterpreted constants. When these are encountered, only
    --   the name and type are included in the serialization and not a definition, if
    --   it exists. See 'lookupName' and 'fpDef'.
  }

-- | Mutable state tracked while serializing. Sequence numbers are used to
--   preserve structural sharing. The first time we encounter a term or definition,
--   we create a new sequence number and emit it along with a 'tagDef' followed by
--   the definition. Subsequent encounters just emit the sequence number along with
--   'tagRef'.
data FPSt = FPSt
  { fpTermMemo    :: !(IntMap BS.Builder)
    -- ^ TermIndex -> 'tagRef' + sequence number (assigned on first serialization).
  , fpDefMemo     :: !(IntMap BS.Builder)
    -- ^ VarIndex of global Name -> 'tagRef' + sequence number.
  , fpNextRef     :: !Int
    -- ^ Next available sequence number.
  }

-- | Markers used to preserve structural sharing without hashing.
tagRef, tagDef :: Word8
tagRef   = 0xF1  -- Reference to a previously serialized term or definition.
tagDef   = 0xF2  -- Introduces a new sequence number followed by its body.

ref :: Int -> BS.Builder
ref n = byte tagRef <> bytes n

def :: Int -> BS.Builder
def n = byte tagDef <> bytes n

freshRef :: MonadState FPSt m => m Int
freshRef = state $ \s ->
  let n = fpNextRef s in (n, s { fpNextRef = n + 1 })

-- | Memoize a term, associating a `TermIndex` with a new sequence number.
--   Returns that sequence number prepended with 'tagDef'.
rememberTerm :: MonadState FPSt m => Term -> m BS.Builder
rememberTerm t = do
  n <- freshRef
  modify' $
    \s -> s { fpTermMemo = IntMap.insert (termIndex t) (ref n) $ fpTermMemo s }
  pure $ def n

lookupTerm :: MonadState FPSt m => Term -> m (Maybe BS.Builder)
lookupTerm t = IntMap.lookup (termIndex t) <$> gets fpTermMemo

-- | Memoize a name, associating a `VarIndex` with a new sequence number.
--   Returns that sequence number prepended with 'tagDef'.
rememberDef :: MonadState FPSt m => Name -> m BS.Builder
rememberDef nm = do
  n <- freshRef
  modify' $
    \s -> s { fpDefMemo = IntMap.insert (nameIndex nm) (ref n) $ fpDefMemo s }
  pure $ def n

lookupDef :: MonadState FPSt m => Name -> m (Maybe BS.Builder)
lookupDef nm = IntMap.lookup (nameIndex nm) <$> gets fpDefMemo

-- | Lookup a name in the 'fpUninterp' set (the `Bool` result) and
--   'fpModuleMap'.
lookupName :: MonadReader FPCfg m => Name -> m (Bool, Maybe ResolvedName)
lookupName nm = do
  cfg <- ask
  pure ( Set.member (nameIndex nm) $ fpUninterp cfg
       , lookupVarIndexInMap (nameIndex nm) $ fpModuleMap cfg
       )

byte :: Word8 -> BS.Builder
byte = BS.word8

-- | Basic serialization of small morsels.
class Bytes a where
  bytes :: a -> BS.Builder
instance Bytes Int where
  bytes = BS.int64BE . fromIntegral
instance Bytes Natural where
  bytes = BS.lazyByteString . encode
instance Bytes Text where
  bytes txt = bytes (BS.length bs) <> BS.byteString bs
    where
      bs = encodeUtf8 txt
instance Bytes NameInfo where
  bytes = \case
    ModuleIdentifier i -> byte 0x1 <> bytes (QN.ppQualName $ moduleIdentToQualName i)
    ImportedName qn _  -> byte 0x2 <> bytes (QN.ppQualName qn)
instance Bytes Sort where
  bytes = \case
    PropSort   -> byte 0x1
    TypeSort n -> byte 0x2 <> bytes n
instance Bytes FirstOrderType where
  bytes = \case
    FOTBit       -> byte 0x1
    FOTInt       -> byte 0x2
    FOTRational  -> byte 0x3
    FOTIntMod n  -> byte 0x4 <> bytes n
    FOTVec n t   -> byte 0x5 <> bytes n <> bytes t
    FOTArray k v -> byte 0x6 <> bytes k <> bytes v
    FOTTuple ts  -> byte 0x7 <> bytes (length ts)
                             <> foldMap bytes ts
    FOTRec m     -> byte 0x8 <> bytes (Map.size m)
                             <> foldMap (\(k, v) -> bytes k <> byte 0 <> bytes v)
                                        (Map.toAscList m)
    FOTFloat e p -> byte 0x9 <> bytes e <> bytes p

fpTerms :: VarCtx -> [Term] -> FP BS.Builder
fpTerms ctx ts = do
  bs <- mapM (fpTerm ctx) ts
  pure $ bytes (length ts) <> mconcat bs

fpTerm :: VarCtx -> Term -> FP BS.Builder
fpTerm ctx t = lookupTerm t >>= \case
  Just n  -> pure n
  Nothing -> do
    tag <- rememberTerm t
    body <- fpTermF ctx (unwrapTermF t)
    pure $ tag <> body

fpTermF :: VarCtx -> TermF Term -> FP BS.Builder
fpTermF ctx = \case

  App e1 e2 -> do
    b1 <- fpTerm ctx e1
    b2 <- fpTerm ctx e2
    pure $ byte 0x1 <> b1 <> b2

  Lambda x ty body -> do
    bty   <- fpTerm ctx ty
    bbody <- fpTerm (consVarCtx x ctx) body
    pure $ byte 0x2 <> bty <> bbody

  Pi x ty body -> do
    bty   <- fpTerm ctx ty
    bbody <- fpTerm (consVarCtx x ctx) body
    pure $ byte 0x3 <> bty <> bbody

  Constant nm -> do
    bdef <- fpDef nm
    pure $ byte 0x4 <> bdef

  Variable vn ty
    | Just dbi <- lookupVarCtx vn ctx -> -- Bound var: use index.
      pure $ byte 0x5 <> bytes dbi
    | otherwise -> do                    -- Free var: use name + type.
      bty <- fpTerm ctx ty
      pure $ byte 0x6 <> bytes (vnName vn) <> bty

  FTermF (Sort s _) -> -- ignoring SortFlags
    pure $ byte 0x7 <> bytes s

  FTermF (StringLit txt) ->
    pure $ byte 0x8 <> bytes txt

  FTermF (ArrayValue elemTy elems) -> do
    bty <- fpTerm ctx elemTy
    bs  <- fpTerms ctx $ V.toList elems
    pure $ byte 0x9 <> bty <> bs

  FTermF (Recursor cr) -> do
    dtB <- fpDef $ recursorDataType cr
    pure $ byte 0xa
        <> bytes (recursorSort cr)
        <> dtB

fpDef :: Name -> FP BS.Builder
fpDef nm = do
  lookupDef nm >>= \case
    Just v  -> pure v
    Nothing -> do
      tag  <- rememberDef nm
      body <- lookupName nm >>= \case
        (True, Just (ResolvedDef d)) -> do -- Uninterpreted.
          bty <- fpTerm emptyVarCtx $ defType d
          pure $ byte 0x11 <> ni <> bty
        (_, Just (ResolvedDef d))
          | Just b <- defBody d -> do
            bty   <- fpTerm emptyVarCtx $ defType d
            bbody <- fpTerm emptyVarCtx b
            pure $ byte 0x12 <> ni <> bty <> bbody
        (_, Just (ResolvedDef d)) -> do
          bty <- fpTerm emptyVarCtx $ defType d
          pure $ byte 0x13 <> ni <> bty
        (_, Just (ResolvedDataType dt)) -> do
          bty    <- fpTerm emptyVarCtx $ dtType dt
          bctors <- fpTerms emptyVarCtx $ ctorType <$> dtCtors dt
          pure $ byte 0x14 <> ni <> bty <> bctors
        (_, Just (ResolvedCtor c)) -> do
          bty <- fpTerm emptyVarCtx $ ctorType c
          pure $ byte 0x15 <> ni <> bty
        (_, Nothing) -> pure $ byte 0x16 <> ni
      pure $ tag <> body
  where
    ni :: BS.Builder
    ni = bytes $ nameInfo nm

fpAssert :: VarCtx -> SATAssert -> FP BS.Builder
fpAssert ctx = \case
  BoolAssert tm -> do
    b <- fpTerm ctx tm
    pure $ byte 0x21 <> b
  UniversalAssert vars hyps concl -> do
    let varTys = foldMap (bytes . snd) vars
        ctx'   = foldl' (\c (v, _) -> consVarCtx v c) ctx vars
    bhyps  <- fpTerms ctx' hyps
    bconcl <- fpTerm ctx' concl
    pure $ byte 0x22
        <> bytes (length vars)
        <> varTys
        <> bhyps
        <> bconcl

-- | Produce a SHA256 fingerprint of a SATQuery. This fingerprint should be:
--   * Stable across runs (has no VarIndex/TermIndex dependence).
--   * Alpha-equivalence-respecting (uses de Bruijn indices for bound variables).
--   * Definition-sensitive (transitively serializes constant bodies).
--   * Relatively fast.
fingerprintSATQuery :: ByteString -> ModuleMap -> SATQuery -> BS.ByteString
fingerprintSATQuery prefix mm satq =
    SHA256.hashlazy $ prefix
                   <> singleton 0
                   <> BS.toLazyByteString (evalState (runReaderT satq' cfg) st0)
  where
    cfg :: FPCfg
    cfg = FPCfg mm $ satUninterp satq

    st0 :: FPSt
    st0 = FPSt mempty mempty 0

    vars :: [(VarName, FirstOrderType)]
    vars = Map.toAscList $ satVariables satq

    varTys :: BS.Builder
    varTys = foldMap (bytes . snd) vars

    queryCtx :: VarCtx
    queryCtx = foldl' (\c (v, _) -> consVarCtx v c) emptyVarCtx vars

    -- Note: asserts are not sorted here, so re-ordering the same
    -- asserts will produce a different fingerprint.
    satq' :: FP BS.Builder
    satq' = do
      asserts <- mapM (fpAssert queryCtx) $ satAsserts satq
      pure $ bytes (length vars) <> varTys <> mconcat asserts
