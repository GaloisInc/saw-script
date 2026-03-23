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

import Control.Monad.Reader (MonadReader, runReaderT, ask)
import Control.Monad.State.Strict (state, gets, modify', evalState, MonadState)
import qualified Crypto.Hash.SHA256 as SHA256
import Data.Binary (encode)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BS
import Data.ByteString.Lazy (ByteString, singleton)
import Data.Foldable (foldl')
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
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

-- | Read-only bits of state.
data FPCfg = FPCfg
  { fpModuleMap :: !ModuleMap
    -- ^ The module map for looking up definitions.
  , fpUninterp  :: !(Set VarIndex)
    -- ^ Uninterpreted constants (only serialize name + type, not body).
  }

-- | Mutable state tracked while serializing.
data FPSt = FPSt
  { fpTermMemo    :: !(IntMap Int)
    -- ^ TermIndex -> sequence number (assigned on first serialization).
  , fpDefMemo     :: !(IntMap Int)
    -- ^ VarIndex of global Name -> sequence number.
  , fpDefVisiting :: !IntSet
    -- ^ VarIndexes currently being traversed.
  , fpNextRef     :: !Int
    -- ^ Next available sequence number.
  }

freshRef :: MonadState FPSt m => m Int
freshRef = state $ \s ->
  let n = fpNextRef s in (n, s { fpNextRef = n + 1 })

rememberTerm :: MonadState FPSt m => Term -> Int -> m ()
rememberTerm t n = modify' $
  \s -> s { fpTermMemo = IntMap.insert (termIndex t) n $ fpTermMemo s }

lookupTermRef :: MonadState FPSt m => Term -> m (Maybe Int)
lookupTermRef t = IntMap.lookup (termIndex t) <$> gets fpTermMemo

rememberDef :: MonadState FPSt m => Name -> Int -> m ()
rememberDef nm n = modify' $
  \s -> s { fpDefMemo = IntMap.insert (nameIndex nm) n $ fpDefMemo s }

lookupDefRef :: MonadState FPSt m => Name -> m (Bool, Maybe Int)
lookupDefRef nm = do
  visiting <- IntSet.member (nameIndex nm) <$> gets fpDefVisiting
  def      <- IntMap.lookup (nameIndex nm) <$> gets fpDefMemo
  pure (visiting, def)

visit :: MonadState FPSt m => Name -> m ()
visit nm = modify' $
  \s -> s { fpDefVisiting = IntSet.insert (nameIndex nm) $ fpDefVisiting s }

unvisit :: MonadState FPSt m => Name -> m ()
unvisit nm = modify' $
  \s -> s { fpDefVisiting = IntSet.delete (nameIndex nm) $ fpDefVisiting s }

lookupName :: MonadReader FPCfg m => Name -> m (Bool, Maybe ResolvedName)
lookupName nm = do
  cfg <- ask
  pure ( Set.member (nameIndex nm) $ fpUninterp cfg
       , lookupVarIndexInMap (nameIndex nm) $ fpModuleMap cfg
       )

byte :: Word8 -> BS.Builder
byte = BS.word8

-- | Markers used to preserve structural sharing without hashing.
tagRef, tagDef, tagCycle :: Word8
tagRef   = 0xF1  -- Reference to a previously serialized term or definition.
tagDef   = 0xF2  -- Introduces a new sequence number followed by its body.
tagCycle = 0xF3  -- Placeholder emitted when a definition cycle is detected.

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

fpTerms :: (MonadState FPSt m, MonadReader FPCfg m) => VarCtx -> [Term] -> m BS.Builder
fpTerms ctx ts = do
  bs <- mapM (fpTerm ctx) ts
  pure $ bytes (length ts) <> mconcat bs

fpTerm :: (MonadState FPSt m, MonadReader FPCfg m) => VarCtx -> Term -> m BS.Builder
fpTerm ctx t = lookupTermRef t >>= \case
  Just n  -> pure $ byte tagRef <> bytes n
  Nothing -> do
    n <- freshRef
    rememberTerm t n
    body <- fpTermF ctx (unwrapTermF t)
    pure $ byte tagDef <> bytes n <> body

fpTermF :: (MonadState FPSt m, MonadReader FPCfg m) => VarCtx -> TermF Term -> m BS.Builder
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
    | otherwise -> do                    -- Free var: use name.
      bty <- fpTerm ctx ty
      pure $ byte 0x6 <> bytes (vnName vn) <> bty

  FTermF (Sort s _) -> -- ignoring SortFlags
    pure $ byte 0x7 <> bytes s

  FTermF (StringLit txt) ->
    pure $ byte 0x8 <> bytes txt

  FTermF (ArrayValue elemTy elems) -> do
    bty <- fpTerm ctx elemTy
    bs  <- fpTerms ctx (V.toList elems)
    pure $ byte 0x9 <> bty <> bs

  FTermF (Recursor cr) -> do
    dtB <- fpDef (recursorDataType cr)
    pure $ byte 0xa
        <> bytes (recursorSort cr)
        <> dtB

fpDef :: (MonadState FPSt m, MonadReader FPCfg m) => Name -> m BS.Builder
fpDef nm = lookupDefRef nm >>= \case
  (_,    Just n)  -> pure $ byte tagRef <> bytes n
  (True, Nothing) -> pure $ byte tagCycle <> ni
  (False, Nothing) -> do
    visit nm
    body <- lookupName nm >>= \case
      (True, Just (ResolvedDef d)) -> do -- Uninterpreted.
        bty <- fpTerm emptyVarCtx $ defType d
        pure $ byte 0x11 <> ni <> bty
      (_, Just (ResolvedDef d))
        | Just b <- defBody d -> do
          bty   <- fpTerm emptyVarCtx $ defType d
          bbody <- fpTerm emptyVarCtx b
          pure $ byte 0x13 <> ni <> bty <> bbody
      (_, Just (ResolvedDef d)) -> do
        bty <- fpTerm emptyVarCtx $ defType d
        pure $ byte 0x12 <> ni <> bty
      (_, Just (ResolvedDataType dt)) -> do
        bty    <- fpTerm emptyVarCtx $ dtType dt
        bctors <- fpTerms emptyVarCtx $ ctorType <$> dtCtors dt
        pure $ byte 0x14 <> ni <> bty <> bctors
      (_, Just (ResolvedCtor c)) -> do
        bty <- fpTerm emptyVarCtx $ ctorType c
        pure $ byte 0x15 <> ni <> bty
      (_, Nothing) -> pure $ byte 0x16 <> ni
    unvisit nm
    n <- freshRef
    rememberDef nm n
    pure $ byte tagDef <> bytes n <> body
  where
    ni :: BS.Builder
    ni = bytes $ nameInfo nm

fpAssert :: (MonadState FPSt m, MonadReader FPCfg m) => VarCtx -> SATAssert -> m BS.Builder
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
    st0 = FPSt mempty mempty mempty 0

    vars :: [(VarName, FirstOrderType)]
    vars = Map.toAscList $ satVariables satq

    varTys :: BS.Builder
    varTys = foldMap (bytes . snd) vars

    queryCtx :: VarCtx
    queryCtx = foldl' (\c (v, _) -> consVarCtx v c) emptyVarCtx vars

    -- Note: asserts are not sorted here, so re-ordering the same
    -- asserts will produce a different fingerprint.
    satq' :: (MonadState FPSt m, MonadReader FPCfg m) => m BS.Builder
    satq' = do
      asserts <- mapM (fpAssert queryCtx) $ satAsserts satq
      pure $ bytes (length vars) <> varTys <> mconcat asserts
