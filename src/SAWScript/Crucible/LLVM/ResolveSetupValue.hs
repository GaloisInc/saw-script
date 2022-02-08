{- |
Module      : SAWScript.Crucible.LLVM.ResolveSetupValue
Description : Turn SetupValues back into LLVMVals
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SAWScript.Crucible.LLVM.ResolveSetupValue
  ( LLVMVal, LLVMPtr
  , resolveSetupVal
  , resolveSetupValBitfield
  , typeOfSetupValue
  , resolveTypedTerm
  , resolveSAWPred
  , resolveSAWSymBV
  , resolveSetupFieldIndex
  , resolveSetupFieldIndexOrFail
  , BitfieldIndex(..)
  , resolveSetupBitfieldIndex
  , resolveSetupBitfieldIndexOrFail
  , resolveSetupElemIndexOrFail
  , equalValsPred
  , memArrayToSawCoreTerm
  , scPtrWidthBvNat
  , W4EvalTactic(..)
  ) where

import Control.Lens ((^.))
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Monad.State
import qualified Data.BitVector.Sized as BV
import Data.Maybe (fromMaybe, listToMaybe, fromJust)

import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as V
import           Data.Word (Word64)
import           Numeric.Natural

import qualified Text.LLVM.AST as L

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Verifier.SAW.Cryptol.Simpset as Cryptol

import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.NatRepr

import qualified What4.BaseTypes    as W4
import qualified What4.Interface    as W4

import qualified Lang.Crucible.LLVM.Bytes       as Crucible
import qualified Lang.Crucible.LLVM.MemModel    as Crucible
import qualified Lang.Crucible.LLVM.MemType     as Crucible
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as Crucible

import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator.Concrete as Concrete

import Verifier.SAW.Cryptol (importType, emptyEnv)
import Verifier.SAW.Name
import Verifier.SAW.TypedTerm
import Verifier.SAW.Simulator.What4
import Verifier.SAW.Simulator.What4.ReturnTrip
import qualified Text.LLVM.DebugUtils as L

import           SAWScript.Crucible.Common (Sym, sawCoreState, HasSymInterface(..))
import           SAWScript.Crucible.Common.MethodSpec (AllocIndex(..), SetupValue(..), ppTypedTermType)

import SAWScript.Crucible.LLVM.MethodSpecIR
import qualified SAWScript.Proof as SP

--import qualified SAWScript.LLVMBuiltins as LB

type LLVMVal = Crucible.LLVMVal Sym
type LLVMPtr wptr = Crucible.LLVMPtr Sym wptr

-- | Use the LLVM metadata to determine the struct field index
-- corresponding to the given field name.
resolveSetupValueInfo ::
  LLVMCrucibleContext wptr            {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
  SetupValue (LLVM arch)                      {- ^ pointer to struct -} ->
  L.Info                          {- ^ field index       -}
resolveSetupValueInfo cc env nameEnv v =
  case v of
    SetupGlobal _ name ->
      case lookup (L.Symbol name) globalTys of
        Just (L.Alias alias) -> L.Pointer (L.guessAliasInfo mdMap alias)
        _ -> L.Unknown

    SetupVar i
      | Just alias <- Map.lookup i nameEnv
      -> L.Pointer (L.guessAliasInfo mdMap alias)

    SetupCast () _ (L.Alias alias)
      -> L.Pointer (L.guessAliasInfo mdMap alias)

    SetupField () a n ->
       fromMaybe L.Unknown $
       do L.Pointer (L.Structure xs) <- return (resolveSetupValueInfo cc env nameEnv a)
          listToMaybe [L.Pointer i | L.StructFieldInfo{L.sfiName = n', L.sfiInfo = i} <- xs, n == n' ]

    _ -> L.Unknown
  where
    globalTys = [ (L.globalSym g, L.globalType g) | g <- L.modGlobals (ccLLVMModuleAST cc) ]
    mdMap = Crucible.llvmMetadataMap (ccTypeCtx cc)

-- | Use the LLVM metadata to determine the struct field index
-- corresponding to the given field name.
resolveSetupFieldIndex ::
  LLVMCrucibleContext arch {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
  SetupValue (LLVM arch) {- ^ pointer to struct -} ->
  String                          {- ^ field name        -} ->
  Maybe Int                       {- ^ field index       -}
resolveSetupFieldIndex cc env nameEnv v n =
  case resolveSetupValueInfo cc env nameEnv v of
    L.Pointer (L.Structure xs) ->
      case [o | L.StructFieldInfo{L.sfiName = n', L.sfiOffset = o} <- xs, n == n' ] of
        [] -> Nothing
        o:_ ->
          do Crucible.PtrType symTy <- typeOfSetupValue cc env nameEnv v
             Crucible.StructType si <-
               let ?lc = lc
               in either (\_ -> Nothing) Just $ Crucible.asMemType symTy
             V.findIndex (\fi -> Crucible.bytesToBits (Crucible.fiOffset fi) == fromIntegral o) (Crucible.siFields si)

    _ -> Nothing
  where
    lc = ccTypeCtx cc

resolveSetupFieldIndexOrFail ::
  Fail.MonadFail m =>
  LLVMCrucibleContext arch {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
  SetupValue (LLVM arch) {- ^ pointer to struct -} ->
  String                          {- ^ field name        -} ->
  m Int                           {- ^ field index       -}
resolveSetupFieldIndexOrFail cc env nameEnv v n =
  case resolveSetupFieldIndex cc env nameEnv v n of
    Just i  -> pure i
    Nothing ->
      let msg = "Unable to resolve field name: " ++ show n
      in
        fail $
          -- Show the user what fields were available (if any)
          case resolveSetupValueInfo cc env nameEnv v of
            L.Pointer (L.Structure xs) -> unlines $
              [ msg
              , "The following field names were found for this struct:"
              ] ++ map ("- "++) [n' | L.StructFieldInfo{L.sfiName = n'} <- xs]
            _ -> unlines [msg, "No field names were found for this struct"]

-- | Information about a field within a bitfield in a struct. For example,
-- given the following C struct:
--
-- @
-- struct s {
--   int32_t w;
--   uint8_t x1:1;
--   uint8_t x2:2;
--   uint8_t y:1;
--   int32_t z;
-- };
-- @
--
-- The 'BitfieldIndex'es for @x1@, @x2@, and @y@ are as follows:
--
-- @
-- -- x1
-- 'BitfieldIndex'
--   { 'biFieldSize' = 1
--   , 'biFieldOffset' = 0
--   , 'biBitfieldIndex' = 4
--   , 'biBitfieldType' = i8
--   }
--
-- -- x2
-- 'BitfieldIndex'
--   { 'biFieldSize' = 2
--   , 'biFieldOffset' = 1
--   , 'biBitfieldIndex' = 4
--   , 'biBitfieldType' = i8
--   }
--
-- -- y
-- 'BitfieldIndex'
--   { 'biFieldSize' = 1
--   , 'biFieldOffset' = 3
--   , 'biBitfieldIndex' = 4
--   , 'biBitfieldType' = i8
--   }
-- @
--
-- Note that the 'biFieldSize's and 'biFieldOffset's are specific to each
-- individual field, while the 'biBitfieldIndex'es and 'biBitfieldType's are
-- all the same, as the latter two all describe the same bitfield.
data BitfieldIndex = BitfieldIndex
  { biFieldSize :: Word64
    -- ^ The size (in bits) of the field within the bitfield.
  , biFieldOffset :: Word64
    -- ^ The offset (in bits) of the field from the start of the bitfield,
    --   counting from the least significant bit.
  , biBitfieldIndex :: Int
    -- ^ The struct field index corresponding to the overall bitfield, where
    --   the index represents the number of bytes the bitfield is from the
    --   start of the struct.
  , biBitfieldType :: Crucible.MemType
    -- ^ The 'Crucible.MemType' of the overall bitfield.
  } deriving Show

-- | Returns @'Just' bi@ if SAW is able to find a field within a bitfield with
-- the supplied name in the LLVM debug metadata. Returns 'Nothing' otherwise.
resolveSetupBitfieldIndex ::
  LLVMCrucibleContext arch {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident {- ^ allocation type names -} ->
  SetupValue (LLVM arch) {- ^ pointer to struct -} ->
  String {- ^ field name -} ->
  Maybe BitfieldIndex {- ^ information about bitfield -}
resolveSetupBitfieldIndex cc env nameEnv v n =
  case resolveSetupValueInfo cc env nameEnv v of
    L.Pointer (L.Structure xs)
      |  (fieldOffsetStartingFromStruct, bfInfo):_ <-
           [ (fieldOffsetStartingFromStruct, bfInfo)
           | L.StructFieldInfo
               { L.sfiName = n'
               , L.sfiOffset = fieldOffsetStartingFromStruct
               , L.sfiBitfield = Just bfInfo
               } <- xs
           , n == n'
           ]
      -> do Crucible.PtrType symTy <- typeOfSetupValue cc env nameEnv v
            Crucible.StructType si <-
              let ?lc = lc
              in either (\_ -> Nothing) Just $ Crucible.asMemType symTy
            bfIndex <-
              V.findIndex (\fi -> Crucible.bytesToBits (Crucible.fiOffset fi)
                                          == fromIntegral (L.biBitfieldOffset bfInfo))
                          (Crucible.siFields si)
            let bfType = Crucible.fiType $ Crucible.siFields si V.! bfIndex
                fieldOffsetStartingFromBitfield =
                  fieldOffsetStartingFromStruct - L.biBitfieldOffset bfInfo
            pure $ BitfieldIndex { biFieldSize     = L.biFieldSize bfInfo
                                 , biFieldOffset   = fieldOffsetStartingFromBitfield
                                 , biBitfieldIndex = bfIndex
                                 , biBitfieldType  = bfType
                                 }

    _ -> Nothing
  where
    lc = ccTypeCtx cc

-- | Like 'resolveSetupBitfieldIndex', but if SAW cannot find the supplied
-- name, fail instead of returning 'Nothing'.
resolveSetupBitfieldIndexOrFail ::
  Fail.MonadFail m =>
  LLVMCrucibleContext arch {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident {- ^ allocation type names -} ->
  SetupValue (LLVM arch) {- ^ pointer to struct -} ->
  String {- ^ field name -} ->
  m BitfieldIndex {- ^ field index -}
resolveSetupBitfieldIndexOrFail cc env nameEnv v n =
  case resolveSetupBitfieldIndex cc env nameEnv v n of
    Just i  -> pure i
    Nothing ->
      let msg = "Unable to resolve field name: " ++ show n
      in
        fail $
          -- Show the user what fields were available (if any)
          case resolveSetupValueInfo cc env nameEnv v of
            L.Pointer (L.Structure xs) -> unlines $
              [ msg
              , "The following bitfield names were found for this struct:"
              ] ++ map ("- "++) [n' | L.StructFieldInfo{ L.sfiName = n'
                                                       , L.sfiBitfield = Just{}
                                                       } <- xs]
            _ -> unlines [msg, "No field names were found for this struct"]

typeOfSetupValue ::
  Fail.MonadFail m =>
  LLVMCrucibleContext arch ->
  Map AllocIndex LLVMAllocSpec ->
  Map AllocIndex Crucible.Ident ->
  SetupValue (LLVM arch) ->
  m Crucible.MemType
typeOfSetupValue cc env nameEnv val =
  do let ?lc = ccTypeCtx cc
     typeOfSetupValue' cc env nameEnv val

typeOfSetupValue' :: forall m arch.
  Fail.MonadFail m =>
  LLVMCrucibleContext arch ->
  Map AllocIndex LLVMAllocSpec ->
  Map AllocIndex Crucible.Ident ->
  SetupValue (LLVM arch) ->
  m Crucible.MemType
typeOfSetupValue' cc env nameEnv val =
  case val of
    SetupVar i ->
      case Map.lookup i env of
        Nothing -> fail ("typeOfSetupValue: Unresolved prestate variable:" ++ show i)
        Just spec ->
          return (Crucible.PtrType (Crucible.MemType (spec ^. allocSpecType)))
    SetupTerm tt ->
      case ttType tt of
        TypedTermSchema (Cryptol.Forall [] [] ty) ->
          case toLLVMType dl (Cryptol.evalValType mempty ty) of
            Left err -> fail (toLLVMTypeErrToString err)
            Right memTy -> return memTy
        tp -> fail $ unlines [ "typeOfSetupValue: expected monomorphic term"
                             , "instead got:"
                             , show (ppTypedTermType tp)
                             ]
    SetupCast () v ltp ->
      do memTy <- typeOfSetupValue cc env nameEnv v
         case memTy of
           Crucible.PtrType _symTy ->
             case let ?lc = lc in Crucible.liftMemType (L.PtrTo ltp) of
               Left err -> fail $ unlines [ "typeOfSetupValue: invalid type " ++ show ltp
                                          , "Details:"
                                          , err
                                          ]
               Right mt -> return mt

           _ -> fail $ unwords $
                  [ "typeOfSetupValue: tried to cast the type of a non-pointer value"
                  , "actual type of value: " ++ show memTy
                  ]
    SetupStruct () packed vs ->
      do memTys <- traverse (typeOfSetupValue cc env nameEnv) vs
         let si = Crucible.mkStructInfo dl packed memTys
         return (Crucible.StructType si)
    SetupArray () [] -> fail "typeOfSetupValue: invalid empty llvm_array_value"
    SetupArray () (v : vs) ->
      do memTy <- typeOfSetupValue cc env nameEnv v
         _memTys <- traverse (typeOfSetupValue cc env nameEnv) vs
         -- TODO: check that all memTys are compatible with memTy
         return (Crucible.ArrayType (fromIntegral (length (v:vs))) memTy)
    SetupField () v n -> do
      i <- resolveSetupFieldIndexOrFail cc env nameEnv v n
      typeOfSetupValue' cc env nameEnv (SetupElem () v i)
    SetupElem () v i ->
      do memTy <- typeOfSetupValue cc env nameEnv v
         let msg = "typeOfSetupValue: llvm_elem requires pointer to struct or array, found " ++ show memTy
         case memTy of
           Crucible.PtrType symTy ->
             case let ?lc = lc in Crucible.asMemType symTy of
               Right memTy' ->
                 case memTy' of
                   Crucible.ArrayType n memTy''
                     | fromIntegral i <= n -> return (Crucible.PtrType (Crucible.MemType memTy''))
                     | otherwise -> fail $ unwords $
                         [ "typeOfSetupValue: array type index out of bounds"
                         , "(index: " ++ show i ++ ")"
                         , "(array length: " ++ show n ++ ")"
                         ]
                   Crucible.StructType si ->
                     case Crucible.siFieldInfo si i of
                       Just fi -> return (Crucible.PtrType (Crucible.MemType (Crucible.fiType fi)))
                       Nothing -> fail $ "typeOfSetupValue: struct type index out of bounds: " ++ show i
                   _ -> fail msg
               Left err -> fail (unlines [msg, "Details:", err])
           _ -> fail msg
    SetupNull () ->
      -- We arbitrarily set the type of NULL to void*, because a) it
      -- is memory-compatible with any type that NULL can be used at,
      -- and b) it prevents us from doing a type-safe dereference
      -- operation.
      return (Crucible.PtrType Crucible.VoidType)
    -- A global and its initializer have the same type.
    SetupGlobal () name -> do
      let m = ccLLVMModuleAST cc
          tys = [ (L.globalSym g, L.globalType g) | g <- L.modGlobals m ] ++
                [ (L.decName d, L.decFunType d) | d <- L.modDeclares m ] ++
                [ (L.defName d, L.defFunType d) | d <- L.modDefines m ]
      case lookup (L.Symbol name) tys of
        Nothing -> fail $ "typeOfSetupValue: unknown global " ++ show name
        Just ty ->
          case let ?lc = lc in Crucible.liftType ty of
            Left err -> fail $ unlines [ "typeOfSetupValue: invalid type " ++ show ty
                                       , "Details:"
                                       , err
                                       ]
            Right symTy -> return (Crucible.PtrType symTy)
    SetupGlobalInitializer () name -> do
      case Map.lookup (L.Symbol name) (Crucible.globalInitMap $ ccLLVMModuleTrans cc) of
        Just (g, _) ->
          case let ?lc = lc in Crucible.liftMemType (L.globalType g) of
            Left err -> fail $ unlines [ "typeOfSetupValue: invalid type " ++ show (L.globalType g)
                                       , "Details:"
                                       , err
                                       ]
            Right memTy -> return memTy
        Nothing             -> fail $ "resolveSetupVal: global not found: " ++ name
  where
    lc = ccTypeCtx cc
    dl = Crucible.llvmDataLayout lc

resolveSetupElemIndexOrFail ::
  Fail.MonadFail m =>
  LLVMCrucibleContext arch {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
  SetupValue (LLVM arch) {- ^ base pointer -} ->
  Int                             {- ^ element index -} ->
  m Crucible.Bytes                {- ^ element offset -}
resolveSetupElemIndexOrFail cc env nameEnv v i = do
  do memTy <- typeOfSetupValue cc env nameEnv v
     let msg = "resolveSetupVal: llvm_elem requires pointer to struct or array, found " ++ show memTy
     case memTy of
       Crucible.PtrType symTy ->
         case let ?lc = lc in Crucible.asMemType symTy of
           Right memTy' ->
             case memTy' of
               Crucible.ArrayType n memTy''
                 | fromIntegral i <= n -> return (fromIntegral i * Crucible.memTypeSize dl memTy'')
               Crucible.StructType si ->
                 case Crucible.siFieldOffset si i of
                   Just d -> return d
                   Nothing -> fail $ "resolveSetupVal: struct type index out of bounds: " ++ show (i, memTy')
               _ -> fail msg
           Left err -> fail $ unlines [msg, "Details:", err]
       _ -> fail msg
  where
    lc = ccTypeCtx cc
    dl = Crucible.llvmDataLayout lc


-- | The tactic for What4 translation for SAWCore expressions during
-- Crucible symbolic execution. The boolean option specifies whether
-- non-user-defined symbols are translated. Note that ground constants are
-- always translated.
newtype W4EvalTactic = W4EvalTactic { doW4Eval :: Bool }
  deriving (Eq, Ord, Show)

-- | Translate a SetupValue into a Crucible LLVM value, resolving
-- references
resolveSetupVal :: forall arch.
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  Crucible.MemImpl Sym ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Map AllocIndex LLVMAllocSpec ->
  Map AllocIndex Crucible.Ident ->
  SetupValue (LLVM arch) ->
  IO LLVMVal
resolveSetupVal cc mem env tyenv nameEnv val =
  ccWithBackend cc $ \bak ->
  let sym = backendGetSym bak
      lc = ccTypeCtx cc
      dl = Crucible.llvmDataLayout lc
  in
  case val of
    SetupVar i
      | Just ptr <- Map.lookup i env -> return (Crucible.ptrToPtrVal ptr)
      | otherwise -> fail ("resolveSetupVal: Unresolved prestate variable:" ++ show i)
    SetupTerm tm -> resolveTypedTerm cc tm
    SetupCast () v _ -> resolveSetupVal cc mem env tyenv nameEnv v
    SetupStruct () packed vs -> do
      vals <- mapM (resolveSetupVal cc mem env tyenv nameEnv) vs
      let tps = map Crucible.llvmValStorableType vals
      let t = Crucible.mkStructType (V.fromList (mkFields packed dl Crucible.noAlignment 0 tps))
      let flds = case Crucible.storageTypeF t of
                   Crucible.Struct v -> v
                   _ -> error "impossible"
      return $ Crucible.LLVMValStruct (V.zip flds (V.fromList vals))
    SetupArray () [] -> fail "resolveSetupVal: invalid empty array"
    SetupArray () vs -> do
      vals <- V.mapM (resolveSetupVal cc mem env tyenv nameEnv) (V.fromList vs)
      let tp = Crucible.llvmValStorableType (V.head vals)
      return $ Crucible.LLVMValArray tp vals
    SetupField () v n -> do
      i <- resolveSetupFieldIndexOrFail cc tyenv nameEnv v n
      resolveSetupVal cc mem env tyenv nameEnv (SetupElem () v i)
    SetupElem () v i ->
      do delta <- resolveSetupElemIndexOrFail cc tyenv nameEnv v i
         ptr <- resolveSetupVal cc mem env tyenv nameEnv v
         case ptr of
           Crucible.LLVMValInt blk off ->
             do delta' <- W4.bvLit sym (W4.bvWidth off) (Crucible.bytesToBV (W4.bvWidth off) delta)
                off' <- W4.bvAdd sym off delta'
                return (Crucible.LLVMValInt blk off')
           _ -> fail "resolveSetupVal: llvm_elem requires pointer value"
    SetupNull () ->
      Crucible.ptrToPtrVal <$> Crucible.mkNullPointer sym Crucible.PtrWidth
    SetupGlobal () name ->
      Crucible.ptrToPtrVal <$> Crucible.doResolveGlobal bak mem (L.Symbol name)
    SetupGlobalInitializer () name ->
      case Map.lookup (L.Symbol name)
                      (Crucible.globalInitMap $ ccLLVMModuleTrans cc) of
        -- There was an error in global -> constant translation
        Just (_, Left e) -> fail e
        Just (_, Right (_, Just v)) ->
          let ?lc = lc
          in Crucible.constToLLVMVal @(Crucible.ArchWidth arch) bak mem v
        Just (_, Right (_, Nothing)) ->
          fail $ "resolveSetupVal: global has no initializer: " ++ name
        Nothing ->
          fail $ "resolveSetupVal: global not found: " ++ name


-- | Like 'resolveSetupVal', but specifically geared towards the needs of
-- fields within bitfields. This is very similar to calling 'resolveSetupVal'
-- on a 'SetupField', instead of computing an offset into the struct based off
-- of the /field's/ offset from the beginning of the struct, this computes an
-- offset based off of the overall /bitfield's/ offset from the beginning of
-- the struct. This is important because in order to impose conditions on
-- fields within bitfields, we must load/store the entire bitfield. The field's
-- offset may be larger than the bitfield's offset, so the former offset is not
-- suited for this purpose.
--
-- In addition to returning the resolved 'LLVMVal', this also returns the
-- 'BitfieldIndex' for the field within the bitfield. This ends up being useful
-- for call sites to this function so that they do not have to recompute it.
resolveSetupValBitfield ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  Crucible.MemImpl Sym ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Map AllocIndex LLVMAllocSpec ->
  Map AllocIndex Crucible.Ident ->
  SetupValue (LLVM arch) ->
  String ->
  IO (BitfieldIndex, LLVMVal)
resolveSetupValBitfield cc mem env tyenv nameEnv val fieldName =
  do let sym = cc^.ccSym
     lval       <- resolveSetupVal cc mem env tyenv nameEnv val
     bfIndex    <- resolveSetupBitfieldIndexOrFail cc tyenv nameEnv val fieldName
     delta      <- resolveSetupElemIndexOrFail cc tyenv nameEnv val (biBitfieldIndex bfIndex)
     offsetLval <- case lval of
       Crucible.LLVMValInt blk off ->
         do deltaBV <- W4.bvLit sym (W4.bvWidth off) (Crucible.bytesToBV (W4.bvWidth off) delta)
            off'    <- W4.bvAdd sym off deltaBV
            return (Crucible.LLVMValInt blk off')
       _ -> fail "resolveSetupValBitfield: expected a pointer value"
     pure (bfIndex, offsetLval)

resolveTypedTerm ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  TypedTerm       ->
  IO LLVMVal
resolveTypedTerm cc tm =
  case ttType tm of
    TypedTermSchema (Cryptol.Forall [] [] ty) ->
      resolveSAWTerm cc (Cryptol.evalValType mempty ty) (ttTerm tm)
    tp -> fail $ unlines
            [ "resolveSetupVal: expected monomorphic term"
            , "instead got term with type"
            , show (ppTypedTermType tp)
            ]

resolveSAWPred ::
  (?w4EvalTactic :: W4EvalTactic) =>
  LLVMCrucibleContext arch ->
  Term ->
  IO (W4.Pred Sym)
resolveSAWPred cc tm = do
  do let sym = cc^.ccSym
     st <- sawCoreState sym
     let sc = saw_ctx st
     let ss = cc^.ccBasicSS
     (_,tm') <- rewriteSharedTerm sc ss tm
     mx <- case getAllExts tm' of
             -- concretely evaluate if it is a closed term
             [] -> do modmap <- scGetModuleMap sc
                      let v = Concrete.evalSharedTerm modmap mempty mempty tm
                      pure (Just (Concrete.toBool v))
             _ -> return Nothing
     case mx of
       Just x  -> return $ W4.backendPred sym x
       Nothing
         | doW4Eval ?w4EvalTactic ->
           do cryptol_ss <- Cryptol.mkCryptolSimpset @SP.TheoremNonce sc
              (_,tm'') <- rewriteSharedTerm sc cryptol_ss tm'
              (_,tm''') <- rewriteSharedTerm sc ss tm''
              if not (any (\(name, _, _) -> not (isPreludeName name)) (Map.elems $ getConstantSet tm''')) then
                do (_names, (_mlabels, p)) <- w4Eval sym st sc mempty Set.empty tm'''
                   return p
              else bindSAWTerm sym st W4.BaseBoolRepr tm'
         | otherwise ->
           bindSAWTerm sym st W4.BaseBoolRepr tm'

resolveSAWSymBV ::
  (?w4EvalTactic :: W4EvalTactic, 1 <= w) =>
  LLVMCrucibleContext arch ->
  NatRepr w ->
  Term ->
  IO (W4.SymBV Sym w)
resolveSAWSymBV cc w tm =
  do let sym = cc^.ccSym
     st <- sawCoreState sym
     let sc = saw_ctx st
     mx <- case getAllExts tm of
             -- concretely evaluate if it is a closed term
             [] -> do modmap <- scGetModuleMap sc
                      let v = Concrete.evalSharedTerm modmap mempty mempty tm
                      pure (Just (Prim.unsigned (Concrete.toWord v)))
             _ -> return Nothing
     case mx of
       Just x  -> W4.bvLit sym w (BV.mkBV w x)
       Nothing
         | doW4Eval ?w4EvalTactic ->
           do let ss = cc^.ccBasicSS
              (_,tm') <- rewriteSharedTerm sc ss tm
              cryptol_ss <- Cryptol.mkCryptolSimpset @SP.TheoremNonce sc
              (_,tm'') <- rewriteSharedTerm sc cryptol_ss tm'
              (_,tm''') <- rewriteSharedTerm sc ss tm''
              if not (any (\(name, _, _) -> not (isPreludeName name)) (Map.elems $ getConstantSet tm''')) then
                do (_names, _, _, x) <- w4EvalAny sym st sc mempty Set.empty tm'''
                   case valueToSymExpr x of
                     Just (Some y)
                       | Just Refl <- testEquality (W4.BaseBVRepr w) (W4.exprType y) ->
                         return y
                     _ -> fail $ "resolveSAWSymBV: unexpected w4Eval result " ++ show x
              else bindSAWTerm sym st (W4.BaseBVRepr w) tm
         | otherwise ->
           bindSAWTerm sym st (W4.BaseBVRepr w) tm

isPreludeName :: NameInfo -> Bool
isPreludeName = \case
  ModuleIdentifier ident -> identModule ident == preludeName
  _ -> False

resolveSAWTerm ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  Cryptol.TValue ->
  Term ->
  IO LLVMVal
resolveSAWTerm cc tp tm =
    case tp of
      Cryptol.TVBit ->
        fail "resolveSAWTerm: unimplemented type Bit (FIXME)"
      Cryptol.TVInteger ->
        fail "resolveSAWTerm: unimplemented type Integer (FIXME)"
      Cryptol.TVIntMod _ ->
        fail "resolveSAWTerm: unimplemented type Z n (FIXME)"
      Cryptol.TVFloat{} ->
        fail "resolveSAWTerm: unimplemented type Float e p (FIXME)"
      Cryptol.TVArray{} ->
        fail "resolveSAWTerm: unimplemented type Array a b (FIXME)"
      Cryptol.TVRational ->
        fail "resolveSAWTerm: unimplemented type Rational (FIXME)"

      Cryptol.TVSeq sz Cryptol.TVBit ->
        case someNat sz of
          Just (Some w)
            | Just LeqProof <- isPosNat w ->
              do v <- resolveSAWSymBV cc w tm
                 Crucible.ptrToPtrVal <$> Crucible.llvmPointer_bv sym v
          _ -> fail ("Invalid bitvector width: " ++ show sz)
      Cryptol.TVSeq sz tp' ->
        do st <- sawCoreState sym
           let sc = saw_ctx st
           sz_tm <- scNat sc (fromIntegral sz)
           tp_tm <- importType sc emptyEnv (Cryptol.tValTy tp')
           let f i = do i_tm <- scNat sc (fromIntegral i)
                        tm' <- scAt sc sz_tm tp_tm tm i_tm
                        resolveSAWTerm cc tp' tm'
           case toLLVMType dl tp' of
             Left e -> fail ("In resolveSAWTerm: " ++ toLLVMTypeErrToString e)
             Right memTy -> do
               gt <- Crucible.toStorableType memTy
               Crucible.LLVMValArray gt . V.fromList <$> mapM f [ 0 .. (sz-1) ]
      Cryptol.TVStream _tp' ->
        fail "resolveSAWTerm: invalid infinite stream type"
      Cryptol.TVTuple tps ->
        do st <- sawCoreState sym
           let sc = saw_ctx st
           tms <- mapM (\i -> scTupleSelector sc tm i (length tps)) [1 .. length tps]
           vals <- zipWithM (resolveSAWTerm cc) tps tms
           storTy <-
             case toLLVMType dl tp of
               Left e -> fail ("In resolveSAWTerm: " ++ toLLVMTypeErrToString e)
               Right memTy -> Crucible.toStorableType memTy
           fields <-
             case Crucible.storageTypeF storTy of
               Crucible.Struct fields -> return fields
               _ -> fail "resolveSAWTerm: impossible: expected struct"
           return (Crucible.LLVMValStruct (V.zip fields (V.fromList vals)))
      Cryptol.TVRec _flds ->
        fail "resolveSAWTerm: unimplemented record type (FIXME)"
      Cryptol.TVFun _ _ ->
        fail "resolveSAWTerm: invalid function type"
      Cryptol.TVAbstract _ _ ->
        fail "resolveSAWTerm: invalid abstract type"
      Cryptol.TVNewtype{} ->
        fail "resolveSAWTerm: invalid newtype"
  where
    sym = cc^.ccSym
    dl = Crucible.llvmDataLayout (ccTypeCtx cc)

scPtrWidthBvNat ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch), Integral a) =>
  LLVMCrucibleContext arch ->
  a ->
  IO Term
scPtrWidthBvNat cc n =
  do let sym = cc^.ccSym
     st <- sawCoreState sym
     let sc = saw_ctx st
     w <- scNat sc $ natValue Crucible.PtrWidth
     scBvNat sc w =<< scNat sc (fromIntegral n)

data ToLLVMTypeErr = NotYetSupported String | Impossible String

toLLVMTypeErrToString :: ToLLVMTypeErr -> String
toLLVMTypeErrToString =
  \case
    NotYetSupported ty ->
      unwords [ "SAW doesn't yet support translating Cryptol's"
              , ty
              , "type(s) into crucible-llvm's type system."
              ]
    Impossible ty ->
      unwords [ "User error: It's impossible to store Cryptol"
              , ty
              , "values in crucible-llvm's memory model."
              ]

toLLVMType ::
  Crucible.DataLayout ->
  Cryptol.TValue ->
  Either ToLLVMTypeErr Crucible.MemType
toLLVMType dl tp =
  case tp of
    Cryptol.TVBit -> Left (NotYetSupported "bit") -- FIXME
    Cryptol.TVInteger -> Left (NotYetSupported "integer")
    Cryptol.TVIntMod _ -> Left (NotYetSupported "integer (mod n)")
    Cryptol.TVFloat{} -> Left (NotYetSupported "float e p")
    Cryptol.TVArray{} -> Left (NotYetSupported "array a b")
    Cryptol.TVRational -> Left (NotYetSupported "rational")

    Cryptol.TVSeq n Cryptol.TVBit
      | n > 0 -> Right (Crucible.IntType (fromInteger n))
      | otherwise -> Left (Impossible "infinite sequence")
    Cryptol.TVSeq n t -> do
      t' <- toLLVMType dl t
      let n' = fromIntegral n
      Right (Crucible.ArrayType n' t')
    Cryptol.TVStream _tp' -> Left (Impossible "stream")
    Cryptol.TVTuple tps -> do
      tps' <- mapM (toLLVMType dl) tps
      let si = Crucible.mkStructInfo dl False tps'
      return (Crucible.StructType si)
    Cryptol.TVRec _flds -> Left (NotYetSupported "record")
    Cryptol.TVFun _ _ -> Left (Impossible "function")
    Cryptol.TVAbstract _ _ -> Left (Impossible "abstract")
    Cryptol.TVNewtype{} -> Left (Impossible "newtype")

toLLVMStorageType ::
  forall w .
  Crucible.HasPtrWidth w =>
  Crucible.DataLayout ->
  Cryptol.TValue ->
  IO Crucible.StorageType
toLLVMStorageType data_layout cryptol_type =
  case toLLVMType data_layout cryptol_type of
    Left e -> fail $ toLLVMTypeErrToString e
    Right memory_type -> Crucible.toStorableType @_ @w memory_type

-- FIXME: This struct-padding logic is already implemented in
-- crucible-llvm. Reimplementing it here is error prone and harder to
-- maintain.
mkFields ::
  Bool {- ^ @True@ = packed, @False@ = unpacked -} ->
  Crucible.DataLayout ->
  Crucible.Alignment ->
  Crucible.Bytes ->
  [Crucible.StorageType] ->
  [(Crucible.StorageType, Crucible.Bytes)]
mkFields _ _ _ _ [] = []
mkFields packed dl a off (ty : tys) =
  (ty, pad) : mkFields packed dl a' off' tys
  where
    end = off + Crucible.storageTypeSize ty
    off' = if packed then end else Crucible.padToAlignment end nextAlign
    pad = off' - end
    a' = max a (typeAlignment dl ty)
    nextAlign = case tys of
      [] -> a'
      (ty' : _) -> typeAlignment dl ty'


typeAlignment :: Crucible.DataLayout -> Crucible.StorageType -> Crucible.Alignment
typeAlignment dl ty =
  case Crucible.storageTypeF ty of
    Crucible.Bitvector bytes -> Crucible.integerAlignment dl (Crucible.bytesToBits bytes)
    Crucible.Float           -> fromJust (Crucible.floatAlignment dl 32)
    Crucible.Double          -> fromJust (Crucible.floatAlignment dl 64)
    Crucible.X86_FP80        -> fromJust (Crucible.floatAlignment dl 80)
    Crucible.Array _sz ty'   -> typeAlignment dl ty'
    Crucible.Struct flds     -> V.foldl max Crucible.noAlignment (fmap (typeAlignment dl . (^. Crucible.fieldVal)) flds)


equalValsPred ::
  LLVMCrucibleContext wptr ->
  LLVMVal ->
  LLVMVal ->
  IO (W4.Pred Sym)
equalValsPred cc v1 v2 =
   fromMaybe (W4.falsePred sym) <$> Crucible.testEqual sym v1 v2

  where
  sym = cc^.ccSym


memArrayToSawCoreTerm ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  LLVMCrucibleContext arch ->
  Crucible.EndianForm ->
  TypedTerm ->
  IO Term
memArrayToSawCoreTerm crucible_context endianess typed_term = do
  let sym = crucible_context ^. ccSym
  let data_layout = Crucible.llvmDataLayout $ ccTypeCtx crucible_context
  st <- sawCoreState sym
  let saw_context = saw_ctx st

  byte_type_term <- importType saw_context emptyEnv $ Cryptol.tValTy $ Cryptol.TVSeq 8 Cryptol.TVBit
  offset_type_term <- scBitvector saw_context $ natValue ?ptrWidth

  let updateArray :: Natural -> Term -> StateT Term IO ()
      updateArray offset byte_term = do
        ptr_width_term <- liftIO $ scNat saw_context $ natValue ?ptrWidth
        offset_term <- liftIO $ scBvNat saw_context ptr_width_term =<< scNat saw_context offset
        array_term <- get
        updated_array_term <- liftIO $
          scArrayUpdate saw_context offset_type_term byte_type_term array_term offset_term byte_term
        put updated_array_term
      setBytes :: Cryptol.TValue -> Term -> Crucible.Bytes -> StateT Term IO ()
      setBytes cryptol_type saw_term offset = case cryptol_type of
        Cryptol.TVSeq size Cryptol.TVBit
          | (byte_count, 0) <- quotRem (fromInteger size) 8 ->
            if byte_count > 1
              then forM_ [0 .. (byte_count - 1)] $ \byte_index -> do
                bit_type_term <- liftIO $ importType
                  saw_context
                  emptyEnv
                  (Cryptol.tValTy Cryptol.TVBit)
                byte_index_term <- liftIO $ scNat saw_context $ byte_index * 8
                byte_size_term <- liftIO $ scNat saw_context 8
                remaining_bits_size_term <- liftIO $ scNat saw_context $
                  (byte_count - byte_index - 1) * 8
                saw_byte_term <- liftIO $ scSlice
                  saw_context
                  bit_type_term
                  byte_index_term
                  byte_size_term
                  remaining_bits_size_term
                  saw_term

                let byte_storage_index = case endianess of
                      Crucible.BigEndian -> byte_index
                      Crucible.LittleEndian -> byte_count - byte_index - 1
                let byte_offset = ((fromIntegral offset) + (fromIntegral byte_storage_index))
                updateArray byte_offset saw_byte_term
            else
              updateArray (fromIntegral offset) saw_term
          | otherwise -> fail $ "unexpected bit count: " ++ show size

        Cryptol.TVSeq size element_cryptol_type -> do
          element_storage_size <- liftIO $
            Crucible.storageTypeSize <$> toLLVMStorageType
              data_layout
              element_cryptol_type

          forM_ [0 .. (size - 1)] $ \element_index -> do
            size_term <- liftIO $ scNat saw_context $ fromInteger size
            elem_type_term <- liftIO $ importType
              saw_context
              emptyEnv
              (Cryptol.tValTy element_cryptol_type)
            index_term <- liftIO $ scNat saw_context $ fromInteger element_index
            inner_saw_term <- liftIO $ scAt
              saw_context
              size_term
              elem_type_term
              saw_term index_term
            setBytes
              element_cryptol_type
              inner_saw_term
              (offset + (fromInteger element_index) * element_storage_size)

        Cryptol.TVTuple tuple_element_cryptol_types -> do
          (Crucible.Struct field_storage_types) <- liftIO $
            Crucible.storageTypeF <$> toLLVMStorageType data_layout cryptol_type

          V.forM_ (V.izipWith (,,) field_storage_types (V.fromList tuple_element_cryptol_types)) $
            \(field_index, field_storage_type, tuple_element_cryptol_type) -> do
              inner_saw_term <- liftIO $ scTupleSelector
                saw_context
                saw_term
                (field_index + 1)
                (length tuple_element_cryptol_types)
              setBytes
                tuple_element_cryptol_type
                inner_saw_term
                (offset + (Crucible.fieldOffset field_storage_type))

        _ -> fail $ "unexpected cryptol type: " ++ show cryptol_type

  case ttType typed_term of
    TypedTermSchema (Cryptol.Forall [] [] cryptol_type) -> do
      let evaluated_type = Cryptol.evalValType mempty cryptol_type
      fresh_array_const <- scFreshGlobal saw_context "arr"
        =<< scArrayType saw_context offset_type_term byte_type_term
      execStateT
        (setBytes evaluated_type (ttTerm typed_term) 0)
        fresh_array_const

    _ -> fail $ "expected monomorphic typed term: " ++ show typed_term
