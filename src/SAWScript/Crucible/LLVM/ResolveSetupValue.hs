{- |
Module      : SAWScript.Crucible.LLVM.ResolveSetupValue
Description : Turn SetupValues back into LLVMVals
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module SAWScript.Crucible.LLVM.ResolveSetupValue
  ( LLVMVal, LLVMPtr
  , resolveSetupVal
  , typeOfLLVMVal
  , typeOfSetupValue
  , resolveTypedTerm
  , resolveSAWPred
  , resolveSetupFieldIndex
  , equalValsPred
  ) where

import Control.Lens
import Control.Monad (zipWithM, foldM)
import Control.Monad.Fail (MonadFail)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe, listToMaybe, fromJust)
import Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

import qualified Text.LLVM.AST as L

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)

import           Data.Parameterized.Classes ((:~:)(..), testEquality)
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.NatRepr
                   (NatRepr(..), someNat, natValue, LeqProof(..), isPosNat)

import qualified What4.BaseTypes    as W4
import qualified What4.Interface    as W4
import qualified What4.Expr.Builder as W4
import qualified What4.ProgramLoc   as W4

import qualified Lang.Crucible.LLVM.MemModel    as Crucible
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.Backend.SAWCore  as Crucible
import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as Crucible

import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.Cryptol (importType, emptyEnv)
import Verifier.SAW.TypedTerm
import Text.LLVM.DebugUtils as L

import qualified Verifier.SAW.Simulator.SBV as SBV (sbvSolveBasic, toWord)
import qualified Data.SBV.Dynamic as SBV (svAsInteger)

import SAWScript.Prover.Rewrite
import SAWScript.Crucible.LLVM.MethodSpecIR

--import qualified SAWScript.LLVMBuiltins as LB

type LLVMVal = Crucible.LLVMVal Sym
type LLVMPtr wptr = Crucible.LLVMPtr Sym wptr

-- | Use the LLVM metadata to determine the struct field index
-- corresponding to the given field name.
resolveSetupValueInfo ::
  CrucibleContext wptr            {- ^ crucible context  -} ->
  Map AllocIndex (W4.ProgramLoc, Crucible.MemType) {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
  SetupValue                      {- ^ pointer to struct -} ->
  L.Info                          {- ^ field index       -}
resolveSetupValueInfo cc env nameEnv v =
  case v of
    -- SetupGlobal g ->
    SetupVar i
      | Just alias <- Map.lookup i nameEnv
      , let mdMap = Crucible.llvmMetadataMap (cc^.ccTypeCtx)
      -> L.Pointer (guessAliasInfo mdMap alias)
    SetupField a n ->
       fromMaybe L.Unknown $
       do L.Pointer (L.Structure xs) <- return (resolveSetupValueInfo cc env nameEnv a)
          listToMaybe [L.Pointer i | (n',_,i) <- xs, n == n' ]

    _ -> L.Unknown

-- | Use the LLVM metadata to determine the struct field index
-- corresponding to the given field name.
resolveSetupFieldIndex ::
  CrucibleContext wptr            {- ^ crucible context  -} ->
  Map AllocIndex (W4.ProgramLoc, Crucible.MemType) {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
  SetupValue                      {- ^ pointer to struct -} ->
  String                          {- ^ field name        -} ->
  Maybe Int                       {- ^ field index       -}
resolveSetupFieldIndex cc env nameEnv v n =
  case resolveSetupValueInfo cc env nameEnv v of
    L.Pointer (L.Structure xs) ->
      case [o | (n',o,_) <- xs, n == n' ] of
        [] -> Nothing
        o:_ ->
          do Crucible.PtrType symTy <- typeOfSetupValue cc env nameEnv v
             Crucible.StructType si <-
               let ?lc = lc
               in either (\_ -> Nothing) Just $ Crucible.asMemType symTy
             V.findIndex (\fi -> Crucible.bytesToBits (Crucible.fiOffset fi) == fromIntegral o) (Crucible.siFields si)

    _ -> Nothing
  where
    lc = cc^.ccTypeCtx

resolveSetupFieldIndexOrFail ::
  MonadFail m =>
  CrucibleContext wptr            {- ^ crucible context  -} ->
  Map AllocIndex (W4.ProgramLoc, Crucible.MemType) {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
  SetupValue                      {- ^ pointer to struct -} ->
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
              ] ++ map ("- "++) [n' | (n', _, _) <- xs]
            _ -> unlines [msg, "No field names were found for this struct"]

typeOfSetupValue ::
  MonadFail m =>
  CrucibleContext wptr ->
  Map AllocIndex (W4.ProgramLoc, Crucible.MemType) ->
  Map AllocIndex Crucible.Ident ->
  SetupValue ->
  m Crucible.MemType
typeOfSetupValue cc env nameEnv val =
  do let ?lc = cc^.ccTypeCtx
     typeOfSetupValue' cc env nameEnv val

typeOfSetupValue' :: forall m wptr.
  MonadFail m =>
  CrucibleContext wptr ->
  Map AllocIndex (W4.ProgramLoc, Crucible.MemType) ->
  Map AllocIndex Crucible.Ident ->
  SetupValue ->
  m Crucible.MemType
typeOfSetupValue' cc env nameEnv val =
  case val of
    SetupVar i ->
      case Map.lookup i env of
        Nothing -> fail ("typeOfSetupValue: Unresolved prestate variable:" ++ show i)
        Just (_,memTy) -> return (Crucible.PtrType (Crucible.MemType memTy))
    SetupTerm tt ->
      case ttSchema tt of
        Cryptol.Forall [] [] ty ->
          case toLLVMType dl (Cryptol.evalValType Map.empty ty) of
            Left err -> fail (toLLVMTypeErrToString err)
            Right memTy -> return memTy
        s -> fail $ unlines [ "typeOfSetupValue: expected monomorphic term"
                            , "instead got:"
                            , show (Cryptol.pp s)
                            ]
    SetupStruct packed vs ->
      do memTys <- traverse (typeOfSetupValue cc env nameEnv) vs
         let si = Crucible.mkStructInfo dl packed memTys
         return (Crucible.StructType si)
    SetupArray [] -> fail "typeOfSetupValue: invalid empty crucible_array"
    SetupArray (v : vs) ->
      do memTy <- typeOfSetupValue cc env nameEnv v
         _memTys <- traverse (typeOfSetupValue cc env nameEnv) vs
         -- TODO: check that all memTys are compatible with memTy
         return (Crucible.ArrayType (fromIntegral (length (v:vs))) memTy)
    SetupField v n -> do
      i <- resolveSetupFieldIndexOrFail cc env nameEnv v n
      typeOfSetupValue' cc env nameEnv (SetupElem v i)
    SetupElem v i ->
      do memTy <- typeOfSetupValue cc env nameEnv v
         let msg = "typeOfSetupValue: crucible_elem requires pointer to struct or array"
         case memTy of
           Crucible.PtrType symTy ->
             case let ?lc = lc in Crucible.asMemType symTy of
               Right memTy' ->
                 case memTy' of
                   Crucible.ArrayType n memTy''
                     | fromIntegral i < n -> return (Crucible.PtrType (Crucible.MemType memTy''))
                     | otherwise -> fail $ "typeOfSetupValue: array type index out of bounds: " ++ show (i, n)
                   Crucible.StructType si ->
                     case Crucible.siFieldInfo si i of
                       Just fi -> return (Crucible.PtrType (Crucible.MemType (Crucible.fiType fi)))
                       Nothing -> fail $ "typeOfSetupValue: struct type index out of bounds: " ++ show i
                   _ -> fail msg
               Left err -> fail (unlines [msg, "Details:", err])
           _ -> fail msg
    SetupNull ->
      -- We arbitrarily set the type of NULL to void*, because a) it
      -- is memory-compatible with any type that NULL can be used at,
      -- and b) it prevents us from doing a type-safe dereference
      -- operation.
      return (Crucible.PtrType Crucible.VoidType)
    -- A global and its initializer have the same type.
    SetupGlobal            name -> do
      let m = cc^.ccLLVMModule
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
    SetupGlobalInitializer name -> do
      case Map.lookup (L.Symbol name) (Crucible.globalInitMap $ cc^.ccLLVMModuleTrans) of
        Just (g, _) ->
          case let ?lc = lc in Crucible.liftMemType (L.globalType g) of
            Left err -> fail $ unlines [ "typeOfSetupValue: invalid type " ++ show (L.globalType g)
                                       , "Details:"
                                       , err
                                       ]
            Right memTy -> return memTy
        Nothing             -> fail $ "resolveSetupVal: global not found: " ++ name
  where
    lc = cc^.ccTypeCtx
    dl = Crucible.llvmDataLayout lc

-- | Translate a SetupValue into a Crucible LLVM value, resolving
-- references
resolveSetupVal :: forall arch.
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  CrucibleContext arch ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Map AllocIndex (W4.ProgramLoc, Crucible.MemType) ->
  Map AllocIndex Crucible.Ident ->
  SetupValue             ->
  IO LLVMVal
resolveSetupVal cc env tyenv nameEnv val =
  case val of
    SetupVar i
      | Just ptr <- Map.lookup i env -> return (Crucible.ptrToPtrVal ptr)
      | otherwise -> fail ("resolveSetupVal: Unresolved prestate variable:" ++ show i)
    SetupTerm tm -> resolveTypedTerm cc tm
    SetupStruct packed vs -> do
      vals <- mapM (resolveSetupVal cc env tyenv nameEnv) vs
      let tps = map (typeOfLLVMVal dl) vals
      let t = Crucible.mkStructType (V.fromList (mkFields packed dl Crucible.noAlignment 0 tps))
      let flds = case Crucible.storageTypeF t of
                   Crucible.Struct v -> v
                   _ -> error "impossible"
      return $ Crucible.LLVMValStruct (V.zip flds (V.fromList vals))
    SetupArray [] -> fail "resolveSetupVal: invalid empty array"
    SetupArray vs -> do
      vals <- V.mapM (resolveSetupVal cc env tyenv nameEnv) (V.fromList vs)
      let tp = typeOfLLVMVal dl (V.head vals)
      return $ Crucible.LLVMValArray tp vals
    SetupField v n -> do
      i <- resolveSetupFieldIndexOrFail cc tyenv nameEnv v n
      resolveSetupVal cc env tyenv nameEnv (SetupElem v i)
    SetupElem v i ->
      do memTy <- typeOfSetupValue cc tyenv nameEnv v
         let msg = "resolveSetupVal: crucible_elem requires pointer to struct or array"
         delta <- case memTy of
           Crucible.PtrType symTy ->
             case let ?lc = lc in Crucible.asMemType symTy of
               Right memTy' ->
                 case memTy' of
                   Crucible.ArrayType n memTy''
                     | fromIntegral i < n -> return (fromIntegral i * Crucible.memTypeSize dl memTy'')
                   Crucible.StructType si ->
                     case Crucible.siFieldOffset si i of
                       Just d -> return d
                       Nothing -> fail $ "resolveSetupVal: struct type index out of bounds: " ++ show (i, memTy')
                   _ -> fail msg
               Left err -> fail $ unlines [msg, "Details:", err]
           _ -> fail msg
         ptr <- resolveSetupVal cc env tyenv nameEnv v
         case ptr of
           Crucible.LLVMValInt blk off ->
             do delta' <- W4.bvLit sym (W4.bvWidth off) (Crucible.bytesToInteger delta)
                off' <- W4.bvAdd sym off delta'
                return (Crucible.LLVMValInt blk off')
           _ -> fail "resolveSetupVal: crucible_elem requires pointer value"
    SetupNull ->
      Crucible.ptrToPtrVal <$> Crucible.mkNullPointer sym Crucible.PtrWidth
    SetupGlobal name ->
      do let mem = cc^.ccLLVMEmptyMem
         Crucible.ptrToPtrVal <$> Crucible.doResolveGlobal sym mem (L.Symbol name)
    SetupGlobalInitializer name ->
      case Map.lookup (L.Symbol name)
                      (Crucible.globalInitMap $ cc^.ccLLVMModuleTrans) of
        -- There was an error in global -> constant translation
        Just (_, Left e) -> fail e
        Just (_, Right (_, Just v)) ->
          let ?lc = lc
          in Crucible.constToLLVMVal @(Crucible.ArchWidth arch) sym (cc^.ccLLVMEmptyMem) v
        Just (_, Right (_, Nothing)) ->
          fail $ "resolveSetupVal: global has no initializer: " ++ name
        Nothing ->
          fail $ "resolveSetupVal: global not found: " ++ name
  where
    sym = cc^.ccBackend
    lc = cc^.ccTypeCtx
    dl = Crucible.llvmDataLayout lc

resolveTypedTerm ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  CrucibleContext arch ->
  TypedTerm       ->
  IO LLVMVal
resolveTypedTerm cc tm =
  case ttSchema tm of
    Cryptol.Forall [] [] ty ->
      resolveSAWTerm cc (Cryptol.evalValType Map.empty ty) (ttTerm tm)
    _ -> fail "resolveSetupVal: expected monomorphic term"

resolveSAWPred ::
  CrucibleContext wptr ->
  Term ->
  IO (W4.Pred Sym)
resolveSAWPred cc tm =
  Crucible.bindSAWTerm (cc^.ccBackend) W4.BaseBoolRepr tm

resolveSAWTerm ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  CrucibleContext arch ->
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
      Cryptol.TVSeq sz Cryptol.TVBit ->
        case someNat sz of
          Just (Some w)
            | Just LeqProof <- isPosNat w ->
              do sc <- Crucible.saw_ctx <$> readIORef (W4.sbStateManager sym)
                 ss <- basic_ss sc
                 tm' <- rewriteSharedTerm sc ss tm
                 mx <- case getAllExts tm' of
                         [] -> do
                           -- Evaluate in SBV to test whether 'tm' is a concrete value
                           modmap <- scGetModuleMap sc
                           sbv <- SBV.toWord =<< SBV.sbvSolveBasic modmap Map.empty [] tm'
                           return (SBV.svAsInteger sbv)
                         _ -> return Nothing
                 v <- case mx of
                        Just x  -> W4.bvLit sym w x
                        Nothing -> Crucible.bindSAWTerm sym (W4.BaseBVRepr w) tm'
                 Crucible.ptrToPtrVal <$> Crucible.llvmPointer_bv sym v
          _ -> fail ("Invalid bitvector width: " ++ show sz)
      Cryptol.TVSeq sz tp' ->
        do sc    <- Crucible.saw_ctx <$> (readIORef (W4.sbStateManager sym))
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
        do sc <- Crucible.saw_ctx <$> (readIORef (W4.sbStateManager sym))
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
  where
    sym = cc^.ccBackend
    dl = Crucible.llvmDataLayout (cc^.ccTypeCtx)

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

typeOfLLVMVal :: Crucible.DataLayout -> LLVMVal -> Crucible.StorageType
typeOfLLVMVal _dl val =
  case val of
    Crucible.LLVMValInt _bkl bv ->
       Crucible.bitvectorType (Crucible.intWidthSize (fromIntegral (natValue (W4.bvWidth bv))))
    Crucible.LLVMValFloat _ _   -> error "FIXME: typeOfLLVMVal LLVMValFloat"
    Crucible.LLVMValStruct flds -> Crucible.mkStructType (fmap fieldType flds)
    Crucible.LLVMValArray tp vs -> Crucible.arrayType (fromIntegral (V.length vs)) tp
    Crucible.LLVMValZero tp     -> tp
  where
    fieldType (f, _) = (f ^. Crucible.fieldVal, Crucible.fieldPad f)

equalValsPred ::
  CrucibleContext wptr ->
  LLVMVal ->
  LLVMVal ->
  IO (W4.Pred Sym)
equalValsPred cc v1 v2 = go (v1, v2)
  where
  go :: (LLVMVal, LLVMVal) -> IO (W4.Pred Sym)

  go (Crucible.LLVMValInt blk1 off1, Crucible.LLVMValInt blk2 off2)
       | Just Refl <- testEquality (W4.bvWidth off1) (W4.bvWidth off2)
       = do blk_eq <- W4.natEq sym blk1 blk2
            off_eq <- W4.bvEq sym off1 off2
            W4.andPred sym blk_eq off_eq
  --go (Crucible.LLVMValFloat xsz x, Crucible.LLVMValFloat ysz y) | xsz == ysz
  --     = W4.floatEq sym x y -- TODO
  go (Crucible.LLVMValStruct xs, Crucible.LLVMValStruct ys)
       | V.length xs == V.length ys
       = do cs <- mapM go (zip (map snd (toList xs)) (map snd (toList ys)))
            foldM (W4.andPred sym) (W4.truePred sym) cs
  go (Crucible.LLVMValArray _tpx xs, Crucible.LLVMValArray _tpy ys)
       | V.length xs == V.length ys
       = do cs <- mapM go (zip (toList xs) (toList ys))
            foldM (W4.andPred sym) (W4.truePred sym) cs

  go _ = return (W4.falsePred sym)

  sym = cc^.ccBackend
